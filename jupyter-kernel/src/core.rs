// Copyright 2020 The Evcxr Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::connection::Connection;
use crate::control_file;
use crate::jupyter_message::JupyterMessage;
use anyhow::Result;
use json;
use json::JsonValue;
use std;
use std::collections::HashMap;
use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use std::time::Duration;
use zmq;

// Note, to avoid potential deadlocks, each thread should lock at most one mutex at a time.
/// Main server for the kernel.
#[derive(Clone)]
pub(crate) struct Server {
    iopub: Arc<Mutex<Connection>>,
    stdin: Arc<Mutex<Connection>>,
    latest_execution_request: Arc<Mutex<Option<JupyterMessage>>>,
    shutdown_requested_receiver: Arc<Mutex<mpsc::Receiver<(JupyterMessage, Connection)>>>,
    shutdown_requested_sender: Arc<Mutex<mpsc::Sender<(JupyterMessage, Connection)>>>,
}

/// Execution results of the kernel, to be sent to jupyter.
#[derive(Debug)]
pub struct EvalResult {
    pub res: Result<()>,
    pub content_by_mime_type: HashMap<String, String>,
    pub timing: Option<Duration>,
    pub raw_stdout: Option<String>,
    pub raw_stderr: Option<String>,
}

/// A user-provided context for evaluation.
pub struct EvalContext(pub Box<dyn EvalContextImpl>);

/// Metadata about the language this kernel is for.
#[derive(Clone, Debug)]
pub struct MetaData {
    pub language_name: String,
    pub mimetype: String,
    pub file_extension: String,
    pub pygment_lexer: String,
    pub codemirror_mode: String,
}

#[derive(Debug, Clone)]
pub struct CompletionRes {
    pub cursor_start: usize,
    pub cursor_end: usize,
    pub matches: Vec<String>,
}

/// The trait containing methods for evaluation.
pub trait EvalContextImpl {
    /// Evaluate a bit of code.
    fn eval(&mut self, code: &str, execution_count: usize) -> EvalResult;

    /// Metadata for this kernel.
    fn meta(&self) -> MetaData;

    /// Completion request.
    fn completion(&mut self, _s: &str, _i: usize) -> Option<CompletionRes> {
        None
    }

    /// Check if code is complete and ready for evaluation, or if more input
    /// is needed.
    /// - `None`: unknown
    /// - `Some(true)`: complete
    /// - `Some(false)`: incomplete
    fn code_is_complete(&mut self, _s: &str) -> Option<bool> {
        None
    }

    /// Inspect object at given position.
    fn inspect(&mut self, _s: &str, _i: usize) -> Option<String> {
        None
    }

    /// History request.
    fn history(&mut self) -> Option<Vec<String>> {
        None
    }

    // TODO: completion
    // TODO: inspect
}

impl EvalContext {
    /// New eval context.
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce() -> Box<dyn EvalContextImpl>,
    {
        let b = f();
        EvalContext(b)
    }

    /// Obtain metadata.
    pub fn meta(&self) -> MetaData {
        self.0.meta()
    }
}

impl Server {
    pub(crate) fn start(config: &control_file::Control, mut eval: EvalContext) -> Result<()> {
        let meta = eval.0.meta().clone();
        use zmq::SocketType;

        let zmq_context = zmq::Context::new();
        let heartbeat = bind_socket(config, config.hb_port, zmq_context.socket(SocketType::REP)?)?;
        let mut shell_socket = bind_socket(
            config,
            config.shell_port,
            zmq_context.socket(SocketType::ROUTER)?,
        )?;
        let control_socket = bind_socket(
            config,
            config.control_port,
            zmq_context.socket(SocketType::ROUTER)?,
        )?;
        let stdin_socket = bind_socket(
            config,
            config.stdin_port,
            zmq_context.socket(SocketType::ROUTER)?,
        )?;
        let iopub = Arc::new(Mutex::new(bind_socket(
            config,
            config.iopub_port,
            zmq_context.socket(SocketType::PUB)?,
        )?));

        let (shutdown_requested_sender, shutdown_requested_receiver) = mpsc::channel();

        let mut server = Server {
            iopub,
            latest_execution_request: Arc::new(Mutex::new(None)),
            stdin: Arc::new(Mutex::new(stdin_socket)),
            shutdown_requested_receiver: Arc::new(Mutex::new(shutdown_requested_receiver)),
            shutdown_requested_sender: Arc::new(Mutex::new(shutdown_requested_sender)),
        };

        thread::spawn(move || Self::handle_hb(&heartbeat));
        server.start_thread(move |server: Server| server.handle_control(control_socket));

        let mut execution_count = 0;
        loop {
            {
                let recv = server.shutdown_requested_receiver.lock().unwrap();
                if let Ok((message, mut conn_ctrl)) = recv.try_recv() {
                    log::info!("shutdown requested, exiting");
                    message
                        .new_reply()
                        .with_content(object! {"restart" => false})
                        .send(&mut conn_ctrl)?;
                    std::process::exit(0);
                }
            }

            let message = match JupyterMessage::read_poll(&mut shell_socket, 200)? {
                None => continue,
                Some(m) => m,
            };
            log::debug!("recv msg {:?}", message);
            // Processing of every message should be enclosed between "busy" and "idle"
            // see https://jupyter-client.readthedocs.io/en/latest/messaging.html#messages-on-the-shell-router-dealer-channel
            // Jupiter Lab doesn't use the kernel until it received "idle" for kernel_info_request
            message
                .new_message("status")
                .with_content(object! {"execution_state" => "busy"})
                .send(&mut *server.iopub.lock().unwrap())?;
            let idle = message
                .new_message("status")
                .with_content(object! {"execution_state" => "idle"});
            if message.message_type() == "kernel_info_request" {
                message
                    .new_reply()
                    .with_content(kernel_info(&meta))
                    .send(&mut shell_socket)?;
            } else if message.message_type() == "is_complete_request" {
                let code = message.code();
                let r = eval.0.code_is_complete(code);
                let status = match r {
                    None => "unknown",
                    Some(true) => "complete",
                    Some(false) => "incomplete",
                };
                message
                    .new_reply()
                    .with_content(object! {"status" => status})
                    .send(&mut shell_socket)?;
            } else if message.message_type() == "execute_request" {
                // execute here
                execution_count += 1;
                let e = execution_count;
                log::info!("execute request (execution count {})", e);
                let reply = server.handle_execution_requests(&mut eval, e, message)?;
                reply.send(&mut shell_socket)?;
            } else if message.message_type() == "comm_open" {
                message
                    .new_message("comm_close")
                    .with_content(message.get_content().clone())
                    .send(&mut shell_socket)?;
            } else if message.message_type() == "inspect_request" {
                let code = message.code();
                let cursor_pos = message.cursor_pos();
                let res = match eval.0.inspect(code, cursor_pos) {
                    None => {
                        object! {
                            "status" => "ok",
                            "found" => false,
                        }
                    }
                    Some(s) => {
                        object! {
                            "status" => "ok",
                            "found" => true,
                            "data" => object! {
                                "text/plain" => s
                            },
                            "metadata" => HashMap::new(),
                        }
                    }
                };
                message
                    .new_reply()
                    .with_content(res)
                    .send(&mut shell_socket)?
            } else if message.message_type() == "history_request" {
                // TODO
                /*
                type history_request = {
                output : bool;
                raw : bool;
                hist_access_type : string;
                ~hr_session <json name="session"> : int;
                ~start : int;
                ~stop : int;
                n : int;
                ~pattern : string;
                ~unique : bool;
                }
                */

                message
                    .new_reply()
                    .with_content(object! {"history" => array![]})
                    .send(&mut shell_socket)?
            } else if message.message_type() == "complete_request" {
                let code = message.code();
                let cursor_pos = message.cursor_pos();

                if let Some(r) = eval.0.completion(code, cursor_pos) {
                    message
                        .new_reply()
                        .with_content(object! {
                            "status" => "ok",
                            "matches" => r.matches,
                            "cursor_start" => r.cursor_start,
                            "cursor_end" => r.cursor_end,
                            "metadata" => HashMap::new(),
                        })
                        .send(&mut shell_socket)?
                } else {
                    message
                        .new_reply()
                        .with_content(object! {
                            "status" => "error",
                        })
                        .send(&mut shell_socket)?
                }
            } else {
                log::error!(
                    "Got unrecognized message type on shell channel: {}",
                    message.message_type()
                );
            }

            // set status back to `idle`
            idle.send(&mut *server.iopub.lock().unwrap())?;
        }

        //Ok(())
    }

    fn start_thread<F>(&self, body: F)
    where
        F: FnOnce(Server) -> Result<()> + std::marker::Send + 'static,
    {
        let server_clone = self.clone();
        thread::spawn(move || {
            if let Err(error) = body(server_clone) {
                log::error!("{:?}", error);
            }
        });
    }

    fn handle_hb(connection: &Connection) -> Result<()> {
        let mut message = zmq::Message::new();
        let ping: &[u8] = b"ping";
        loop {
            connection.socket.recv(&mut message, 0)?;
            connection.socket.send(ping, 0)?;
        }
    }

    fn handle_execution_requests(
        &mut self,
        eval: &mut EvalContext,
        execution_count: usize,
        message: JupyterMessage,
    ) -> Result<JupyterMessage> {
        // If we want this clone to be cheaper, we probably only need the header, not the
        // whole message.
        *self.latest_execution_request.lock().unwrap() = Some(message.clone());
        let src = message.code();
        message
            .new_message("execute_input")
            .with_content(object! {
                "execution_count" => execution_count,
                "code" => src
            })
            .send(&mut *self.iopub.lock().unwrap())?;
        let r = {
            let evctx = &mut eval.0;
            evctx.eval(src, execution_count)
        };

        if let Some(s) = r.raw_stdout {
            message
                .new_message("stream")
                .with_content(object! { "name" => "stdout", "text" => s})
                .send(&mut self.iopub.lock().unwrap())?;
        }

        if let Some(s) = r.raw_stderr {
            message
                .new_message("stream")
                .with_content(object! { "name" => "stderr", "text" => s})
                .send(&mut self.iopub.lock().unwrap())?;
        }

        let reply = {
            let mut data = HashMap::new();
            let is_ok = match r.res {
                Ok(()) => {
                    for (k, v) in &r.content_by_mime_type {
                        data.insert(k.clone(), json::from(v.clone()));
                    }
                    true
                }
                Err(e) => {
                    data.insert(
                        "text/html".into(),
                        json::from(format!(
                            "<span style=\"color: red\">{}</span>",
                            e.to_string()
                        )),
                    );
                    false
                }
            };

            if let Some(duration) = r.timing {
                let ms = duration.as_millis();
                data.insert(
                    "text/html".into(),
                    json::from(format!(
                        "<span style=\"color: rgba(0,0,0,0.4);\">Took {}ms</span>",
                        ms
                    )),
                );
            };

            message
                .new_message("execute_result")
                .with_content(object! {
                    "execution_count" => execution_count,
                    "data" => data.clone(),
                    "metadata" => HashMap::new(),
                })
                .send(&mut *self.iopub.lock().unwrap())?;

            message.new_reply().with_content(object! {
                "status" => if is_ok { "ok" } else { "error" },
                "execution_count" => execution_count,
                "data" => data,
                "metadata" => HashMap::new(),
            })
        };
        Ok(reply)
    }

    fn request_input(
        &self,
        current_request: &JupyterMessage,
        prompt: &str,
        password: bool,
    ) -> Option<String> {
        if current_request.get_content()["allow_stdin"].as_bool() != Some(true) {
            return None;
        }
        let mut stdin = self.stdin.lock().unwrap();
        let stdin_request = current_request
            .new_reply()
            .with_message_type("input_request")
            .with_content(object! {
                "prompt" => prompt,
                "password" => password,
            });
        stdin_request.send(&mut *stdin).ok()?;

        let input_response = JupyterMessage::read(&mut *stdin).ok()?;
        input_response.get_content()["value"]
            .as_str()
            .map(|value| value.to_owned())
    }

    /// Handle control channel, for interruptions and shutdown.
    fn handle_control(self, mut connection: Connection) -> Result<()> {
        loop {
            let message = JupyterMessage::read(&mut connection)?;
            match message.message_type() {
                "shutdown_request" => {
                    // do not answer here, let main loop do it after it winds down
                    let chan = self.shutdown_requested_sender.lock().unwrap();
                    chan.send((message, connection));
                    return Ok(());
                }
                "interrupt_request" => {
                    message.new_reply().send(&mut connection)?;
                    log::error!("Interrupting execution is not supported. Perhaps restart kernel?");
                }
                _ => {
                    log::error!(
                        "Got unrecognized message type on control channel: {}",
                        message.message_type()
                    );
                }
            }
        }
    }

    fn start_output_pass_through_thread(
        self,
        output_name: &'static str,
        channel: mpsc::Receiver<String>,
    ) {
        thread::spawn(move || {
            while let Ok(line) = channel.recv() {
                let mut message = None;
                if let Some(exec_request) = &*self.latest_execution_request.lock().unwrap() {
                    message = Some(exec_request.new_message("stream"));
                }
                if let Some(message) = message {
                    if let Err(error) = message
                        .with_content(object! {
                            "name" => output_name,
                            "text" => format!("{}\n", line),
                        })
                        .send(&mut *self.iopub.lock().unwrap())
                    {
                        log::error!("{}", error);
                    }
                }
            }
        });
    }

    fn emit_errors(&self, e: &anyhow::Error, parent_message: &JupyterMessage) -> Result<()> {
        parent_message
            .new_message("error")
            .with_content(object! {
                "ename" => "Error",
                "evalue" => e.to_string(),
                //"traceback" => traceback,
            })
            .send(&mut *self.iopub.lock().unwrap())?;
        Ok(())
    }
}

fn bind_socket(
    config: &control_file::Control,
    port: u16,
    socket: zmq::Socket,
) -> Result<Connection> {
    let endpoint = format!("{}://{}:{}", config.transport, config.ip, port);
    socket.bind(&endpoint)?;
    Ok(Connection::new(socket, &config.key)?)
}

/// See [Kernel info documentation](https://jupyter-client.readthedocs.io/en/stable/messaging.html#kernel-info)
fn kernel_info(meta: &MetaData) -> JsonValue {
    object! {
        "protocol_version" => "5.3",
        "implementation" => env!("CARGO_PKG_NAME"),
        "implementation_version" => env!("CARGO_PKG_VERSION"),
        "language_info" => object!{
            "name" => meta.language_name.clone(),
            "version" => "",
            "mimetype" => meta.mimetype.clone(),
            "file_extension" => meta.file_extension.clone(),
            // Pygments lexer, for highlighting Only needed if it differs from the 'name' field.
            // see http://pygments.org/docs/lexers/#lexers-for-the-rust-language
            "pygment_lexer" => meta.pygment_lexer.clone(),
            // Codemirror mode, for for highlighting in the notebook. Only needed if it differs from the 'name' field.
            // codemirror use text/x-rustsrc as mimetypes
            // see https://codemirror.net/mode/rust/
            "codemirror_mode" => meta.codemirror_mode.clone(),
        },
        "banner" => format!("Evaluation context for {}", meta.language_name.clone()),
        "status" => "ok",
    }
}

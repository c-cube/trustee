use {
    std::{
        ffi::{c_void, CStr},
        fmt,
    },
    trustee::{kernel_of_trust as k, meta},
};

mod janet {
    use super::*;
    use janet_ll as j;
    use std::{ffi, ptr, slice};

    #[repr(transparent)]
    #[derive(Clone)]
    pub struct Value(j::Janet);

    #[derive(Debug, Clone)]
    pub enum ValueKind<'a> {
        ABSTRACT,
        ARRAY(&'a [Value]),
        BOOLEAN,
        BUFFER,
        CFUNCTION,
        FIBER,
        FUNCTION,
        KEYWORD(&'a CStr),
        NIL,
        NUMBER(f64),
        POINTER(*const c_void),
        STRING(&'a CStr),
        STRUCT,
        SYMBOL,
        TABLE,
        TUPLE(&'a [Value]),
    }

    fn kind_of_value<'a>(v: j::Janet) -> ValueKind<'a> {
        unsafe {
            match j::janet_type(v) {
                j::JanetType_JANET_ABSTRACT => ValueKind::ABSTRACT,
                j::JanetType_JANET_ARRAY => {
                    let a = &*j::janet_unwrap_array(v);
                    let slice = slice::from_raw_parts(
                        a.data as *const Value,
                        a.count as usize,
                    );
                    ValueKind::ARRAY(slice)
                }
                j::JanetType_JANET_BOOLEAN => ValueKind::BOOLEAN,
                j::JanetType_JANET_BUFFER => ValueKind::BUFFER,
                j::JanetType_JANET_CFUNCTION => ValueKind::CFUNCTION,
                j::JanetType_JANET_FIBER => ValueKind::FIBER,
                j::JanetType_JANET_FUNCTION => ValueKind::FUNCTION,
                j::JanetType_JANET_KEYWORD => {
                    let a = j::janet_unwrap_keyword(v);
                    let s = CStr::from_ptr(a as *const i8);
                    ValueKind::KEYWORD(s)
                }
                j::JanetType_JANET_NIL => ValueKind::NIL,
                j::JanetType_JANET_NUMBER => {
                    let i = j::janet_unwrap_number(v);
                    ValueKind::NUMBER(i)
                }
                j::JanetType_JANET_POINTER => {
                    let v = j::janet_unwrap_pointer(v);
                    ValueKind::POINTER(v)
                }
                j::JanetType_JANET_STRING => {
                    let a = j::janet_unwrap_keyword(v);
                    let s = CStr::from_ptr(a as *const i8);
                    ValueKind::STRING(s)
                }
                j::JanetType_JANET_STRUCT => ValueKind::STRUCT,
                j::JanetType_JANET_SYMBOL => ValueKind::SYMBOL,
                j::JanetType_JANET_TABLE => ValueKind::TABLE,
                j::JanetType_JANET_TUPLE => {
                    let t = j::janet_unwrap_tuple(v);
                    let h = &*j::janet_tuple_head(t);
                    let slice = slice::from_raw_parts(
                        h.data.as_ptr() as *const Value,
                        h.length as usize,
                    );
                    ValueKind::TUPLE(slice)
                }
                i => panic!("unknown janet value kind `{}`", i),
            }
        }
    }

    impl fmt::Debug for Value {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "value({:#?})", self.kind())
        }
    }

    impl Value {
        /// Kind of value.
        pub fn kind(&self) -> ValueKind {
            kind_of_value(self.0)
        }
    }

    /// A janet core environment.
    pub struct VM(*mut j::JanetTable);

    impl Drop for VM {
        fn drop(&mut self) {
            unsafe { j::janet_deinit() }
        }
    }

    impl VM {
        /// New VM.
        pub fn new() -> Self {
            unsafe {
                j::janet_init();
                let ptr =
                    j::janet_core_env(ptr::null::<j::JanetTable>() as *mut _);
                Self(ptr)
            }
        }

        /// Evaluate string.
        pub fn run(&mut self, s: &str) -> trustee::Result<Value> {
            let mut v = j::Janet { i64: 0 };
            let code = unsafe {
                j::janet_dobytes(
                    self.0,
                    s.as_ptr() as *const u8,
                    s.len() as i32,
                    "main".as_ptr() as *const i8,
                    &mut v as *mut _,
                )
            };
            if code == 0 {
                Ok(Value(v))
            } else {
                Err(k::Error::new("janet error"))
            }
        }
    }
}
use janet::VM;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = k::Ctx::new();
    let mut ml = meta::State::new(&mut ctx);

    let mut j = VM::new();

    let mut args = pico_args::Arguments::from_env();
    if args.contains("--hol") {
        ml.run(&"hol_prelude source")?;
    }
    if let Some(x) = args.opt_value_from_str::<&str, String>("--include")? {
        ml.run(&format!(r#""{}" load_file source"#, &x))?;
    }

    let mut rl = rustyline::Editor::<()>::new();
    if rl.load_history(".history.txt").is_err() {
        log::info!("No previous history.");
    }
    // TODO: completion based on dictionary

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());

                log::info!("parse line {:?}", &line);
                match j.run(&line) {
                    Ok(v) => println!("result: ok {:?}", v.kind()),
                    Err(e) => println!("error: {}", e),
                }
                /*
                match ml.run(&line) {
                    Ok(()) => {}
                    Err(e) => {
                        log::error!("err: {}", e);
                    }
                }
                */
            }
            Err(rustyline::error::ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(rustyline::error::ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history(".history.txt").unwrap();

    Ok(())
}

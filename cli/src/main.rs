use trustee::*;

use gumdrop::Options;
use liner::{self, Context as LinerCtx};
use std::io;

#[derive(Options)]
struct Opts {
    #[options(help = "load HOL prelude")]
    load_hol: bool,
    #[options(help = "include given file")]
    include: Vec<String>,
    #[options(help = "do not enter interactive mode")]
    batch: bool,
    #[options(help = "print proofs", default = "true")]
    proofs: bool,
    #[options(help = "print help")]
    help: bool,
}

/// Completion for CLI
struct CliCompleter<'a> {
    ctx: &'a Ctx,
}

impl<'a> liner::Completer for CliCompleter<'a> {
    fn completions(&mut self, start: &str) -> Vec<String> {
        use trustee::meta::lexer::Tok as T;

        let mut last_tok = None;
        let mut off = 0; // offset at which last_tok starts

        {
            let mut lexer = meta::lexer::Lexer::new(start, None);
            loop {
                let t = lexer.cur().clone();
                if t == T::Eof {
                    break;
                }
                last_tok = Some(t);
                off = lexer.offset();
                lexer.next();
            }
        }

        let mut compls: Vec<String> = vec![];

        let token = match last_tok {
            Some(T::Id(pre)) => pre,
            _ => return compls,
        };

        let completion_prefix = {
            // completion will replace `pre`
            let off = off - token.as_bytes().len();
            &start.as_bytes()[..off]
        };

        let mut add_compl = |s: &str| {
            // TODO: instead use `prefix` and restore it afterwards
            let mut buf = vec![];
            buf.extend_from_slice(completion_prefix);
            buf.extend_from_slice(s.as_bytes());
            match std::str::from_utf8(&buf[..]) {
                Ok(s) => compls.push(s.to_string()),
                Err(e) => {
                    log::warn!("non utf8 completion for '{}': {}", s, e);
                }
            }
        };

        for (s, _e) in self.ctx.iter_meta_values() {
            if s.starts_with(token) {
                add_compl(s)
            }
        }
        for s in meta::all_builtin_names() {
            if s.starts_with(token) {
                add_compl(s)
            }
        }
        compls
    }
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    trustee::tef::init();
    log::info!("start cli");

    let mut ctx = Ctx::new();
    ctx.enable_proof_recording(true);

    let opts = Opts::parse_args_default_or_exit();

    if opts.load_hol {
        meta::load_prelude_hol(&mut ctx)?;
    }

    ctx.set_meta_value("print_full_traces", false.into());
    let mut vm = meta::VM::new(&mut ctx);
    let mut out = |s: &str| println!("{}", s);
    vm.set_stdout(&mut out);

    for x in &opts.include {
        let file_content = std::fs::read_to_string(x)?;
        vm.run(&file_content, None)?;
    }

    let mut rl = LinerCtx::new();
    if rl
        .history
        .set_file_name_and_load_history(".history.txt")
        .is_err()
    {
        log::info!("No previous history.");
    }
    rl.history.append_duplicate_entries = false;
    rl.history.set_max_file_size(32 * 1024 * 1024);

    if opts.batch {
        return Ok(());
    }

    loop {
        let mut compl = CliCompleter { ctx: vm.ctx };
        let readline = rl.read_line("> ", None, &mut compl);
        match readline {
            Ok(line) => {
                log::info!("parse line {:?}", &line);

                match vm.run(&line, None) {
                    Ok(meta::Value::Nil) => {}
                    Ok(meta::Value::Thm(th)) => {
                        println!("  {:?}", th);
                        if opts.proofs {
                            if let Some(spr) = trustee::proof::print_proof::proof_to_string(&th) {
                                println!("proof:\n{}", spr);
                            }
                        }
                    }
                    Ok(v) => {
                        println!("  {}", v);
                    }
                    Err(e) => {
                        log::error!("err: {}", e);
                    }
                }
                rl.history.push(line.into())?;
            }
            //Err(liner::error::ReadlineError::Interrupted) => {
            //    println!("CTRL-C");
            //    break;
            //}
            Err(e) => match e.kind() {
                io::ErrorKind::Interrupted => continue,
                io::ErrorKind::UnexpectedEof => {
                    println!("CTRL-D");
                    break;
                }
                _ => {
                    println!("Error: {:?}", e);
                    break;
                }
            },
        }
    }

    rl.history.commit_to_file();

    Ok(())
}

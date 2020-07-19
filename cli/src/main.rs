use trustee::*;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = Ctx::new();

    let mut args = pico_args::Arguments::from_env();
    if args.contains("--hol") {
        meta::load_prelude_hol(&mut ctx)?;
    }

    let mut vm = meta::VM::new(&mut ctx);
    if let Some(x) = args.opt_value_from_str::<&str, String>("--include")? {
        vm.run(&format!(r#"(eval (load_file "{}"))"#, &x))?;
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
                match vm.run(&line) {
                    Ok(meta::Value::Nil) => {}
                    Ok(v) => {
                        println!("> {}", v);
                    }
                    Err(e) => {
                        log::error!("err: {}", e);
                    }
                }
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

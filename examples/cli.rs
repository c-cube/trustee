use trustee::*;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = Ctx::new();
    let mut ml = meta::State::new(&mut ctx);

    let mut args = pico_args::Arguments::from_env();
    if args.contains("--load-hol") {
        ml.run(&"prelude_hol load")?;
    }
    if args.contains("--include") {
        let x: String = args.value_from_str("--include")?;
        ml.run(&format!("/{:?} load", x))?;
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
                match ml.run(&line) {
                    Ok(()) => {}
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

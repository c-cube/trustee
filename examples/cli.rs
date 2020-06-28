use trustee::*;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = Ctx::new();

    let mut args = pico_args::Arguments::from_env();
    if args.contains("--load-hol") {
        syntax::parse_statement(&mut ctx, "load_hol.")?;
    }
    if args.contains("--include") {
        let x: String = args.value_from_str("--include")?;
        syntax::parse_statement(&mut ctx, &format!("include {:?}.", x))?;
    }

    let mut rl = rustyline::Editor::<()>::new();
    if rl.load_history(".history.txt").is_err() {
        log::info!("No previous history.");
    }
    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());

                log::info!("parse line {:?}", &line);
                match syntax::parse_statements(&mut ctx, &line) {
                    Ok(res) => {
                        for x in res {
                            println!("got: {:#?}", x)
                        }
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

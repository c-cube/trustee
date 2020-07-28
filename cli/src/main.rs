use trustee::*;

use gumdrop::Options;

#[derive(Options)]
struct Opts {
    #[options(help = "load HOL prelude")]
    load_hol: bool,
    #[options(help = "include given file")]
    include: Vec<String>,
    #[options(help = "do not enter interactive mode")]
    batch: bool,
    #[options(help = "print help")]
    help: bool,
}

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = Ctx::new();

    let opts = Opts::parse_args_default_or_exit();

    if opts.load_hol {
        meta::load_prelude_hol(&mut ctx)?;
    }

    let mut vm = meta::VM::new(&mut ctx);
    for x in &opts.include {
        let file_content = std::fs::read_to_string(x)?;
        vm.run(&file_content)?;
    }

    let mut rl = rustyline::Editor::<()>::new();
    if rl.load_history(".history.txt").is_err() {
        log::info!("No previous history.");
    }
    // TODO: completion based on dictionary

    if opts.batch {
        return Ok(());
    }

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_str());

                log::info!("parse line {:?}", &line);
                match vm.run(&line) {
                    Ok(meta::Value::Nil) => {}
                    Ok(v) => {
                        println!("  {}", v);
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

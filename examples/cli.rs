use std::io::{BufRead, Write};
use trustee::*;

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = Ctx::new();
    let stdin = std::io::stdin();
    let stdin = &mut stdin.lock();
    let stdout = std::io::stdout();
    let stdout = &mut stdout.lock();
    let mut buf = String::new();
    loop {
        write!(stdout, "> ")?;
        stdout.flush()?;
        let n = stdin.read_line(&mut buf)?;
        if n == 0 {
            break;
        }
        log::info!("parse line {:?}", &buf);
        match syntax::parse_statements(&mut ctx, &buf) {
            Ok(res) => {
                for x in res {
                    println!("got: {:#?}", x)
                }
            }
            Err(e) => {
                log::error!("err: {}", e);
            }
        }
        buf.clear();
    }
    Ok(())
}

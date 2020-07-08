#[macro_use]
extern crate log;
use std::{env::args, fs::File, io::BufReader};
use trustee::*;
use trustee_opentheory as open_theory;

struct LogCB;

impl open_theory::Callbacks for LogCB {
    fn debug<F>(&mut self, f: F)
    where
        F: Fn() -> String,
    {
        debug!("{}", f());
    }
}

fn parse_all() -> trustee::Result<()> {
    let mut ctx = Ctx::new();
    let mut vm = open_theory::VM::new_with(&mut ctx, LogCB);
    for f in args().skip(1) {
        info!("# parsing file {:?}", f);
        let file =
            File::open(f).map_err(|e| Error::new_string(format!("{:?}", e)))?;
        let mut read = BufReader::new(file);
        vm.parse_str(&mut read)?;
    }
    info!("done parsing!");
    let article = vm.into_article();
    info!("article: {}", &article);
    info!("success!");

    Ok(())
}
fn main() {
    env_logger::init();
    match parse_all() {
        Ok(()) => (),
        Err(s) => {
            eprintln!("error: {}", s);
            std::process::exit(1)
        }
    }
}

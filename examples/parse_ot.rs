use std::{env::args, fs::File, io::BufReader};
use trustee::*;

fn parse_all() -> Result<(), String> {
    let mut em = ExprManager::new();
    let mut vm = open_theory::VM::new(&mut em);
    for f in args().skip(1) {
        eprintln!("# parsing file {:?}", f);
        let file = File::open(f).map_err(|e| format!("{:?}", e))?;
        let mut read = BufReader::new(file);
        vm.parse_str(&mut read)?;
    }
    println!("done parsing!");
    let article = vm.into_article();
    println!("article: {:#?}", &article);

    Ok(())
}
fn main() {
    match parse_all() {
        Ok(()) => (),
        Err(s) => {
            eprintln!("error: {}", s);
            std::process::exit(1)
        }
    }
}

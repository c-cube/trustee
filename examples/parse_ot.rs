use std::{
    env::args,
    fs::File,
    io::{BufRead, BufReader},
};
use trustee::*;

fn main() -> Result<(), String> {
    let mut vm = open_theory::VM::new();
    for f in args().skip(1) {
        eprintln!("# parsing file {:?}", f);
        let file = File::open(f).map_err(|e| format!("{:?}", e))?;
        let mut read = BufReader::new(file);
        vm.parse_str(&mut read)?;
    }
    println!("done parsing!");
    println!("article: {:?}", vm.into_article());

    Ok(())
}

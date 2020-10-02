//! # Proof parser

use anyhow::{anyhow, Result};
use trustee::{proof::parse_proof, Ctx};

fn main() -> Result<()> {
    env_logger::init();

    let mut ctx = Ctx::new();
    let mut p = parse_proof::Parser::new(&mut ctx);
    {
        let stdin = std::io::stdin();
        p.parse(&mut stdin.lock())?;
    }
    println!("done");
    Ok(())
}

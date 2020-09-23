use gumdrop::Options;
use std::{collections::HashMap, fs::File, io::BufReader};
use trustee::*;
use trustee_opentheory as open_theory;

/// Logger.
struct LogCB {
    store_proof: bool,
    thms: HashMap<String, Thm>,
    proof: Vec<u8>,
    n: usize,
}

impl<'a> open_theory::Callbacks for &'a mut LogCB {
    fn debug<F>(&mut self, f: F)
    where
        F: Fn() -> String,
    {
        log::debug!("{}", f());
    }

    fn on_add_thm(&mut self, th: Thm) -> Thm {
        use {
            kernel::{Proof, ProofView},
            std::io::Write,
        };

        let name = format!("th-{}", self.n);
        self.n += 1;

        write!(&mut self.proof, "(set {} ", name).unwrap();
        th.print_proof(false, &mut self.proof).unwrap();
        writeln!(&mut self.proof, ")").unwrap();

        // update proof
        let newpr = Proof::new(ProofView::GetThm(name.into()));
        let th = th.set_proof(newpr);
        th
    }
}

#[derive(Options)]
struct Opts {
    #[options(free, help = "files to parse")]
    files: Vec<String>,
    #[options(short = "o", help = "produce proof into that file")]
    dump_proof: Option<String>,
    #[options(help = "display help")]
    help: bool,
}

fn parse_all(opt: Opts) -> trustee::Result<()> {
    let mut ctx = Ctx::new();
    if opt.dump_proof.is_some() {
        ctx.enable_proof_recording(true);
    }

    let mut cb = LogCB {
        store_proof: opt.dump_proof.is_some(),
        thms: HashMap::new(),
        proof: vec![],
        n: 0,
    };

    let mut vm = open_theory::VM::new_with(&mut ctx, &mut cb);
    for f in opt.files {
        trustee::tefbegin!("ot.parse-file");
        log::info!("# parsing file {:?}", f);
        let file = File::open(f).map_err(|e| Error::new_string(format!("{:?}", e)))?;
        let mut read = BufReader::new(file);
        vm.parse_str(&mut read)?;
    }
    log::info!("done parsing!");

    let (article, cb) = vm.into_article();
    log::info!("article: {}", &article);

    if let Some(file) = &opt.dump_proof {
        log::info!("dump proof into {}", file);
        trustee::tefbegin!("ot.dump-proof");
        std::fs::write(file, &cb.proof)?;
    }

    log::info!("success!");

    Ok(())
}
fn main() {
    env_logger::init();
    trustee::tef::init();

    let opt = Opts::parse_args_default_or_exit();

    match parse_all(opt) {
        Ok(()) => (),
        Err(s) => {
            eprintln!("error: {}", s);
            std::process::exit(1)
        }
    }
}

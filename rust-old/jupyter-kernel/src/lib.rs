// Copyright 2020 The Evcxr Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[macro_use]
extern crate json;

mod connection;
mod control_file;
pub mod core;
pub mod install;
mod jupyter_message;

pub use crate::core::{
    CompletionRes, EvalContext, EvalContextImpl, EvalResult, MetaData,
};

use anyhow::{anyhow, Error};

pub fn run(control_file_name: &str, e: core::EvalContext) -> Result<(), Error> {
    let config = control_file::Control::parse_file(&control_file_name)?;
    core::Server::start(&config, e)?;
    Ok(())
}

pub fn run_main(e: core::EvalContext) -> Result<(), Error> {
    let mut args = std::env::args();
    let bin = args.next().unwrap();
    if let Some(arg) = args.next() {
        match arg.as_str() {
            "--control_file" => {
                let cfile = args
                    .next()
                    .ok_or_else(|| anyhow!("Missing control file"))?;
                return run(&cfile, e);
            }
            "--install" => return install::install(&e.0.meta()),
            "--uninstall" => return install::uninstall(&e.0.meta()),
            "--help" => {}
            x => return Err(anyhow!("Unrecognised option {}", x)),
        }
    }
    println!("To install, run:\n  {} --install", bin);
    println!("To uninstall, run:\n  {} --uninstall", bin);
    Ok(())
}

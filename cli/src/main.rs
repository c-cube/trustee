use trustee::{kernel_of_trust as k, meta};

mod data {
    use super::*;

    #[derive(Clone)]
    pub struct LExpr(pub k::Expr);

    impl rlua::UserData for LExpr {
        fn add_methods<'lua, T>(meths: &mut T)
        where
            T: rlua::UserDataMethods<'lua, Self>,
        {
            meths.add_method("__tostring", |_, e, ()| Ok(e.0.to_string()));
        }
    }

    #[derive(Clone)]
    pub struct LThm(pub k::Thm);

    impl rlua::UserData for LThm {
        fn add_methods<'lua, T>(meths: &mut T)
        where
            T: rlua::UserDataMethods<'lua, Self>,
        {
            meths.add_method("__tostring", |_, e, ()| Ok(e.0.to_string()));
        }
    }
}
use data::{LExpr, LThm};

fn main() -> anyhow::Result<()> {
    env_logger::init();
    log::info!("start cli");

    let mut ctx = k::Ctx::new();
    let mut ml = meta::State::new(&mut ctx);

    // init: load prelude
    let mut args = pico_args::Arguments::from_env();
    if args.contains("--hol") {
        ml.run(&"hol_prelude source")?;
    }
    if let Some(x) = args.opt_value_from_str::<&str, String>("--include")? {
        ml.run(&format!(r#""{}" load_file source"#, &x))?;
    }

    drop(ml); // no need anymore

    let mut rl = rustyline::Editor::<()>::new();
    if rl.load_history(".history.txt").is_err() {
        log::info!("No previous history.");
    }

    let lua = rlua::Lua::new();

    lua.context(|lua_ctx| -> anyhow::Result<()> {
        // TODO: completion based on dictionary
        //

        let th_assume = |_ctx: rlua::Context, e: LExpr| -> rlua::Result<LThm> {
            let th = ctx
                .thm_assume(e.0)
                .map_err(|_| /* FIXME */ rlua::Error::UserDataTypeMismatch)?;
            Ok(LThm(th))
        };

        lua_ctx.scope(|sc| -> anyhow::Result<()> {
            {
                let e = LExpr(ctx.mk_ty().clone());
                let data = sc.create_static_userdata(e)?;
                lua_ctx.globals().set("ty", data)?;
            }
            {
                let e = LExpr(ctx.mk_bool().clone());
                let data = sc.create_static_userdata(e)?;
                lua_ctx.globals().set("bool", data)?;
            }

            /* FIXME
            {
                let f = sc.create_function(th_assume)?;
                lua_ctx.globals().set("assume", f);
            }
            */

            loop {
                let readline = rl.readline("> ");
                match readline {
                    Ok(line) => {
                        rl.add_history_entry(line.as_str());

                        log::info!("parse line {:?}", &line);
                        let chunk = lua_ctx.load(&line);
                        match chunk.eval::<rlua::Value>() {
                            Ok(x) => {
                                println!("res: {:?}", x);
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
            Ok(())
        })?;
        Ok(())
    })?;
    rl.save_history(".history.txt").unwrap();

    Ok(())
}

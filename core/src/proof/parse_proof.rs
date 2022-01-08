//! # Parse proofs

use {
    crate::{
        errorstr,
        kernel::{self as k, Ctx, Expr, Thm},
        Error, Result,
    },
    smallvec::smallvec,
    std::io::{BufRead, Read},
};

/// The parser state.
pub struct Parser<'a> {
    ctx: &'a mut Ctx,
    slots: Vec<V>,
}

#[derive(Debug, Clone)]
enum V {
    Expr(Expr),
    Thm(Thm),
    Nil,
}

macro_rules! read_str {
    ($tok: expr) => {
        $tok.next().ok_or_else(|| Error::new("expected str"))
    };
}

macro_rules! parse_id {
    ($e: expr) => {
        $e.parse()
            .map_err(|_| Error::new("expected ID to be an int"))
    };
}

macro_rules! read_id {
    ($tok: expr) => {
        $tok.next()
            .ok_or_else(|| Error::new("expected ID"))
            .and_then(|s| parse_id!(s))
    };
}

macro_rules! read_eol {
    ($tok: expr) => {
        if $tok.next().is_some() {
            return Err(Error::new("expected end of line"));
        }
    };
}

impl<'a> Parser<'a> {
    /// New parser.
    pub fn new(ctx: &'a mut Ctx) -> Self {
        Self { ctx, slots: vec![] }
    }

    fn extend_to_(&mut self, i: usize) {
        if i >= self.slots.len() {
            self.slots.resize_with(i + 1, || V::Nil)
        }
    }

    fn set_(&mut self, i: usize, e: impl Into<V>) {
        self.extend_to_(i + 1);
        let v = e.into();
        crate::logtrace!("set slot {} to {:?}", i, v);
        self.slots[i] = v;
    }

    fn get_expr(&self, i: usize) -> Result<Expr> {
        match &self.slots[i] {
            V::Expr(e) => Ok(e.clone()),
            _ => return Err(Error::new("expected an expression in slot")),
        }
    }

    /// Parse the given IO stream.
    pub fn parse(&mut self, io: &mut dyn Read) -> Result<()> {
        let io = std::io::BufReader::new(io);
        for line in io.lines() {
            let line = line?;
            let mut tok = line.split_whitespace();

            match tok.next() {
                None => return Err(Error::new("invalid line")),
                Some("ty") => {
                    let n = read_id!(tok)?;
                    read_eol!(tok);
                    let e = self.ctx.mk_ty();
                    self.set_(n, e);
                }
                Some("bool") => {
                    let n = read_id!(tok)?;
                    read_eol!(tok);
                    let e = self.ctx.mk_bool();
                    self.set_(n, e);
                }
                Some("bv") => {
                    let n = read_id!(tok)?;
                    let idx = read_id!(tok)?;
                    let ty = self.get_expr(read_id!(tok)?)?;
                    let e = self.ctx.mk_bound_var(idx, ty);
                    self.set_(n, e);
                }
                Some("v") => {
                    let n = read_id!(tok)?;
                    let s = read_str!(tok)?;
                    let ty = self.get_expr(read_id!(tok)?)?;
                    let e = self.ctx.mk_var(k::Var { name: s.into(), ty });
                    self.set_(n, e);
                }
                Some("\\") => {
                    let n = read_id!(tok)?;
                    let ty_v = self.get_expr(read_id!(tok)?)?;
                    let bod = self.get_expr(read_id!(tok)?)?;
                    let e = self.ctx.mk_lambda_db(ty_v, bod)?;
                    self.set_(n, e);
                }
                Some("c") => {
                    // FIXME: need to be able to define constants, too
                    let n = read_id!(tok)?;
                    let name = read_str!(tok)?;
                    let c = self
                        .ctx
                        .find_const(name)
                        .cloned()
                        .ok_or_else(|| errorstr!("finding constant `{}` from proof", name))?;
                    let mut args = smallvec![];
                    while let Some(id) = tok.next() {
                        let e = self.get_expr(parse_id!(id)?)?;
                        args.push(e)
                    }
                    let e = self.ctx.mk_const(c, args)?;
                    self.set_(n, e);
                }
                Some("@") => {
                    let n = read_id!(tok)?;
                    let f = self.get_expr(read_id!(tok)?)?;
                    let a = self.get_expr(read_id!(tok)?)?;
                    let e = self.ctx.mk_app(f, a)?;
                    self.set_(n, e);
                }
                Some(cmd) => {
                    return Err(Error::new_string(format!(
                        "unknown command `{}` on line \"{}\"",
                        cmd, line
                    )))
                }
            }

            println!("line: {}", line);
        }
        Ok(())
    }
}

impl From<Expr> for V {
    fn from(e: Expr) -> Self {
        V::Expr(e)
    }
}

impl From<Thm> for V {
    fn from(th: Thm) -> Self {
        V::Thm(th)
    }
}

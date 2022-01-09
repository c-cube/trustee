use {
    super::Const, crate::fnv::FnvHashMap as HM, crate::syntax::Fixity, std::default::Default,
    std::rc::Rc,
};

/// A table storing fixity (precedence) for each constant.
#[derive(Default, Clone)]
pub struct FixityTbl(HM<Const, Fixity>);

impl FixityTbl {
    #[inline]
    pub fn new() -> Self {
        FixityTbl(HM::default())
    }

    #[inline]
    pub fn find_fixity(&self, c: &Const) -> Option<&Fixity> {
        self.0.get(c)
    }

    #[inline]
    pub fn set_fixity(&mut self, c: Const, f: Fixity) {
        self.0.insert(c, f);
    }

    pub fn cleanup(&mut self) {
        self.0.retain(|c, _| {
            let n = Rc::strong_count(&c.0);
            // we have this one strong ref. If it's the only one (ie. n==1)
            // then we can drop it safely.
            n > 1
        });
    }
}

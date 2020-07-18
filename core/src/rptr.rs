//! Refcounted pointer.
//!
//! A lightweight version of `std::rc::Rc`, with only one `u32` counter.

use std::{cell::Cell, fmt::Debug, ops::Deref, ptr, u32};

/// A refcounted pointer.
pub struct RPtr<T>(*const RPtrImpl<T>);

struct RPtrImpl<T> {
    rc: Cell<u32>,
    v: T,
}

macro_rules! get_impl_ref {
    ($p: expr) => {{
        let p: &RPtrImpl<T> = &*$p.0;
        p
    }};
}

impl<T> Clone for RPtr<T> {
    #[inline]
    fn clone(&self) -> Self {
        unsafe {
            let i = get_impl_ref!(self);
            i.rc.set(1 + i.rc.get());
        };
        RPtr(self.0)
    }
}

impl<T> Debug for RPtr<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl<T> std::fmt::Display for RPtr<T>
where
    T: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.deref())
    }
}

impl<T> PartialEq for RPtr<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl<T> Eq for RPtr<T> where T: Eq {}

impl<T> PartialOrd for RPtr<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.deref(), other.deref())
    }
}
impl<T> Ord for RPtr<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(self.deref(), other.deref())
    }
}

impl<T> std::hash::Hash for RPtr<T>
where
    T: std::hash::Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl<T> Drop for RPtr<T> {
    fn drop(&mut self) {
        unsafe {
            let i = get_impl_ref!(self);
            let rc = i.rc.get() - 1;
            i.rc.set(rc);
            if rc == 0 {
                let b = Box::from_raw(self.0 as *mut RPtrImpl<T>);
                drop(b);
                self.0 = ptr::null_mut();
            }
        }
    }
}

impl<T> std::ops::Deref for RPtr<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl<T> std::borrow::Borrow<T> for RPtr<T> {
    fn borrow(&self) -> &T {
        self.deref()
    }
}

impl<T> From<T> for RPtr<T> {
    fn from(x: T) -> Self {
        RPtr::new(x)
    }
}

impl<T> From<&T> for RPtr<T>
where
    T: Clone,
{
    fn from(x: &T) -> Self {
        RPtr::new(x.clone())
    }
}

impl<T> RPtr<T> {
    /// New pointer.
    pub fn new(v: T) -> Self {
        let s = Box::new(RPtrImpl {
            rc: Cell::new(1),
            v,
        });
        let res = RPtr(s.as_ref() as *const _);
        std::mem::forget(s);
        res
    }

    pub fn refcount(&self) -> usize {
        unsafe { get_impl_ref!(self) }.rc.get() as usize
    }

    #[inline]
    pub fn get(&self) -> &T {
        unsafe {
            let p = get_impl_ref!(self);
            &p.v
        }
    }
}

// TODO: some tests
#[cfg(test)]
mod test {
    use super::*;

    #[derive(Debug, Eq, PartialEq, Clone)]
    struct Foo(isize);

    #[test]
    fn test1() {
        let s = RPtr::new(Foo(42));
        let s2 = RPtr::new(Foo(10));
        assert_ne!(s, s2);
        assert_eq!(s.refcount(), 1);
        let ss = s.clone();
        assert_eq!(s, ss);
        assert_eq!(s.refcount(), 2);
        drop(s);
        drop(ss);
    }

    #[test]
    fn test2() {
        let mut v = vec![];
        for i in 0..1000 {
            let s = RPtr::new(Foo(i));
            let s2 = s.clone();
            v.push(s);
            drop(s2)
        }
        let v2: Vec<RPtr<_>> = v.iter().cloned().collect();
        for i in 0..1000 {
            assert_eq!(&v[i], &v2[i]);
        }
    }
}

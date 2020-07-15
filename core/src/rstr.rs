//! Refcounted string.
//!
//! These strings are accessed via a thin pointer and are refcounted
//! with a `u32`. They cannot be bigger than `u32::MAX`.

use std::{cell::Cell, fmt::Debug, ops::Deref, ptr, u32};

/// A refcounted string in one block on the heap.
#[derive(Eq, Ord)]
pub struct RStr(*const RStrImpl);

struct RStrImpl {
    rc: Cell<u32>,
    len: u32,
    data: *const u8,
}

macro_rules! get_impl_ref {
    ($p: expr) => {{
        let p: &RStrImpl = &*$p.0;
        p
    }};
}

impl Clone for RStr {
    #[inline]
    fn clone(&self) -> Self {
        unsafe {
            let i = get_impl_ref!(self);
            i.rc.set(1 + i.rc.get());
        };
        RStr(self.0)
    }
}

impl Debug for RStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.deref() as &str)
    }
}

impl std::fmt::Display for RStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.deref() as &str)
    }
}

impl PartialEq for RStr {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}

impl PartialOrd for RStr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.deref(), other.deref())
    }
}

impl std::hash::Hash for RStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
    }
}

impl Drop for RStr {
    fn drop(&mut self) {
        unsafe {
            let i = get_impl_ref!(self);
            let rc = i.rc.get() - 1;
            i.rc.set(rc);
            if rc == 0 {
                let b = Vec::from_raw_parts(i.data as *mut u8, i.len as usize, i.len as usize);
                drop(b);
                drop(i);
                let b = Box::from_raw(self.0 as *mut RStrImpl);
                drop(b);
                self.0 = ptr::null();
            }
        }
    }
}

impl std::ops::Deref for RStr {
    type Target = str;
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.get()
    }
}

impl std::borrow::Borrow<str> for RStr {
    fn borrow(&self) -> &str {
        self.deref()
    }
}

impl From<&str> for RStr {
    fn from(s: &str) -> Self {
        RStr::from_str(s)
    }
}

impl From<String> for RStr {
    fn from(s: String) -> Self {
        RStr::from_string(s)
    }
}

impl RStr {
    fn from_vec_(v: Vec<u8>) -> Self {
        let s: Box<[u8]> = v.into_boxed_slice();
        let len = s.len();
        if len > u32::MAX as usize {
            panic!("from_str: capacity exceeded");
        }
        let i = Box::new(RStrImpl {
            rc: Cell::new(1),
            len: len as u32,
            data: s.as_ref().as_ptr(),
        });
        std::mem::forget(s);
        let res = RStr(i.as_ref() as *const _);
        std::mem::forget(i);
        res
    }

    /// Copy the given `str` into the heap.
    pub fn from_str(s: &str) -> Self {
        Self::from_vec_(s.as_bytes().to_vec())
    }

    pub fn from_string(s: String) -> Self {
        Self::from_vec_(s.into_bytes())
    }

    pub fn refcount(&self) -> usize {
        unsafe { get_impl_ref!(self) }.rc.get() as usize
    }

    pub fn get(&self) -> &str {
        unsafe {
            let p = get_impl_ref!(self);
            let sl = std::slice::from_raw_parts(p.data, p.len as usize);
            std::str::from_utf8_unchecked(sl)
        }
    }
}

// TODO: some tests
#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test1() {
        let s = RStr::from_str("abcd");
        let s2 = RStr::from_str("foo");
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
            let s = RStr::from_str(&format!("my string {}!", i));
            let s2 = s.clone();
            v.push(s);
            drop(s2)
        }
        let v2: Vec<RStr> = v.iter().cloned().collect();
        for i in 0..1000 {
            assert_eq!(&v[i], &v2[i]);
        }
    }
}

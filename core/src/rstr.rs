//! Refcounted string.
//!
//! These strings are accessed via a thin pointer and are refcounted
//! with a `u32`. They cannot be bigger than `u32::MAX`.

use crate::rptr::RPtr;
use std::{fmt::Debug, ops::Deref, u32};

/// A refcounted string in one block on the heap.
#[derive(Eq, PartialEq, Ord, PartialOrd, Clone)]
pub struct RStr(RPtr<RStrImpl>);

#[derive(Eq, Ord)]
struct RStrImpl {
    len: u32,
    data: *const u8,
}

impl Debug for RStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.get() as &str)
    }
}

impl std::fmt::Display for RStr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.get() as &str)
    }
}

impl PartialEq for RStrImpl {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl PartialOrd for RStrImpl {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        PartialOrd::partial_cmp(self.deref(), other.deref())
    }
}

impl std::hash::Hash for RStr {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.deref().hash(state)
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
        self.get()
    }
}

impl Drop for RStrImpl {
    fn drop(&mut self) {
        unsafe {
            let b = Vec::from_raw_parts(self.data as *mut u8, self.len as usize, self.len as usize);
            drop(b);
        }
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

impl RStrImpl {
    fn from_vec_(v: Vec<u8>) -> Self {
        let s: Box<[u8]> = v.into_boxed_slice();
        let len = s.len();
        if len > u32::MAX as usize {
            panic!("from_str: capacity exceeded");
        }
        let res = RStrImpl {
            len: len as u32,
            data: s.as_ref().as_ptr(),
        };
        std::mem::forget(s);
        res
    }

    /// Copy the given `str` into the heap.
    pub fn from_str(s: &str) -> Self {
        Self::from_vec_(s.as_bytes().to_vec())
    }

    pub fn get(&self) -> &str {
        unsafe {
            let sl = std::slice::from_raw_parts(self.data, self.len as usize);
            std::str::from_utf8_unchecked(sl)
        }
    }
}

impl RStr {
    fn from_vec_(v: Vec<u8>) -> Self {
        RStr(RPtr::new(RStrImpl::from_vec_(v)))
    }

    /// Copy the given `str` into the heap.
    pub fn from_str(s: &str) -> Self {
        RStr(RPtr::new(RStrImpl::from_str(s)))
    }

    pub fn from_string(s: String) -> Self {
        Self::from_vec_(s.into_bytes())
    }

    pub fn refcount(&self) -> usize {
        self.0.refcount()
    }

    pub fn get(&self) -> &str {
        self.0.get().get()
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

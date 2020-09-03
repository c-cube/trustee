//! Errors for Trustee.

use std::fmt;

/// Result type.
pub type Result<T> = std::result::Result<T, Error>;

/// Location in a source file.
pub use crate::meta::Location;

/// Errors that can be returned from the Kernel or the meta-language.
#[derive(Debug, Clone)]
pub struct Error(Box<ErrorImpl>);

#[derive(Debug, Clone)]
pub struct ErrorImpl {
    pub msg: ErrorMsg,
    pub source: Option<Error>,
}

/// An error message.
#[derive(Debug, Clone)]
pub enum ErrorMsg {
    EStatic(&'static str),
    EDyn(String),
    EMeta { loc: Location, msg: String },
}

mod impls {
    use super::*;

    impl std::ops::Deref for Error {
        type Target = ErrorImpl;
        fn deref(&self) -> &Self::Target {
            &*self.0
        }
    }

    impl fmt::Display for Error {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            match &self.msg {
                ErrorMsg::EStatic(msg) => write!(out, "{}", msg),
                ErrorMsg::EDyn(s) => write!(out, "{}", &s),
                ErrorMsg::EMeta { loc, msg } => write!(out, "{} at {}", msg, loc),
            }
        }
    }

    impl std::error::Error for Error {
        fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
            match &self.source {
                None => None,
                Some(p) => Some(&*p),
            }
        }
    }
}

impl Error {
    /// Build a new error.
    pub fn new(msg: &'static str) -> Self {
        Error(Box::new(ErrorImpl {
            msg: ErrorMsg::EStatic(msg),
            source: None,
        }))
    }

    pub fn new_string(msg: String) -> Self {
        Error(Box::new(ErrorImpl {
            msg: ErrorMsg::EDyn(msg.into()),
            source: None,
        }))
    }

    /// New meta-language error.
    pub fn new_meta(msg: String, loc: Location) -> Self {
        Error(Box::new(ErrorImpl {
            msg: ErrorMsg::EMeta { loc, msg },
            source: None,
        }))
    }

    /// Change the source of this error.
    pub fn set_source(&mut self, src: Self) {
        // append at the end of the `source` linked list.
        if let Some(e2) = &mut self.0.source {
            e2.set_source(src)
        } else {
            self.0.source = Some(src);
        }
    }

    pub fn with_source(mut self, src: Self) -> Self {
        self.set_source(src);
        self
    }

    pub fn to_string(&self) -> String {
        format!("{}", self)
    }

    /// Display the error, along with its source if any.
    pub fn to_string_with_src(&self) -> String {
        use std::fmt::Write;

        let mut s = String::new();
        let mut e = self;
        loop {
            write!(&mut s, "{}", e).unwrap();
            if let Some(src) = &e.0.source {
                write!(&mut s, "\nin ").unwrap();
                e = src;
            } else {
                break;
            }
        }
        s
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_size() {
        // errors should be relatively small (one pointer here)
        assert!(std::mem::size_of::<Error>() <= 8);
    }

    #[test]
    fn test_send() {
        let _: &dyn Send = &Error::new("foo");
    }
}

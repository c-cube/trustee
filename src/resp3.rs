//! # RESP3 Protocol.
//!
//! We follow the spec at https://github.com/antirez/RESP3/blob/master/spec.md.
//! This is used to provide a direct API for Trustee to be called from other
//! processes, on stdin/stdout, or across the network.

use std::io;

/// A message being written.
///
/// Given a standard IO writer, one can create a `MsgWriter` around it
/// only for the time taken to write a message.
pub struct MsgWriter<'a> {
    w: &'a mut dyn io::Write,
    /// How many values must be written still
    missing: usize,
}

/// A handle on a streamed string being written.
///
/// This is available only within `MsgWriter::write_streamed_str` and
/// is used to write chunks, with the last chunk of empty size.
/// If no empty chunk is written, one will be added automatically.
pub struct MsgStreamedStringWriter<'a, 'b> {
    w: &'b mut MsgWriter<'a>,
    eof: bool,
}

impl<'a> MsgWriter<'a> {
    /// Create a sender.
    pub fn new(w: &'a mut dyn io::Write) -> Self {
        Self { w, missing: 1 }
    }

    fn consume1_(&mut self) {
        if self.missing == 0 {
            panic!("MsgWriter: all writing already done")
        } else {
            self.missing -= 1;
        }
    }

    /// Write an integer.
    pub fn write_int(&mut self, i: i64) -> io::Result<()> {
        self.consume1_();
        write!(self.w, ":{}\r\n", i)
    }

    /// Write a boolean
    pub fn write_bool(&mut self, b: bool) -> io::Result<()> {
        self.consume1_();
        write!(self.w, "#{}\r\n", if b { 't' } else { 'f' })
    }

    /// Write a string.
    pub fn write_bytes(&mut self, s: &[u8]) -> io::Result<()> {
        self.consume1_();
        if s.len() < 32 && s.iter().all(|c| c.is_ascii_graphic()) {
            // short simple string, on one line
            write!(self.w, "+")?;
            self.w.write(s)?;
            write!(self.w, "\r\n")
        } else {
            // blob
            write!(self.w, "${}\r\n", s.len())?;
            self.w.write(s)?;
            write!(self.w, "\r\n")
        }
    }

    /// Write a string.
    #[inline]
    pub fn write_str(&mut self, s: &str) -> io::Result<()> {
        let s = s.as_bytes();
        self.write_bytes(s)
    }

    /// Write an error.
    pub fn write_err(&mut self, s: &str) -> io::Result<()> {
        let s = s.as_bytes();
        self.consume1_();
        if s.len() < 32 && s.iter().all(|c| c.is_ascii_graphic()) {
            // short simple string, on one line
            write!(self.w, "-")?;
            self.w.write(s)?;
            write!(self.w, "\r\n")
        } else {
            // blob
            write!(self.w, "!{}\r\n", s.len())?;
            self.w.write(s)?;
            write!(self.w, "\r\n")
        }
    }

    /// Write `null`.
    pub fn write_null(&mut self) -> io::Result<()> {
        self.consume1_();
        let _ = self.w.write("_\r\n".as_bytes())?;
        Ok(())
    }

    // TODO: write double
    // TODO: big number
    // TODO: attributes

    /// String to be rendered exactly as is, client side.
    pub fn write_verbatim_str(&mut self, s: &str) -> io::Result<()> {
        debug_assert!(
            s.len() >= 4 && (s.starts_with("txt:") || s.starts_with("mkd:"))
        );
        write!(self.w, "={}\r\n", s.len())?;
        self.w.write(s.as_bytes())?;
        write!(self.w, "\r\n")
    }

    /// Start writing an array of size `size`.
    pub fn write_array(&mut self, size: usize) -> io::Result<()> {
        self.consume1_();
        self.missing += size;
        write!(self.w, "*{}\r\n", size)
    }

    /// Start writing a set of size `size`.
    pub fn write_set(&mut self, size: usize) -> io::Result<()> {
        self.consume1_();
        self.missing += size;
        write!(self.w, "~{}\r\n", size)
    }

    /// Start writing a map of size `size` (`2*size` values total).
    pub fn write_map(&mut self, size: usize) -> io::Result<()> {
        self.consume1_();
        self.missing += 2 * size;
        write!(self.w, "%{}\r\n", size)
    }

    /// Start writing a "push" message of size `size`.
    ///
    /// The first element is a string that indicates what kind of
    /// push message is sent. It is counted in `size`, so `size-1` other
    /// elements must be written after this call.
    pub fn write_push(&mut self, size: usize, first: &str) -> io::Result<()> {
        assert!(size > 0);
        self.consume1_();
        self.missing += size;
        write!(self.w, ">{}\r\n", size)?;
        self.write_str(first)
    }

    pub fn write_streamed_str<F>(&mut self, mut f: F) -> io::Result<()>
    where
        F: for<'b> FnMut(
            &mut MsgStreamedStringWriter<'a, 'b>,
        ) -> io::Result<()>,
    {
        write!(self.w, "$?\r\n")?;
        let mut ssw = MsgStreamedStringWriter { w: self, eof: false };
        f(&mut ssw)?;
        if !ssw.eof {
            ssw.close()?;
        }
        Ok(())
    }

    // TODO: streamed array/map/set?
}

impl<'a, 'b> MsgStreamedStringWriter<'a, 'b> {
    pub fn write_chunk_bytes(&mut self, s: &[u8]) -> io::Result<()> {
        if self.eof {
            panic!("MsgStreamedStringWriter: stream is already finished");
        }
        if s.len() == 0 {
            self.eof = true;
        }
        write!(self.w.w, ";{}\r\n", s.len())?;
        self.w.w.write(s)?;
        write!(self.w.w, "\r\n")
    }

    #[inline]
    pub fn close(&mut self) -> io::Result<()> {
        self.write_chunk_bytes(&[])
    }

    #[inline]
    pub fn write_chunk_str(&mut self, s: &str) -> io::Result<()> {
        self.write_chunk_bytes(s.as_bytes())
    }
}

/// Read event, an atomic event generated by the parser.
#[derive(Debug, Clone)]
pub enum MsgReadEvent<'a> {
    Int(i64),
    Double(f64),
    Bool(bool),
    Null,
    Str(&'a str),
    Blob(&'a [u8]),
    VerbatimStr(&'a str),
    Error(&'a str),
    ArrayStart(Option<usize>),
    ArrayEnd,
    MapStart(Option<usize>),
    MapEnd,
    SetStart(Option<usize>),
    SetEnd,
    PushStart(usize),
    PushEnd(usize),
    StreamedStringStart,
    StreamedStringChunk(&'a [u8]),
    StreamedStringEnd,
}

/// Parser for messages.
///
/// This reader yields a stream of `MsgReadEvent` that, together, compose
/// a whole message.
pub struct MsgReader<'a> {
    r: &'a mut dyn io::BufRead,
    /// Buffer used to read lines.
    buf: String,
    /// how many more events must be read
    missing: usize,
}

impl<'a> MsgReader<'a> {
    /// New reader.
    pub fn new(r: &'a mut dyn io::BufRead) -> Self {
        Self { r, missing: 1, buf: String::new() }
    }

    /// Fetch the next event.
    pub fn next_event(&mut self) -> io::Result<MsgReadEvent> {
        use MsgReadEvent as E;
        let _ = self.r.read_line(&mut self.buf)?;
        todo!() // TODO
                //Ok(E::Null)
    }
}

/// A simple tree representation of a RESP3 Message.
///
/// Using this is less efficient than interpreting messages on the fly, but useful
/// nonetheless for its simplicity or for debugging.
#[derive(Clone, Debug, PartialEq)]
pub enum SimpleMsg {
    Int(i64),
    Bool(bool),
    Double(f64),
    Null,
    Str(String),
    Verbatim(String),
    Error(String),
    Array(Vec<SimpleMsg>),
    Map(Vec<(SimpleMsg, SimpleMsg)>),
    Set(Vec<SimpleMsg>),
    Push(Vec<SimpleMsg>),
    Attribute { attrs: Vec<(SimpleMsg, SimpleMsg)>, sub: Box<SimpleMsg> },
}

impl SimpleMsg {
    /// Simple function to parse the given string.
    pub fn parse_str(s: &[u8]) -> Result<Self, &'static str> {
        todo!() // TODO: visitor + reader
    }
}

/*
impl SimpleMsgVisitor {
    pub fn new() -> Self {
        Self { st: vec![] }
    }

    /// Consume the visitor into the parsed message.
    pub fn into_msg(mut self) -> Result<SimpleMsg, &'static str> {
        if self.st.len() != 1 {
            return Err("SimpleMsgVisitor: expected single value");
        }
        Ok(self.st.pop().unwrap())
    }

    fn push_v(&mut self, v: SimpleMsg) {
        if self.st.is_empty() {
            self.st.push(v)
        } else {
            // TODO
            todo!("push_v")
            //match self.st.last() {
            //    SimpleMsg
            //}
        }
    }
}

impl MsgReadVisitor for SimpleMsgVisitor {
    type Error = &'static str;

    fn on_event(&mut self, e: MsgReadEvent) -> Result<(), Self::Error> {
        use SimpleMsg as M;
        match e {
            MsgReadEvent::Int(i) => self.push_v(M::Int(i)),
            MsgReadEvent::Double(d) => self.push_v(M::Double(d)),
            MsgReadEvent::Bool(_) => todo!(),
            MsgReadEvent::Null => todo!(),
            MsgReadEvent::Str(_) => todo!(),
            MsgReadEvent::Blob(_) => todo!(),
            MsgReadEvent::VerbatimStr(_) => todo!(),
            MsgReadEvent::Error(_) => todo!(),
            MsgReadEvent::ArrayStart(_) => todo!(),
            MsgReadEvent::ArrayEnd => todo!(),
            MsgReadEvent::MapStart(_) => todo!(),
            MsgReadEvent::MapEnd => todo!(),
            MsgReadEvent::SetStart(_) => todo!(),
            MsgReadEvent::SetEnd => todo!(),
            MsgReadEvent::PushStart(_) => todo!(),
            MsgReadEvent::PushEnd(_) => todo!(),
            MsgReadEvent::StreamedStringStart => todo!(),
            MsgReadEvent::StreamedStringChunk(_) => todo!(),
            MsgReadEvent::StreamedStringEnd => todo!(),
        };
        Ok(())
    }
}
*/

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
#[derive(Debug, Clone, Copy, PartialEq)]
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
    MapStart(Option<usize>),
    SetStart(Option<usize>),
    End,
    PushStart(usize),
    StreamedStringStart,
    StreamedStringChunk(&'a [u8]),
    StreamedStringEnd,
}

macro_rules! invdata {
    ($s: expr) => {
        io::Error::new(io::ErrorKind::InvalidData, $s)
    };
}

enum ReaderState<'a> {
    Start,
    Cur(MsgReadEvent<'a>),
    Done,
}

/// Parser for messages.
///
/// This reader yields a stream of `MsgReadEvent` that, together, compose
/// a whole message.
pub struct MsgReader<'a> {
    /// State of the reader.
    st: ReaderState<'a>,
    r: &'a mut dyn io::BufRead,
    /// Buffer used to read lines.
    buf: Vec<u8>,
}

impl<'a> MsgReader<'a> {
    /// read the next line
    fn next_line_(&mut self) -> io::Result<bool> {
        let size = self.r.read_until(b'\n', &mut self.buf)?;
        if size == 0 {
            return Ok(false);
        }
        if size < 2 {
            return Err(invdata!("when reading a new line in resp3"));
        }
        if self.buf[size - 1] != b'\n' || self.buf[size - 2] != b'\r' {
            return Err(invdata!(format!("line must end with \\r\\n")));
        }
        Ok(true)
    }

    fn parse_blob_(&mut self, len: usize) -> io::Result<()> {
        if len > 500 * 1024 * 1024 {
            panic!("blob of size {} is too big", len);
        }
        self.buf.clear();
        self.buf.reserve_exact(len);
        loop {
            let missing = len - self.buf.len();
            if missing == 0 {
                return Ok(());
            }

            let mut slice = self.r.fill_buf()?;
            if slice.len() == 0 {
                return Err(invdata!("not enough data for the blob"));
            } else if slice.len() > missing {
                // trim
                slice = &slice[0..missing];
            }

            self.buf.extend_from_slice(&slice);
        }
    }

    fn parse_event_(&'a mut self) -> io::Result<Option<MsgReadEvent<'a>>> {
        fn parse_int(s: &[u8]) -> io::Result<i64> {
            // parse integer
            let s = std::str::from_utf8(s)
                .map_err(|_| invdata!("expected integer"))?;
            let i =
                s.parse::<i64>().map_err(|_| invdata!("expected integer"))?;
            Ok(i)
        }

        macro_rules! ret {
            ($e: expr) => {
                Ok(Some($e))
            };
        }

        self.buf.clear();
        if !self.next_line_()? {
            return Ok(None);
        }
        let c = self.buf[0];
        match c {
            b'_' if self.buf.len() == 1 => ret!(MsgReadEvent::Null),
            b'#' => match self.buf[1] {
                b't' if self.buf.len() == 2 => ret!(MsgReadEvent::Bool(true)),
                b'f' if self.buf.len() == 2 => ret!(MsgReadEvent::Bool(false)),
                _ => return Err(invdata!("bool must be #t or #f")),
            },
            b':' => {
                // parse integer
                let i = parse_int(&self.buf[1..])?;
                ret!(MsgReadEvent::Int(i))
            }
            b'+' => {
                // simple string
                let s = std::str::from_utf8(&self.buf[1..]).ok().ok_or_else(
                    || invdata!("`+` must be followed by a unicode string"),
                )?;
                ret!(MsgReadEvent::Str(s))
            }
            b'-' => {
                // simple error
                let s = std::str::from_utf8(&self.buf[1..]).ok().ok_or_else(
                    || invdata!("`-` must be followed by a unicode string"),
                )?;
                ret!(MsgReadEvent::Error(s))
            }
            b'$' if self.buf.len() == 2 && self.buf[1] == b'?' => {
                ret!(MsgReadEvent::StreamedStringStart)
            }
            b';' if self.buf.len() == 2 && self.buf[1] == b'0' => {
                ret!(MsgReadEvent::StreamedStringEnd)
            }
            b'$' | b';' | b'!' => {
                // some form of blob string
                let len = parse_int(&self.buf[1..])?;
                self.parse_blob_(len as usize)?;
                let blob = &self.buf[..];
                let ev = if c == b'$' {
                    MsgReadEvent::Blob(blob)
                } else if c == b'!' {
                    let err =
                        std::str::from_utf8(blob).ok().ok_or_else(|| {
                            invdata!("`!` must be followed by a unicode string")
                        })?;
                    MsgReadEvent::Error(err)
                } else {
                    MsgReadEvent::StreamedStringChunk(blob)
                };
                ret!(ev)
            }
            b'*' if self.buf.len() == 2 && self.buf[1] == b'?' => {
                ret!(MsgReadEvent::ArrayStart(None))
            }
            b'*' => {
                // array
                let len = parse_int(&self.buf[1..])?;
                ret!(MsgReadEvent::ArrayStart(Some(len as usize)))
            }
            b'>' => {
                // push
                let len = parse_int(&self.buf[1..])?;
                ret!(MsgReadEvent::PushStart(len as usize))
            }
            b'%' if self.buf.len() == 2 && self.buf[1] == b'?' => {
                ret!(MsgReadEvent::MapStart(None))
            }
            b'%' => {
                // map
                let len = parse_int(&self.buf[1..])?;
                ret!(MsgReadEvent::MapStart(Some(len as usize)))
            }
            b'~' if self.buf.len() == 2 && self.buf[1] == b'?' => {
                ret!(MsgReadEvent::SetStart(None))
            }
            b'~' => {
                // set
                let len = parse_int(&self.buf[1..])?;
                ret!(MsgReadEvent::SetStart(Some(len as usize)))
            }
            b'.' => {
                if self.buf.len() != 1 {
                    return Err(invdata!("`.` should be alone on its line"));
                }
                ret!(MsgReadEvent::End)
            }
            // TODO: blob error
            // TODO: verbatim string
            // TODO: push

            // TODO: double
            // TODO: annotation
            c => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("unknown message prefix {:?}", c),
                ));
            }
        }
    }

    /// Discard current event.
    pub fn discard(&mut self) {
        use ReaderState::*;

        match self.st {
            Done | Start => (),
            Cur(..) => self.st = Start,
        }
    }

    /// Get currrent event, possibly parsing it from the reader.
    pub fn get_event<'b: 'a>(
        &'b mut self,
    ) -> io::Result<Option<MsgReadEvent<'b>>> {
        use ReaderState::*;

        match &self.st {
            Done => Ok(None),
            Cur(m) => Ok(Some(*m)),
            Start => {
                let evopt = self.parse_event_()?;
                match evopt {
                    None => {
                        self.st = Done;
                        Ok(None)
                    }
                    Some(m) => {
                        self.st = Cur(m);
                        Ok(Some(m))
                    }
                }
            }
        }
    }

    /// New message reader.
    pub fn new(r: &'a mut dyn io::BufRead) -> Self {
        Self { r, buf: vec![], st: ReaderState::Start }
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
    Blob(Vec<u8>),
    Verbatim(String),
    Error(String),
    Array(Vec<SimpleMsg>),
    Map(Vec<(SimpleMsg, SimpleMsg)>),
    Set(Vec<SimpleMsg>),
    Push(Vec<SimpleMsg>),
    Attribute { attrs: Vec<(SimpleMsg, SimpleMsg)>, sub: Box<SimpleMsg> },
}

fn parse_simple_(r: &mut MsgReader) -> io::Result<SimpleMsg> {
    use MsgReadEvent::*;

    // get current event
    let ev =
        r.get_event()?.ok_or_else(|| invdata!("expected message, got eof"))?;

    macro_rules! ret {
        ($e: expr) => {{
            r.discard();
            return Ok($e);
        }};
    }

    match ev {
        Int(i) => ret!(SimpleMsg::Int(i)),
        Bool(b) => ret!(SimpleMsg::Bool(b)),
        Null => ret!(SimpleMsg::Null),
        Double(f) => ret!(SimpleMsg::Double(f)),
        Str(s) => ret!(SimpleMsg::Str(s.to_string())),
        VerbatimStr(s) => ret!(SimpleMsg::Verbatim(s.to_string())),
        Error(s) => ret!(SimpleMsg::Error(s.to_string())),
        Blob(s) => ret!(SimpleMsg::Blob(s.iter().copied().collect())),
        ArrayStart(None) => {
            r.discard();
            drop(ev);

            let mut v = vec![];
            loop {
                let ev2 = r
                    .get_event()?
                    .ok_or_else(|| invdata!("eof in the middle of parsing"))?;

                if ev2 == End {
                    let msg = SimpleMsg::Array(v);
                    ret!(msg)
                }

                let sub = parse_simple_(r)?;
                v.push(sub)
            }
        }
        _ => todo!("parse {:?}", ev), // TODO
    }
}

impl SimpleMsg {
    /// Simple function to parse the given string.
    pub fn parse_str(s: &[u8]) -> io::Result<Self> {
        let mut r = s;
        let mr = MsgReader::new(&mut r);
        parse_simple_(&mut mr)
    }
}

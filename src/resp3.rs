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

/// read the next line into `buf`.
fn read_next_line_<'a, 'b>(
    r: &'a mut dyn io::BufRead,
    buf: &'b mut Vec<u8>,
) -> io::Result<bool> {
    let size = r.read_until(b'\n', buf)?;
    if size == 0 {
        return Ok(false);
    }
    if size < 2 {
        return Err(invdata!("when reading a new line in resp3"));
    }
    if buf[size - 1] != b'\n' || buf[size - 2] != b'\r' {
        return Err(invdata!(format!("line must end with \\r\\n")));
    }
    Ok(true)
}

fn parse_blob_<'a, 'b>(
    r: &'a mut dyn io::BufRead,
    buf: &'b mut Vec<u8>,
    len: usize,
) -> io::Result<()> {
    if len > 500 * 1024 * 1024 {
        panic!("blob of size {} is too big", len);
    }
    buf.clear();
    buf.reserve_exact(len);
    loop {
        let missing = len - buf.len();
        if missing == 0 {
            return Ok(());
        }

        let mut slice = r.fill_buf()?;
        if slice.len() == 0 {
            return Err(invdata!("not enough data for the blob"));
        } else if slice.len() > missing {
            // trim
            slice = &slice[0..missing];
        }

        buf.extend_from_slice(&slice);
    }
}

pub fn parse_event_<'a, 'b>(
    r: &'a mut dyn io::BufRead,
    buf: &'b mut Vec<u8>,
) -> io::Result<Option<MsgReadEvent<'b>>> {
    fn parse_int(s: &[u8]) -> io::Result<i64> {
        // parse integer
        let s =
            std::str::from_utf8(s).map_err(|_| invdata!("expected integer"))?;
        let i = s.parse::<i64>().map_err(|_| invdata!("expected integer"))?;
        Ok(i)
    }

    macro_rules! ret {
        ($e: expr) => {
            Ok(Some($e))
        };
    }

    buf.clear();
    if !read_next_line_(r, buf)? {
        return Ok(None);
    }
    let c = buf[0];
    match c {
        b'_' if buf.len() == 1 => ret!(MsgReadEvent::Null),
        b'#' => match buf[1] {
            b't' if buf.len() == 2 => ret!(MsgReadEvent::Bool(true)),
            b'f' if buf.len() == 2 => ret!(MsgReadEvent::Bool(false)),
            _ => return Err(invdata!("bool must be #t or #f")),
        },
        b':' => {
            // parse integer
            let i = parse_int(&buf[1..])?;
            ret!(MsgReadEvent::Int(i))
        }
        b'+' => {
            // simple string
            let s = std::str::from_utf8(&buf[1..]).ok().ok_or_else(|| {
                invdata!("`+` must be followed by a unicode string")
            })?;
            ret!(MsgReadEvent::Str(s))
        }
        b'-' => {
            // simple error
            let s = std::str::from_utf8(&buf[1..]).ok().ok_or_else(|| {
                invdata!("`-` must be followed by a unicode string")
            })?;
            ret!(MsgReadEvent::Error(s))
        }
        b'$' if buf.len() == 2 && buf[1] == b'?' => {
            ret!(MsgReadEvent::StreamedStringStart)
        }
        b';' if buf.len() == 2 && buf[1] == b'0' => {
            ret!(MsgReadEvent::StreamedStringEnd)
        }
        b'$' | b';' | b'!' => {
            // some form of blob string
            let len = parse_int(&buf[1..])?;
            parse_blob_(r, buf, len as usize)?;
            let blob = &buf[..];
            let ev = if c == b'$' {
                MsgReadEvent::Blob(blob)
            } else if c == b'!' {
                let err = std::str::from_utf8(blob).ok().ok_or_else(|| {
                    invdata!("`!` must be followed by a unicode string")
                })?;
                MsgReadEvent::Error(err)
            } else {
                MsgReadEvent::StreamedStringChunk(blob)
            };
            ret!(ev)
        }
        b'*' if buf.len() == 2 && buf[1] == b'?' => {
            ret!(MsgReadEvent::ArrayStart(None))
        }
        b'*' => {
            // array
            let len = parse_int(&buf[1..])?;
            ret!(MsgReadEvent::ArrayStart(Some(len as usize)))
        }
        b'>' => {
            // push
            let len = parse_int(&buf[1..])?;
            ret!(MsgReadEvent::PushStart(len as usize))
        }
        b'%' if buf.len() == 2 && buf[1] == b'?' => {
            ret!(MsgReadEvent::MapStart(None))
        }
        b'%' => {
            // map
            let len = parse_int(&buf[1..])?;
            ret!(MsgReadEvent::MapStart(Some(len as usize)))
        }
        b'~' if buf.len() == 2 && buf[1] == b'?' => {
            ret!(MsgReadEvent::SetStart(None))
        }
        b'~' => {
            // set
            let len = parse_int(&buf[1..])?;
            ret!(MsgReadEvent::SetStart(Some(len as usize)))
        }
        b'.' => {
            if buf.len() != 1 {
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

fn parse_simple_<'a, 'b>(
    r: &'a mut dyn io::BufRead,
    buf: &'b mut Vec<u8>,
    ev: Option<MsgReadEvent<'b>>,
) -> io::Result<SimpleMsg>
where
    'a: 'b,
{
    use MsgReadEvent::*;

    // get current event
    let ev = match ev {
        None => parse_event_(r, buf)?
            .ok_or_else(|| invdata!("expected message, got eof"))?,
        Some(ev) => ev,
    };

    macro_rules! ret {
        ($e: expr) => {{
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
        ArrayStart(Some(n)) => {
            let mut v = vec![];
            for _i in 0..n {
                let ev = parse_simple_(r, buf, None)?;
                v.push(ev)
            }
            ret!(SimpleMsg::Array(v))
        }
        MapStart(Some(n)) => {
            let mut v = vec![];
            for _i in 0..n {
                let x = parse_simple_(r, buf, None)?;
                let y = parse_simple_(r, buf, None)?;
                v.push((x, y))
            }
            ret!(SimpleMsg::Map(v))
        }
        SetStart(Some(n)) => {
            let mut v = vec![];
            for _i in 0..n {
                let ev = parse_simple_(r, buf, None)?;
                v.push(ev)
            }
            ret!(SimpleMsg::Set(v))
        }
        ArrayStart(None) | SetStart(None) => {
            let is_arr = match ev {
                ArrayStart(..) => true,
                _ => false,
            };
            drop(ev);

            let mut v = vec![];
            loop {
                let ev2 = parse_event_(r, buf)?
                    .ok_or_else(|| invdata!("eof in the middle of parsing"))?;

                if ev2 == End {
                    let msg = if is_arr {
                        SimpleMsg::Array(v)
                    } else {
                        SimpleMsg::Set(v)
                    };
                    ret!(msg)
                }

                // NOTE: we should reuse `buf` here, but borrowck is mad at us.
                let mut buf2 = vec![];
                let sub = parse_simple_(r, &mut buf2, Some(ev2))?;
                v.push(sub)
            }
        }
        MapStart(None) => {
            let mut v = vec![];
            loop {
                let ev2 = parse_event_(r, buf)?
                    .ok_or_else(|| invdata!("eof in the middle of parsing"))?;

                if ev2 == End {
                    ret!(SimpleMsg::Map(v))
                }

                let x = parse_simple_(r, buf, None)?;
                let y = parse_simple_(r, buf, None)?;
                v.push((x, y))
            }
        }
        StreamedStringStart => {
            let mut s = vec![];
            loop {
                let ev2 = parse_event_(r, buf)?
                    .ok_or_else(|| invdata!("eof in the middle of parsing"))?;

                match ev2 {
                    StreamedStringEnd => ret!(SimpleMsg::Blob(s)),
                    StreamedStringChunk(v) => s.extend_from_slice(&v[..]),
                    _ => {
                        return Err(invdata!("expected streamed string chunk"))
                    }
                }
            }
        }
        PushStart(..) => todo!("handle push start"), // TODO: implement that? callback?
        End => return Err(invdata!("expected message, not `end`")),
        StreamedStringChunk(..) => {
            return Err(invdata!("expected message, not `end`"))
        }
        StreamedStringEnd => {
            return Err(invdata!("expected message, not `end`"))
        }
    }
}

impl SimpleMsg {
    /// Simple function to parse the given bytestring.
    pub fn parse_bytes(s: &[u8]) -> io::Result<Self> {
        let mut r = s;
        let mut buf = vec![];
        parse_simple_(&mut r, &mut buf, None)
    }

    /// Serialize the message into the given writer.
    pub fn write(&self, w: &mut MsgWriter) -> io::Result<()> {
        match self {
            SimpleMsg::Int(i) => w.write_int(*i),
            SimpleMsg::Bool(b) => w.write_bool(*b),
            SimpleMsg::Null => w.write_null(),
            SimpleMsg::Double(..) => todo!("write double"), // TODO
            SimpleMsg::Str(s) => w.write_str(s),
            SimpleMsg::Blob(b) => w.write_bytes(b),
            SimpleMsg::Verbatim(s) => w.write_verbatim_str(s),
            SimpleMsg::Error(s) => w.write_err(s),
            SimpleMsg::Array(v) => {
                w.write_array(v.len())?;
                for x in v {
                    x.write(w)?;
                }
                Ok(())
            }
            SimpleMsg::Set(v) => {
                w.write_set(v.len())?;
                for x in v {
                    x.write(w)?;
                }
                Ok(())
            }
            SimpleMsg::Map(v) => {
                w.write_map(v.len())?;
                for (x, y) in v {
                    x.write(w)?;
                    y.write(w)?;
                }
                Ok(())
            }
            SimpleMsg::Push(v) => {
                assert!(v.len() > 0);
                match &v[0] {
                    SimpleMsg::Str(s) => w.write_push(v.len(), &s)?,
                    _ => {
                        return Err(invdata!(
                            "first message in a push must be a string"
                        ))
                    }
                }
                for x in &v[1..] {
                    x.write(w)?;
                }
                Ok(())
            }
            SimpleMsg::Attribute { .. } => todo!("write attribute"), // TODO
        }
    }

    /// Serialize to a bytestring.
    pub fn ser_to_bytes(&self) -> io::Result<Vec<u8>> {
        let mut v = vec![];
        let mut msg_w = MsgWriter::new(&mut v);
        self.write(&mut msg_w)?;
        Ok(v)
    }
}

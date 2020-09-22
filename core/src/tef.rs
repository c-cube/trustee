//! # Tracing
//!
//! This uses the Tracing Event Format, or "catapult", accessible from
//! `chrome://tracing` in chromium.

use std::{
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc, Once,
    },
    thread,
    time::{Duration, Instant},
};

#[derive(Debug, Copy, Clone)]
pub enum Case {
    B,
    E,
}

/// An event to log.
struct Event {
    dur: Duration,
    tid: u64,
    case: Case,
    name: &'static str,
}

static START: Once = Once::new();
static ENABLED: AtomicBool = AtomicBool::new(false);

static mut CHAN: Option<mpsc::SyncSender<Event>> = None;

thread_local! {
    // local copy of `CHAN`
    static SEND: mpsc::SyncSender<Event> = {
        #[allow(unsafe_code)]
        let s = unsafe {
            match &CHAN {
                None => unreachable!(),
                Some(c) => c.clone()
            }
        };
        s
    };

    static START_TS: Instant = Instant::now();
}

// logger thread
fn log_thread(c: mpsc::Receiver<Event>) {
    use std::io::Write;

    let mut out = std::fs::File::create("/tmp/trace.json").expect("trace");
    let mut out = std::io::BufWriter::new(&mut out);
    let pid = std::process::id();
    write!(out, "[").expect("trace");

    let mut first = true;
    while let Ok(ev) = c.recv_timeout(std::time::Duration::from_millis(5)) {
        if !first {
            write!(out, ",").unwrap()
        }
        first = false;

        let ph = match ev.case {
            Case::B => "\"B\"",
            Case::E => "\"E\"",
        };
        let dur = ev.dur.as_micros();
        writeln!(
            out,
            r#"{{"ph":{},"pid":{},"tid":{},"ts":{},"name":"{}"}}"#,
            ph, pid, ev.tid, dur, ev.name
        )
        .unwrap();
        out.flush().expect("flush");
    }
    write!(out, "]").expect("write");
    drop(out);
}

// check environment and set variable
#[allow(unsafe_code)]
fn init() {
    let b = std::env::var("TEF")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(false);
    crate::logdebug!("enable tracing: {}", b);
    ENABLED.store(b, Ordering::SeqCst);
    if b {
        let (send, recv) = mpsc::sync_channel(256);
        unsafe {
            let s = &mut CHAN;
            *s = Some(send);
        }
        // start thread after `CHAN` is ready.
        let _th = thread::spawn(|| log_thread(recv));
    }
}

/// Is tracing enabled?
///
/// This is computed once, based on the environment variable "TEF".
#[inline(always)]
pub fn enabled() -> bool {
    START.call_once(|| init());
    ENABLED.load(Ordering::Relaxed)
}

/// Send an event explicitly.
pub fn send_event(case: Case, name: &'static str) {
    let ts0 = START_TS.with(|ts0| ts0.clone());
    let dur = Instant::now().duration_since(ts0);

    let ev = Event {
        case,
        name,
        tid: 0, // FIXME: this is unstable for now
        dur,
    };
    SEND.with(|c| c.send(ev).expect("cannot send TEF event"))
}

/// A RAII guard for closing a duration or other range.
pub struct GuardClose<F: Fn()>(pub Option<F>);

#[macro_export]
macro_rules! tefbegin {
    ($name: expr) => {
        let _guard = if crate::tef::enabled() {
            crate::tef::send_event(crate::tef::Case::B, $name);
            crate::tef::GuardClose(Some(move || {
                crate::tef::send_event(crate::tef::Case::E, $name)
            }))
        } else {
            crate::tef::GuardClose(None)
        };
    };
}

mod impls {
    use super::*;

    impl<F: Fn()> Drop for GuardClose<F> {
        fn drop(&mut self) {
            let mut s = None;
            std::mem::swap(&mut s, &mut self.0); // move out of `self.0`
            if let Some(f) = s {
                f()
            }
        }
    }
}

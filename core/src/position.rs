use std::fmt;

/// Position in the text. 0 based.
#[derive(Clone, Copy, Eq, PartialEq, PartialOrd, Ord)]
pub struct Position {
    pub line: usize,
    pub col: usize,
}

impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[line={}, col={}]", self.line, self.col)
    }
}

impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

impl Position {
    /// Is `self` between the two given positions?
    pub fn between(self, p1: Position, p2: Position) -> bool {
        self >= p1 && self <= p2
    }

    /// Previous column, if any.
    pub fn prev_col(self) -> Self {
        Position {
            col: 1.min(self.col.wrapping_sub(1)),
            ..self
        }
    }
}

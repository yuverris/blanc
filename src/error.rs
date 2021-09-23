#![allow(non_snake_case)]
use crate::source_location::SourceLocation;
#[derive(Debug, Clone)]
pub enum Kind {
    TypeError,
    SyntaxError,
    RuntimeError,
    Overflow,
    Underflow,
    InvalidTypeError,
    Error,
}

#[derive(Debug, Clone)]
pub struct Error {
    pub message: String,
    pub location: SourceLocation,
    pub kind: Kind,
}

impl Error {
    pub fn TypeError(location: SourceLocation, message: String) -> Self {
        Self {
            message,
            location,
            kind: Kind::TypeError,
        }
    }
    pub fn SyntaxError(location: SourceLocation, message: String) -> Self {
        Self {
            message,
            location,
            kind: Kind::SyntaxError,
        }
    }
    pub fn RuntimeError(location: SourceLocation, message: String) -> Self {
        Self {
            message,
            location,
            kind: Kind::RuntimeError,
        }
    }
    pub fn Error(location: SourceLocation, message: String) -> Self {
        Self {
            message,
            location,
            kind: Kind::Error,
        }
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            fmt,
            "in '<{}>', line: {}, column: {}\n{}: {}",
            self.location
                .file
                .as_ref()
                .cloned()
                .unwrap_or_else(|| "unkown".to_string()),
            self.location.line,
            self.location.column,
            self.kind,
            self.message
        )
    }
}

impl std::fmt::Display for Kind {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(fmt, "{:?}", self)
    }
}

impl std::error::Error for Kind {}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.kind)
    }
}

pub(crate) fn format_err(err: Error, input: String) -> String {
    let upper_line = '^';
    let low_line = " ";
    let loc = &err.location;
    let lines: Vec<&str> = input.lines().collect();
    let filled = format!("{}{}", low_line.repeat(loc.column), upper_line);
    // in case the input was a single line
    let index = if loc.line == 1 { 0 } else { loc.line };
    let formatted_input = format!("{}\n{}", lines[index], filled);

    format!("{}\n\n{}", err.to_string(), formatted_input)
}

pub type Result<T> = std::result::Result<T, Error>;

use crate::source_location::SourceLocation;
#[derive(Debug)]
pub enum Error {
    TypeError(SourceLocation, String),
    RuntimeError(SourceLocation, String),
    SyntaxError(SourceLocation, String),
    ParseError(SourceLocation, String),
    Error(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::TypeError(loc, err) => write!(
                fmt,
                "in '{}', line: {}, column: {}\ntype error: {}",
                loc.file.as_ref().unwrap_or(&"<unkown>".to_string()),
                loc.line,
                loc.column,
                err
            ),
            Error::RuntimeError(loc, err) => write!(
                fmt,
                "in '{}', line: {}, column: {}\nruntime error: {}",
                loc.file.as_ref().unwrap_or(&"<unkown>".to_string()),
                loc.line,
                loc.column,
                err
            ),
            Error::SyntaxError(loc, err) => write!(
                fmt,
                "in '{}', line: {}, column: {}\nsyntax error: {}",
                loc.file.as_ref().unwrap_or(&"<unkown>".to_string()),
                loc.line,
                loc.column,
                err
            ),
            Error::ParseError(loc, err) => write!(
                fmt,
                "in '{}', line: {}, column: {}\nparse error: {}",
                loc.file.as_ref().unwrap_or(&"<unkown>".to_string()),
                loc.line,
                loc.column,
                err
            ),
            Error::Error(err) => write!(fmt, "error: {}", err),
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;

//! Error types for the l4yaml crate.

use std::fmt;

/// Errors returned by the l4yaml API.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// YAML syntax error from the verified parser.
    #[error("parse error: {0}")]
    Parse(String),

    /// Security limit exceeded (depth, alias expansion, input size, etc.).
    #[error("limit error: {0}")]
    Limit(String),

    /// Error parsing a YAML config string for `ParserLimits` or `DumpConfig`.
    #[error("config error: {0}")]
    Config(String),

    /// The C library returned an invalid string (non-UTF-8).
    #[error("invalid UTF-8 from C API: {0}")]
    Utf8(#[from] std::str::Utf8Error),

    /// Null pointer where a valid handle was expected.
    #[error("null handle returned by C API")]
    NullHandle,
}

/// Convenience alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Classify a raw error message string into `Parse` or `Limit`.
///
/// The Lean parser prefixes limit errors with "limit:" or "security:" —
/// we match on those heuristically. Everything else is a parse error.
pub(crate) fn classify_error(msg: String) -> Error {
    let lower = msg.to_ascii_lowercase();
    if lower.starts_with("limit:")
        || lower.starts_with("security:")
        || lower.contains("limit exceeded")
        || lower.contains("maximum")
    {
        Error::Limit(msg)
    } else {
        Error::Parse(msg)
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Scalar => write!(f, "scalar"),
            Kind::Sequence => write!(f, "sequence"),
            Kind::Mapping => write!(f, "mapping"),
            Kind::Alias => write!(f, "alias"),
        }
    }
}

/// YAML value node kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Kind {
    Scalar = 0,
    Sequence = 1,
    Mapping = 2,
    Alias = 3,
}

impl Kind {
    pub(crate) fn from_u8(v: u8) -> Self {
        match v {
            0 => Kind::Scalar,
            1 => Kind::Sequence,
            2 => Kind::Mapping,
            3 => Kind::Alias,
            _ => Kind::Scalar, // defensive
        }
    }
}

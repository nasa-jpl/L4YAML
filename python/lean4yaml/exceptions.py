"""Exception types for the lean4yaml verified YAML parser."""


class Lean4YamlError(Exception):
    """Base exception for all lean4yaml errors."""


class ParseError(Lean4YamlError):
    """YAML syntax or grammar error (scanner/parser failure)."""


class LimitError(Lean4YamlError):
    """Security limit exceeded (DoS protection, tag validation).

    Raised when input exceeds configured ParserLimits (alias depth,
    node count, scalar size, tag policy, etc.).
    """


class ConfigError(Lean4YamlError):
    """Error parsing a YAML configuration string for ParserLimits or DumpConfig."""

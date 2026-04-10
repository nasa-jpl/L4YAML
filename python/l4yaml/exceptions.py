"""Exception types for the l4yaml verified YAML parser."""


class L4YAMLError(Exception):
    """Base exception for all l4yaml errors."""


class ParseError(L4YAMLError):
    """YAML syntax or grammar error (scanner/parser failure)."""


class LimitError(L4YAMLError):
    """Security limit exceeded (DoS protection, tag validation).

    Raised when input exceeds configured ParserLimits (alias depth,
    node count, scalar size, tag policy, etc.).
    """


class ConfigError(L4YAMLError):
    """Error parsing a YAML configuration string for ParserLimits or DumpConfig."""

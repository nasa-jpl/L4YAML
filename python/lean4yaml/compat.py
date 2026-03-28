"""PyYAML-compatible API backed by the verified Lean 4 YAML parser.

Drop-in replacements for ``yaml.safe_load`` and ``yaml.safe_load_all``
that return native Python types (``dict``, ``list``, ``str``, ``int``,
``float``, ``bool``, ``None``).

Usage::

    # Before:  import yaml; data = yaml.safe_load(text)
    # After:
    from lean4yaml.compat import safe_load, safe_load_all

    data = safe_load("key: [1, true, null]")
    # → {"key": [1, True, None]}

Parser limits and dump configuration are specified as YAML strings
or file paths, matching lean4yaml's configuration-as-YAML model::

    data = safe_load(text, limits="structural:\\n  maxDepth: 10")
    data = safe_load(text, limits=Path("limits.yaml"))
"""
from __future__ import annotations

import math
from pathlib import Path
from typing import Any, Iterator

from lean4yaml import _ffi
from lean4yaml.exceptions import ConfigError, Lean4YamlError
from lean4yaml.types import YamlDocument, YamlValue

__all__: list[str] = [
    "safe_load",
    "safe_load_all",
    "safe_dump",
    "safe_dump_all",
    "to_python",
]

# ── YAML Core Schema type coercion (YAML 1.2 §10.3.2) ───────────────

_BOOL_TRUE: frozenset[str] = frozenset({"true", "True", "TRUE"})
_BOOL_FALSE: frozenset[str] = frozenset({"false", "False", "FALSE"})
_NULL_VALS: frozenset[str] = frozenset({"null", "Null", "NULL", "~", ""})

_POS_INF: frozenset[str] = frozenset({".inf", ".Inf", ".INF", "+.inf", "+.Inf", "+.INF"})
_NEG_INF: frozenset[str] = frozenset({"-.inf", "-.Inf", "-.INF"})
_NAN_VALS: frozenset[str] = frozenset({".nan", ".NaN", ".NAN"})


def _coerce_scalar(s: str) -> Any:
    """Convert a YAML scalar string to the appropriate Python type.

    Follows the YAML 1.2 Core Schema resolution rules:
    null, bool, int (decimal/octal/hex), float (including inf/nan).
    Unrecognized values remain as ``str``.
    """
    if s in _NULL_VALS:
        return None
    if s in _BOOL_TRUE:
        return True
    if s in _BOOL_FALSE:
        return False

    # Integer: decimal, 0o octal, 0x hex
    if s and s[0] in "+-0123456789":
        try:
            return int(s, 0)
        except (ValueError, TypeError):
            pass

    # Float: inf, nan, and decimal floats
    if s in _POS_INF:
        return math.inf
    if s in _NEG_INF:
        return -math.inf
    if s in _NAN_VALS:
        return math.nan
    if s and s[0] in "+-.0123456789":
        try:
            return float(s)
        except (ValueError, TypeError):
            pass

    return s


# ── Recursive conversion ─────────────────────────────────────────────


def to_python(v: YamlValue) -> Any:
    """Recursively convert a :class:`~lean4yaml.YamlValue` to native Python.

    - Scalars are coerced to ``int``, ``float``, ``bool``, ``None``,
      or ``str`` per the YAML 1.2 Core Schema.
    - Sequences become ``list``.
    - Mappings become ``dict`` (keys are coerced too).
    - Aliases return the raw anchor name as ``str``.
    """
    kind: str = v.kind
    if kind == "scalar":
        return _coerce_scalar(v.as_str())
    if kind == "sequence":
        return [to_python(item) for item in v.as_list()]
    if kind == "mapping":
        return {
            _coerce_scalar(k): to_python(val)
            for k, val in v.items()
        }
    if kind == "alias":
        return v.as_str()
    return None


# ── Input helpers ─────────────────────────────────────────────────────


def _read_input(source: str | bytes | Path | Any) -> str:
    """Accept ``str``, ``bytes``, ``Path``, or file-like objects."""
    if isinstance(source, str):
        return source
    if isinstance(source, bytes):
        return source.decode("utf-8")
    if isinstance(source, Path):
        return source.read_text("utf-8")
    if hasattr(source, "read"):
        data = source.read()
        return data.decode("utf-8") if isinstance(data, bytes) else data
    raise TypeError(
        f"Expected str, bytes, Path, or file-like; got {type(source).__name__}"
    )


def _read_limits_config(limits: str | Path | None) -> str | None:
    """Read a limits config from a YAML string or file path."""
    if limits is None:
        return None
    if isinstance(limits, Path):
        return limits.read_text("utf-8")
    return limits


def _read_dump_config(config: str | Path | None) -> str | None:
    """Read a dump config from a YAML string or file path."""
    if config is None:
        return None
    if isinstance(config, Path):
        return config.read_text("utf-8")
    return config


# ── Parsing helpers (configured) ──────────────────────────────────────


def _load_configured_single(input_str: str, config_yaml: str) -> YamlValue:
    """Parse a single YAML document with custom limits (YAML config)."""
    lib = _ffi.ensure_initialized()
    data: bytes = input_str.encode("utf-8")
    cfg: bytes = config_yaml.encode("utf-8")
    result: int = lib.lean4yaml_parse_configured(
        data, len(data), cfg, len(cfg),
    )
    ok: int = lib.lean4yaml_result_is_ok(result)
    if not ok:
        raw: bytes | None = lib.lean4yaml_result_error_message(result)
        msg: str = raw.decode("utf-8") if raw else "unknown parse error"
        lib.lean4yaml_free(result)
        from lean4yaml.exceptions import LimitError, ParseError
        if "limit" in msg.lower() or "exceeded" in msg.lower():
            raise LimitError(msg)
        raise ParseError(msg)
    # lean4yaml_parse_configured returns a multi-doc result;
    # extract the first document's root value.
    docs_h: int = lib.lean4yaml_result_docs(result)
    count: int = lib.lean4yaml_docs_count(docs_h)
    if count == 0:
        lib.lean4yaml_free(docs_h)
        lib.lean4yaml_free(result)
        raise ParseError("No documents in input")
    dh: int = lib.lean4yaml_docs_get(docs_h, 0)
    val_h: int = lib.lean4yaml_doc_root(dh)
    lib.lean4yaml_free(dh)
    lib.lean4yaml_free(docs_h)
    lib.lean4yaml_free(result)
    return YamlValue(handle=val_h, lib=lib)


def _load_configured_all(
    input_str: str, config_yaml: str,
) -> list[YamlDocument]:
    """Parse a multi-document YAML string with custom limits."""
    lib = _ffi.ensure_initialized()
    data: bytes = input_str.encode("utf-8")
    cfg: bytes = config_yaml.encode("utf-8")
    result: int = lib.lean4yaml_parse_configured(
        data, len(data), cfg, len(cfg),
    )
    ok: int = lib.lean4yaml_result_is_ok(result)
    if not ok:
        raw: bytes | None = lib.lean4yaml_result_error_message(result)
        msg: str = raw.decode("utf-8") if raw else "unknown parse error"
        lib.lean4yaml_free(result)
        from lean4yaml.exceptions import LimitError, ParseError
        if "limit" in msg.lower() or "exceeded" in msg.lower():
            raise LimitError(msg)
        raise ParseError(msg)
    docs_h: int = lib.lean4yaml_result_docs(result)
    count: int = lib.lean4yaml_docs_count(docs_h)
    docs: list[YamlDocument] = []
    for i in range(count):
        dh: int = lib.lean4yaml_docs_get(docs_h, i)
        docs.append(YamlDocument(handle=dh, lib=lib))
    lib.lean4yaml_free(docs_h)
    lib.lean4yaml_free(result)
    return docs


# ── Public API ────────────────────────────────────────────────────────


def safe_load(
    stream: str | bytes | Path | Any,
    *,
    limits: str | Path | None = None,
) -> Any:
    """Parse YAML and return native Python objects.

    Compatible with ``yaml.safe_load()`` — returns ``dict``, ``list``,
    ``str``, ``int``, ``float``, ``bool``, or ``None``.

    Args:
        stream: YAML input as ``str``, ``bytes``, ``Path``, or file-like.
        limits: Optional parser limits as a YAML configuration string
            or a ``Path`` to a YAML config file.  ``None`` uses the
            default limits.

    Returns:
        Native Python object.

    Raises:
        lean4yaml.ParseError: On syntax/grammar errors.
        lean4yaml.LimitError: When a security limit is exceeded.
        lean4yaml.ConfigError: If *limits* YAML is invalid.
    """
    input_str: str = _read_input(stream)
    cfg: str | None = _read_limits_config(limits)
    if cfg is not None:
        v: YamlValue = _load_configured_single(input_str, cfg)
    else:
        from lean4yaml import load
        v = load(input_str)
    return to_python(v)


def safe_load_all(
    stream: str | bytes | Path | Any,
    *,
    limits: str | Path | None = None,
) -> Iterator[Any]:
    """Parse multi-document YAML and yield native Python objects.

    Compatible with ``yaml.safe_load_all()`` — yields one native
    Python object per YAML document.

    Args:
        stream: YAML input as ``str``, ``bytes``, ``Path``, or file-like.
        limits: Optional parser limits as a YAML configuration string
            or a ``Path`` to a YAML config file.

    Yields:
        Native Python objects, one per document.
    """
    input_str: str = _read_input(stream)
    cfg: str | None = _read_limits_config(limits)
    if cfg is not None:
        docs: list[YamlDocument] = _load_configured_all(input_str, cfg)
    else:
        from lean4yaml import load_all
        docs = load_all(input_str)
    for doc in docs:
        yield to_python(doc.root)


def safe_dump(
    data: Any,
    stream: Any | None = None,
    *,
    config: str | Path | None = None,
) -> str | None:
    """Dump a native Python object to YAML.

    Compatible with ``yaml.safe_dump()`` — accepts ``dict``, ``list``,
    ``str``, ``int``, ``float``, ``bool``, ``None``.

    Strategy: serializes the Python object to a minimal YAML string,
    parses it through the verified parser, then dumps it with the
    verified dumper.  This ensures the output is always valid YAML 1.2.2.

    Args:
        data: Python object to serialize.
        stream: Optional file-like object to write to.  If ``None``,
            returns the YAML string.
        config: Optional dump configuration as a YAML string or
            a ``Path`` to a YAML config file.

    Returns:
        YAML string if *stream* is ``None``, otherwise ``None``.
    """
    yaml_str: str = _python_to_yaml(data)
    from lean4yaml import dump, dump_configured, load

    v: YamlValue = load(yaml_str, limits="unlimited")
    cfg: str | None = _read_dump_config(config)
    if cfg is not None:
        result: str = dump_configured(v, config_yaml=cfg)
    else:
        result = dump(v)

    if stream is not None:
        stream.write(result)
        return None
    return result


def safe_dump_all(
    documents: list[Any],
    stream: Any | None = None,
    *,
    config: str | Path | None = None,
) -> str | None:
    """Dump multiple Python objects as a multi-document YAML stream.

    Args:
        documents: List of Python objects to serialize.
        stream: Optional file-like object.
        config: Optional dump config as YAML string or ``Path``.

    Returns:
        YAML string if *stream* is ``None``, otherwise ``None``.
    """
    parts: list[str] = []
    for doc in documents:
        chunk: str | None = safe_dump(doc, config=config)
        if chunk is not None:
            parts.append(chunk)
    result: str = "---\n".join(parts)
    if stream is not None:
        stream.write(result)
        return None
    return result


# ── Python → YAML serialization ──────────────────────────────────────


def _python_to_yaml(obj: Any, indent: int = 0) -> str:
    """Serialize a Python object to a minimal YAML string.

    This is a simple serializer for constructing inputs to the verified
    parser.  It handles the types that ``safe_load`` produces.
    """
    if obj is None:
        return "null"
    if isinstance(obj, bool):
        return "true" if obj else "false"
    if isinstance(obj, int):
        return str(obj)
    if isinstance(obj, float):
        if math.isinf(obj):
            return ".inf" if obj > 0 else "-.inf"
        if math.isnan(obj):
            return ".nan"
        return repr(obj)
    if isinstance(obj, str):
        return _quote_scalar(obj)
    if isinstance(obj, list):
        return _dump_sequence(obj, indent)
    if isinstance(obj, dict):
        return _dump_mapping(obj, indent)
    raise TypeError(f"Cannot serialize {type(obj).__name__} to YAML")


def _quote_scalar(s: str) -> str:
    """Quote a string if it could be misinterpreted as a non-string."""
    if not s:
        return "''"
    # Values that need quoting
    if s in _NULL_VALS or s in _BOOL_TRUE or s in _BOOL_FALSE:
        return f"'{s}'"
    if s in _POS_INF or s in _NEG_INF or s in _NAN_VALS:
        return f"'{s}'"
    # Strings that look like numbers
    try:
        int(s, 0)
        return f"'{s}'"
    except (ValueError, TypeError):
        pass
    try:
        float(s)
        return f"'{s}'"
    except (ValueError, TypeError):
        pass
    # Strings with special YAML characters
    if any(c in s for c in ":#{}[]|>&*!?,\\\"'\n\r\t"):
        # Use double-quoted form for strings with newlines
        if "\n" in s or "\r" in s or "\t" in s:
            escaped = s.replace("\\", "\\\\").replace('"', '\\"')
            escaped = escaped.replace("\n", "\\n").replace("\r", "\\r")
            escaped = escaped.replace("\t", "\\t")
            return f'"{escaped}"'
        return f"'{s}'"
    if s.startswith(("-", "?", " ")) or s.endswith(" "):
        return f"'{s}'"
    return s


def _dump_sequence(items: list[Any], indent: int) -> str:
    """Serialize a list to YAML block sequence."""
    if not items:
        return "[]"
    prefix: str = "  " * indent
    lines: list[str] = []
    for item in items:
        if isinstance(item, (dict, list)) and item:
            child: str = _python_to_yaml(item, indent + 1)
            lines.append(f"{prefix}-\n{child}")
        else:
            lines.append(f"{prefix}- {_python_to_yaml(item, indent + 1)}")
    return "\n".join(lines)


def _dump_mapping(mapping: dict[Any, Any], indent: int) -> str:
    """Serialize a dict to YAML block mapping."""
    if not mapping:
        return "{}"
    prefix: str = "  " * indent
    lines: list[str] = []
    for key, val in mapping.items():
        key_str: str = _quote_scalar(str(key))
        if isinstance(val, (dict, list)) and val:
            child: str = _python_to_yaml(val, indent + 1)
            lines.append(f"{prefix}{key_str}:\n{child}")
        else:
            lines.append(
                f"{prefix}{key_str}: {_python_to_yaml(val, indent + 1)}"
            )
    return "\n".join(lines)

"""l4yaml — Python bindings for the verified Lean 4 YAML parser.

Usage::

    import l4yaml

    value = l4yaml.load("key: value")
    assert value["key"].as_str() == "value"

    docs = l4yaml.load_all("---\\nfirst\\n---\\nsecond")
    assert docs[0].root.as_str() == "first"

    print(l4yaml.dump(value))
"""
from __future__ import annotations

from l4yaml import _ffi
from l4yaml.exceptions import (
    ConfigError,
    L4YAMLError,
    LimitError,
    ParseError,
)
from l4yaml.types import YamlDocument, YamlValue

# Keep this in sync with python/pyproject.toml's `version` field,
# and with the version declarations in lakefile.toml and the rust
# crates.  See "Versioning" in the project README.
__version__ = "0.4.6"

__all__: list[str] = [
    "load",
    "load_all",
    "dump",
    "dump_configured",
    "parse_limits_yaml",
    "YamlValue",
    "YamlDocument",
    "L4YAMLError",
    "ParseError",
    "LimitError",
    "ConfigError",
    "compat",
]

# ── Preset mapping ───────────────────────────────────────────────────

_PRESETS: dict[str, int] = {
    "default": 0,
    "strict": 1,
    "permissive": 2,
    "unlimited": 3,
    "safe_tags": 4,
}


def _resolve_preset(limits: str) -> int:
    """Convert a preset name to the C API uint8 constant."""
    try:
        return _PRESETS[limits]
    except KeyError:
        valid: str = ", ".join(sorted(_PRESETS))
        raise ValueError(
            f"Unknown limits preset {limits!r}; choose from: {valid}"
        ) from None


def _check_result(result: int, lib: object) -> None:
    """Raise ParseError/LimitError if the result handle encodes an error."""
    ok: int = lib.l4yaml_result_is_ok(result)
    if ok:
        return
    raw: bytes | None = lib.l4yaml_result_error_message(result)
    msg: str = raw.decode("utf-8") if raw else "unknown parse error"
    lib.l4yaml_free(result)
    if "limit" in msg.lower() or "exceeded" in msg.lower():
        raise LimitError(msg)
    raise ParseError(msg)


# ── Public API ───────────────────────────────────────────────────────


def load(input: str, *, limits: str = "default") -> YamlValue:
    """Parse a YAML string and return the root value.

    Expects exactly one document.

    Args:
        input: UTF-8 YAML string.
        limits: Preset name — ``"default"``, ``"strict"``,
            ``"permissive"``, ``"unlimited"``, or ``"safe_tags"``.

    Returns:
        The root :class:`YamlValue`.

    Raises:
        ParseError: On syntax/grammar errors.
        LimitError: When a security limit is exceeded.
    """
    lib = _ffi.ensure_initialized()
    preset: int = _resolve_preset(limits)
    data: bytes = input.encode("utf-8")
    result: int = lib.l4yaml_parse_single(data, len(data), preset)
    _check_result(result, lib=lib)
    val_h: int = lib.l4yaml_result_value(result)
    lib.l4yaml_free(result)
    return YamlValue(handle=val_h, lib=lib)


def load_all(input: str, *, limits: str = "default") -> list[YamlDocument]:
    """Parse a multi-document YAML string.

    Args:
        input: UTF-8 YAML string (may contain ``---`` separators).
        limits: Preset name (see :func:`load`).

    Returns:
        List of :class:`YamlDocument` objects.

    Raises:
        ParseError: On syntax/grammar errors.
        LimitError: When a security limit is exceeded.
    """
    lib = _ffi.ensure_initialized()
    preset: int = _resolve_preset(limits)
    data: bytes = input.encode("utf-8")
    result: int = lib.l4yaml_parse(data, len(data), preset)
    _check_result(result, lib=lib)
    docs_h: int = lib.l4yaml_result_docs(result)
    count: int = lib.l4yaml_docs_count(docs_h)
    docs: list[YamlDocument] = []
    for i in range(count):
        dh: int = lib.l4yaml_docs_get(docs_h, i)
        docs.append(YamlDocument(handle=dh, lib=lib))
    lib.l4yaml_free(docs_h)
    lib.l4yaml_free(result)
    return docs


def dump(value: YamlValue) -> str:
    """Dump a :class:`YamlValue` to a YAML string.

    Uses default dump configuration.

    Args:
        value: The YAML value to serialize.

    Returns:
        YAML-formatted string.
    """
    lib = _ffi.ensure_initialized()
    raw: bytes | None = lib.l4yaml_dump(value._handle)
    if raw is None:
        return ""
    return raw.decode("utf-8")


def dump_configured(value: YamlValue, *, config_yaml: str) -> str:
    """Dump a :class:`YamlValue` using a YAML-based dump configuration.

    Args:
        value: The YAML value to serialize.
        config_yaml: YAML string describing the ``DumpConfig``.

    Returns:
        YAML-formatted string.

    Raises:
        ConfigError: If *config_yaml* fails to parse.
    """
    lib = _ffi.ensure_initialized()
    cfg: bytes = config_yaml.encode("utf-8")
    raw: bytes | None = lib.l4yaml_dump_configured(
        value._handle, cfg, len(cfg),
    )
    if raw is None:
        raise ConfigError("dump_configured returned null")
    return raw.decode("utf-8")


def parse_limits_yaml(config_yaml: str) -> int:
    """Parse a YAML string describing ``ParserLimits``.

    Returns an opaque handle suitable for use with
    :func:`l4yaml_parse_configured` (low-level).

    Args:
        config_yaml: YAML string describing parser limits.

    Returns:
        Opaque limits handle (``int``).

    Raises:
        ConfigError: If the YAML cannot be parsed into valid limits.
    """
    lib = _ffi.ensure_initialized()
    cfg: bytes = config_yaml.encode("utf-8")
    result: int = lib.l4yaml_parse_limits_yaml(cfg, len(cfg))
    ok: int = lib.l4yaml_config_is_ok(result)
    if not ok:
        raw: bytes | None = lib.l4yaml_config_error_message(result)
        msg: str = raw.decode("utf-8") if raw else "unknown config error"
        lib.l4yaml_free(result)
        raise ConfigError(msg)
    limits_h: int = lib.l4yaml_config_get_limits(result)
    lib.l4yaml_free(result)
    return limits_h

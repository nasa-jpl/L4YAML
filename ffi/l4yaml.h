/*
 * l4yaml.h — Public C API for the verified YAML parser
 *
 * This header exposes Lean 4's verified YAML parser (lean4-yaml-verified)
 * through a C ABI.  All parsing enforces configurable security limits
 * (DoS protection, tag validation) verified at the type level in Lean 4.
 *
 * Memory model:
 *   All handles (l4yaml_result_t, l4yaml_value_t, etc.) are opaque
 *   pointers to Lean-managed objects.  Call l4yaml_free() when done.
 *   Child handles obtained via accessor functions hold their own reference
 *   and must be freed independently.
 *
 * String lifetime:
 *   Functions returning const char * return a pointer into Lean-managed
 *   memory.  The pointer is valid until the next l4yaml_* call that
 *   returns const char * (from the same thread), or until l4yaml_free()
 *   is called on the owning handle — whichever comes first.  Copy the
 *   string if you need it to outlive either condition.
 *
 * Thread safety:
 *   All calls must originate from the thread that called
 *   l4yaml_initialize(), unless the Lean task manager is initialized
 *   for multi-threaded use.
 *
 * See C_PYTHON_APIs.md for the full design and usage examples.
 */
#ifndef L4YAML_H
#define L4YAML_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ── Opaque handles — callers must not dereference ───────────────── */

typedef void *l4yaml_result_t;
typedef void *l4yaml_value_t;
typedef void *l4yaml_docs_t;
typedef void *l4yaml_doc_t;
typedef void *l4yaml_string_t;

/* ── Limit presets ───────────────────────────────────────────────── */

#define L4YAML_LIMITS_DEFAULT      0
#define L4YAML_LIMITS_STRICT       1
#define L4YAML_LIMITS_PERMISSIVE   2
#define L4YAML_LIMITS_UNLIMITED    3
#define L4YAML_LIMITS_SAFE_TAGS    4

/* ── Node kinds (from l4yaml_value_kind) ──────────────────────── */

#define L4YAML_SCALAR    0
#define L4YAML_SEQUENCE  1
#define L4YAML_MAPPING   2
#define L4YAML_ALIAS     3

/* ── Lifecycle ───────────────────────────────────────────────────── */

/*
 * Initialize the Lean runtime and the l4yaml library.
 * Must be called exactly once before any parsing.
 * If using a fixed-size memory pool, call l4yaml_init_fixed_pool()
 * or l4yaml_init_static_pool() BEFORE this function.
 */
void l4yaml_initialize(void);

/*
 * Finalize the Lean runtime.  Call after all handles have been freed.
 */
void l4yaml_finalize(void);

/* ── Fixed-size memory pool (flight software) ────────────────────── */

/*
 * Option A: OS-backed pool.  Reserves pool_bytes via mmap as an
 * exclusive mimalloc arena, then disables further OS allocation.
 * Returns 0 on success, non-zero on failure.
 * Must be called BEFORE l4yaml_initialize().
 */
int l4yaml_init_fixed_pool(size_t pool_bytes);

/*
 * Option B: Static-buffer pool.  Registers a caller-provided buffer
 * (e.g. a .bss array) as an exclusive mimalloc arena, then disables
 * further OS allocation.  The buffer must be page-aligned (4096).
 * Returns 0 on success, non-zero on failure.
 * Must be called BEFORE l4yaml_initialize().
 */
int l4yaml_init_static_pool(void *buf, size_t buf_bytes);

/* ── Parsing ─────────────────────────────────────────────────────── */

/*
 * Parse a YAML byte string (UTF-8) with the given limit preset.
 * Returns an opaque result handle.  Use l4yaml_result_is_ok() to
 * check success, then l4yaml_result_docs() or
 * l4yaml_result_error_message() to extract the payload.
 */
l4yaml_result_t l4yaml_parse(const char *input, size_t len,
                                   uint8_t preset);

/*
 * Parse expecting exactly one YAML document.  Returns a result handle
 * whose payload is a single YamlValue (use l4yaml_result_value()).
 */
l4yaml_result_t l4yaml_parse_single(const char *input, size_t len,
                                          uint8_t preset);

/* ── Result inspection ───────────────────────────────────────────── */

/*
 * Returns 1 if the parse succeeded (Except.ok), 0 if error.
 * Works for both multi-doc and single-doc results.
 */
uint8_t l4yaml_result_is_ok(l4yaml_result_t r);

/*
 * Extract the error message from a failed result.
 * Returns NULL if the result is actually ok.
 * See "String lifetime" note at the top of this header.
 */
const char *l4yaml_result_error_message(l4yaml_result_t r);

/* ── Multi-document access ───────────────────────────────────────── */

/*
 * Extract the document array from a successful multi-doc result.
 * Caller must free the returned handle.
 * Undefined behavior if called on a single-doc result.
 */
l4yaml_docs_t l4yaml_result_docs(l4yaml_result_t r);

/* Number of documents in the array. */
uint32_t l4yaml_docs_count(l4yaml_docs_t docs);

/* Get the i-th document.  Caller must free the returned handle. */
l4yaml_doc_t l4yaml_docs_get(l4yaml_docs_t docs, uint32_t i);

/* Root YamlValue of a document.  Caller must free. */
l4yaml_value_t l4yaml_doc_root(l4yaml_doc_t doc);

/* ── Single-document access ──────────────────────────────────────── */

/*
 * Extract the YamlValue from a successful single-doc result.
 * Caller must free the returned handle.
 * Undefined behavior if called on a multi-doc result.
 */
l4yaml_value_t l4yaml_result_value(l4yaml_result_t r);

/* ── Value inspection ────────────────────────────────────────────── */

/*
 * Node kind: L4YAML_SCALAR (0), L4YAML_SEQUENCE (1),
 * L4YAML_MAPPING (2), L4YAML_ALIAS (3).
 */
uint8_t l4yaml_value_kind(l4yaml_value_t v);

/*
 * Scalar content as a C string.  Returns "" for non-scalar values.
 * See "String lifetime" note at the top of this header.
 */
const char *l4yaml_value_string(l4yaml_value_t v);

/* Sequence item count.  Returns 0 for non-sequence values. */
uint32_t l4yaml_value_seq_length(l4yaml_value_t v);

/* i-th sequence element.  Caller must free.  Returns null-value if OOB. */
l4yaml_value_t l4yaml_value_seq_get(l4yaml_value_t v, uint32_t i);

/* Mapping pair count.  Returns 0 for non-mapping values. */
uint32_t l4yaml_value_map_length(l4yaml_value_t v);

/* i-th mapping key.  Caller must free. */
l4yaml_value_t l4yaml_value_map_key(l4yaml_value_t v, uint32_t i);

/* i-th mapping value.  Caller must free. */
l4yaml_value_t l4yaml_value_map_val(l4yaml_value_t v, uint32_t i);

/*
 * Look up a mapping key by string content.
 * Returns the associated YamlValue, or NULL if not found / not a mapping.
 * Caller must free a non-NULL result.
 */
l4yaml_value_t l4yaml_value_lookup(l4yaml_value_t v,
                                         const char *key);

/*
 * YAML tag string (e.g. "!!int", "!custom").
 * Returns NULL if no explicit tag.
 * See "String lifetime" note.
 */
const char *l4yaml_value_tag(l4yaml_value_t v);

/*
 * Anchor name (e.g. "anchor1").
 * Returns NULL if no anchor.
 * See "String lifetime" note.
 */
const char *l4yaml_value_anchor(l4yaml_value_t v);

/* ── Dumping ─────────────────────────────────────────────────────── */

/*
 * Dump a YamlValue to a YAML string (default DumpConfig).
 * See "String lifetime" note.
 */
const char *l4yaml_dump(l4yaml_value_t v);

/*
 * Dump an array of YamlDocuments to a YAML string.
 * See "String lifetime" note.
 */
const char *l4yaml_dump_docs(l4yaml_docs_t docs);

/*
 * Dump a YamlValue using a YAML-configured DumpConfig.
 * The config_yaml string is itself parsed (bootstrapping) with strict
 * limits.  Falls back to default DumpConfig on config parse error.
 * See "String lifetime" note.
 */
const char *l4yaml_dump_configured(l4yaml_value_t v,
                                      const char *config_yaml,
                                      size_t config_len);

/* ── Config deserialization (self-hosted) ────────────────────────── */

typedef void *l4yaml_config_result_t;

/*
 * Parse a YAML string into ParserLimits.  The config YAML is parsed
 * using hardcoded strict limits (bootstrapping: the parser parses its
 * own configuration safely).
 *
 * All struct fields are optional — omitted fields use the struct default.
 *
 * Returns an opaque result handle.  Use l4yaml_config_is_ok() and
 * l4yaml_config_error_message() / l4yaml_config_get_limits().
 */
l4yaml_config_result_t l4yaml_parse_limits_yaml(const char *yaml,
                                                      size_t len);

/*
 * Check whether a config parse result succeeded.
 * Returns 1 for success, 0 for error.
 */
uint8_t l4yaml_config_is_ok(l4yaml_config_result_t r);

/*
 * Extract error message from a failed config parse.
 * Returns NULL on success.  See "String lifetime" note.
 */
const char *l4yaml_config_error_message(l4yaml_config_result_t r);

/*
 * Extract the ParserLimits handle from a successful config parse.
 * Caller must free.  Returns default limits on error.
 */
void *l4yaml_config_get_limits(l4yaml_config_result_t r);

/*
 * Parse YAML with custom limits specified as a YAML config string.
 * Two-step bootstrap: parses the config YAML first (strict limits),
 * then parses the input with the resulting ParserLimits.
 * Falls back to default limits on config parse error.
 */
l4yaml_result_t l4yaml_parse_configured(const char *input, size_t len,
                                              const char *config_yaml,
                                              size_t config_len);

/* ── Memory management ───────────────────────────────────────────── */

/*
 * Release an opaque handle (result, value, docs, doc, string).
 * Passing NULL is a no-op.
 */
void l4yaml_free(void *handle);

#ifdef __cplusplus
}
#endif

#endif /* L4YAML_H */

/*
 * lean4yaml_shim.c — C bridge between lean4yaml.h and Lean @[export] symbols
 *
 * This file implements the public C API declared in lean4yaml.h by:
 *   1. Converting const char * ↔ Lean String at the boundary
 *   2. Unwrapping Option types to nullable pointers
 *   3. Managing Lean runtime initialization / finalization
 *   4. Implementing fixed-size memory pool via mimalloc arena API
 *   5. Wrapping lean_dec behind lean4yaml_free
 *
 * Functions whose Lean @[export] name already matches the C header name
 * and whose types are ABI-compatible (opaque handles, uint8/32) are NOT
 * wrapped here — they link directly from the Lean-compiled object files:
 *   lean4yaml_result_is_ok, lean4yaml_result_docs, lean4yaml_result_value,
 *   lean4yaml_docs_count, lean4yaml_docs_get, lean4yaml_doc_root,
 *   lean4yaml_value_kind, lean4yaml_value_seq_length, lean4yaml_value_seq_get,
 *   lean4yaml_value_map_length, lean4yaml_value_map_key, lean4yaml_value_map_val
 *
 * Compile with:
 *   cc -fPIC -c -I$(lean --print-prefix)/include/lean \
 *      ffi/lean4yaml_shim.c -o ffi/lean4yaml_shim.o
 */

#include <lean/lean.h>
#include <string.h>

/* lean_initialize_runtime_module is exported by libleanshared.so but not
   declared in lean.h (Lean 4.28).  Forward-declare it here. */
extern void lean_initialize_runtime_module(void);

/* ── Forward-declare Lean module initializer ─────────────────────── */

extern lean_obj_res initialize_Lean4Yaml(uint8_t builtin, lean_obj_arg);

/* ── Forward-declare Lean @[export] functions (internal names) ───── */

/* Parsing */
extern lean_obj_res lean4yaml_parse_safe(b_lean_obj_arg input, uint8_t preset);
extern lean_obj_res lean4yaml_parse_single_safe(b_lean_obj_arg input,
                                                uint8_t preset);

/* Result / error extraction */
extern lean_obj_res lean4yaml_result_get_error(b_lean_obj_arg result);
extern lean_obj_res lean4yaml_result_single_get_error(b_lean_obj_arg result);

/* Value → String extraction (returns owned Lean String) */
extern lean_obj_res lean4yaml_value_as_string(b_lean_obj_arg val);

/* Value → Option (returns owned Option handle) */
extern lean_obj_res lean4yaml_value_lookup_raw(b_lean_obj_arg val,
                                               b_lean_obj_arg key);
extern lean_obj_res lean4yaml_value_tag_raw(b_lean_obj_arg val);
extern lean_obj_res lean4yaml_value_anchor_raw(b_lean_obj_arg val);

/* Dumping (returns owned Lean String) */
extern lean_obj_res lean4yaml_dump_raw(b_lean_obj_arg val);
extern lean_obj_res lean4yaml_dump_docs_raw(b_lean_obj_arg docs);
extern lean_obj_res lean4yaml_dump_with_yaml_config(b_lean_obj_arg val,
                                                     b_lean_obj_arg config_yaml);

/* Config deserialization */
extern lean_obj_res lean4yaml_parse_limits_yaml_impl(b_lean_obj_arg yaml);
extern lean_obj_res lean4yaml_parse_dump_config_yaml_impl(b_lean_obj_arg yaml);
extern uint8_t      lean4yaml_config_result_is_ok(b_lean_obj_arg result);
extern lean_obj_res lean4yaml_config_result_get_error(b_lean_obj_arg result);
extern lean_obj_res lean4yaml_config_result_get_limits(b_lean_obj_arg result);
extern lean_obj_res lean4yaml_parse_with_yaml_config_impl(b_lean_obj_arg input,
                                                           b_lean_obj_arg config_yaml);
extern lean_obj_res lean4yaml_dump_with_yaml_config_impl(b_lean_obj_arg val,
                                                          b_lean_obj_arg config_yaml);

/* ── Thread-local string holder ──────────────────────────────────── */

/*
 * Every function that returns const char * stores the backing Lean String
 * here so the pointer remains valid until the next such call (or until
 * lean4yaml_free releases the parent handle).
 */
static _Thread_local lean_object *tls_last_string = NULL;

static const char *capture_string(lean_object *s) {
    if (tls_last_string)
        lean_dec(tls_last_string);
    tls_last_string = s;
    return lean_string_cstr(s);
}

/*
 * Extract a Lean Option String:
 *   none (tag 0) → NULL
 *   some s (tag 1) → capture_string(s)
 */
static const char *extract_option_string(lean_object *opt) {
    if (lean_ptr_tag(opt) == 0) {
        lean_dec(opt);
        return NULL;
    }
    lean_object *s = lean_ctor_get(opt, 0);
    lean_inc(s);
    lean_dec(opt);
    return capture_string(s);
}

/* ── Lifecycle ───────────────────────────────────────────────────── */

void lean4yaml_initialize(void) {
    lean_initialize_runtime_module();
    lean_init_task_manager();
    lean_object *r = initialize_Lean4Yaml(1 /* builtin */, lean_io_mk_world());
    if (lean_io_result_is_ok(r)) {
        lean_dec(r);
    } else {
        lean_io_result_show_error(r);
        lean_dec(r);
        lean_internal_panic("lean4yaml_initialize: module init failed");
    }
}

void lean4yaml_finalize(void) {
    if (tls_last_string) {
        lean_dec(tls_last_string);
        tls_last_string = NULL;
    }
    lean_finalize_task_manager();
}

/* ── Fixed-size memory pool ──────────────────────────────────────── */

int lean4yaml_init_fixed_pool(size_t pool_bytes) {
    mi_arena_id_t arena_id;
    int err = mi_reserve_os_memory_ex(
        pool_bytes,
        /*commit=*/1,
        /*allow_large=*/0,
        /*exclusive=*/1,
        &arena_id);
    if (err != 0)
        return err;
    mi_option_set(mi_option_disallow_os_alloc, 1);
    return 0;
}

int lean4yaml_init_static_pool(void *buf, size_t buf_bytes) {
    mi_arena_id_t arena_id;
    bool ok = mi_manage_os_memory_ex(
        buf, buf_bytes,
        /*is_committed=*/1,
        /*is_large=*/0,
        /*is_zero=*/1,   /* static storage is zero-initialized */
        /*numa_node=*/0,
        /*exclusive=*/1,
        &arena_id);
    if (!ok)
        return -1;
    mi_option_set(mi_option_disallow_os_alloc, 1);
    return 0;
}

/* ── Parsing ─────────────────────────────────────────────────────── */

void *lean4yaml_parse(const char *input, size_t len, uint8_t preset) {
    lean_object *lean_input = lean_mk_string_from_bytes(input, len);
    lean_object *result = lean4yaml_parse_safe(lean_input, preset);
    lean_dec(lean_input);
    return result;
}

void *lean4yaml_parse_single(const char *input, size_t len, uint8_t preset) {
    lean_object *lean_input = lean_mk_string_from_bytes(input, len);
    lean_object *result = lean4yaml_parse_single_safe(lean_input, preset);
    lean_dec(lean_input);
    return result;
}

/* ── Result inspection ───────────────────────────────────────────── */

const char *lean4yaml_result_error_message(void *r) {
    if (!r)
        return NULL;
    lean_object *s = lean4yaml_result_get_error((lean_object *)r);
    /* result_get_error returns "" for ok results */
    if (lean_string_size(s) <= 1) {
        lean_dec(s);
        return NULL;
    }
    return capture_string(s);
}

/* ── Value inspection (string bridge) ────────────────────────────── */

const char *lean4yaml_value_string(void *v) {
    lean_object *s = lean4yaml_value_as_string((lean_object *)v);
    return capture_string(s);
}

void *lean4yaml_value_lookup(void *v, const char *key) {
    lean_object *lean_key = lean_mk_string(key);
    lean_object *opt = lean4yaml_value_lookup_raw((lean_object *)v, lean_key);
    lean_dec(lean_key);
    /* Option.none = tag 0, Option.some = tag 1 */
    if (lean_ptr_tag(opt) == 0) {
        lean_dec(opt);
        return NULL;
    }
    lean_object *val = lean_ctor_get(opt, 0);
    lean_inc(val);
    lean_dec(opt);
    return val;
}

const char *lean4yaml_value_tag(void *v) {
    lean_object *opt = lean4yaml_value_tag_raw((lean_object *)v);
    return extract_option_string(opt);
}

const char *lean4yaml_value_anchor(void *v) {
    lean_object *opt = lean4yaml_value_anchor_raw((lean_object *)v);
    return extract_option_string(opt);
}

/* ── Dumping ─────────────────────────────────────────────────────── */

const char *lean4yaml_dump(void *v) {
    lean_object *s = lean4yaml_dump_raw((lean_object *)v);
    return capture_string(s);
}

const char *lean4yaml_dump_docs(void *docs) {
    lean_object *s = lean4yaml_dump_docs_raw((lean_object *)docs);
    return capture_string(s);
}

/* ── Config deserialization ──────────────────────────────────────── */

void *lean4yaml_parse_limits_yaml(const char *yaml, size_t len) {
    lean_object *lean_yaml = lean_mk_string_from_bytes(yaml, len);
    lean_object *result = lean4yaml_parse_limits_yaml_impl(lean_yaml);
    lean_dec(lean_yaml);
    return result;
}

uint8_t lean4yaml_config_is_ok(void *r) {
    return lean4yaml_config_result_is_ok((lean_object *)r);
}

const char *lean4yaml_config_error_message(void *r) {
    if (!r)
        return NULL;
    lean_object *s = lean4yaml_config_result_get_error((lean_object *)r);
    if (lean_string_size(s) <= 1) {
        lean_dec(s);
        return NULL;
    }
    return capture_string(s);
}

void *lean4yaml_config_get_limits(void *r) {
    lean_object *limits = lean4yaml_config_result_get_limits((lean_object *)r);
    return limits;
}

void *lean4yaml_parse_configured(const char *input, size_t len,
                                 const char *config_yaml, size_t config_len) {
    lean_object *lean_input = lean_mk_string_from_bytes(input, len);
    lean_object *lean_config = lean_mk_string_from_bytes(config_yaml, config_len);
    lean_object *result = lean4yaml_parse_with_yaml_config_impl(lean_input, lean_config);
    lean_dec(lean_input);
    lean_dec(lean_config);
    return result;
}

const char *lean4yaml_dump_configured(void *v, const char *config_yaml,
                                      size_t config_len) {
    lean_object *lean_config = lean_mk_string_from_bytes(config_yaml, config_len);
    lean_object *s = lean4yaml_dump_with_yaml_config_impl((lean_object *)v, lean_config);
    lean_dec(lean_config);
    return capture_string(s);
}

/* ── Memory management ───────────────────────────────────────────── */

void lean4yaml_free(void *handle) {
    if (handle)
        lean_dec((lean_object *)handle);
}

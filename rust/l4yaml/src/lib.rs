//! Safe Rust wrapper for the Lean 4 verified YAML parser.
//!
//! # Quick start
//!
//! ```no_run
//! use l4yaml::{load, LimitsPreset, Kind};
//!
//! // Initialize the Lean runtime (once, before any parsing)
//! l4yaml::initialize();
//!
//! let value = load("key: value", LimitsPreset::Default).unwrap();
//! assert_eq!(value.kind(), Kind::Mapping);
//! assert_eq!(value.get("key").unwrap().as_str().unwrap(), "value");
//!
//! l4yaml::finalize();
//! ```
//!
//! # Thread safety
//!
//! All `YamlValue` and `YamlDocument` types are `!Send` and `!Sync`.
//! Call all l4yaml functions from the thread that called `initialize()`.

pub mod config;
pub mod document;
pub mod error;
pub mod value;

pub use config::LimitsPreset;
pub use document::YamlDocument;
pub use error::{Error, Kind, Result};
pub use value::{YamlItem, YamlValue, YamlValueIter};

use std::ffi::{CStr, c_void};
use std::sync::Once;

use l4yaml_sys::*;

static INIT: Once = Once::new();

/// Initialize the Lean runtime. Must be called once before any parsing.
///
/// Calling this multiple times is safe (subsequent calls are no-ops).
pub fn initialize() {
    INIT.call_once(|| unsafe {
        l4yaml_initialize();
    });
}

/// Finalize the Lean runtime. Call after all handles have been freed.
///
/// After calling this, no further l4yaml calls are valid.
pub fn finalize() {
    unsafe {
        l4yaml_finalize();
    }
}

/// Parse a YAML string expecting exactly one document.
///
/// Returns the root `YamlValue` of the single document.
pub fn load(input: &str, preset: LimitsPreset) -> Result<YamlValue> {
    initialize();
    unsafe {
        let result = l4yaml_parse_single(input.as_ptr().cast(), input.len(), preset.as_u8());
        extract_single_result(result)
    }
}

/// Parse a YAML string that may contain multiple documents.
///
/// Returns a `Vec<YamlDocument>` with one entry per `---` document.
pub fn load_all(input: &str, preset: LimitsPreset) -> Result<Vec<YamlDocument>> {
    initialize();
    unsafe {
        let result = l4yaml_parse(input.as_ptr().cast(), input.len(), preset.as_u8());
        extract_multi_result(result)
    }
}

/// Dump a `YamlValue` to a YAML string using the default `DumpConfig`.
pub fn dump(value: &YamlValue) -> Result<String> {
    let ptr = unsafe { l4yaml_dump(value.as_raw()) };
    if ptr.is_null() {
        return Err(Error::NullHandle);
    }
    let cstr = unsafe { CStr::from_ptr(ptr) };
    Ok(cstr.to_str()?.to_string())
}

/// Dump a `YamlValue` using a YAML-configured `DumpConfig`.
pub fn dump_configured(value: &YamlValue, config_yaml: &str) -> Result<String> {
    let ptr = unsafe {
        l4yaml_dump_configured(
            value.as_raw(),
            config_yaml.as_ptr().cast(),
            config_yaml.len(),
        )
    };
    if ptr.is_null() {
        return Err(Error::NullHandle);
    }
    let cstr = unsafe { CStr::from_ptr(ptr) };
    Ok(cstr.to_str()?.to_string())
}

/// Parse a YAML string with custom limits specified as a YAML config string.
///
/// Two-step bootstrap: parses the config YAML first (strict limits),
/// then parses the input with the resulting limits.
/// Returns all documents (multi-doc result).
pub fn load_all_configured(input: &str, config_yaml: &str) -> Result<Vec<YamlDocument>> {
    initialize();
    unsafe {
        let result = l4yaml_parse_configured(
            input.as_ptr().cast(),
            input.len(),
            config_yaml.as_ptr().cast(),
            config_yaml.len(),
        );
        extract_multi_result(result)
    }
}

/// Parse a YAML string with custom limits, expecting exactly one document.
///
/// Convenience wrapper around `load_all_configured` that returns the root
/// value of the first document.
pub fn load_configured(input: &str, config_yaml: &str) -> Result<YamlValue> {
    let mut docs = load_all_configured(input, config_yaml)?;
    if docs.is_empty() {
        return Err(Error::Parse("no documents in input".to_string()));
    }
    docs.remove(0).root()
}

// --- Internal helpers ---

unsafe fn extract_single_result(result: *mut c_void) -> Result<YamlValue> {
    if result.is_null() {
        return Err(Error::NullHandle);
    }
    unsafe {
        let ok = l4yaml_result_is_ok(result);
        if ok == 0 {
            let msg = extract_error_message(result);
            l4yaml_free(result);
            return Err(error::classify_error(msg));
        }
        let value_handle = l4yaml_result_value(result);
        l4yaml_free(result);
        YamlValue::from_raw(value_handle)
    }
}

unsafe fn extract_multi_result(result: *mut c_void) -> Result<Vec<YamlDocument>> {
    if result.is_null() {
        return Err(Error::NullHandle);
    }
    unsafe {
        let ok = l4yaml_result_is_ok(result);
        if ok == 0 {
            let msg = extract_error_message(result);
            l4yaml_free(result);
            return Err(error::classify_error(msg));
        }
        let docs_handle = l4yaml_result_docs(result);
        l4yaml_free(result);

        if docs_handle.is_null() {
            return Err(Error::NullHandle);
        }

        let count = l4yaml_docs_count(docs_handle) as usize;
        let mut docs = Vec::with_capacity(count);
        for i in 0..count {
            let doc_handle = l4yaml_docs_get(docs_handle, i as u32);
            docs.push(YamlDocument::from_raw(doc_handle)?);
        }
        l4yaml_free(docs_handle);
        Ok(docs)
    }
}

unsafe fn extract_error_message(result: *mut c_void) -> String {
    unsafe {
        let ptr = l4yaml_result_error_message(result);
        if ptr.is_null() {
            return "unknown error".to_string();
        }
        CStr::from_ptr(ptr)
            .to_str()
            .unwrap_or("non-utf8 error")
            .to_string()
    }
}

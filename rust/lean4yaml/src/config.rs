//! Configuration types: limit presets and YAML-based config parsing.

use std::ffi::{CStr, c_void};
use std::marker::PhantomData;

use lean4yaml_sys::*;

use crate::error::{Error, Result};

/// Parser limit presets matching the C API constants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum LimitsPreset {
    /// Balanced defaults: 10 MB input, depth 64, moderate alias limits.
    Default = 0,
    /// Tight limits for web/untrusted input: 1 MB, depth 20, strict alias.
    Strict = 1,
    /// Relaxed limits for trusted large inputs.
    Permissive = 2,
    /// No limits (testing only — not recommended for production).
    Unlimited = 3,
    /// Default limits + core-schema-only tag policy.
    SafeTags = 4,
}

impl LimitsPreset {
    pub(crate) fn as_u8(self) -> u8 {
        self as u8
    }
}

/// Parse a YAML string into custom `ParserLimits`.
///
/// Returns an opaque handle that can be used with `parse_with_limits`.
/// The config YAML itself is parsed with hardcoded strict limits
/// (bootstrapping).
pub fn parse_limits_yaml(yaml: &str) -> Result<ParserLimitsHandle> {
    unsafe {
        let result = lean4yaml_parse_limits_yaml(yaml.as_ptr().cast(), yaml.len());
        if result.is_null() {
            return Err(Error::NullHandle);
        }
        let ok = lean4yaml_config_is_ok(result);
        if ok == 0 {
            let err_ptr = lean4yaml_config_error_message(result);
            let msg = if err_ptr.is_null() {
                "unknown config error".to_string()
            } else {
                CStr::from_ptr(err_ptr).to_str().unwrap_or("non-utf8 error").to_string()
            };
            lean4yaml_free(result);
            return Err(Error::Config(msg));
        }
        let limits = lean4yaml_config_get_limits(result);
        lean4yaml_free(result);
        Ok(ParserLimitsHandle { handle: limits, _marker: PhantomData })
    }
}

/// Opaque handle to a `ParserLimits` value parsed from YAML config.
pub struct ParserLimitsHandle {
    handle: *mut c_void,
    _marker: PhantomData<*mut ()>,
}

impl Drop for ParserLimitsHandle {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { lean4yaml_free(self.handle) };
        }
    }
}

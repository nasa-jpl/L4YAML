//! `YamlDocument` — a single YAML document containing a root value.

use std::ffi::c_void;
use std::marker::PhantomData;

use lean4yaml_sys::*;

use crate::error::Result;
use crate::value::YamlValue;

/// A single YAML document parsed from a multi-document stream.
pub struct YamlDocument {
    handle: *mut c_void,
    _marker: PhantomData<*mut ()>,
}

impl YamlDocument {
    /// Wrap a raw `lean4yaml_doc_t` handle.
    pub(crate) unsafe fn from_raw(handle: *mut c_void) -> Result<Self> {
        if handle.is_null() {
            return Err(crate::error::Error::NullHandle);
        }
        Ok(YamlDocument { handle, _marker: PhantomData })
    }

    /// The root `YamlValue` of this document.
    pub fn root(&self) -> Result<YamlValue> {
        let h = unsafe { lean4yaml_doc_root(self.handle) };
        unsafe { YamlValue::from_raw(h) }
    }
}

impl Drop for YamlDocument {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { lean4yaml_free(self.handle) };
        }
    }
}

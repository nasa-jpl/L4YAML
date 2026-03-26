//! `YamlValue` — safe RAII wrapper around an opaque Lean YAML value handle.

use std::ffi::{CStr, c_void};
use std::fmt;
use std::marker::PhantomData;
use std::ops::Index;

use lean4yaml_sys::*;

use crate::error::{Error, Kind, Result};

/// An immutable YAML value backed by an opaque Lean `lean_object *` handle.
///
/// **Ownership**: each `YamlValue` owns one reference count on the Lean
/// object. `Drop` calls `lean4yaml_free` to release it. Child values
/// obtained via indexing or iteration are independently owned.
///
/// **Thread safety**: `YamlValue` is `!Send` and `!Sync` because the Lean
/// runtime is single-threaded unless the task manager is explicitly
/// initialized for multi-threaded use.
pub struct YamlValue {
    handle: *mut c_void,
    // *mut () is !Send + !Sync, making YamlValue !Send + !Sync.
    _marker: PhantomData<*mut ()>,
}

impl YamlValue {
    /// Wrap a raw handle obtained from the C API.
    ///
    /// # Safety
    /// `handle` must be a valid, owned `lean_object *` pointer obtained from
    /// one of the `lean4yaml_*` C functions. The caller transfers ownership.
    pub(crate) unsafe fn from_raw(handle: *mut c_void) -> Result<Self> {
        if handle.is_null() {
            return Err(Error::NullHandle);
        }
        Ok(YamlValue { handle, _marker: PhantomData })
    }

    /// Return the raw handle without releasing ownership.
    pub(crate) fn as_raw(&self) -> *mut c_void {
        self.handle
    }

    /// Node kind: scalar, sequence, mapping, or alias.
    pub fn kind(&self) -> Kind {
        let k = unsafe { lean4yaml_value_kind(self.handle) };
        Kind::from_u8(k)
    }

    /// Scalar string content. Returns `""` for non-scalar nodes.
    pub fn as_str(&self) -> Result<&str> {
        let ptr = unsafe { lean4yaml_value_string(self.handle) };
        if ptr.is_null() {
            return Ok("");
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        Ok(cstr.to_str()?)
    }

    /// Number of items (sequence) or pairs (mapping). 0 for scalars.
    pub fn len(&self) -> usize {
        match self.kind() {
            Kind::Sequence => unsafe { lean4yaml_value_seq_length(self.handle) as usize },
            Kind::Mapping => unsafe { lean4yaml_value_map_length(self.handle) as usize },
            _ => 0,
        }
    }

    /// Whether this value has zero children.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the i-th sequence element.
    pub fn seq_get(&self, i: usize) -> Result<YamlValue> {
        let h = unsafe { lean4yaml_value_seq_get(self.handle, i as u32) };
        unsafe { YamlValue::from_raw(h) }
    }

    /// Get the i-th mapping key.
    pub fn map_key(&self, i: usize) -> Result<YamlValue> {
        let h = unsafe { lean4yaml_value_map_key(self.handle, i as u32) };
        unsafe { YamlValue::from_raw(h) }
    }

    /// Get the i-th mapping value.
    pub fn map_val(&self, i: usize) -> Result<YamlValue> {
        let h = unsafe { lean4yaml_value_map_val(self.handle, i as u32) };
        unsafe { YamlValue::from_raw(h) }
    }

    /// Look up a mapping key by string. Returns `None` if not found or
    /// if this value is not a mapping.
    pub fn get(&self, key: &str) -> Option<YamlValue> {
        let key_cstr = std::ffi::CString::new(key).ok()?;
        let h = unsafe { lean4yaml_value_lookup(self.handle, key_cstr.as_ptr()) };
        if h.is_null() {
            None
        } else {
            unsafe { YamlValue::from_raw(h).ok() }
        }
    }

    /// YAML tag (e.g. `"!!int"`), or `None` if no explicit tag.
    pub fn tag(&self) -> Option<&str> {
        let ptr = unsafe { lean4yaml_value_tag(self.handle) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        cstr.to_str().ok()
    }

    /// Anchor name (e.g. `"anchor1"`), or `None` if no anchor.
    pub fn anchor(&self) -> Option<&str> {
        let ptr = unsafe { lean4yaml_value_anchor(self.handle) };
        if ptr.is_null() {
            return None;
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        cstr.to_str().ok()
    }

    /// Collect all mapping keys as strings.
    pub fn keys(&self) -> Result<Vec<String>> {
        let n = self.len();
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let k = self.map_key(i)?;
            out.push(k.as_str()?.to_string());
        }
        Ok(out)
    }

    /// Collect mapping as `(key_string, YamlValue)` pairs.
    pub fn items(&self) -> Result<Vec<(String, YamlValue)>> {
        let n = self.len();
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            let k = self.map_key(i)?;
            let v = self.map_val(i)?;
            out.push((k.as_str()?.to_string(), v));
        }
        Ok(out)
    }

    /// Collect sequence elements into a `Vec`.
    pub fn as_list(&self) -> Result<Vec<YamlValue>> {
        let n = self.len();
        let mut out = Vec::with_capacity(n);
        for i in 0..n {
            out.push(self.seq_get(i)?);
        }
        Ok(out)
    }
}

impl Drop for YamlValue {
    fn drop(&mut self) {
        if !self.handle.is_null() {
            unsafe { lean4yaml_free(self.handle) };
        }
    }
}

// --- Index impls ---

impl Index<&str> for YamlValue {
    type Output = YamlValue;

    /// Panics if the key is not found.
    fn index(&self, key: &str) -> &YamlValue {
        // We leak a Box here because Index requires returning a reference.
        // This is intentional: the caller should prefer `.get(key)` for
        // non-panicking access.
        let val = self
            .get(key)
            .unwrap_or_else(|| panic!("YamlValue: key not found: {key:?}"));
        // Safety: we leak the allocation; the reference is valid forever.
        // In practice users should prefer .get() to avoid the leak.
        Box::leak(Box::new(val))
    }
}

impl Index<usize> for YamlValue {
    type Output = YamlValue;

    /// Panics if the index is out of bounds.
    fn index(&self, i: usize) -> &YamlValue {
        let val = self
            .seq_get(i)
            .unwrap_or_else(|_| panic!("YamlValue: sequence index {i} out of bounds"));
        Box::leak(Box::new(val))
    }
}

// --- Display ---

impl fmt::Display for YamlValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ptr = unsafe { lean4yaml_dump(self.handle) };
        if ptr.is_null() {
            return write!(f, "<null>");
        }
        let cstr = unsafe { CStr::from_ptr(ptr) };
        match cstr.to_str() {
            Ok(s) => write!(f, "{s}"),
            Err(_) => write!(f, "<non-utf8>"),
        }
    }
}

impl fmt::Debug for YamlValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("YamlValue")
            .field("kind", &self.kind())
            .field("len", &self.len())
            .finish()
    }
}

// --- IntoIterator ---

/// Iterator over sequence items or mapping `(key, value)` pairs.
pub struct YamlValueIter<'a> {
    value: &'a YamlValue,
    index: usize,
    len: usize,
    is_mapping: bool,
}

/// Items yielded by `YamlValueIter`: either a single value (sequence)
/// or a `(key, value)` pair (mapping).
pub enum YamlItem {
    SeqItem(YamlValue),
    MapEntry(YamlValue, YamlValue),
}

impl<'a> Iterator for YamlValueIter<'a> {
    type Item = Result<YamlItem>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.len {
            return None;
        }
        let i = self.index;
        self.index += 1;
        if self.is_mapping {
            let k = match self.value.map_key(i) {
                Ok(v) => v,
                Err(e) => return Some(Err(e)),
            };
            let v = match self.value.map_val(i) {
                Ok(v) => v,
                Err(e) => return Some(Err(e)),
            };
            Some(Ok(YamlItem::MapEntry(k, v)))
        } else {
            match self.value.seq_get(i) {
                Ok(v) => Some(Ok(YamlItem::SeqItem(v))),
                Err(e) => Some(Err(e)),
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.len - self.index;
        (remaining, Some(remaining))
    }
}

impl<'a> IntoIterator for &'a YamlValue {
    type Item = crate::error::Result<YamlItem>;
    type IntoIter = YamlValueIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        YamlValueIter {
            value: self,
            index: 0,
            len: self.len(),
            is_mapping: self.kind() == Kind::Mapping,
        }
    }
}

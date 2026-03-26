//! Integration tests for the lean4yaml safe Rust wrapper.
//!
//! These tests require `liblean4yaml.so` to be built and discoverable.
//! Set `LEAN4YAML_LIB_DIR` if it is not at `../../ffi/out/`.
//!
//! Run: `cargo test -- --test-threads=1` (from `rust/`)
//!
//! Tests MUST run single-threaded because the Lean runtime is not
//! thread-safe without explicit task manager initialization.

use lean4yaml::*;

// --- Scalar parsing ---

#[test]
fn parse_scalar() {
    let v = load("hello", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Scalar);
    assert_eq!(v.as_str().unwrap(), "hello");
}

#[test]
fn parse_quoted_scalar() {
    let v = load("\"hello world\"", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Scalar);
    assert_eq!(v.as_str().unwrap(), "hello world");
}

// --- Sequence parsing ---

#[test]
fn parse_sequence() {
    let v = load("- a\n- b\n- c", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Sequence);
    assert_eq!(v.len(), 3);
    assert_eq!(v.seq_get(0).unwrap().as_str().unwrap(), "a");
    assert_eq!(v.seq_get(1).unwrap().as_str().unwrap(), "b");
    assert_eq!(v.seq_get(2).unwrap().as_str().unwrap(), "c");
}

#[test]
fn parse_flow_sequence() {
    let v = load("[1, 2, 3]", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Sequence);
    assert_eq!(v.len(), 3);
}

// --- Mapping parsing ---

#[test]
fn parse_mapping() {
    let v = load("name: alice\nage: 30", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Mapping);
    assert_eq!(v.len(), 2);
    assert_eq!(v.get("name").unwrap().as_str().unwrap(), "alice");
    assert_eq!(v.get("age").unwrap().as_str().unwrap(), "30");
}

#[test]
fn parse_flow_mapping() {
    let v = load("{a: 1, b: 2}", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Mapping);
    assert_eq!(v.len(), 2);
}

#[test]
fn mapping_lookup_missing_key() {
    let v = load("key: value", LimitsPreset::Default).unwrap();
    assert!(v.get("nonexistent").is_none());
}

// --- Nested structures ---

#[test]
fn parse_nested() {
    let yaml = "users:\n  - name: alice\n    role: admin\n  - name: bob\n    role: user";
    let v = load(yaml, LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Mapping);
    let users = v.get("users").unwrap();
    assert_eq!(users.kind(), Kind::Sequence);
    assert_eq!(users.len(), 2);
    let alice = users.seq_get(0).unwrap();
    assert_eq!(alice.get("name").unwrap().as_str().unwrap(), "alice");
    assert_eq!(alice.get("role").unwrap().as_str().unwrap(), "admin");
}

// --- Multi-document ---

#[test]
fn parse_multi_document() {
    let yaml = "---\na: 1\n---\nb: 2\n---\nc: 3";
    let docs = load_all(yaml, LimitsPreset::Default).unwrap();
    assert_eq!(docs.len(), 3);
    let r0 = docs[0].root().unwrap();
    assert_eq!(r0.get("a").unwrap().as_str().unwrap(), "1");
    let r2 = docs[2].root().unwrap();
    assert_eq!(r2.get("c").unwrap().as_str().unwrap(), "3");
}

// --- Dump ---

#[test]
fn dump_scalar() {
    let v = load("hello", LimitsPreset::Default).unwrap();
    let s = dump(&v).unwrap();
    assert!(s.contains("hello"));
}

#[test]
fn dump_roundtrip() {
    let yaml = "name: test\nitems:\n  - a\n  - b";
    let v = load(yaml, LimitsPreset::Default).unwrap();
    let dumped = dump(&v).unwrap();
    let v2 = load(&dumped, LimitsPreset::Default).unwrap();
    assert_eq!(v2.kind(), Kind::Mapping);
    assert_eq!(v2.get("name").unwrap().as_str().unwrap(), "test");
    let items = v2.get("items").unwrap();
    assert_eq!(items.len(), 2);
}

// --- Limit presets ---

#[test]
fn all_presets_parse_simple() {
    let presets = [
        LimitsPreset::Default,
        LimitsPreset::Strict,
        LimitsPreset::Permissive,
        LimitsPreset::Unlimited,
        LimitsPreset::SafeTags,
    ];
    for preset in &presets {
        let v = load("hello", *preset).unwrap();
        assert_eq!(v.kind(), Kind::Scalar);
    }
}

// --- Error handling ---

#[test]
fn invalid_yaml_returns_error() {
    let result = load(":\n  :\n    : [", LimitsPreset::Default);
    assert!(result.is_err());
    match result.unwrap_err() {
        Error::Parse(_) | Error::Limit(_) => {}
        e => panic!("unexpected error variant: {e:?}"),
    }
}

// --- Value navigation helpers ---

#[test]
fn keys_and_items() {
    let v = load("a: 1\nb: 2\nc: 3", LimitsPreset::Default).unwrap();
    let keys = v.keys().unwrap();
    assert_eq!(keys.len(), 3);
    assert!(keys.contains(&"a".to_string()));
    assert!(keys.contains(&"b".to_string()));
    assert!(keys.contains(&"c".to_string()));

    let items = v.items().unwrap();
    assert_eq!(items.len(), 3);
}

#[test]
fn as_list() {
    let v = load("[x, y, z]", LimitsPreset::Default).unwrap();
    let list = v.as_list().unwrap();
    assert_eq!(list.len(), 3);
    assert_eq!(list[0].as_str().unwrap(), "x");
}

// --- Iterator ---

#[test]
fn iterate_sequence() {
    let v = load("[a, b, c]", LimitsPreset::Default).unwrap();
    let mut count = 0;
    for item in &v {
        match item.unwrap() {
            YamlItem::SeqItem(val) => {
                assert_eq!(val.kind(), Kind::Scalar);
                count += 1;
            }
            _ => panic!("expected SeqItem"),
        }
    }
    assert_eq!(count, 3);
}

#[test]
fn iterate_mapping() {
    let v = load("a: 1\nb: 2", LimitsPreset::Default).unwrap();
    let mut count = 0;
    for item in &v {
        match item.unwrap() {
            YamlItem::MapEntry(k, val) => {
                assert_eq!(k.kind(), Kind::Scalar);
                assert_eq!(val.kind(), Kind::Scalar);
                count += 1;
            }
            _ => panic!("expected MapEntry"),
        }
    }
    assert_eq!(count, 2);
}

// --- Display ---

#[test]
fn display_value() {
    let v = load("hello", LimitsPreset::Default).unwrap();
    let s = format!("{v}");
    assert!(s.contains("hello"));
}

// --- Empty values ---

#[test]
fn empty_sequence() {
    let v = load("[]", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Sequence);
    assert!(v.is_empty());
    assert_eq!(v.len(), 0);
}

#[test]
fn empty_mapping() {
    let v = load("{}", LimitsPreset::Default).unwrap();
    assert_eq!(v.kind(), Kind::Mapping);
    assert!(v.is_empty());
    assert_eq!(v.len(), 0);
}

// --- Config-based parsing ---

#[test]
fn load_configured_basic() {
    let config = "structural:\n  maxDepth: 10";
    let v = load_configured("key: value", config).unwrap();
    assert_eq!(v.kind(), Kind::Mapping);
}

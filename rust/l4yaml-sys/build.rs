//! build.rs — locate libl4yaml.so and generate raw FFI bindings via bindgen.

use std::env;
use std::path::PathBuf;

fn main() {
    // 1. Locate libl4yaml.so
    let lib_dir = if let Ok(dir) = env::var("L4YAML_LIB_DIR") {
        PathBuf::from(dir)
    } else {
        // Default: ffi/out/ relative to the project root (two levels up from rust/l4yaml-sys/)
        let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        manifest.join("../../ffi/out")
    };

    if !lib_dir.exists() {
        panic!(
            "libl4yaml.so not found at {}. \
             Build with `cmake -B ffi/out -S ffi && cmake --build ffi/out`, \
             or set L4YAML_LIB_DIR.",
            lib_dir.display()
        );
    }

    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!("cargo:rustc-link-lib=dylib=l4yaml");

    // 2. Locate libleanshared.so (transitive dep)
    let lean_lib_dir = if let Ok(dir) = env::var("LEAN_LIB_DIR") {
        PathBuf::from(dir)
    } else {
        // Try `lean --print-prefix`/lib/lean
        let output = std::process::Command::new("lean")
            .arg("--print-prefix")
            .output()
            .expect("Failed to run `lean --print-prefix`. Set LEAN_LIB_DIR.");
        let prefix = String::from_utf8(output.stdout)
            .expect("non-UTF8 lean prefix")
            .trim()
            .to_string();
        PathBuf::from(prefix).join("lib/lean")
    };
    println!("cargo:rustc-link-search=native={}", lean_lib_dir.display());
    println!("cargo:rustc-link-lib=dylib=leanshared");

    // 3. Generate bindings from l4yaml.h
    let header = {
        let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        manifest.join("../../ffi/l4yaml.h")
    };

    if !header.exists() {
        panic!("l4yaml.h not found at {}", header.display());
    }

    let bindings = bindgen::Builder::default()
        .header(header.to_str().unwrap())
        .allowlist_function("l4yaml_.*")
        .allowlist_var("L4YAML_.*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("bindgen failed to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindings.rs");
    bindings
        .write_to_file(&out_path)
        .expect("failed to write bindings.rs");
}

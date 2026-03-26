//! build.rs — locate liblean4yaml.so and generate raw FFI bindings via bindgen.

use std::env;
use std::path::PathBuf;

fn main() {
    // 1. Locate liblean4yaml.so
    let lib_dir = if let Ok(dir) = env::var("LEAN4YAML_LIB_DIR") {
        PathBuf::from(dir)
    } else {
        // Default: ffi/out/ relative to the project root (two levels up from rust/lean4yaml-sys/)
        let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        manifest.join("../../ffi/out")
    };

    if !lib_dir.exists() {
        panic!(
            "liblean4yaml.so not found at {}. \
             Build with `cmake -B ffi/out -S ffi && cmake --build ffi/out`, \
             or set LEAN4YAML_LIB_DIR.",
            lib_dir.display()
        );
    }

    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!("cargo:rustc-link-lib=dylib=lean4yaml");

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

    // 3. Generate bindings from lean4yaml.h
    let header = {
        let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        manifest.join("../../ffi/lean4yaml.h")
    };

    if !header.exists() {
        panic!("lean4yaml.h not found at {}", header.display());
    }

    let bindings = bindgen::Builder::default()
        .header(header.to_str().unwrap())
        .allowlist_function("lean4yaml_.*")
        .allowlist_var("LEAN4YAML_.*")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("bindgen failed to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindings.rs");
    bindings
        .write_to_file(&out_path)
        .expect("failed to write bindings.rs");
}

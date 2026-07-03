//! build.rs — bake runtime rpaths into this crate's binaries/examples/tests.
//!
//! l4yaml-sys locates libl4yaml.so and libleanshared.so at BUILD time
//! (rustc-link-search) and exports both directories through the
//! `links = "l4yaml"` metadata channel. Link-search alone leaves the
//! produced binaries dependent on LD_LIBRARY_PATH at RUNTIME (the
//! suiterunner rust backend ran `examples/tryparse` bare and every
//! invocation died with exit 127, which scored as a parse rejection).
//! Emitting -rpath here mirrors tryparse_c's CMake BUILD_RPATH.

fn main() {
    for dep_var in ["DEP_L4YAML_LIB_DIR", "DEP_L4YAML_LEAN_LIB_DIR"] {
        if let Ok(dir) = std::env::var(dep_var) {
            println!("cargo:rustc-link-arg=-Wl,-rpath,{dir}");
        }
    }
}

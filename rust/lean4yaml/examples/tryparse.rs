//! tryparse_rust — Minimal Rust tryparse for yaml-test-suite integration.
//!
//! Reads a YAML file, parses it via the Rust API (lean4yaml::load_all), and
//! exits 0 on success, 1 on parse error.  Mirrors the Lean tryparse
//! binary exactly so the suiterunner can swap backends.
//!
//! Usage: tryparse_rust <file.yaml> [preset]
//!   preset: unlimited (default) | default | strict | permissive | safe_tags

use lean4yaml::LimitsPreset;

fn parse_preset(s: &str) -> Option<LimitsPreset> {
    match s {
        "unlimited" => Some(LimitsPreset::Unlimited),
        "default" => Some(LimitsPreset::Default),
        "strict" => Some(LimitsPreset::Strict),
        "permissive" => Some(LimitsPreset::Permissive),
        "safe_tags" => Some(LimitsPreset::SafeTags),
        _ => None,
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 || args.len() > 3 {
        eprintln!("Usage: tryparse_rust <file.yaml> [preset]");
        std::process::exit(2);
    }

    let preset = if args.len() == 3 {
        match parse_preset(&args[2]) {
            Some(p) => p,
            None => {
                eprintln!("Unknown preset '{}'; choose from: unlimited, default, strict, permissive, safe_tags", args[2]);
                std::process::exit(2);
            }
        }
    } else {
        LimitsPreset::Unlimited
    };

    let content = match std::fs::read_to_string(&args[1]) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("Cannot open {}: {}", args[1], e);
            std::process::exit(2);
        }
    };

    lean4yaml::initialize();

    let code = match lean4yaml::load_all(&content, preset) {
        Ok(_) => 0,
        Err(e) => {
            eprintln!("{e}");
            1
        }
    };

    lean4yaml::finalize();
    std::process::exit(code);
}

/-
  L4YAML — Verified YAML 1.2.2 Parser Documentation

  Written in Verso (Manual genre) for the L4YAML project,
  formerly lean4-yaml-verified.
-/
import VersoManual

import Doc.L4YAML.Overview
import Doc.L4YAML.Architecture
import Doc.L4YAML.Verification
import Doc.L4YAML.Security
import Doc.L4YAML.FFI
import Doc.L4YAML.Testing
import Doc.L4YAML.TestResults

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "L4YAML: A Verified YAML 1.2.2 Parser in Lean 4" =>

%%%
authors := ["the L4YAML contributors"]
shortTitle := "L4YAML"
%%%

L4YAML is a fully verified YAML 1.2.2 parser written in pure Lean 4.
It delivers 2,309 machine-checked theorems across 61 proof modules,
zero axioms, zero `sorry`, and zero `partial def` — while passing
100% of the YAML 1.2.2 specification examples and 100% of the
applicable yaml-test-suite test IDs (225/225).

This manual documents the project's architecture, verification
strategy, security model, and FFI bindings for C, Python, and Rust.

A PDF version of this manual is available for download:
[L4YAML.pdf](L4YAML.pdf).

{include 0 Doc.L4YAML.Overview}

{include 0 Doc.L4YAML.Architecture}

{include 0 Doc.L4YAML.Verification}

{include 0 Doc.L4YAML.Security}

{include 0 Doc.L4YAML.FFI}

{include 0 Doc.L4YAML.Testing}

{include 0 Doc.L4YAML.TestResults}

# Index
%%%
tag := "index"
number := false
%%%

{theIndex}

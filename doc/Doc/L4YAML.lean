/-
  L4YAML — Verified YAML 1.2.2 Parser Documentation

  Written in Verso (Manual genre) for the L4YAML project,
  formerly lean4-yaml-verified.
-/
import VersoManual

import Doc.L4YAML.Stats
import Doc.L4YAML.Overview
import Doc.L4YAML.Architecture
import Doc.L4YAML.Verification
import Doc.L4YAML.Security
import Doc.L4YAML.FFI
import Doc.L4YAML.Testing
import Doc.L4YAML.TestResults

open Verso.Genre Manual
open Doc.L4YAML.Stats

set_option pp.rawOnError true

#doc (Manual) "L4YAML: A Verified YAML 1.2.2 Parser in Lean 4" =>

%%%
authors := ["Nicolas F. Rouquette"]
shortTitle := "L4YAML"
%%%

L4YAML is a fully verified YAML 1.2.2 parser written in pure Lean 4.
It delivers {numTheorems}[] machine-checked theorems across
{numProofModules}[] proof modules, zero axioms, zero `sorry`, and
zero `partial def` — while passing 100% of the YAML 1.2.2
specification examples and 100% of the applicable yaml-test-suite
test IDs (225/225).

This manual documents the project's architecture, verification
strategy, security model, and FFI bindings for C, Python, and Rust.

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

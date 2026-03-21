import Lean4Yaml.TokenParser

/-!
# %TAG Directive Resolution Proofs (§6.8.2)

Formally verified properties of tag shorthand resolution.  `resolveTag`
maps `(handle, suffix)` pairs to fully expanded tag URIs using the
per-document `%TAG` handle→prefix mapping.

## Theorems

- **§1**: Verbatim tags pass through unchanged
- **§2**: Declared handles expand to `prefix ++ suffix`
- **§3**: Default secondary handle preserves `!!` shorthand
- **§4**: Default primary handle preserves `!` shorthand
- **§5**: Edge cases
-/

open Lean4Yaml.TokenParser

namespace Lean4Yaml.Proofs.TagResolution

/-! ## §1: Verbatim tags -/

/-- Verbatim tag (empty handle, non-empty suffix) passes through as-is (§6.8.2). -/
theorem resolveTag_verbatim (tagHandles : Array (String × String))
    (suffix : String) (h : suffix ≠ "") :
    resolveTag tagHandles "" suffix = suffix := by
  unfold resolveTag; simp [h]

/-- Verbatim tag resolution is independent of the tag handle mapping. -/
theorem resolveTag_verbatim_independent
    (th₁ th₂ : Array (String × String)) (suffix : String) (h : suffix ≠ "") :
    resolveTag th₁ "" suffix = resolveTag th₂ "" suffix := by
  simp [resolveTag, h]

/-! ## §2: Declared handles -/

/-- When a handle is found in the mapping, the tag resolves to `prefix ++ suffix`. -/
theorem resolveTag_declared (tagHandles : Array (String × String))
    (handle pfx suffix : String) (h_ne : handle ≠ "")
    (h_found : tagHandles.find? (·.1 == handle) = some (handle, pfx)) :
    resolveTag tagHandles handle suffix = pfx ++ suffix := by
  unfold resolveTag
  simp [h_ne, h_found]

/-! ## §3: Default secondary handle -/

/-- Without a `%TAG !!` declaration, `!!` tags keep shorthand `!!suffix`. -/
theorem resolveTag_default_secondary (tagHandles : Array (String × String))
    (suffix : String)
    (h_none : tagHandles.find? (·.1 == "!!") = none) :
    resolveTag tagHandles "!!" suffix = "!!" ++ suffix := by
  unfold resolveTag; simp [h_none]

/-- Default secondary handle: example with empty mapping. -/
theorem resolveTag_secondary_empty :
    resolveTag #[] "!!" "str" = "!!str" := by native_decide

/-! ## §4: Default primary handle -/

/-- Without a `%TAG !` declaration, primary tags keep shorthand `!suffix`. -/
theorem resolveTag_default_primary (tagHandles : Array (String × String))
    (suffix : String)
    (h_none : tagHandles.find? (·.1 == "!") = none) :
    resolveTag tagHandles "!" suffix = "!" ++ suffix := by
  unfold resolveTag; simp [h_none]

/-- Default primary handle: example with empty mapping. -/
theorem resolveTag_primary_empty :
    resolveTag #[] "!" "foo" = "!foo" := by native_decide

/-! ## §5: Edge cases -/

/-- Empty handle ++ empty suffix produces empty string. -/
theorem resolveTag_empty_empty :
    resolveTag #[] "" "" = "" := by native_decide

/-- Named handle `!e!` resolves via mapping. -/
theorem resolveTag_named_example :
    resolveTag #[("!e!", "tag:example.com,2000:app/")] "!e!" "foo" =
    "tag:example.com,2000:app/foo" := by native_decide

/-- Named handle `!yaml!` resolves via mapping. -/
theorem resolveTag_yaml_example :
    resolveTag #[("!yaml!", "tag:yaml.org,2002:")] "!yaml!" "str" =
    "tag:yaml.org,2002:str" := by native_decide

/-- Secondary handle override: `%TAG !! prefix` overrides the default. -/
theorem resolveTag_secondary_override :
    resolveTag #[("!!", "tag:example.com,2000:app/")] "!!" "int" =
    "tag:example.com,2000:app/int" := by native_decide

/-- Primary handle override: `%TAG ! prefix` overrides the default. -/
theorem resolveTag_primary_override :
    resolveTag #[("!", "!foo")] "!" "bar" = "!foobar" := by native_decide

end Lean4Yaml.Proofs.TagResolution

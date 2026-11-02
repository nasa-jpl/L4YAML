module

public import Scripts.Flip.Round
meta import Scripts.Flip.Round

@[expose] public section Blanket

/-!
# Scripts.Flip.Report — the lines a flip prints

The report the `flip_*.py` scripts printed, written once: the headline
`TAG exit=E errors=N decls=M`, one line per owner with its site count, one
line per site with the message head (`msgWidth` characters, the Python's
`msg[:100]`/`[:110]`), and the fixpoint summary when rounds were repeated.
-/

open Scripts.Flip.Round

namespace Scripts.Flip.Report

def headline (tag : String) (exit : UInt32) (sites : Array Site) : String :=
  s!"{tag} exit={exit} errors={sites.size} decls={(byOwner sites).size}"

def ownerLines (sites : Array Site) (msgWidth : Nat) : Array String := Id.run do
  let mut out := #[]
  for (d, es) in byOwner sites do
    out := out.push s!"  {d}: {es.size} site(s)"
    for e in es do
      out := out.push s!"    {e.line}: {e.msg.take msgWidth}"
  return out

#guard headline "T" 1 #[⟨3, "m", "a"⟩, ⟨9, "n", "a"⟩, ⟨12, "o", "b"⟩] == "T exit=1 errors=3 decls=2"
#guard ownerLines #[⟨3, "message", "a"⟩, ⟨9, "n", "a"⟩] 4 == #["  a: 2 site(s)", "    3: mess", "    9: n"]

end Scripts.Flip.Report

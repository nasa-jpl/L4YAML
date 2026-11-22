import Tests.DeclineCornerCensus

/-!
Item 221's entry point.  The census is a library so the proof module can import
its predicates; a module carrying a root-level `main` cannot be imported.
-/

def main (args : List String) : IO UInt32 := Tests.DeclineCornerCensus.main args

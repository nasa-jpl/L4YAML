import Tests.DeclineReachCensus

/-! Entry point for `lake exe declinereach` (item 219).  It lives in its own
module so that `Tests.DeclineReachCensus` — the predicates, the walk and the
pins — can be IMPORTED by later censuses; a root-level `main` cannot be. -/

def main (args : List String) : IO UInt32 := Tests.DeclineReachCensus.main args

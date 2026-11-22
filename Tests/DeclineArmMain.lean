import Tests.DeclineArmCensus

/-! Entry point for `lake exe declinearm` (item 220).  It lives in its own
module for the same reason item 219's does: a module carrying a root-level
`main` cannot be imported, and `Tests.Guards.Proofs.DeclineArmLattice` imports
the census. -/

def main (args : List String) : IO UInt32 := Tests.DeclineArmCensus.main args

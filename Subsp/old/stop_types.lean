import Subsp.Buchholz.Rank1
import Subsp.old.subsp

def T.isSubNF (n : Nat) (s : T) :=
  isNF1 s ∧ s < P 0 (P n Z Z) Z

def T.SubNF (lam : Nat) := { s : T // T.isSubNF lam s }

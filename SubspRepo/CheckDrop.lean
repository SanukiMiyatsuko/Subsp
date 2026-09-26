import SubspRepo.DecodeGen
open T

def dropH (s:T):T := T.unone (T.uncard1 (T.part s).1)
def chkDrop (k depth:Nat):Bool :=
  (terms depth).all (fun s =>
    if decide (s ≠ Z) &&
        decide (s < T.mul (P 1 Z Z) (T.ofNat (k+1))) then
      decide (dropH s < T.mul (P 1 Z Z) (T.ofNat k))
    else true)
def badDrop(k depth:Nat):=
  (terms depth).find? (fun s =>
    decide (s ≠ Z) &&
    decide (s < T.mul (P 1 Z Z) (T.ofNat (k+1))) &&
    !decide (dropH s < T.mul (P 1 Z Z) (T.ofNat k)))
#eval (chkDrop 0 3, chkDrop 1 3, chkDrop 2 3, chkDrop 3 3)
#eval (badDrop 0 3).map rawT
#eval (badDrop 1 3).map rawT

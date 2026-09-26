import SubspRepo.DecodeGen

open T

/-
Recovered exploration snapshot.  The decoder definitions are in DecodeGen.lean.
The stronger checks below are the ones that exposed the failure of the naive
canonical decoder beyond the initial shallow tests.
-/

def chkNC2 (lam depth fuel : Nat) : Bool :=
  (terms depth).all (fun t =>
    if nf1b t && decide (t < C lam) then
      decide (trans (decN lam fuel t) = t) &&
        decide (new.T.isNF (decN lam fuel t))
    else true)

def badNC2 (lam depth fuel : Nat) :=
  (terms depth).find? (fun t =>
    nf1b t && decide (t < C lam) &&
      !(decide (trans (decN lam fuel t) = t) &&
        decide (new.T.isNF (decN lam fuel t))))

#eval (chkNC2 0 3 20, chkNC2 1 3 20, chkNC2 2 3 20,
  chkNC2 3 3 20, chkNC2 4 3 20, chkNC2 5 3 20)
#eval (badNC2 1 3 20).map (fun t => (rawT t, rawT (trans (decN 1 20 t))))
#eval (badNC2 2 3 20).map (fun t => (rawT t, rawT (trans (decN 2 20 t))))
#eval (badNC2 3 3 20).map (fun t => (rawT t, rawT (trans (decN 3 20 t))))

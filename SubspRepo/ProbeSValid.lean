import SubspRepo.ProbeDecS

open T

def chkSauxNZ (lam k depth fuel : Nat) : Bool :=
  (terms depth).all (fun s =>
    if good0 s && decide (s ≠ T.Z) &&
        decide (s < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) then
      match auxS lam k fuel s with
      | (f, sum, a0) =>
          f && decide (sum = s) && decide (a0 = T.Z) &&
            (new.Vec.toList (decS lam fuel k s)).all compB
    else true)

#eval (chkSauxNZ 2 1 3 20, chkSauxNZ 3 2 3 20,
  chkSauxNZ 4 3 3 20, chkSauxNZ 5 4 3 20)

import SubspRepo.DecodeGen

open T

def auxS (lam k fuel : Nat) (s : T) :=
  transAux (vcons (new.T.Z : new.T lam) (decS lam fuel k s))

def chkSaux (lam k depth fuel : Nat) : Bool :=
  (terms depth).all (fun s =>
    if good0 s && decide (s < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) then
      match auxS lam k fuel s with
      | (f, sum, a0) =>
          f && decide (sum = s) && decide (a0 = T.Z) &&
            (new.Vec.toList (decS lam fuel k s)).all compB
    else true)

#eval (chkSaux 2 1 3 20, chkSaux 3 2 3 20,
  chkSaux 4 3 3 20, chkSaux 5 4 3 20)

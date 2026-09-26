import SubspRepo.DecodeGen
open T

def partSndGood (x:T):Bool :=
  if good0 x then
    let L := (T.part x).2
    (T.G1 0 L).all (fun y => decide (y < L))
  else true

def badPartGood(depth:Nat):=
  (terms depth).find? (fun x => !(partSndGood x))
#eval (badPartGood 3).map rawT

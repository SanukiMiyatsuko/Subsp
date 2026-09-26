import SubspRepo.DecodeGen
open T

def idx0b (x:T):Bool := decide (T.index_Prop1 0 x)
def goodb (x:T):Bool :=
  decide (T.isNF1 x) && (T.G1 0 x).all (fun y => decide (y < x))
def propUnec (x:T):Bool :=
  if decide (T.isNF1 x) && idx0b x then goodb (T.unec x) else true
def badUnec(depth:Nat):=
  (terms depth).find? (fun x => !(propUnec x))
#eval (badUnec 3).map rawT

import Subsp.new.subsp

def v2s (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def gens : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gens n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2s a b) c)))
def nfcb (s:new.T 2) : Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
def bad := (gens 3).findSome? (fun a =>
  if !(nfcb a && decide (new.T.dom a = .Omega)) then none else
  match a with
  | .Z => none
  | .P va _ => (gens 3).find? (fun t =>
      let b := new.T.P va t
      nfcb b && decide (new.compareT b a = Ordering.lt) && !nfcb t))
#eval (gens 3).length
#eval bad.isSome

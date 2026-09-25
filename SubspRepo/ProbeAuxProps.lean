import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v3 (a b c : new.T 3) := new.Vec.ofFn 3 (fun i => if i.val = 0 then a else if i.val = 1 then b else c)
def gen : Nat → List (new.T 3)
| 0 => [new.T.Z]
| n + 1 =>
  let p := gen n
  [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v3 a b c) new.T.Z)))
def ngood (x:new.T 3) : Bool := decide (new.T.isNF x) && (new.T.G x).all (fun y => decide (y < x))
def good1 (x:T):Bool := decide (T.isNF1 x) && (T.G1 1 x).all (fun y => decide (y<x))
def idx1 : T → Bool | Z => true | P p _ b => decide (p ≤ 1) && idx1 b
def vs := (gen 2).filter ngood
def sums := vs.map (fun a => let v := match a with | new.T.Z => v3 new.T.Z new.T.Z new.T.Z | new.T.P ls _ => ls; (transAux v).2.1)
#eval vs.length
#eval sums.all good1
#eval sums.all idx1
#eval sums.all (fun s => good1 (T.one_del s))
#eval sums.all (fun s => idx1 (T.one_del s))
#eval sums.all (fun s => good1 (T.card_times 1 (T.one_del s)))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v3 (a b c : new.T 3) := new.Vec.ofFn 3 (fun i => if i.val = 0 then a else if i.val = 1 then b else c)
def gen : Nat → List (new.T 3)
| 0 => [new.T.Z]
| n + 1 => let p := gen n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v3 a b c) new.T.Z)))
def ngood (x:new.T 3) : Bool := decide (new.T.isNF x) && (new.T.G x).all (fun y => decide (y < x))
def vs := (gen 2).filter ngood
def sums := vs.map (fun a => let v := match a with | new.T.Z => v3 new.T.Z new.T.Z new.T.Z | new.T.P ls _ => ls; (transAux v).2.1)
def leB (a b:T):Bool := decide (a≤b)
#eval sums.all (fun s => leB (T.head (T.one_del s)) (T.P 1 T.Z T.Z))
#eval sums.find? (fun s => !(leB (T.head (T.one_del s)) (T.P 1 T.Z T.Z))) |>.map (fun s=>reprStr s++" / "++reprStr(T.one_del s))

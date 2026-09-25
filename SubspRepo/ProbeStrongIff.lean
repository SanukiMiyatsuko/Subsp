import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def ngood (s:new.T 2):Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y=>decide (new.compareT y s = Ordering.lt))
def ogood (s:T):Bool := decide (T.isNF1 s) && (T.G1 0 s).all (fun y=>decide (y < s))
#eval (gen2 3).length
#eval (gen2 3).all (fun s => ngood s == ogood (trans s))

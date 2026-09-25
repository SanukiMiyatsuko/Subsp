import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def ngood (x:new.T 2):Bool := decide (new.T.isNF x) && (new.T.G x).all (fun y=>decide (new.compareT y x = Ordering.lt))
def xs := (gen2 3).filter ngood
def drops (x:new.T 2):Bool := let s:=trans x; let p:=T.part s; !(decide (p.1=T.Z)) && decide (T.early_collapse s = p.2)
#eval xs.length
#eval xs.any drops
#eval (xs.find? drops).map (fun x => reprStr (trans x))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def gen1 : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 => let p:=gen1 n; [new.T.Z] ++ p.flatMap (fun a => p.map (fun b => new.T.P (new.Vec.snoc 0 new.Vec.nil a) b))
def goodOld (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y => decide (y<x))
def goodNew (x:new.T 1):Bool := decide (new.T.isNF x) && (new.T.G x).all (fun y => decide (new.compareT y x = Ordering.lt))
def gs := (gen1 3).filter goodNew
#eval gs.length
#eval gs.all (fun x => goodOld 0 (trans x))
#eval gs.all (fun x => goodOld 0 (T.early_collapse (trans x)))
#eval gs.all (fun x => goodOld 1 (T.card_times 1 (T.early_collapse (trans x))))

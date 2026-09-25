import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v1P (a:new.T 1) := new.Vec.snoc 0 new.Vec.nil a
def gen1P : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 => let p:=gen1P n; [new.T.Z] ++ p.flatMap (fun a => p.map (fun b=>new.T.P (v1P a) b))
def oldgoodP (s:T):Bool := decide (T.isNF1 s) && (T.G1 0 s).all (fun x=>decide (x < s))
def propP (a:new.T 1):Bool := if oldgoodP (trans a) then oldgoodP (trans (new.T.P (v1P a) new.T.Z)) else true
#eval (gen1P 4).length
#eval (gen1P 4).all propP
#eval ((gen1P 4).find? (fun a=>!(propP a))).map (fun a => (reprStr (trans a), reprStr (trans (new.T.P (v1P a) new.T.Z))))

#eval ((gen1P 4).find? (fun a => reprStr (trans a) == "1^1")).map (fun a => reprStr (trans (new.T.P (v1P a) new.T.Z)))

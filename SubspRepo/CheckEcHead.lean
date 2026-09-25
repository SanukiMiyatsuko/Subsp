import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def gen1 : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 => let p:=gen1 n; [new.T.Z] ++ p.flatMap (fun a => p.map (fun b => new.T.P (new.Vec.snoc 0 new.Vec.nil a) b))
def headIdx : T → Nat | Z=>0 | P i _ _=>i
def ok (xs:List (new.T 1)) := xs.all (fun a => match T.early_collapse (trans a) with | Z => true | P i _ _ => i==0)
#eval ok (gen1 3)

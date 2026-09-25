import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def nf := (gen 2).filter (fun x => decide (T.isNF1 x))
def chkMap (f:T→T) (xs:List T) := xs.all (fun a => xs.all (fun b => (decide (a<b)) == (decide (f a < f b))))
#eval nf.length
#eval chkMap T.early_collapse nf
#eval chkMap (fun x => T.card_times 1 (T.early_collapse x)) nf
#eval chkMap (fun x => T.card_times 2 (T.early_collapse x)) nf

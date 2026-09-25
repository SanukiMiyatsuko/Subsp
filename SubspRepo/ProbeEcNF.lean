import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def nfs := (gen 3).filter (fun x => decide (T.isNF1 x))
#eval nfs.length
#eval nfs.all (fun x => decide (T.isNF1 (T.early_collapse x)))

import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0 (x:T):Bool := decide (T.isNF1 x) && (T.G1 0 x).all (fun y=>decide (y < x))
def leB (a b:T):Bool := decide (a<b) || decide (a = b)
#eval (gen 3).filter good0 |>.all (fun x => leB (T.early_collapse x) x)
#eval (gen 3).filter good0 |>.all (fun x => leB x (T.early_collapse x))

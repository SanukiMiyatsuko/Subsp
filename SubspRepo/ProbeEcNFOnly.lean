import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genE : Nat → List T
| 0 => [Z]
| n+1 => let p:=genE n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def nfB (a:T):Bool := match T.decIsNF a with | isTrue _ => true | isFalse _ => false
#eval (genE 3).filter nfB |>.all (fun x => nfB (T.early_collapse x))
#eval (genE 3).filter nfB |>.filter (fun x=>!nfB (T.early_collapse x)) |>.take 10 |>.map reprStr

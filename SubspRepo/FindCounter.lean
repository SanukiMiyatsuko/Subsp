import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y => decide (y < x))
def bads := (gen 2).filter (fun x => good 0 x && !(good 0 (T.early_collapse x)))
#eval bads.length
#eval bads.take 10 |>.map reprStr

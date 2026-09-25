import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0 (x:T):Bool := decide (T.isNF1 x) && (T.G1 0 x).all (fun y=>decide (y < x))
def xs := (gen 2).filter good0
def chk := xs.all (fun a => xs.all (fun b => !(decide (a < b)) || decide (a < T.early_collapse b)))
#eval xs.length
#eval chk

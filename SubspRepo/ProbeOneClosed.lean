import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y=>decide (y<x))
def idxb (u:Nat) : T → Bool | Z=>true | P p _ t => decide (p≤u) && idxb u t
def xs := (gen 3).filter (fun x=>good 1 x && idxb 1 x)
#eval xs.length
#eval xs.all (fun x=>good 1 (T.one_del x) && idxb 1 (T.one_del x))
#eval xs.find? (fun x=>!(good 1 (T.one_del x) && idxb 1 (T.one_del x))) |>.map reprStr

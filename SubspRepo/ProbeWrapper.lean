import Subsp.Buchholz.Rank1
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idxb (u:Nat) : T → Bool | Z => true | P p _ t => decide (p≤u) && idxb u t
def good1 (m:T):Bool := decide (T.isNF1 m) && idxb 1 m && (T.G1 1 m).all (fun x=>decide (x<m))
def claim (m:T):Bool := (T.G1 0 m).all (fun x=>decide (x < T.P 1 m T.Z))
def xs := (gen 3).filter good1
#eval xs.length
#eval xs.all claim
#eval (xs.find? (fun m=>!claim m)).map reprStr

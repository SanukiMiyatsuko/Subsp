import Subsp.Buchholz.Rank1
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idxb (u:Nat) : T → Bool | Z => true | P p _ t => decide (p≤u) && idxb u t
def nfidx := (gen 3).filter (fun x => decide (T.isNF1 x) && idxb 1 x)
#eval nfidx.length
#eval nfidx.all (fun x => (T.G1 1 x).all (fun y => decide (y<x)))
#eval (nfidx.find? (fun x => !(T.G1 1 x).all (fun y => decide (y<x)))).map reprStr

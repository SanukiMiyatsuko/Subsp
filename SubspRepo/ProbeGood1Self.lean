import Subsp.Buchholz.Rank1
open T

def genGS : Nat → List T
| 0 => [Z]
| n+1 => let p := genGS n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1GS : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1GS b
def good1GS (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def propGS (s:T) : Bool := if decide (T.isNF1 s) && idx1GS s && good1GS s then decide (s < P 1 s Z) else true
def xsGS := genGS 3
#eval xsGS.length
#eval xsGS.all propGS
#eval (xsGS.find? (fun s => !(propGS s))).map reprStr

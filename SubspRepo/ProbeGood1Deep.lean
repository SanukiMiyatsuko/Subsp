import Subsp.Buchholz.Rank1
open T

def genGD : Nat → List T
| 0 => [Z]
| n+1 => let p := genGD n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1GD : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1GD b
def deep1GD (s:T) : Bool := idx1GD s && (T.G1 0 s).all idx1GD
def good1GD (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def propGD (s:T) : Bool := if decide (T.isNF1 s) && idx1GD s && good1GD s then deep1GD s else true
def xsGD := genGD 3
#eval xsGD.length
#eval xsGD.all propGD
#eval (xsGD.find? (fun s => !(propGD s))).map reprStr

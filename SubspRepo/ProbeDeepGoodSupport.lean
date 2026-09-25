import Subsp.Buchholz.Rank1
open T

def genDG : Nat → List T
| 0 => [Z]
| n+1 => let p := genDG n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1DG : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1DG b
def deep1DG (s:T) : Bool := idx1DG s && (T.G1 0 s).all idx1DG
def good1DG (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def propDG (s:T) : Bool := if deep1DG s && good1DG s then (T.G1 0 s).all (fun x => decide (x < P 1 s Z)) else true
def xsDG := genDG 3
#eval xsDG.length
#eval xsDG.all propDG
#eval (xsDG.find? (fun s => !(propDG s))).map (fun s => (reprStr s,(T.G1 0 s).map reprStr))

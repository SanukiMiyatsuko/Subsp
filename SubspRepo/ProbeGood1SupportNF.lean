import Subsp.Buchholz.Rank1
open T

def genGSN : Nat → List T
| 0 => [Z]
| n+1 => let p := genGSN n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1GSN : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1GSN b
def good1GSN (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def propGSN (s:T) : Bool := if decide (T.isNF1 s) && idx1GSN s && good1GSN s then (T.G1 0 s).all (fun x => decide (x < P 1 s Z)) else true
def xsGSN := genGSN 3
#eval xsGSN.length
#eval xsGSN.all propGSN
#eval (xsGSN.find? (fun s => !(propGSN s))).map (fun s => (reprStr s,(T.G1 0 s).map reprStr))

import Subsp.Buchholz.Rank1
open T

def genI0 : Nat → List T
| 0 => [Z]
| n+1 => let p := genI0 n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx0I : T → Bool
| Z => true
| P p _ b => decide (p=0) && idx0I b
def propI(s:T):Bool := if decide (T.isNF1 s) && idx0I s then (T.G1 0 s).all(fun x => decide (x < s)) else true
def xsI:=genI0 3
#eval xsI.length
#eval xsI.all propI
#eval (xsI.find? (fun s => !(propI s))).map (fun s => (reprStr s, (T.G1 0 s).map reprStr))

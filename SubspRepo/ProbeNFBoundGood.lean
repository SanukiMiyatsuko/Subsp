import Subsp.Buchholz.Rank1
open T

def genNBG : Nat → List T
| 0 => [Z]
| n+1 => let p:=genNBG n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def propNBG(s:T):Bool := if decide (T.isNF1 s) && decide (s < P 1 Z Z) then (T.G1 0 s).all (fun x => decide (x<s)) else true
def xsNBG:=genNBG 3
#eval xsNBG.length
#eval xsNBG.all propNBG
#eval (xsNBG.find? (fun s => !(propNBG s))).map (fun s => (reprStr s,(T.G1 0 s).map reprStr))

import Subsp.Buchholz.Rank1
open T

def genTG : Nat → List T
| 0 => [Z]
| n+1 => let p:=genTG n; [Z] ++ [0,1].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0TG (s:T):Bool := (T.G1 0 s).all (fun x => decide (x<s))
def nfTG (s:T):Bool := decide (T.isNF1 s)
def badTG := (genTG 4).find? (fun s => match s with | Z=>false | P _ _ b => nfTG s && good0TG s && !(good0TG b))
#eval badTG.map reprStr

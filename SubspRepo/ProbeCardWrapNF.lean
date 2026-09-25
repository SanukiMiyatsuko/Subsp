import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genCWN : Nat → List T
| 0 => [Z]
| n+1 => let p := genCWN n; [Z] ++ [0,1].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1CWN : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1CWN b
def good1CWN (s:T):Bool := (T.G1 1 s).all (fun x=>decide (x<s))
def propCWN(c:T):Bool := if decide (T.isNF1 c) && idx1CWN c && good1CWN c then let A:=T.card_times 1 c; (T.G1 0 A).all (fun x=>decide (x<P 1 A Z)) else true
def xsCWN:=genCWN 3
#eval xsCWN.length
#eval xsCWN.all propCWN
#eval (xsCWN.find? (fun c=>!(propCWN c))).map (fun c=>(reprStr c,reprStr(T.card_times 1 c),(T.G1 0(T.card_times 1 c)).map reprStr))

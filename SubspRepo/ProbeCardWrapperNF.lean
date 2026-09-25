import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genCW : Nat → List T
| 0 => [Z]
| n+1 => let p:=genCW n; [Z] ++ [0,1,2].flatMap (fun i=>p.flatMap (fun a=>p.map (fun b=>P i a b)))
def idx0CW : T → Bool | Z=>true | P p _ b=>decide (p = 0)&&idx0CW b
def propCW (c:T):Bool := if decide (T.isNF1 c) && idx0CW c then let A:=T.card_times 1 c; (T.G1 0 A).all (fun x=>decide (x < T.P 1 A Z)) else true
def xsCW:=genCW 3
#eval xsCW.length
#eval xsCW.all propCW
#eval (xsCW.find? (fun c=>!(propCW c))).map reprStr

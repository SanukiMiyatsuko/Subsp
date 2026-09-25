import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genCS : Nat → List T | 0=>[Z] | n+1=>let p:=genCS n; [Z]++[0,1].flatMap (fun i=>p.flatMap (fun a=>p.map (fun b=>P i a b)))
def idx1CS : T→Bool | Z=>true | P p _ b=>decide (p ≤ 1)&&idx1CS b
def propCS (c:T):Bool := if c==Z || !(decide (T.isNF1 c)) || !(idx1CS c) then true else decide (c < T.card_times 1 c)
def xsCS:=genCS 3
#eval xsCS.length
#eval xsCS.all propCS
#eval (xsCS.find? (fun c=>!(propCS c))).map (fun c=>(reprStr c,reprStr (T.card_times 1 c)))

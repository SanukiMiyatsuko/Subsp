import Subsp.Buchholz.Rank1
open T

def genDS : Nat → List T | 0=>[Z] | n+1=>let p:=genDS n; [Z]++[0,1,2].flatMap (fun i=>p.flatMap (fun a=>p.map (fun b=>P i a b)))
def idx1DS : T→Bool | Z=>true | P p _ b=>decide (p≤1)&&idx1DS b
def deep1DS(s:T):Bool:=idx1DS s&&(T.G1 0 s).all idx1DS
def propDS(s:T):Bool:=if s==Z || !deep1DS s then true else decide (s<P 1 s Z)
def xsDS:=genDS 3
#eval xsDS.length
#eval xsDS.all propDS
#eval (xsDS.find? (fun s=>!(propDS s))).map (fun s=>reprStr s)

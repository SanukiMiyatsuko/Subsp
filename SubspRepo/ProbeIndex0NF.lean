import Subsp.Buchholz.Rank1
open T
def gen : Nat → List T | 0=>[Z] | n+1=>let p:=gen n; [Z] ++ [0,1,2].flatMap(fun i=>p.flatMap(fun a=>p.map(fun b=>P i a b)))
def idx0:T→Bool | Z=>true | P p _ b=>decide(p=0) && idx0 b
def good0(x:T):Bool := decide(T.isNF1 x) && (T.G1 0 x).all(fun y=>decide(y<x))
def xs:=(gen 3).filter(fun x=>decide(T.isNF1 x)&&idx0 x)
#eval xs.length
#eval xs.all good0
#eval (xs.find? (fun x=>!good0 x)).map reprStr

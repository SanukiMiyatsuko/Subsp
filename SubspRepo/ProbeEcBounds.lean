import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T | 0=>[Z] | n+1=>let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i=>p.flatMap (fun a=>p.map (fun b=>P i a b)))
def good0 (x:T):Bool := decide (T.isNF1 x) && (T.G1 0 x).all (fun y=>decide (y<x))
def xs := (gen 3).filter good0
def leqB (a b:T):Bool := decide (a<b) || decide (a=b)
def bad := xs.findSome? (fun t => match xs.find? (fun s=>decide (s<t) && !(decide (s<T.early_collapse t))) with | none=>none | some s=>some (s,t))
#eval xs.length
#eval xs.all (fun s => leqB (T.early_collapse s) s)
#eval xs.all (fun t => xs.all (fun s => !(decide (s<t)) || decide (s < T.early_collapse t)))
#eval match bad with | none=>"none" | some p=>reprStr p.1++" / "++reprStr p.2++" ecT="++reprStr (T.early_collapse p.2)

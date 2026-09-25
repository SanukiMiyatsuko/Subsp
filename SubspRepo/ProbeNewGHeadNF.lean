import Subsp.new.subsp
import Subsp.new.trans
open T

def v2N (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2N : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2N n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2N a b) c)))
def nfN (s:new.T 2):Bool := decide (new.T.isNF s)
def propN (s:new.T 2):Bool := (new.T.G s).all (fun y=>decide (new.compareT y (new.T.head s)=Ordering.lt))
def xsN := (gen2N 3).filter nfN
#eval xsN.length
#eval xsN.all propN

#eval (xsN.find? (fun s=>!propN s)).map (fun s => (reprStr (trans s), reprStr (trans (new.T.head s)), (new.T.G s).filter (fun y=>!(decide (new.compareT y (new.T.head s)=Ordering.lt))) |>.map (fun y=>reprStr (trans y))))

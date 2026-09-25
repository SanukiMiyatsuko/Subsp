import Subsp.new.subsp
import Subsp.new.trans
open T

def v1C (a:new.T 1) := new.Vec.snoc 0 new.Vec.nil a
def gen1C : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 => let p:=gen1C n; [new.T.Z] ++ p.flatMap (fun a => p.map (fun c => new.T.P (v1C a) c))
def compC (s:new.T 1):Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y=>decide (new.compareT y s=Ordering.lt))
def propC (s:new.T 1):Bool := (new.T.G s).all (fun y=>decide (new.compareT y (new.T.head s)=Ordering.lt))
def xsC := (gen1C 4).filter compC
#eval (gen1C 4).length
#eval xsC.length
#eval xsC.all propC
#eval (xsC.find? (fun s=>!propC s)).map (fun s => (reprStr (trans s), reprStr (trans (new.T.head s)), (new.T.G s).filter (fun y=>!(decide (new.compareT y (new.T.head s)=Ordering.lt))) |>.map (fun y=>reprStr (trans y))))

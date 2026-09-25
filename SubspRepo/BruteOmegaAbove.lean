import Subsp.new.subsp

def v2oa (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def genoa : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=genoa n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2oa a b) c)))

def xs := genoa 3

def omegas := xs.filter (fun a => decide (new.T.isNFComp a) && decide (new.T.dom a = .Omega))
def chk := omegas.all (fun a => xs.all (fun b => !(decide (new.T.isNFComp b)) || !(decide (b<a)) || decide (b < new.T.fund a b)))
#eval omegas.length
#eval chk

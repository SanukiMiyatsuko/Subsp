import Subsp.new.subsp

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def nf (s:new.T 2):Bool := decide (new.T.isNF s)
def leN (a b:new.T 2):Bool := decide (new.compareT a b = Ordering.lt) || decide (new.compareT a b = Ordering.eq)
def prop (s:new.T 2):Bool := (new.T.G s).all (fun y => leN (new.T.head y) (new.T.head s))
def xs := (gen2 3).filter nf
#eval xs.length
#eval xs.all prop

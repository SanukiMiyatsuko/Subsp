import Subsp.new.subsp

def v2ct (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def genct : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=genct n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2ct a b) c)))

def nfcb (s:new.T 2) : Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
def tailbad : new.T 2 → Bool
| .Z => false
| .P _ a => nfcb (.P (v2ct new.T.Z new.T.Z) a) -- dummy no

def bad := (genct 3).find? (fun s => match s with | .Z=>false | .P _ a => nfcb s && !nfcb a)
#eval (genct 3).length
#eval bad.isSome

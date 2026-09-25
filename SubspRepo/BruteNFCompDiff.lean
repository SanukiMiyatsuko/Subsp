import Subsp.new.subsp

def v2d (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gend : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gend n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2d a b) c)))

def nfcb (s:new.T 2) : Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
def bad := (gend 3).find? (fun s => decide (new.T.isNF s) && !nfcb s)
#eval (gend 3).length
#eval bad.isSome


def shFuel : Nat → new.T 2 → String
| 0, _ => "..."
| _+1, .Z => "Z"
| n+1, .P v a => "P(" ++ shFuel n (v.idx ⟨0,by decide⟩) ++ "," ++ shFuel n (v.idx ⟨1,by decide⟩) ++ ";" ++ shFuel n a ++ ")"
#eval match bad with | none=>"none" | some s=>shFuel 10 s

import Subsp.new.stop_global_nf
open T

def v2r (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def genr : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=genr n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2r a b) c)))

def chkref := (genr 3).all (fun s => !(decide (T.isNF1 (trans s))) || decide (new.T.isNF s))
def badref := (genr 3).find? (fun s => decide (T.isNF1 (trans s)) && !(decide (new.T.isNF s)))
#eval (genr 3).length
#eval chkref
#eval badref.isSome

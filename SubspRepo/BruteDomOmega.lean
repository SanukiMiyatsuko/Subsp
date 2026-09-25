import Subsp.new.subsp

def v2o (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def geno : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=geno n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2o a b) c)))

def badO := (geno 3).filter (fun s => decide (new.T.isNF s) && decide (new.T.dom s = .Omega))
def nonTail : new.T 2 → Bool | .Z=>false | .P _ a=>!(decide (a=new.T.Z))
#eval badO.length
#eval (badO.filter nonTail).length

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def chk := (gen2 3).all (fun s => decide (new.T.isNF s) == decide (T.isNF1 (trans s)))
def bad := (gen2 3).find? (fun s => decide (new.T.isNF s) != decide (T.isNF1 (trans s)))
#eval (gen2 3).length
#eval chk
#eval bad.isSome

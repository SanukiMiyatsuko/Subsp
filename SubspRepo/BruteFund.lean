import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def gen0 : Nat → List (new.T 0)
| 0 => [new.T.Z]
| n+1 => let p:=gen0 n; [new.T.Z] ++ p.map (fun b => new.T.P new.Vec.nil b)

def gen1 : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 => let p:=gen1 n; [new.T.Z] ++ p.flatMap (fun a => p.map (fun b => new.T.P (new.Vec.snoc 0 new.Vec.nil a) b))

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))

def chk {l} (xs : List (new.T l)) := xs.all (fun s => xs.all (fun t => decide (trans (new.T.fund s t) = T.fund1 (trans s) (trans t))))
#eval (gen0 3).length
#eval chk (gen0 3)
#eval (gen1 2).length
#eval chk (gen1 2)
#eval (gen2 2).length
#eval chk (gen2 2)

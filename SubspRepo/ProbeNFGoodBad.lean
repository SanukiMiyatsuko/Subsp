import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2x (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2x : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2x n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2x a b) c)))
def nfx (s:new.T 2):Bool := decide (new.T.isNF s)
def goodx (s:new.T 2):Bool := (T.G1 0 (trans s)).all (fun y => decide (y < trans s))
def bads := (gen2x 3).filter (fun s => nfx s && !goodx s)
#eval bads.length
#eval bads.take 10 |>.map (fun s => (reprStr (trans s), (T.G1 0 (trans s)).map reprStr))

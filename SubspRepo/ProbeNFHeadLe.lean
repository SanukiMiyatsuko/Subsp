import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def nf (s:new.T 2):Bool := decide (new.T.isNF s)
def leB (a b:T):Bool := decide (a < b) || decide (a=b)
def prop (s:new.T 2):Bool := (T.G1 0 (trans s)).all (fun y => leB y (trans (new.T.head s)))
def xs := (gen2 3).filter nf
#eval xs.length
#eval xs.all prop
#eval (xs.find? (fun s => !(prop s))).map (fun s => (reprStr s, reprStr (trans s), reprStr (trans (new.T.head s)), (T.G1 0 (trans s)).map reprStr))

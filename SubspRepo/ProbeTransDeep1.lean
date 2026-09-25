import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2TD (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2TD : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2TD n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2TD a b) c)))
def idx1TD : T → Bool | Z=>true | P p _ b=>decide (p ≤ 1)&&idx1TD b
def deep1TD (s:T):Bool := idx1TD s && (T.G1 0 s).all idx1TD
def xsTD := gen2TD 3
#eval xsTD.length
#eval xsTD.all (fun s => deep1TD (trans s))
#eval (xsTD.find? (fun s => !(deep1TD (trans s)))).map (fun s=>reprStr (trans s))

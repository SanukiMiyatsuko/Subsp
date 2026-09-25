import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def ngood (x:new.T 2):Bool := decide (new.T.isNF x) && (new.T.G x).all (fun y=>decide (new.compareT y x = Ordering.lt))
def comps := (gen2 2).filter ngood
def vecs := comps.flatMap (fun a => comps.map (fun b => v2 a b))
def auxSum (v:new.Vec (new.T 2) 2) := (transAux v).2.1
def auxFound (v:new.Vec (new.T 2) 2) := (transAux v).1
def good (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y=>decide (y<x))
def idxb (u:Nat) : T → Bool | Z => true | P p _ t => decide (p≤u) && idxb u t
#eval comps.length
#eval vecs.all (fun v => decide (T.isNF1 (auxSum v)))
#eval vecs.all (fun v => good 0 (auxSum v))
#eval vecs.all (fun v => good 1 (auxSum v))
#eval vecs.all (fun v => idxb 1 (auxSum v))
#eval vecs.all (fun v => if auxFound v then good 1 (T.card_times 1 (T.one_del (auxSum v))) else true)
#eval vecs.all (fun v => if auxFound v then decide (T.isNF1 (T.one_del (auxSum v))) else true)
#eval vecs.all (fun v => if auxFound v then good 0 (T.one_del (auxSum v)) else true)
#eval vecs.all (fun v => if auxFound v then good 1 (T.one_del (auxSum v)) else true)

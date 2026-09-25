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
def vecs := comps.map (fun b => v2 new.T.Z b)
def auxSum (v:new.Vec (new.T 2) 2) := (transAux v).2.1
def chk := vecs.all (fun v => vecs.all (fun w => (decide (new.compareVec v w = Ordering.lt)) == decide (auxSum v < auxSum w)))
def F (v:new.Vec (new.T 2) 2) := T.card_times 1 (T.one_del (auxSum v))
def nzvecs := vecs.filter (fun v => (transAux v).1)
def chkF := nzvecs.all (fun v => nzvecs.all (fun w => (decide (new.compareVec v w = Ordering.lt)) == decide (F v < F w)))
#eval comps.length
#eval chk
#eval nzvecs.length
#eval chkF

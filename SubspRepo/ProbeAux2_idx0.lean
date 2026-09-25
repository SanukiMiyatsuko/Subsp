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
def idxb (u:Nat) : T → Bool | Z => true | P p _ t => decide (p≤u) && idxb u t
def leB (a b:T):Bool := decide (a < b) || decide (a = b)
#eval vecs.all (fun v => if auxFound v then leB (T.head (T.one_del (auxSum v))) (T.P 1 T.Z T.Z) else true)
#eval vecs.all (fun v => if auxFound v then idxb 0 (T.one_del (auxSum v)) else true)
#eval vecs.filter (fun v => auxFound v) |>.take 20 |>.map (fun v => reprStr (T.one_del (auxSum v)))

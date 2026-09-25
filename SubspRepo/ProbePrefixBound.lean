import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def ngood (x:new.T 2):Bool := decide (new.T.isNF x) && (new.T.G x).all (fun y=>decide (new.compareT y x = Ordering.lt))
def comps := (gen2 3).filter ngood
def vecs := comps.flatMap (fun a => comps.map (fun b => v2 a b))
def pref (v:new.Vec (new.T 2) 2) := T.card_times 1 (T.one_del (transAux v).2.1)
def sum (v:new.Vec (new.T 2) 2) := (transAux v).2.1
def leB (a b:T):Bool := decide (a<b) || decide (a=b)
def prop (v:new.Vec (new.T 2) 2):Bool := (T.G1 0 (pref v)).all (fun x => leB x (T.P 1 (sum v) T.Z))
def bad := vecs.find? (fun v => (transAux v).1 && !(prop v))
#eval match bad with | none=>"none" | some v => let p:=pref v; let s:=sum v; reprStr p ++ " sum="++reprStr s ++ " bad=" ++ match (T.G1 0 p).find? (fun x => !(leB x (T.P 1 s T.Z))) with | none=>"?" | some x=>reprStr x

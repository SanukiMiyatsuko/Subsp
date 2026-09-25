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
def badx (s:T) := (T.G1 0 s).find? (fun x => !(decide (x<s)))
def bad := vecs.find? (fun v => (transAux v).1 && match badx (pref v) with | none=>false | some _=>true)
#eval match bad with | none=>"none" | some v => let s:=pref v; reprStr s ++ " G=" ++ toString ((T.G1 0 s).map reprStr) ++ " bad=" ++ match badx s with | none=>"?" | some x=>reprStr x

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
def mid (v:new.Vec (new.T 2) 2) := let (f,s,a):=transAux v; if f then T.card_times 1 (T.one_del s)+T.early_collapse a else a
def good (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y=>decide (y<x))
#eval vecs.all (fun v=>good 0 (mid v))
#eval vecs.all (fun v=>good 1 (mid v))

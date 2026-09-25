import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p := gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0 (x:T) : Bool := decide (T.isNF1 x) && (T.G1 0 x).all (fun y => decide (y < x))
def good1 (x:T) : Bool := decide (T.isNF1 x) && (T.G1 1 x).all (fun y => decide (y < x))
def idx0 : T → Bool
| Z => true
| P p _ t => decide (p = 0) && idx0 t
def xs := (gen 3).filter good0
#eval xs.length
#eval xs.all (fun x => good1 (T.one_del (T.early_collapse x)))
#eval xs.all (fun x => idx0 (T.one_del (T.early_collapse x)))
#eval xs.all (fun a => xs.all (fun b => !(decide (a < b)) || decide (T.one_del (T.early_collapse a) < T.one_del (T.early_collapse b))))
#eval xs.all (fun a => xs.all (fun b => !(decide (a < b)) || decide (T.card_times 1 (T.one_del (T.early_collapse a)) < T.card_times 1 (T.one_del (T.early_collapse b)))))

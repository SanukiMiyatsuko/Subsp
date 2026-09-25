import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p := gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good1 (x:T) : Bool := decide (T.isNF1 x) && (T.G1 1 x).all (fun y => decide (y < x))
def idx0 : T → Bool
| Z => true
| P p _ t => decide (p = 0) && idx0 t
def xs := (gen 3).filter (fun x => good1 x && idx0 x && !(decide (x = Z)))
def bad := xs.findSome? (fun a => match xs.find? (fun b => decide (a < b) && !(decide (T.one_del a < T.one_del b))) with | none => none | some b => some (a,b))
#eval match bad with | none => "none" | some p => reprStr p.1 ++ " < " ++ reprStr p.2 ++ " -> " ++ reprStr (T.one_del p.1) ++ " / " ++ reprStr (T.one_del p.2)

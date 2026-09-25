import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p := gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0 (x:T) : Bool := decide (T.isNF1 x) && (T.G1 0 x).all (fun y => decide (y < x))
def xs := (gen 3).filter (fun x => good0 x && !decide (x = Z))
def F (x:T) := T.card_times 1 (T.one_del (T.early_collapse x))
def bad := xs.findSome? (fun a => match xs.find? (fun b => decide (a < b) && !(decide (F a < F b))) with | none => none | some b => some (a,b))
#eval match bad with | none => "none" | some p => reprStr p.1 ++ " < " ++ reprStr p.2 ++ " ; ec=" ++ reprStr (T.early_collapse p.1) ++ "/" ++ reprStr (T.early_collapse p.2) ++ " ; F=" ++ reprStr (F p.1) ++ "/" ++ reprStr (F p.2)

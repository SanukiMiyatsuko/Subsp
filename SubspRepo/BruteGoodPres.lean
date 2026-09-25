import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y => decide (y < x))
def gs := (gen 2).filter (good 0)
#eval gs.length
#eval gs.all (fun x => good 1 (T.early_collapse x))
#eval gs.all (fun x => good 0 (T.card_times 0 (T.early_collapse x)))
#eval gs.all (fun x => good 0 (T.card_times 1 (T.early_collapse x)))
#eval gs.all (fun x => good 1 (T.card_times 1 (T.early_collapse x)))
#eval gs.all (fun x => good 1 (T.card_times 2 (T.early_collapse x)))

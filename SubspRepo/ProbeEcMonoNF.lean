import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def xs := (gen 3).filter (fun x => decide (T.isNF1 x))
def bad := xs.findSome? (fun a => match xs.find? (fun b => decide (a<b) && !(decide (T.early_collapse a < T.early_collapse b))) with | none=>none | some b=>some (a,b))
#eval xs.length
#eval bad.isSome

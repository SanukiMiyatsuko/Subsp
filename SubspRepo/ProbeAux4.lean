import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v3 (a b c:new.T 3) := new.Vec.ofFn 3 (fun i => if i.val=0 then a else if i.val=1 then b else c)
def z : new.T 3 := new.T.Z
def one : new.T 3 := new.T.ofNat 1
def q : new.T 3 := new.T.P (new.Vec.ofFn 3 (fun i => if i.val=0 then one else z)) z
#eval decide (new.T.isNF q)
#eval reprStr (trans q)
#eval reprStr (T.early_collapse (trans q))
def s := (transAux (v3 z z q)).2.1
#eval reprStr s
#eval reprStr (T.one_del s)
#eval decide (T.head (T.one_del s) ≤ T.P 1 T.Z T.Z)
#eval decide (T.isNF1 (T.one_del s))
#eval decide (∀y:T, y∈T.G1 1 (T.one_del s) → y < T.one_del s)
#eval reprStr (T.card_times 1 (T.one_del s))
#eval decide (T.isNF1 (T.card_times 1 (T.one_del s)))

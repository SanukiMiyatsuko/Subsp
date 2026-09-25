import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T
def v2 (a0 a1:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a0 else a1)
def s := new.T.P (v2 new.T.Z (new.T.ofNat 1)) new.T.Z
#eval decide (new.T.isNF s)
#eval (new.T.G s).map (fun x => reprStr (trans x))
#eval (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
#eval reprStr (trans s)
#eval decide (T.isNF1 (trans s))
#eval (T.G1 0 (trans s)).map reprStr
#eval (T.G1 0 (trans s)).all (fun y => decide (y < trans s))
#eval reprStr (T.early_collapse (trans s))
#eval (T.G1 0 (T.early_collapse (trans s))).map reprStr
#eval (T.G1 0 (T.early_collapse (trans s))).all (fun y => decide (y < T.early_collapse (trans s)))

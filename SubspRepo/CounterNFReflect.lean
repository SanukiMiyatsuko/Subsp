import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def z : new.T 2 := new.T.Z
def one : new.T 2 := new.T.P (v2 z z) z
def c : new.T 2 := new.T.P (v2 z one) z
def s : new.T 2 := new.T.P (v2 c z) z
-- s NF, trans s = P0(P1ZZ)Z, but likely not NFComp
-- outer with coord0=s and coord1=one (nonzero NFComp)
def out : new.T 2 := new.T.P (v2 s one) z
#eval decide (new.T.isNF s)
#eval (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
#eval decide (new.T.isNF out)
#eval reprStr (trans s)
#eval reprStr (trans out)
#eval decide (T.isNF1 (trans out))

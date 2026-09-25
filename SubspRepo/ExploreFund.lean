import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2a : new.Vec (new.T 2) 2 := new.Vec.ofFn 2 (fun i => if i.val = 1 then new.T.ofNat 1 else new.T.ofNat 2)
def s2 : new.T 2 := new.T.P v2a new.T.Z
def t2 : new.T 2 := new.T.P (new.Vec.ofFn 2 (fun i => if i.val=0 then new.T.ofNat 1 else new.T.Z)) new.T.Z
#eval decide (trans (new.T.fund s2 t2) = T.fund1 (trans s2) (trans t2))
#eval decide (trans (new.T.fund s2 t2) = T.fund1 (trans s2) (T.ofNat 2))

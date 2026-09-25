import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v3 (a b c:new.T 3) := new.Vec.ofFn 3 (fun i => if i.val=0 then a else if i.val=1 then b else c)
def z : new.T 3 := new.T.Z
def one : new.T 3 := new.T.ofNat 1
def two : new.T 3 := new.T.ofNat 2
def auxSum (v:new.Vec (new.T 3) 3) := (transAux v).2.1
def showAux (v:new.Vec (new.T 3) 3) := reprStr (auxSum v) ++ " | del=" ++ reprStr (T.one_del (auxSum v)) ++ " | ct=" ++ reprStr (T.card_times 1 (T.one_del (auxSum v)))
#eval showAux (v3 z z one)
#eval showAux (v3 z one one)
#eval showAux (v3 z z two)
#eval decide (T.head (T.one_del (auxSum (v3 z z one))) ≤ T.P 1 T.Z T.Z)
#eval decide (T.isNF1 (T.one_del (auxSum (v3 z z one))))
#eval decide (∀y:T, y ∈ T.G1 1 (T.one_del (auxSum (v3 z z one))) → y < T.one_del (auxSum (v3 z z one)))

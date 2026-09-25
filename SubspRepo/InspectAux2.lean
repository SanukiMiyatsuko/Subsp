import Subsp.new.stop
open T

def v4 (a b c d:new.T 4) := new.Vec.ofFn 4 (fun i => if i.val=0 then a else if i.val=1 then b else if i.val=2 then c else d)
def z : new.T 4 := new.T.Z
def one : new.T 4 := new.T.ofNat 1
def two : new.T 4 := new.T.ofNat 2
def sh (v:new.Vec (new.T 4) 4) := let q:=transAux v; (reprStr q.2.1, reprStr (T.one_del q.2.1), reprStr (T.card_times 1 (T.one_del q.2.1)), toString q.1)
#eval sh (v4 z one z z)
#eval sh (v4 z z one z)
#eval sh (v4 z z z one)
#eval sh (v4 z one one z)
#eval sh (v4 z z one one)
#eval sh (v4 z one one one)

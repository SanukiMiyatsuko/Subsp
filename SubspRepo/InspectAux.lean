import Subsp.new.stop
open T

def v3 (a b c:new.T 3) := new.Vec.ofFn 3 (fun i => if i.val=0 then a else if i.val=1 then b else c)
def z : new.T 3 := new.T.Z
def one : new.T 3 := new.T.ofNat 1
def two : new.T 3 := new.T.ofNat 2
def showAux (v:new.Vec (new.T 3) 3) : String := let q:=transAux v; toString q.1 ++ " | " ++ reprStr q.2.1 ++ " | " ++ reprStr q.2.2
#eval showAux (v3 z z z)
#eval showAux (v3 one z z)
#eval showAux (v3 z one z)
#eval showAux (v3 z two z)
#eval showAux (v3 z z one)
#eval showAux (v3 z one one)
#eval reprStr (trans (new.T.P (v3 z one z) z))
#eval reprStr (trans (new.T.P (v3 z z one) z))
#eval reprStr (trans (new.T.P (v3 one one one) z))

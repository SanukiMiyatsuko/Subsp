import Subsp.new.stop
open T

def v2 (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def z:new.T 2:=new.T.Z
def o:new.T 2:=new.T.ofNat 1
def mk (a b c:new.T 2):new.T 2 := new.T.P (v2 a b) c
def disp (x:new.T 2):String := reprStr (trans x) ++ " | ec=" ++ reprStr (T.early_collapse (trans x)) ++ " | part=" ++ reprStr (T.part (trans x)).1 ++ "/" ++ reprStr (T.part (trans x)).2
#eval disp z
#eval disp o
#eval disp (mk z o z)
#eval disp (mk o z z)
#eval disp (mk z o o)
#eval disp (mk z o (mk o z z))
#eval disp (mk z o (mk z o z))

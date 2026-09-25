import Subsp.new.stop
open T

def v2 (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def z:new.T 2:=new.T.Z
def o:new.T 2:=new.T.ofNat 1
def two:new.T 2:=new.T.ofNat 2
def mk (a b c:new.T 2):new.T 2:=new.T.P (v2 a b) c
def disp (x:new.T 2):String := reprStr (_root_.trans x)++" ec="++reprStr (T.early_collapse (_root_.trans x))++" od="++reprStr (T.one_del (T.early_collapse (_root_.trans x)))
#eval disp z
#eval disp o
#eval disp two
#eval disp (mk z o z)
#eval disp (mk o z z)
#eval disp (mk z o o)

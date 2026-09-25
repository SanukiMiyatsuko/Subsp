import Subsp.new.stop
open T

def showT : T → String
| .Z => "Z"
| .P n a b => "P(" ++ toString n ++ "," ++ showT a ++ "," ++ showT b ++ ")"

def loop (l n : Nat) : String := showT (trans (new.T.LF l n))
#eval loop 0 0
#eval loop 0 1
#eval loop 0 2
#eval loop 1 1
#eval loop 1 2
#eval loop 2 1
#eval loop 2 2
#eval loop 3 1
#eval loop 3 2

def bs (k n:Nat) : new.T (k+1) := new.T.P (new.Vec.ofFn (k+1) (fun i => if i.val=0 then new.T.LF (k+1) n else new.T.Z)) new.T.Z
#eval showT (trans (bs 0 2))
#eval showT (trans (bs 1 2))
#eval showT (trans (bs 2 2))

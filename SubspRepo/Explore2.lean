import Subsp.new.stop
open T

def showT : T → String
| .Z => "Z"
| .P n a b => "P(" ++ toString n ++ "," ++ showT a ++ "," ++ showT b ++ ")"

def nb (l:Nat) : new.T l := new.T.P (new.Vec.ofFn l (fun x => if x.val=1 then new.T.P (new.Vec.ofFn l (fun _ => new.T.Z)) new.T.Z else new.T.Z)) new.T.Z
#eval showT (trans (nb 0))
#eval showT (trans (nb 1))
#eval showT (trans (nb 2))
#eval showT (trans (nb 3))
#eval showT (trans (nb 4))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def showNewDom : new.Dom → String
| .zero => "zero" | .one => "one" | .omega => "omega" | .Omega => "Omega"
def showOldDom : Dom1 → String
| .Zero => "Zero" | .One => "One" | .ω => "w" | .Ω n => s!"O{n}"

def v2 (a0 a1 : new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a0 else a1)
def p2 (a0 a1 : new.T 2) := new.T.P (v2 a0 a1) new.T.Z

#eval showNewDom (new.T.dom (new.T.Z : new.T 2)) ++ "/" ++ showOldDom (T.dom1 (trans (new.T.Z : new.T 2)))
#eval showNewDom (new.T.dom (new.T.ofNat (lam:=2) 1)) ++ "/" ++ showOldDom (T.dom1 (trans (new.T.ofNat (lam:=2) 1)))
#eval showNewDom (new.T.dom (p2 (new.T.ofNat 1) new.T.Z)) ++ "/" ++ showOldDom (T.dom1 (trans (p2 (new.T.ofNat 1) new.T.Z)))
#eval showNewDom (new.T.dom (p2 new.T.Z (new.T.ofNat 1))) ++ "/" ++ showOldDom (T.dom1 (trans (p2 new.T.Z (new.T.ofNat 1))))
#eval reprStr (trans (p2 new.T.Z (new.T.ofNat 1)))

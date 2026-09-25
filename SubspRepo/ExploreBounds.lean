import Subsp.new.stop_global_nf
open T

def BoldX : Nat → T
| 0 => P 0 (P 0 Z Z) Z
| 1 => P 0 (P 1 Z Z) Z
| n' + 1 => P 0 (P 1 (P 1 (mul (P 1 Z Z) (ofNat n')) Z) Z) Z

def BnewX (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun x => if x.val = 1 then new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z else new.T.Z)) new.T.Z

def cmp (a b:T):String := match T.compareT a b with | .lt=>"lt"|.eq=>"eq"|.gt=>"gt"
#eval cmp (trans (BnewX 2)) (BoldX 2)
#eval cmp (trans (BnewX 3)) (BoldX 3)
#eval cmp (trans (BnewX 4)) (BoldX 4)
#eval reprStr (trans (BnewX 2))
#eval reprStr (trans (BnewX 3))
#eval reprStr (trans (BnewX 4))

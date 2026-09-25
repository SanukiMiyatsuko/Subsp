import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def Bold : Nat → T
| 0 => P 0 (P 0 Z Z) Z
| 1 => P 0 (P 1 Z Z) Z
| n' + 1 => P 0 (P 1 (P 1 (mul (P 1 Z Z) (ofNat n')) Z) Z) Z

def Bnew (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun x => if x.val = 1 then new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z else new.T.Z)) new.T.Z

#eval reprStr (trans (Bnew 2))
#eval reprStr (Bold 2)
#eval reprStr (trans (Bnew 3))
#eval reprStr (Bold 3)
#eval reprStr (T.fund1 (Bold 2) (T.ofNat 0))
#eval reprStr (T.fund1 (Bold 2) (T.ofNat 1))
#eval reprStr (trans (new.T.P (new.Vec.ofFn 2 (fun i => if i.val=0 then new.T.LF 2 0 else new.T.Z)) new.T.Z))
#eval reprStr (trans (new.T.P (new.Vec.ofFn 2 (fun i => if i.val=0 then new.T.LF 2 1 else new.T.Z)) new.T.Z))

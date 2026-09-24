import Subsp.order
import Subsp.Buchholz.Base
import Subsp.Buchholz.Rank1
import Subsp.new.Base
import Subsp.new.subsp
import Subsp.new.trans

theorem new.T.OT_iff_NF (lam : Nat) (s : T lam) : isOT lam s ↔ isNF s ∧ (1 < lam → s < P (Vec.ofFn lam (fun x => if x.val = 1 then P (Vec.ofFn lam (fun y => Z)) Z else Z)) Z) := sorry

theorem NF_is_NF1 (lam : Nat) (s : new.T lam) : new.T.isNF s → T.isNF1 (trans s) := sorry

theorem order_embeding (lam : Nat) (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) : s < t ↔ trans s < trans t := sorry

def new.T.NF (lam : Nat) := { s : T lam // isNF s }

theorem wellfounded_NF (lam : Nat) : WellFounded (fun s t : new.T.NF lam => s.val < t.val) := sorry

def T.isSubNF (n : Nat) (s : T) :=
  isNF1 s ∧
    match n with
    | 0 => s < P 0 (P 1 Z Z) Z
    | _ + 1 => s < P 0 (P 1 (P 1 (mul (P 1 Z Z) (ofNat n)) Z) Z) Z

theorem OT_iff_NF1 (lam : Nat) (s : new.T (lam + 1)) : new.T.isOT (lam + 1) s ↔ T.isSubNF lam (trans s) := sorry

def new.T.OT (lam : Nat) := { s : T lam // isOT lam s }

theorem wellfounded_OT (lam : Nat) : WellFounded (fun s t : new.T.OT lam => s.val < t.val) := sorry

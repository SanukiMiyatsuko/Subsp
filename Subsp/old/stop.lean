import Subsp.Buchholz.Rank1
import Subsp.old.subsp

def T.isSubNF (n : Nat) (s : T) :=
  isNF1 s ∧ s < P 0 (P n Z Z) Z

def T.SubNF (lam : Nat) := { s : T // T.isSubNF lam s }

theorem OT_SubNF_order_iso (lam : Nat) :
    ∃ f : new.T.OT lam → T.SubNF lam,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  sorry

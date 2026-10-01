import Subsp.old.stop_low_dims
import Subsp.old.stop_translation

theorem OT_SubNF_order_iso (lam : Nat) :
    ∃ f : new.T.OT lam → T.SubNF lam,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  sorry

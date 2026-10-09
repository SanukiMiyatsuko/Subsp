import Subsp.Buchholz.Rank1
import Subsp.multi.emp.nt

def T.SubNF := { s : T // T.isNF1 s ∧ s < P 0 (P 1 (P 1 (P 1 (P 0 Z Z) Z) Z) Z) Z }

theorem NOT_SubNF_order_iso :
    ∃ f : emp.sys.NOT → T.SubNF,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  sorry

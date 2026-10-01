import Subsp.old.stop_collapse

/-! Elementary algebra for the indexed legacy cardinal multiplier. -/

namespace LegacyTranslation

open T

theorem card_times_ne_zero (n : Nat) (s : T) (hs : s ≠ T.Z) :
    T.card_times n s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P p a b =>
      simp only [T.card_times]
      split <;> split <;> split <;> split <;>
        intro h <;> cases h

theorem card_times_add (n : Nat) (a b : T) :
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  induction a with
  | Z => rfl
  | P p x y _ ih =>
      rw [T.P_add_eq]
      simp only [T.card_times]
      rw [ih, Rank1Termination.add_assoc]

theorem one_del_NF (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.one_del s) := by
  cases s with
  | Z => exact hs
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z =>
              simpa [T.one_del] using (T.isNF1_P_inv 0 T.Z b hs).2.1
          | P q c d => simpa [T.one_del] using hs
      | succ p => simpa [T.one_del] using hs

theorem one_del_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) :
    T.index_Prop1 n (T.one_del s) := by
  cases hs with
  | z => exact .z
  | p p a b hp hb =>
      cases p with
      | zero =>
          cases a with
          | Z => simpa [T.one_del] using hb
          | P q c d =>
              simpa [T.one_del] using
                (T.index_Prop1.p 0 (T.P q c d) b hp hb)
      | succ p =>
          simpa [T.one_del] using
            (T.index_Prop1.p (p + 1) a b hp hb)

end LegacyTranslation

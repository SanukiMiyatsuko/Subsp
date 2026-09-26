import Subsp.new.stop_nf_order_c

open T

namespace StopSurjMeasure

-- Count nesting through exponents; appending a tail does not add a level.
def degree : T → Nat
  | T.Z => 0
  | T.P _ a b => max (degree a + 1) (degree b)

theorem degree_add (a b : T) : degree (T.add a b) = max (degree a) (degree b) := by
  induction a with
  | Z =>
      rw [T.add.eq_1, degree, Nat.zero_max]
  | P p c d ihc ihd =>
      rw [T.P_add_eq, degree, ihd, degree, Nat.max_assoc]

theorem degree_part (a : T) : degree (T.part a).1 ≤ degree a ∧
    degree (T.part a).2 ≤ degree a := by
  induction a with
  | Z => exact ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | P p c d ihc ihd =>
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [T.part, ite_eq_left hp]
        exact ⟨Nat.zero_le _, Nat.le_refl _⟩
      · intro hp
        rw [T.part, ite_eq_right hp]
        constructor
        · change max (degree c + 1) (degree (T.part d).1) ≤ max (degree c + 1) (degree d)
          exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ihd.1 (Nat.le_max_right _ _)⟩
        · exact Nat.le_trans ihd.2 (Nat.le_max_right _ _)

theorem degree_middle_lt (p : Nat) (a b : T) : degree a < degree (T.P p a b) := by
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (degree a)) (Nat.le_max_left _ _)

theorem degree_tail_le (p : Nat) (a b : T) : degree b ≤ degree (T.P p a b) := by
  exact Nat.le_max_right _ _

theorem degree_pos (s : T) (hs : s ≠ T.Z) : 0 < degree s := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P p a b => exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_max_left _ _)

end StopSurjMeasure

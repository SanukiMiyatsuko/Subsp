import AuxCore

open T

theorem tac_a0 {lam : Nat} : ∀ (k : Nat)
    (v : new.Vec (new.T lam) (k + 1)),
    (transAux v).2.2 = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  intro k
  induction k with
  | zero =>
    intro v
    cases v with
    | snoc n xs a =>
      cases xs with
      | nil =>
        rw [transAux.eq_2]
        rfl
  | succ k ih =>
    intro v
    cases v with
    | snoc n xs a =>
      rw [transAux.eq_3]
      cases haux : transAux xs with
      | mk found rest =>
        cases rest with
        | mk sum a0 =>
          have hrec := ih xs
          rw [haux] at hrec
          change a0 = trans (xs.idx ⟨0, Nat.zero_lt_succ k⟩) at hrec
          change a0 = trans (xs.idx ⟨0, Nat.zero_lt_succ k⟩)
          exact hrec

#print axioms tac_a0

import Subsp.old.stop_source_components

/-! Canonical case splits for indexed source domains of principal terms. -/

namespace new

theorem T.dom_PZ_Omega_split {lam : Nat}
    (ls : Vec (T lam) lam) (i : Fin lam)
    (hd : T.dom (T.P ls T.Z) = .Omega i) :
    ∃ m : Fin lam, ∃ d : Dom lam,
      T.domVecMinIdx ls = some (m, d) ∧
        ((d = .one ∧ 0 < m.val ∧ i = m) ∨
          ∃ j : Fin lam, d = .Omega j ∧ j ≤ m ∧ i = j) := by
  rw [T.dom, ite_eq_left rfl] at hd
  cases hmin : T.domVecMinIdx ls with
  | none =>
      rw [hmin] at hd
      cases hd
  | some md =>
      obtain ⟨m, d⟩ := md
      refine ⟨m, d, hmin, ?_⟩
      rw [hmin] at hd
      cases d with
      | zero => cases hd
      | omega => cases hd
      | one =>
          by_cases hm : m.val = 0
          · simp [hm] at hd
          · simp only [hm, ite_false] at hd
            cases hd
            exact Or.inl ⟨rfl, Nat.pos_of_ne_zero hm, rfl⟩
      | Omega j =>
          by_cases hjm : j ≤ m
          · simp only [hjm, ite_true] at hd
            cases hd
            exact Or.inr ⟨j, rfl, hjm, rfl⟩
          · simp [hjm] at hd

theorem T.dom_PZ_omega_split {lam : Nat}
    (ls : Vec (T lam) lam)
    (hd : T.dom (T.P ls T.Z) = .omega) :
    ∃ m : Fin lam, ∃ d : Dom lam,
      T.domVecMinIdx ls = some (m, d) ∧
        ((d = .one ∧ m.val = 0) ∨
          d = .omega ∨
          ∃ j : Fin lam, d = .Omega j ∧ ¬ j ≤ m) := by
  rw [T.dom, ite_eq_left rfl] at hd
  cases hmin : T.domVecMinIdx ls with
  | none =>
      rw [hmin] at hd
      cases hd
  | some md =>
      obtain ⟨m, d⟩ := md
      have hspec := T.domVecMinIdx_some_spec ls m d hmin
      refine ⟨m, d, hmin, ?_⟩
      rw [hmin] at hd
      cases d with
      | zero => exact False.elim (hspec.1 rfl)
      | omega => exact Or.inr (Or.inl rfl)
      | one =>
          by_cases hm : m.val = 0
          · exact Or.inl ⟨rfl, hm⟩
          · simp [hm] at hd
      | Omega j =>
          by_cases hjm : j ≤ m
          · simp [hjm] at hd
          · exact Or.inr (Or.inr ⟨j, rfl, hjm⟩)

end new

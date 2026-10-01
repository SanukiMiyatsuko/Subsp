import Subsp.old.stop_source_domain_split

/-! Positivity of indexed uncountable domains. -/

namespace new

theorem T.dom_Omega_pos {lam : Nat} :
    ∀ (s : T lam) (i : Fin lam), T.dom s = .Omega i → 0 < i.val := by
  intro s
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      intro i hd
      cases s with
      | Z => cases hd
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            rw [T.dom, ite_eq_left rfl] at hd
            cases hmin : T.domVecMinIdx ls with
            | none => rw [hmin] at hd; cases hd
            | some md =>
                obtain ⟨m, d⟩ := md
                rw [hmin] at hd
                have hspec := T.domVecMinIdx_some_spec ls m d hmin
                cases d with
                | zero => cases hd
                | omega => cases hd
                | one =>
                    by_cases hm : m.val = 0
                    · simp [hm] at hd
                    · simp only [hm, ite_false] at hd
                      cases hd
                      exact Nat.pos_of_ne_zero hm
                | Omega j =>
                    by_cases hjm : j ≤ m
                    · simp only [hjm, ite_true] at hd
                      cases hd
                      exact ih (ls.idx m) (T.idx_size_lt_P ls T.Z m) j hspec.2.1
                    · simp [hjm] at hd
          · rw [T.dom, ite_eq_right hadd] at hd
            exact ih add (T.add_size_lt_P ls add) i hd

end new

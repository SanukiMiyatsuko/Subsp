import Subsp.old.outer_trans
import Subsp.Buchholz.Rank1

namespace new

/-- Every indexed old Omega-domain has a positive index. -/
theorem T.dom_Omega_pos {lam : Nat} (s : T lam) (i : Fin lam)
    (hdom : T.dom s = .Omega i) : 0 < i.val := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z => cases hdom
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            simp only [T.dom, ite_true] at hdom
            cases hmin : T.domVecMinIdx ls with
            | none => rw [hmin] at hdom; cases hdom
            | some md =>
                obtain ⟨m, d⟩ := md
                rw [hmin] at hdom
                have hspec := T.domVecMinIdx_some_spec ls m d hmin
                cases d with
                | zero => exact False.elim (hspec.1 rfl)
                | one =>
                    by_cases hm : m.val = 0
                    · simp [hm] at hdom
                    · simp [hm] at hdom
                      cases hdom
                      exact Nat.pos_of_ne_zero hm
                | omega => cases hdom
                | Omega j =>
                    by_cases hjm : j ≤ m
                    · simp [hjm] at hdom
                      cases hdom
                      exact ih (ls.idx m) (T.idx_size_lt_P ls T.Z m) hspec.2.1
                    · simp [hjm] at hdom
          · rw [T.dom, ite_eq_right hadd] at hdom
            exact ih add (T.add_size_lt_P ls add) hdom

end new

namespace new

theorem trans_ofNat {lam : Nat} (n : Nat) :
    _root_.trans (T.ofNat (lam := lam) n) = _root_.T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases lam with
      | zero =>
          rw [T.ofNat, _root_.trans]
          simp only [Vec.ofFn, transAux]
          rw [ih, _root_.T.P_Z_add]
          rfl
      | succ k =>
          rw [T.ofNat]
          have hz : Vec.outer0 (Vec.ofFn (k + 1) (fun _ => (T.Z : T (k + 1)))) := by
            intro i hi
            rw [Vec.ofFn_idx]
          rw [trans_outer0_P _ _ hz]
          simp [Vec.ofFn_idx, _root_.T.ofNat, ih]

end new

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

theorem T.dom_PZ_ne_zero {lam : Nat} (ls : Vec (T lam) lam) :
    T.dom (T.P ls T.Z) ≠ .zero := by
  cases hmin : T.domVecMinIdx ls with
  | none => simp [T.dom, hmin]
  | some md =>
      obtain ⟨m, d⟩ := md
      cases d with
      | zero => simp [T.dom, hmin]
      | one => by_cases hm : m.val = 0 <;> simp [T.dom, hmin, hm]
      | omega => simp [T.dom, hmin]
      | Omega i => by_cases hi : i ≤ m <;> simp [T.dom, hmin, hi]

theorem T.dom_ne_zero_of_ne_Z {lam : Nat} (s : T lam) (hne : s ≠ T.Z) :
    T.dom s ≠ .zero := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z => exact False.elim (hne rfl)
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            exact T.dom_PZ_ne_zero ls
          · rw [T.dom, ite_eq_right hadd]
            exact ih add (T.add_size_lt_P ls add) hadd

theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam)
    (hdom : T.dom s = .zero) : s = T.Z := by
  cases s with
  | Z => rfl
  | P ls add =>
      exact False.elim
        (T.dom_ne_zero_of_ne_Z (T.P ls add) (by intro h; cases h) hdom)

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

namespace new

theorem transAux_fst_ne_Z {lam k : Nat} (v : Vec (T lam) k) :
    (transAux v).1 ≠ _root_.T.Z := by
  induction v with
  | nil => simp [transAux]
  | snoc k xs x ih =>
      cases k with
      | zero =>
          cases xs
          cases x <;> simp [transAux]
      | succ m =>
          cases x with
          | Z => simpa [transAux] using ih
          | P ls add => simp [transAux]

theorem target_add_ne_Z_left (a b : _root_.T) (ha : a ≠ _root_.T.Z) :
    a + b ≠ _root_.T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p x y =>
      intro h
      cases b <;> cases h

theorem trans_eq_Z_iff {lam : Nat} (s : T lam) :
    _root_.trans s = _root_.T.Z ↔ s = T.Z := by
  cases s with
  | Z => simp [_root_.trans]
  | P ls add =>
      constructor
      · intro h
        rw [_root_.trans] at h
        exact False.elim (target_add_ne_Z_left _ _ (transAux_fst_ne_Z ls) h)
      · intro h; cases h

end new

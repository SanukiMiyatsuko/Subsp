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

theorem Vec.outer0_min_index_zero {lam : Nat}
    (ls : Vec (T lam) lam) (hls : Vec.outer0 ls)
    (m : Fin lam) (d : Dom lam)
    (hmin : T.domVecMinIdx ls = some (m, d)) :
    m.val = 0 := by
  have hspec := T.domVecMinIdx_some_spec ls m d hmin
  by_cases hm : m.val = 0
  · exact hm
  · have hz := hls m hm
    have hd := hspec.2.1
    rw [hz] at hd
    exact False.elim (hspec.1 hd.symm)

theorem T.outer0_Omega_not_le {lam : Nat}
    (ls : Vec (T lam) lam) (hls : Vec.outer0 ls)
    (m i : Fin lam)
    (hmin : T.domVecMinIdx ls = some (m, Dom.Omega i)) :
    ¬ i ≤ m := by
  intro him
  have hm0 := Vec.outer0_min_index_zero ls hls m (.Omega i) hmin
  have hiPos := T.dom_Omega_pos (ls.idx m) i
    (T.domVecMinIdx_some_spec ls m (.Omega i) hmin).2.1
  have hval : i.val ≤ m.val := him
  omega

theorem T.fund_PZ_outer0_Omega {lam : Nat}
    (ls : Vec (T lam) lam) (hls : Vec.outer0 ls)
    (t : T lam) (m i : Fin lam)
    (hmin : T.domVecMinIdx ls = some (m, Dom.Omega i)) :
    T.fund (T.P ls T.Z) t =
      T.P (ls.rplc m
        (T.fund ls[m] (T.iter (fun x => T.fund ls[m] x) t))) T.Z := by
  rw [T.fund_PZ_Omega ls t m i hmin,
    ite_eq_right (T.outer0_Omega_not_le ls hls m i hmin)]

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


namespace new

def T.outerChain {lam : Nat} : T lam → Prop
| .Z => True
| .P ls add => Vec.outer0 ls ∧ T.outerChain add

theorem T.outerChain_mul_PZ {lam : Nat}
    (v : Vec (T lam) lam) (t : T lam)
    (hv : Vec.outer0 v) :
    T.outerChain (T.mul (T.P v T.Z) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => trivial
  | P tls add _ ih =>
      rw [T.mul]
      change Vec.outer0 v ∧ T.outerChain (T.mul (T.P v T.Z) add)
      exact ⟨hv, ih⟩
  | nil => trivial
  | snoc => trivial

theorem T.outerChain_fund {lam : Nat}
    (s t : T lam) (hs : T.outerChain s) :
    T.outerChain (T.fund s t) := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z => simp [T.fund, T.outerChain]
      | P ls add =>
          have hls : Vec.outer0 ls := hs.1
          have haddChain : T.outerChain add := hs.2
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none => rw [T.fund_PZ_none ls t hmin]; trivial
            | some md =>
                obtain ⟨m, d⟩ := md
                have hm0 := Vec.outer0_min_index_zero ls hls m d hmin
                have hrplc (u : T lam) : Vec.outer0 (ls.rplc m u) :=
                  Vec.outer0_rplc_zero ls m u hls hm0
                cases d with
                | zero =>
                    exact False.elim ((T.domVecMinIdx_some_spec ls m .zero hmin).1 rfl)
                | one =>
                    rw [T.fund, ite_eq_left rfl, hmin]
                    obtain ⟨mv, mh⟩ := m
                    cases mv with
                    | zero =>
                        exact T.outerChain_mul_PZ _ t (hrplc _)
                    | succ r =>
                        change r + 1 = 0 at hm0
                        exact False.elim (Nat.noConfusion hm0)
                | omega =>
                    rw [T.fund, ite_eq_left rfl, hmin]
                    exact ⟨hrplc _, trivial⟩
                | Omega i =>
                    rw [T.fund_PZ_outer0_Omega ls hls t m i hmin]
                    exact ⟨hrplc _, trivial⟩
          · rw [T.fund, ite_eq_right hadd]
            exact ⟨hls, ih add (T.add_size_lt_P ls add) t haddChain⟩

theorem T.base_succ_outerChain (k n : Nat) :
    T.outerChain
      (T.P (Vec.ofFn (k + 1)
        (fun i => if i.val = 0 then T.LF (k + 1) n else T.Z)) T.Z) := by
  constructor
  · intro i hi
    rw [Vec.ofFn_idx]
    simp [hi]
  · trivial

theorem T.isOT_outerChain {lam : Nat} {s : T lam} (hs : T.isOT lam s) :
    T.outerChain s := by
  induction hs with
  | base_0 n =>
      induction n with
      | zero => trivial
      | succ n ih =>
          rw [T.LF]
          exact ⟨fun i => i.elim0, ih⟩
  | base_succ k n => exact T.base_succ_outerChain k n
  | step lam s hs n ih => exact T.outerChain_fund s (T.ofNat n) ih

theorem T.outerChain_dom_not_Omega {lam : Nat}
    (s : T lam) (hs : T.outerChain s) (i : Fin lam) :
    T.dom s ≠ .Omega i := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z => intro hd; cases hd
      | P ls add =>
          have hls := hs.1
          have ha := hs.2
          by_cases hadd : add = T.Z
          · subst add
            intro hd
            simp only [T.dom, ite_true] at hd
            cases hmin : T.domVecMinIdx ls with
            | none => rw [hmin] at hd; cases hd
            | some md =>
                obtain ⟨m, d⟩ := md
                rw [hmin] at hd
                have hm0 := Vec.outer0_min_index_zero ls hls m d hmin
                cases d with
                | zero =>
                    exact False.elim ((T.domVecMinIdx_some_spec ls m .zero hmin).1 rfl)
                | one => simp [hm0] at hd
                | omega => cases hd
                | Omega j =>
                    have hjpos := T.dom_Omega_pos (ls.idx m) j
                      (T.domVecMinIdx_some_spec ls m (.Omega j) hmin).2.1
                    have hjm : ¬ j ≤ m := by
                      intro hjm
                      have hv : j.val ≤ m.val := hjm
                      omega
                    simp [hjm] at hd
          · rw [T.dom, ite_eq_right hadd]
            exact ih add (T.add_size_lt_P ls add) ha

theorem T.isOT_dom_not_Omega {lam : Nat} {s : T lam}
    (hs : T.isOT lam s) (i : Fin lam) :
    T.dom s ≠ .Omega i :=
  T.outerChain_dom_not_Omega s (T.isOT_outerChain hs) i

end new

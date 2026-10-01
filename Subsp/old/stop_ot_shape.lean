import Subsp.old.stop_source_ot_bound
import Subsp.old.stop_outer

/-! Outer-zero shape of legacy OT terms and its preservation by fundamental sequences. -/

namespace new

def Vec.outer0 {lam : Nat} (v : Vec (T lam) lam) : Prop :=
  ∀ i : Fin lam, i.val ≠ 0 → v.idx i = T.Z

def T.outer0 {lam : Nat} : T lam → Prop
  | .Z => True
  | .P ls _ => Vec.outer0 ls

theorem Vec.outer0_rplc_zero {lam : Nat}
    (v : Vec (T lam) lam) (m : Fin lam) (a : T lam)
    (hv : Vec.outer0 v) (hm : m.val = 0) :
    Vec.outer0 (v.rplc m a) := by
  intro j hj
  rw [Vec.rplc_idx_of_ne v m j a (by omega)]
  exact hv j hj

theorem T.outer0_mul_PZ {lam : Nat}
    (v : Vec (T lam) lam) (t : T lam)
    (hv : Vec.outer0 v) :
    T.outer0 (T.mul (T.P v T.Z) t) := by
  cases t with
  | Z => simp [T.mul, T.outer0]
  | P tls add =>
      change Vec.outer0 v
      exact hv

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
            | none =>
                rw [T.fund, ite_eq_left rfl, hmin]
                trivial
            | some md =>
                obtain ⟨m, d⟩ := md
                have hm0 := Vec.outer0_min_index_zero ls hls m d hmin
                have hrplc (u : T lam) : Vec.outer0 (ls.rplc m u) :=
                  Vec.outer0_rplc_zero ls m u hls hm0
                rw [T.fund, ite_eq_left rfl, hmin]
                cases d with
                | zero =>
                    exact False.elim ((T.domVecMinIdx_some_spec ls m .zero hmin).1 rfl)
                | one =>
                    obtain ⟨mv, mh⟩ := m
                    cases mv with
                    | zero => exact T.outerChain_mul_PZ _ t (hrplc _)
                    | succ r =>
                        change r + 1 = 0 at hm0
                        exact False.elim (Nat.noConfusion hm0)
                | omega => exact ⟨hrplc _, trivial⟩
                | Omega i =>
                    have hnot := T.outer0_Omega_not_le ls hls m i hmin
                    simp only [hnot, ite_false]
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

theorem T.isOT_outerChain {lam : Nat} {s : T lam}
    (hs : T.isOT lam s) : T.outerChain s := by
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


end new

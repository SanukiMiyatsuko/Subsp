import Subsp.old.stop_basic

/-! Countable head indices in the legacy OT fundamental-sequence closure. -/

namespace new

inductive T.Countable {lam : Nat} : T lam → Prop where
  | z : Countable T.Z
  | p (v : Vec (T lam) lam) (b : T lam)
      (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
      (hb : Countable b) : Countable (T.P v b)

theorem T.Countable_min_zero {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
    (m : Fin lam) (d : Dom lam) (hm : T.domVecMinIdx v = some (m, d)) : m.val = 0 := by
  have hspec := T.domVecMinIdx_some_spec v m d hm
  by_cases hzero : m.val = 0
  · exact hzero
  · have he : v.idx m = T.Z := hv m (Nat.pos_of_ne_zero hzero)
    rw [he] at hspec
    exact False.elim (hspec.1 hspec.2.1.symm)

theorem T.Countable_rplc_zero {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
    (m : Fin lam) (hm : m.val = 0) (a : T lam) :
    ∀ i : Fin lam, 0 < i.val → (v.rplc m a).idx i = T.Z := by
  intro i hi
  rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega)]
  exact hv i hi

theorem T.Countable_mul {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z) (t : T lam) :
    T.Countable (T.mul (T.P v T.Z) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact .z
  | P _ b _ ih => exact .p v _ hv ih
  | nil => trivial
  | snoc => trivial

theorem T.Countable_fund {lam : Nat} (s : T lam) (hs : T.Countable s) (t : T lam) :
    T.Countable (T.fund s t) := by
  induction hs with
  | z => rw [T.fund]; exact .z
  | p v b hv hb ih =>
      by_cases hbz : b = T.Z
      · subst b
        rw [T.fund, ite_eq_left rfl]
        cases hmin : T.domVecMinIdx v with
        | none => exact .z
        | some md =>
            obtain ⟨m, d⟩ := md
            have hm := T.Countable_min_zero v hv m d hmin
            have hrep (a) := T.Countable_rplc_zero v hv m hm a
            cases d with
            | zero => exact .p _ _ (hrep _) .z
            | omega => exact .p _ _ (hrep _) .z
            | Omega i =>
                dsimp only
                split <;> exact .p _ _ (hrep _) .z
            | one =>
                obtain ⟨mv, mh⟩ := m
                change mv = 0 at hm
                subst mv
                exact T.Countable_mul _ (hrep _) t
      · rw [T.fund, ite_eq_right hbz]
        exact .p v _ hv ih

theorem T.Countable_LF_zero (n : Nat) : T.Countable (T.LF 0 n) := by
  induction n with
  | zero => exact .z
  | succ n ih => exact .p Vec.nil _ (fun i => i.elim0) ih

theorem T.isOT_Countable (lam : Nat) (s : T lam) (hs : T.isOT lam s) : T.Countable s := by
  induction hs with
  | base_0 n => exact T.Countable_LF_zero n
  | base_succ k n =>
      refine .p _ T.Z ?_ .z
      intro i hi
      rw [Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hi)]
  | step lam a _ n ih => exact T.Countable_fund a ih _

theorem T.Countable_dom_not_Omega {lam : Nat} (s : T lam) (hs : T.Countable s) (i : Fin lam) :
    T.dom s ≠ .Omega i := by
  induction hs with
  | z => intro h; cases h
  | p v b hv hb ih =>
      intro hdom
      by_cases hbz : b = T.Z
      · subst b
        rw [T.dom, ite_eq_left rfl] at hdom
        cases hmin : T.domVecMinIdx v with
        | none => rw [hmin] at hdom; cases hdom
        | some md =>
            obtain ⟨m, d⟩ := md
            have hm := T.Countable_min_zero v hv m d hmin
            have hspec := T.domVecMinIdx_some_spec v m d hmin
            rw [hmin] at hdom
            cases d with
            | zero => cases hdom
            | omega => cases hdom
            | one => simp [hm] at hdom
            | Omega j =>
                have hj := T.dom_Omega_pos _ j hspec.2.1
                have hnot : ¬ j ≤ m := by
                  change ¬ j.val ≤ m.val
                  omega
                simp [hnot] at hdom
      · rw [T.dom, ite_eq_right hbz] at hdom
        exact ih hdom

theorem T.isOT_dom_not_Omega (lam : Nat) (s : T lam) (hs : T.isOT lam s) (i : Fin lam) :
    T.dom s ≠ .Omega i := T.Countable_dom_not_Omega s (T.isOT_Countable lam s hs) i

def T.OTBound (lam : Nat) : T lam :=
  T.P (Vec.ofFn lam (fun i => if i.val = 1 then T.ofNat 1 else T.Z)) T.Z

theorem T.Countable_lt_OTBound {lam : Nat} (s : T lam) (hs : T.Countable s) (hlam : 1 < lam) :
    s < T.OTBound lam := by
  cases hs with
  | z => rfl
  | p v b hv _ =>
      apply T.P_lt_P_of_compareVec_lt
      apply Vec.compare_lt_of_pivot _ _ ⟨1, hlam⟩
      · intro j hj
        rw [hv j (Nat.lt_trans (Nat.zero_lt_succ 0) hj), Vec.ofFn_idx,
          ite_eq_right (Nat.ne_of_gt hj)]
      · rw [hv ⟨1, hlam⟩ (Nat.zero_lt_succ 0), Vec.ofFn_idx, ite_eq_left rfl]
        rfl

theorem T.isOT_lt_OTBound (lam : Nat) (s : T lam) (hs : T.isOT lam s) (hlam : 1 < lam) :
    s < T.OTBound lam := T.Countable_lt_OTBound s (T.isOT_Countable lam s hs) hlam

end new

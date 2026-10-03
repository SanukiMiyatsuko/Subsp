import Subsp.old.subsp

/-! Basic comparison and fundamental-sequence lemmas for the indexed legacy domain. -/

namespace new

theorem T.domVecMinIdx_spec {lam m : Nat} (v : Vec (T lam) m) :
    match T.domVecMinIdx v with
    | none => ∀ i : Fin m, T.dom (v.idx i) = .zero
    | some (i, d) => d ≠ .zero ∧ T.dom (v.idx i) = d ∧
        ∀ j : Fin m, j.val < i.val → T.dom (v.idx j) = .zero := by
  induction v with
  | nil => exact fun i => i.elim0
  | snoc k xs x ih =>
      rw [T.domVecMinIdx]
      cases hrec : T.domVecMinIdx xs with
      | some p =>
          obtain ⟨i, d⟩ := p
          rw [hrec] at ih
          refine ⟨ih.1, by simpa [Vec.idx, i.isLt] using ih.2.1, fun j hj => ?_⟩
          have hjk := Nat.lt_trans hj i.isLt
          simpa [Vec.idx, hjk] using ih.2.2 ⟨j.val, hjk⟩ hj
      | none =>
          rw [hrec] at ih
          by_cases hx : T.dom x = .zero
          · rw [ite_eq_left hx]
            intro i
            by_cases hi : i.val < k
            · simpa [Vec.idx, hi] using ih ⟨i.val, hi⟩
            · simpa [Vec.idx, hi] using hx
          · rw [ite_eq_right hx]
            exact ⟨hx, by simp [Vec.idx], fun j (hj : j.val < k) => by
              simpa [Vec.idx, hj] using ih ⟨j.val, hj⟩⟩

theorem T.domVecMinIdx_some_spec {lam m : Nat} (v : Vec (T lam) m) (i : Fin m) (d : Dom lam)
    (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero ∧ T.dom (v.idx i) = d ∧ ∀ j : Fin m, j.val < i.val → T.dom (v.idx j) = .zero := by
  simpa only [h] using T.domVecMinIdx_spec v

theorem Vec.rplc_idx_same {A : Type} {n : Nat} (v : Vec A n) (i : Fin n) (a : A) :
    (v.rplc i a).idx i = a := by
  simp [Vec.rplc, Vec.ofFn_idx]

theorem Vec.rplc_idx_of_ne {A : Type} {n : Nat} (v : Vec A n) (i j : Fin n) (a : A)
    (h : j.val ≠ i.val) : (v.rplc i a).idx j = v.idx j := by
  simp [Vec.rplc, Vec.ofFn_idx, h]
  rfl

theorem Vec.compare_lt_of_pivot {lam m : Nat} (v w : Vec (T lam) m) (i : Fin m)
    (heq : ∀ j : Fin m, i.val < j.val → v.idx j = w.idx j) (hlt : v.idx i < w.idx i) :
    compareVec v w = Ordering.lt := by
  induction m with
  | zero => exact i.elim0
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          by_cases hik : i.val = k
          · have hxy : x < y := by simpa [Fin.eq_of_val_eq (j := Fin.last k) hik, Vec.idx] using hlt
            simp [compareVec, show compareT x y = .lt from hxy]
          · have hiklt : i.val < k := by omega
            have hxy : x = y := by simpa [Vec.idx] using heq (Fin.last k) hiklt
            simpa [compareVec, hxy, T_refl] using ih xs ys ⟨i.val, hiklt⟩
              (fun j hj => by simpa [Vec.idx, j.isLt] using heq j.castSucc hj)
              (by simpa [Vec.idx, hiklt] using hlt)

theorem Vec.compare_lt_has_pivot {lam m : Nat} (v w : Vec (T lam) m)
    (h : compareVec v w = Ordering.lt) :
    ∃ i : Fin m, (∀ j : Fin m, i.val < j.val → v.idx j = w.idx j) ∧ v.idx i < w.idx i := by
  induction m with
  | zero => cases v; cases w; cases h
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          cases hc : compareT x y with
          | lt =>
              exact ⟨Fin.last k, fun j (hj : k < j.val) => by omega,
                by simpa [Vec.idx] using (show x < y from hc)⟩
          | eq =>
              obtain ⟨i, hiAbove, hiLt⟩ := ih xs ys (by simpa [compareVec, hc] using h)
              refine ⟨i.castSucc, fun j hij => ?_, by simpa [Vec.idx, i.isLt] using hiLt⟩
              by_cases hjk : j.val < k
              · simpa [Vec.idx, hjk] using hiAbove ⟨j.val, hjk⟩ hij
              · simpa [Vec.idx, hjk] using T_eq_sound x y hc
          | gt => simp [compareVec, hc] at h

theorem Vec.compare_rplc_lt {lam m : Nat} (v : Vec (T lam) m) (i : Fin m) (a : T lam)
    (h : a < v.idx i) : compareVec (v.rplc i a) v = Ordering.lt :=
  Vec.compare_lt_of_pivot _ _ i (fun j hj => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj))
    (by simpa only [Vec.rplc_idx_same] using h)

theorem Vec.compare_rplc_rplc_lt {lam m : Nat} (v : Vec (T lam) m) (i j : Fin m) (a b : T lam)
    (hji : j.val < i.val) (ha : a < v.idx i) : compareVec ((v.rplc i a).rplc j b) v = .lt :=
  Vec.compare_lt_of_pivot _ _ i (fun q hq => by
    rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega), Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq)])
    (by simpa only [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hji), Vec.rplc_idx_same] using ha)

theorem T.P_lt_P_of_compareVec_lt {lam : Nat} (v w : Vec (T lam) lam) (a b : T lam)
    (h : compareVec v w = Ordering.lt) : T.P v a < T.P w b := by
  simp only [LT.lt, T.lt, compareT, h]

theorem T.fund_lt_self {lam : Nat} (s t : T lam) (hne : s ≠ T.Z) : T.fund s t < s := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z => exact False.elim (hne rfl)
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none => rw [T.fund, ite_eq_left rfl, hmin]; rfl
            | some md =>
                obtain ⟨m, d⟩ := md
                have hspec := T.domVecMinIdx_some_spec ls m d hmin
                have hrec (u) : T.fund (ls.idx m) u < ls.idx m :=
                  ih _ (T.idx_size_lt_P ls T.Z m) u
                    fun hz => hspec.1 (hspec.2.1.symm.trans (congrArg T.dom hz))
                have key (u) (a b : T lam) := T.P_lt_P_of_compareVec_lt _ _ a b
                  (Vec.compare_rplc_lt _ _ _ (hrec u))
                rw [T.fund, ite_eq_left rfl, hmin]
                cases d with
                | one =>
                    obtain ⟨_ | r, mh⟩ := m
                    · cases t with
                      | Z => rfl
                      | P => exact key T.Z _ _
                    · exact T.P_lt_P_of_compareVec_lt _ _ _ _
                        (Vec.compare_rplc_rplc_lt _ _ _ _ _ (Nat.lt_succ_self r) (hrec T.Z))
                | _ => dsimp only; (try split) <;> exact key _ _ _
          · rw [T.fund, ite_eq_right hadd]
            change (match compareVec ls ls with
              | .eq => compareT (T.fund add t) add | ord => ord) = .lt
            rw [Vec_refl]
            exact ih _ (T.add_size_lt_P ls add) t hadd

theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam) (hdom : T.dom s = .zero) : s = T.Z := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z => rfl
      | P v b =>
          by_cases hb : b = T.Z
          · subst b
            rw [T.dom, ite_eq_left rfl] at hdom
            split at hdom
            · cases hdom
            · split at hdom <;> (try split at hdom) <;> cases hdom
          · rw [T.dom, ite_eq_right hb] at hdom
            exact False.elim (hb (ih b (T.add_size_lt_P v b) hdom))

theorem T.dom_Omega_pos {lam : Nat} (s : T lam) (i : Fin lam) (hdom : T.dom s = .Omega i) :
    0 < i.val := by
  induction s using (measure T.size).wf.induction generalizing i with
  | h s ih =>
      cases s with
      | Z => cases hdom
      | P v b =>
          by_cases hb : b = T.Z
          · subst b
            rw [T.dom, ite_eq_left rfl] at hdom
            split at hdom
            · cases hdom
            · rename_i m d hm
              split at hdom <;> (try split at hdom) <;> cases hdom
              · exact Nat.pos_of_ne_zero ‹_›
              · exact ih _ (T.idx_size_lt_P v T.Z m) _ (T.domVecMinIdx_some_spec v m _ hm).2.1
          · rw [T.dom, ite_eq_right hb] at hdom
            exact ih b (T.add_size_lt_P v b) i hdom

/-! Countable head indices in the legacy OT fundamental-sequence closure. -/

inductive T.Countable {lam : Nat} : T lam → Prop where
  | z : Countable T.Z
  | p (v : Vec (T lam) lam) (b : T lam) (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
      (hb : Countable b) : Countable (T.P v b)

theorem T.Countable_min_zero {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
    (m : Fin lam) (d : Dom lam) (hm : T.domVecMinIdx v = some (m, d)) : m.val = 0 :=
  have hspec := T.domVecMinIdx_some_spec v m d hm
  Nat.eq_zero_of_not_pos fun hpos => hspec.1 (hspec.2.1.symm.trans (congrArg T.dom (hv m hpos)))

theorem T.Countable_mul {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z) (t : T lam) :
    T.Countable (T.mul (T.P v T.Z) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact .z
  | P _ b _ ih => exact .p v _ hv ih
  | nil | snoc => trivial

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
            have hrep (a) : ∀ i : Fin lam, 0 < i.val → (v.rplc m a).idx i = T.Z :=
              fun i hi => (Vec.rplc_idx_of_ne _ _ _ _ (by omega)).trans (hv i hi)
            cases d with
            | one =>
                obtain ⟨mv, mh⟩ := m
                change mv = 0 at hm
                subst mv
                exact T.Countable_mul _ (hrep _) t
            | _ => dsimp only; (try split) <;> exact .p _ _ (hrep _) .z
      · rw [T.fund, ite_eq_right hbz]
        exact .p v _ hv ih

theorem T.isOT_Countable (lam : Nat) (s : T lam) (hs : T.isOT lam s) : T.Countable s := by
  induction hs with
  | base_0 n =>
      induction n with
      | zero => exact .z
      | succ n ih => exact .p Vec.nil _ (fun i => i.elim0) ih
  | base_succ k n =>
      exact .p _ T.Z (fun i hi => by rw [Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hi)]) .z
  | step lam a _ n ih => exact T.Countable_fund a ih _

theorem T.isOT_dom_not_Omega (lam : Nat) (s : T lam) (hs : T.isOT lam s) (i : Fin lam) :
    T.dom s ≠ .Omega i := by
  have hc := T.isOT_Countable lam s hs
  clear hs
  induction hc with
  | z => intro h; cases h
  | p v b hv hb ih =>
      intro hdom
      by_cases hbz : b = T.Z
      · subst b
        rw [T.dom, ite_eq_left rfl] at hdom
        split at hdom
        · cases hdom
        · rename_i m d hmin
          have hm := T.Countable_min_zero v hv m d hmin
          split at hdom <;> (try split at hdom) <;> cases hdom
          have hj := T.dom_Omega_pos _ _ (T.domVecMinIdx_some_spec v m _ hmin).2.1
          exact absurd (‹_ ≤ m› : _ ≤ m.val) (by omega)
      · rw [T.dom, ite_eq_right hbz] at hdom
        exact ih hdom

end new

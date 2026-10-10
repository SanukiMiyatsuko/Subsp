import Subsp.Support.Dimension

/-! Source fund order, codes, and the image map `DimensionImage.convert`. -/

namespace Support.SourceFundOrder

open new Support.OTQuotient Support.DimensionCut

theorem compareVec_of_lt_at {lam m : Nat} (xs ys : Vec (T lam) m) (i : Fin m)
    (hi : compareT (xs.idx i) (ys.idx i) = .lt)
    (hh : ∀ j : Fin m, i.val < j.val → xs.idx j = ys.idx j) :
    compareVec xs ys = .lt := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    cases ys with
    | snoc _ ys y =>
      by_cases him : i.val < m
      · let k : Fin m := ⟨i.val, him⟩
        have he : i = k.castSucc := Fin.ext rfl
        have hxy : x = y := by
          simpa only [vec_snoc_idx_last] using hh (Fin.last m) him
        have hlow : compareT (xs.idx k) (ys.idx k) = .lt := by
          simpa only [he, vec_snoc_idx_cast] using hi
        have hl := ih ys k hlow (fun j hj => by
          simpa only [vec_snoc_idx_cast] using hh j.castSucc hj)
        simp only [compareVec, hxy, T_refl, hl]
      · have he : i = Fin.last m := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
        rw [he, vec_snoc_idx_last, vec_snoc_idx_last] at hi
        simp only [compareVec, hi]

theorem compareVec_rplc_lt {lam m : Nat} (xs : Vec (T lam) m) (i : Fin m) (a : T lam)
    (ha : compareT a (xs.idx i) = .lt) : compareVec (xs.rplc i a) xs = .lt := by
  apply compareVec_of_lt_at _ _ i
  · simpa only [vec_rplc_idx, ↓reduceIte] using ha
  · intro j hj
    rw [vec_rplc_idx, ite_eq_right (by omega)]

theorem compareVec_rplc_lower_lt {lam m : Nat} (xs : Vec (T lam) m)
    (i j : Fin m) (a b : T lam) (hji : j.val < i.val)
    (ha : compareT a (xs.idx i) = .lt) :
    compareVec ((xs.rplc i a).rplc j b) xs = .lt := by
  apply compareVec_of_lt_at _ _ i
  · rw [vec_rplc_idx, ite_eq_right (by omega), vec_rplc_idx, ite_eq_left rfl]
    exact ha
  · intro k hk
    rw [vec_rplc_idx, ite_eq_right (by omega), vec_rplc_idx, ite_eq_right (by omega)]

theorem compareVec_rplc_pair_lt {lam m : Nat} (xs : Vec (T lam) m)
    (i : Fin m) (a b : T lam) (h : T.lt a b) :
    compareVec (xs.rplc i a) (xs.rplc i b) = .lt := by
  change compareT a b = .lt at h
  apply compareVec_of_lt_at _ _ i
  · simpa only [vec_rplc_idx, ↓reduceIte] using h
  · intro j hj
    simp only [vec_rplc_idx, ite_eq_right (by omega : j.val ≠ i.val)]

theorem mul_principal_lt {lam : Nat} {xs ys : Vec (T lam) lam}
    (h : compareVec xs ys = .lt) (t b : T lam) :
    T.lt (T.mul (.P xs .Z) t) (.P ys b) := by
  cases t with
  | Z => rfl
  | P us c =>
    change compareT (.P xs (T.mul (.P xs .Z) c)) (.P ys b) = .lt
    simp only [compareT, h]

theorem fund_lt {lam : Nat} (s t : T lam) (hs : s ≠ .Z) : T.lt (T.fund s t) s := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P xs b =>
    rw [T.fund]
    by_cases hb : b = .Z
    · subst b
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => rfl
      | some p =>
        obtain ⟨i, d⟩ := p
        have hd := minIdx_spec xs hm
        have hn : xs.idx i ≠ .Z := by
          intro hz
          have he := hd.1
          rw [hz, T.dom] at he
          exact hd.2.1 he
        have hi : ∀ u : T lam, T.lt (T.fund (xs.idx i) u) (xs.idx i) :=
          fun u => fund_lt (xs.idx i) u hn
        change ∀ u : T lam, compareT (T.fund (xs.idx i) u) (xs.idx i) = .lt at hi
        simp only [GetElem.getElem, Fin.eta]
        cases d with
        | zero => exact False.elim (hd.2.1 rfl)
        | omega =>
          change compareT (.P (xs.rplc i (T.fund (xs.idx i) t)) .Z) (.P xs .Z) = .lt
          simp only [compareT, compareVec_rplc_lt xs i _ (hi t)]
        | Omega ys =>
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte]
            change compareT (.P (xs.rplc i _) .Z) (.P xs .Z) = .lt
            simp only [compareT, compareVec_rplc_lt xs i _ (hi _)]
          · simp only [hv, ↓reduceIte]
            change compareT (.P (xs.rplc i _) .Z) (.P xs .Z) = .lt
            simp only [compareT, compareVec_rplc_lt xs i _ (hi _)]
        | one =>
          obtain ⟨m, hmi⟩ := i
          cases m with
          | zero =>
            exact mul_principal_lt (compareVec_rplc_lt xs ⟨0, hmi⟩ _ (hi .Z)) t .Z
          | succ m =>
            change compareT (.P ((xs.rplc ⟨m + 1, hmi⟩ _).rplc ⟨m, Nat.lt_of_succ_lt hmi⟩ t) .Z)
              (.P xs .Z) = .lt
            simp only [compareT, compareVec_rplc_lower_lt xs ⟨m + 1, hmi⟩
              ⟨m, Nat.lt_of_succ_lt hmi⟩ _ t (by exact Nat.lt_succ_self m) (hi .Z)]
    · simp only [hb, ↓reduceIte]
      have h := fund_lt b t hb
      change compareT (T.fund b t) b = .lt at h
      change compareT (.P xs (T.fund b t)) (.P xs b) = .lt
      simp only [compareT, Vec_refl, h]
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

theorem fund_mono {lam : Nat} (s : T lam) {v : Vec (T lam) lam}
    (hd : T.dom s = .Omega v) (t u : T lam) (htu : T.lt t u) :
    T.lt (T.fund s t) (T.fund s u) := by
  cases s with
  | Z => cases hd
  | P xs b =>
    change compareT (T.fund (.P xs b) t) (T.fund (.P xs b) u) = .lt
    by_cases hb : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte] at hd
      rw [T.fund.eq_def (.P xs .Z) t, T.fund.eq_def (.P xs .Z) u]
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchild := (minIdx_spec xs hm).1.symm
        simp only [GetElem.getElem, Fin.eta]
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          simp only [hm] at hd
          by_cases hz : i.val = 0
          · simp only [hz, ↓reduceIte] at hd; cases hd
          · obtain ⟨m, him⟩ := i
            cases m with
            | zero => exact False.elim (hz rfl)
            | succ m =>
              change compareT (.P ((xs.rplc ⟨m + 1, him⟩ _).rplc ⟨m, Nat.lt_of_succ_lt him⟩ t) .Z)
                (.P ((xs.rplc ⟨m + 1, him⟩ _).rplc ⟨m, Nat.lt_of_succ_lt him⟩ u) .Z) = .lt
              simp only [compareT, compareVec_rplc_pair_lt _ ⟨m, Nat.lt_of_succ_lt him⟩ t u htu]
        | Omega ys =>
          simp only [hm] at hd
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte] at hd; cases hd
          · simp only [hv, ↓reduceIte]
            have hi := fund_mono (xs.idx i) hchild t u htu
            change compareT (.P (xs.rplc i _) .Z) (.P (xs.rplc i _) .Z) = .lt
            simp only [compareT, compareVec_rplc_pair_lt xs i _ _ hi]
    · rw [T.dom, ite_eq_right hb] at hd
      rw [T.fund.eq_def (.P xs b) t, T.fund.eq_def (.P xs b) u]
      simp only [hb, ↓reduceIte]
      have hi := fund_mono b hd t u htu
      change compareT (.P xs (T.fund b t)) (.P xs (T.fund b u)) = .lt
      simp only [compareT, Vec_refl]
      exact hi
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

def RegularVector {lam : Nat} (v : Vec (T lam) lam) : Prop :=
  ∃ i : Fin lam, 0 < i.val ∧ T.domVecMinIdx v = some (i, .one)

theorem domOmega_regular {lam : Nat} (s : T lam) {v : Vec (T lam) lam}
    (hd : T.dom s = .Omega v) : RegularVector v := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte] at hd
      cases hm : T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchild := (minIdx_spec xs hm).1.symm
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          simp only [hm] at hd
          by_cases hz : i.val = 0
          · simp only [hz, ↓reduceIte] at hd; cases hd
          · simp only [hz, ↓reduceIte] at hd
            have he := Dom.Omega.inj hd
            rw [← he]
            exact ⟨i, by omega, hm⟩
        | Omega ys =>
          simp only [hm] at hd
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte] at hd; cases hd
          · simp only [hv, ↓reduceIte] at hd
            have he := Dom.Omega.inj hd
            rw [← he]
            exact domOmega_regular (xs.idx i) hchild
    · rw [T.dom, ite_eq_right hb] at hd
      exact domOmega_regular b hd
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

theorem regularVector_dom {lam : Nat} {v : Vec (T lam) lam} (hv : RegularVector v) :
    T.dom (.P v .Z) = .Omega v := by
  obtain ⟨i, hi, hm⟩ := hv
  simp only [T.dom, ↓reduceIte, hm, ite_eq_right (Nat.ne_of_gt hi)]

theorem fund_regular_bound {lam m : Nat} (v : Vec (T lam) lam) (hml : m + 1 < lam)
    (hv : T.domVecMinIdx v = some (⟨m + 1, hml⟩, .one)) (t : T lam) :
    T.fund (.P v .Z) t =
      .P ((v.rplc ⟨m + 1, hml⟩ (T.fund (v.idx ⟨m + 1, hml⟩) .Z)).rplc
        ⟨m, Nat.lt_of_succ_lt hml⟩ t) .Z := by
  rw [T.fund]
  simp only [↓reduceIte, hv, GetElem.getElem]

theorem lowVec_below_positive {lam : Nat} (k : Nat) (a : T lam)
    (v : Vec (T lam) (k + 1)) (i : Fin (k + 1)) (hi : 0 < i.val)
    (hv : v.idx i ≠ .Z) : compareVec (CountableSource.lowVec k a) v = .lt := by
  induction k with
  | zero => have := i.isLt; omega
  | succ k ih =>
    cases v with
    | snoc _ xs x =>
      rw [CountableSource.lowVec_succ, compareVec]
      cases x with
      | P ys b => rfl
      | Z =>
        have him : i.val < k + 1 := by
          by_cases h : i.val < k + 1
          · exact h
          · have he : i = Fin.last (k + 1) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
            exact False.elim (hv (by rw [he, vec_snoc_idx_last]))
        let j : Fin (k + 1) := ⟨i.val, him⟩
        have he : i = j.castSucc := Fin.ext rfl
        have hx : xs.idx j ≠ .Z := by simpa only [he, vec_snoc_idx_cast] using hv
        simpa only [compareT] using ih xs j hi hx

theorem lowVec_below_regular {lam k : Nat} (a : T lam) (v : Vec (T lam) (k + 1))
    (i : Fin (k + 1)) (hi : 0 < i.val) (hm : T.domVecMinIdx v = some (i, .one)) :
    compareVec (CountableSource.lowVec k a) v = .lt := by
  apply lowVec_below_positive k a v i hi
  intro hz
  have hd := (minIdx_spec v hm).1
  rw [hz, T.dom] at hd
  cases hd

theorem outer_not_Omega {k : Nat} {s : T (k + 1)} (hs : CountableSource.Outer s)
    (v : Vec (T (k + 1)) (k + 1)) : T.dom s ≠ .Omega v := by
  induction hs with
  | zero => intro hd; cases hd
  | cons a b hb ih =>
    intro hd
    by_cases hz : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte, CountableSource.minIdx_lowVec] at hd
      cases ha : T.dom a with
      | zero => simp only [ha, ↓reduceIte] at hd; cases hd
      | one | omega => simp only [ha, reduceCtorEq, ↓reduceIte] at hd
      | Omega w =>
        obtain ⟨i, hi, hm⟩ := domOmega_regular a ha
        have hlt : Vec.lt (CountableSource.lowVec k a) w := lowVec_below_regular a w i hi hm
        simp only [ha, reduceCtorEq, ↓reduceIte] at hd
        rw [ite_eq_left hlt] at hd
        cases hd
    · rw [T.dom, ite_eq_right hz] at hd
      exact ih hd

end Support.SourceFundOrder

namespace Support.SourceSummands

open new Support.OTQuotient

def tail {lam : Nat} : T lam → T lam
  | .Z => .Z
  | .P _ b => b

theorem tail_fund_isOT {lam : Nat} {s : T lam} (hs : T.isOT lam s)
    (ht : T.isOT lam (tail s)) (n : Nat) : T.isOT lam (tail (T.fund s (T.ofNat n))) := by
  cases s with
  | Z => simpa only [T.fund, tail] using ht
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [T.fund]
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => exact ht
      | some p =>
        obtain ⟨i, d⟩ := p
        simp only
        cases d with
        | zero | omega => exact isOT_ofNat lam 0
        | Omega ys =>
          simp only
          by_cases hv : Vec.lt xs ys
          · rw [ite_eq_left hv]
            exact isOT_ofNat lam 0
          · rw [ite_eq_right hv]
            exact isOT_ofNat lam 0
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero =>
            cases n with
            | zero => exact isOT_ofNat lam 0
            | succ n =>
              have h := T.isOT.step lam (.P xs .Z) hs n
              simpa only [T.fund, ↓reduceIte, hm, T.ofNat, T.mul, HAdd.hAdd,
                Add.add, T.oplus, tail] using h
          | succ j => exact isOT_ofNat lam 0
    · rw [T.fund, ite_eq_right hb]
      exact T.isOT.step lam b ht n

theorem tail_isOT {lam : Nat} {s : T lam} (hs : T.isOT lam s) : T.isOT lam (tail s) := by
  induction hs with
  | base_0 n =>
    cases n with
    | zero => exact T.isOT.base_0 0
    | succ n => exact T.isOT.base_0 n
  | base_succ k n => exact isOT_ofNat (k + 1) 0
  | step lam s hs n ih => exact tail_fund_isOT hs ih n

end Support.SourceSummands

namespace Support.SourceDescending

open new Support.OTQuotient

theorem le_trans {lam : Nat} {a b c : T lam} (hab : T.le a b) (hbc : T.le b c) : T.le a c := by
  rcases hab with h | h
  · rcases hbc with h' | h'
    · exact Or.inl (T_trans _ _ _ h h')
    · rw [T_eq_sound _ _ h'] at h
      exact Or.inl h
  · rw [T_eq_sound _ _ h]
    exact hbc

theorem head_le_of_lt {lam : Nat} {s t : T lam} (h : T.lt s t) : T.le (T.head s) (T.head t) := by
  cases s with
  | Z => cases t with
    | Z => exact Or.inr rfl
    | P ys c => exact Or.inl rfl
  | P xs b =>
    cases t with
    | Z => cases h
    | P ys c =>
      change compareT (.P xs b) (.P ys c) = .lt at h
      change compareT (.P xs .Z) (.P ys .Z) = .lt ∨ compareT (.P xs .Z) (.P ys .Z) = .eq
      cases hv : compareVec xs ys with
      | lt => exact Or.inl (by simp only [compareT, hv])
      | eq => exact Or.inr (by simp only [compareT, hv])
      | gt => simp only [compareT, hv, reduceCtorEq] at h

theorem head_fund_le {lam : Nat} (s t : T lam) : T.le (T.head (T.fund s t)) (T.head s) := by
  by_cases hz : s = .Z
  · subst s
    exact Or.inr (by simp only [T.fund, T.head, compareT])
  · exact head_le_of_lt (SourceFundOrder.fund_lt s t hz)

def Descending {lam : Nat} : T lam → Prop
  | .Z => True
  | .P xs b => Descending b ∧ T.le (T.head b) (.P xs .Z)

theorem principal_descending {lam : Nat} (xs : Vec (T lam) lam) : Descending (.P xs .Z) :=
  ⟨True.intro, Or.inl rfl⟩

theorem mul_principal_descending {lam : Nat} (xs : Vec (T lam) lam) (t : T lam) :
    Descending (T.mul (.P xs .Z) t) := by
  cases t with
  | Z => trivial
  | P ys b =>
    change Descending (.P xs (T.mul (.P xs .Z) b))
    refine ⟨mul_principal_descending xs b, ?_⟩
    cases b with
    | Z => exact Or.inl rfl
    | P zs c => exact Or.inr (T_refl _)
termination_by T.size t
decreasing_by exact T.add_size_lt_P _ _

theorem fund_descending {lam : Nat} (s t : T lam) (hs : Descending s) : Descending (T.fund s t) := by
  cases s with
  | Z => simpa only [T.fund] using hs
  | P xs b =>
    rw [T.fund]
    by_cases hb : b = .Z
    · subst b
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => trivial
      | some p =>
        obtain ⟨i, d⟩ := p
        simp only
        cases d with
        | zero | omega => exact principal_descending _
        | Omega ys =>
          change Descending (if Vec.lt xs ys then
            .P (xs.rplc i (T.fund (xs.idx i) (T.iter (T.fund (xs.idx i)) t))) .Z
            else .P (xs.rplc i (T.fund (xs.idx i) t)) .Z)
          by_cases hv : Vec.lt xs ys
          · rw [ite_eq_left hv]
            exact principal_descending _
          · rw [ite_eq_right hv]
            exact principal_descending _
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero => exact mul_principal_descending _ t
          | succ j => exact principal_descending _
    · rw [ite_eq_right hb]
      exact ⟨fund_descending b t hs.1, le_trans (head_fund_le b t) hs.2⟩
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals omega

theorem ofNat_descending (lam n : Nat) : Descending (T.ofNat (lam := lam) n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change Descending (.P (zeros lam) (T.ofNat n))
    refine ⟨ih, ?_⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr (T_refl _)

theorem lt_one_iff_zero {lam : Nat} (s : T lam) : T.lt s (T.ofNat 1) ↔ s = .Z := by
  cases s with
  | Z => constructor <;> intro h <;> rfl
  | P xs b =>
    constructor
    · intro h
      change compareT (.P xs b) (.P (zeros lam) .Z) = .lt at h
      cases hv : compareVec xs (zeros lam) with
      | lt => exact False.elim (DimensionCut.compareVec_zero_not_lt xs hv)
      | gt => simp only [compareT, hv, reduceCtorEq] at h
      | eq => cases b <;> simp only [compareT, hv, reduceCtorEq] at h
    · intro h; cases h

end Support.SourceDescending

namespace Support.SourceSuccessor

open new Support.OTQuotient

def succ {lam : Nat} (s : T lam) : T lam := s + T.ofNat 1

theorem succ_ne_zero {lam : Nat} (s : T lam) : succ s ≠ .Z := by
  cases s <;> intro h <;> cases h

theorem dom_succ {lam : Nat} (s : T lam) : T.dom (succ s) = .one := by
  cases s with
  | Z => exact dom_one
  | P xs b =>
    change T.dom (.P xs (succ b)) = .one
    rw [T.dom, ite_eq_right (succ_ne_zero b)]
    exact dom_succ b
termination_by T.size s
decreasing_by simp only [T.size]; omega

theorem fund_succ {lam : Nat} (s t : T lam) : T.fund (succ s) t = s := by
  cases s with
  | Z => exact fund_one t
  | P xs b =>
    change T.fund (.P xs (succ b)) t = .P xs b
    rw [T.fund, ite_eq_right (succ_ne_zero b), fund_succ b t]
termination_by T.size s
decreasing_by simp only [T.size]; omega

theorem lt_succ_iff_le {lam : Nat} (s t : T lam) : T.lt s (succ t) ↔ T.le s t := by
  cases t with
  | Z =>
    rw [show succ (.Z : T lam) = T.ofNat 1 from rfl, SourceDescending.lt_one_iff_zero]
    constructor
    · rintro rfl; exact Or.inr rfl
    · rintro (h | h)
      · cases s <;> cases h
      · exact T_eq_sound _ _ h
  | P ys b =>
    cases s with
    | Z => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
    | P xs a =>
      change compareT (.P xs a) (.P ys (succ b)) = .lt ↔
        compareT (.P xs a) (.P ys b) = .lt ∨ compareT (.P xs a) (.P ys b) = .eq
      simp only [compareT]
      cases hc : compareVec xs ys with
      | lt => simp only [true_or]
      | gt => simp only [reduceCtorEq, false_or]
      | eq =>
        exact lt_succ_iff_le a b
termination_by T.size t
decreasing_by all_goals simp only [T.size]; all_goals omega

theorem nat_succ {lam : Nat} (n : Nat) : succ (T.ofNat (lam := lam) n) = T.ofNat (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (T.P (zeros lam)) ih

end Support.SourceSuccessor

namespace Support.UserImage

open new OCF.Jaeger Support.OTQuotient Support.BinaryTranslation
open Support.TargetArithmetic

universe u

def oneCode : Code := .p [] .zero

end Support.UserImage

namespace Support.GeneralTranslation

open OCF.Jaeger Support.OTQuotient

mutual
  def normalize (s : Code) : Code :=
    match s with
    | .zero => .zero
    | .p args tail => .p (trim (normalizeArgs args)) (normalize tail)
  termination_by sizeOf s

  def normalizeArgs (xs : List Code) : List Code :=
    match xs with
    | [] => []
    | x :: xs => normalize x :: normalizeArgs xs
  termination_by sizeOf xs
end

end Support.GeneralTranslation

namespace Support.CodeReification

open new Support.OTQuotient Support.GeneralTranslation

mutual
  def width (s : Code) : Nat :=
    match s with
    | .zero => 0
    | .p args tail => max args.length (max (argsWidth args) (width tail))
  termination_by sizeOf s

  def argsWidth (xs : List Code) : Nat :=
    match xs with
    | [] => 0
    | x :: xs => max (width x) (argsWidth xs)
  termination_by sizeOf xs
end

theorem argsWidth_le (xs : List Code) (n : Nat) : argsWidth xs ≤ n ↔ ∀ x ∈ xs, width x ≤ n := by
  induction xs with
  | nil => simp [argsWidth]
  | cons a xs ih => simp [argsWidth, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

theorem trim_length_le (xs : List Code) : (trim xs).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    cases ht : trim xs with
    | nil => cases ha : a.isZero <;> simp [trim, ht, ha]
    | cons b bs => simpa only [trim, ht, List.length_cons, Nat.add_le_add_iff_right] using ih

theorem argsWidth_trim_le (xs : List Code) : argsWidth (trim xs) ≤ argsWidth xs := by
  apply (argsWidth_le _ _).mpr
  intro x hx
  exact (argsWidth_le xs (argsWidth xs)).mp (Nat.le_refl _) x (mem_trim hx)

mutual
  theorem width_code {lam : Nat} (s : T lam) : width (code s) ≤ lam := by
    cases s with
    | Z => simp [code, width]
    | P args tail =>
      rw [code, width]
      exact Nat.max_le.mpr ⟨Nat.le_trans (trim_length_le _) (by rw [codes_length]; exact Nat.le_refl _),
        Nat.max_le.mpr ⟨Nat.le_trans (argsWidth_trim_le _) (argsWidth_codes args), width_code tail⟩⟩

  theorem argsWidth_codes {lam m : Nat} (xs : Vec (T lam) m) : argsWidth (codes xs) ≤ lam := by
    cases xs with
    | nil => simp [codes, argsWidth]
    | snoc n xs x =>
      apply (argsWidth_le _ _).mpr
      intro y hy
      rw [codes] at hy
      rcases List.mem_append.mp hy with hy | hy
      · exact (argsWidth_le _ _).mp (argsWidth_codes xs) y hy
      · have he := List.mem_singleton.mp hy
        rw [he]
        exact width_code x
end

def consVec {A : Type} (a : A) : {n : Nat} → Vec A n → Vec A (n + 1)
  | 0, .nil => .snoc 0 .nil a
  | n + 1, .snoc _ xs b => .snoc (n + 1) (consVec a xs) b

def fromList {A : Type} (xs : List A) : Vec A xs.length :=
  match xs with
  | [] => .nil
  | x :: xs => consVec x (fromList xs)

def extend {A : Type} {n : Nat} (a : A) (xs : Vec A n) : (k : Nat) → Vec A (n + k)
  | 0 => xs
  | k + 1 => .snoc (n + k) (extend a xs k) a

theorem codes_consVec {lam m : Nat} (a : T lam) (xs : Vec (T lam) m) :
    codes (consVec a xs) = code a :: codes xs := by
  induction xs with
  | nil => rfl
  | snoc n xs x ih => simp only [consVec, codes, ih, List.cons_append]

theorem codes_fromList {lam : Nat} (xs : List (T lam)) : codes (fromList xs) = xs.map code := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [fromList, codes_consVec, List.map_cons, ih]

theorem replicate_append_singleton (k : Nat) (a : Code) :
    List.replicate k a ++ [a] = List.replicate (k + 1) a := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem codes_extend {lam m : Nat} (xs : Vec (T lam) m) (k : Nat) :
    codes (extend T.Z xs k) = codes xs ++ List.replicate k Code.zero := by
  induction k with
  | zero => simp [extend]
  | succ k ih =>
    simp only [extend, codes, code, ih]
    rw [List.append_assoc]
    congr 1
    exact replicate_append_singleton k .zero

theorem codes_length_cast {lam m n : Nat} (e : m = n) (xs : Vec (T lam) m) :
    codes (Eq.mp (congrArg (Vec (T lam)) e) xs) = codes xs := by cases e; rfl

def makeVec (lam : Nat) (xs : List (T lam)) (h : xs.length ≤ lam) : Vec (T lam) lam :=
  Eq.mp (congrArg (Vec (T lam)) (Nat.add_sub_of_le h))
    (extend T.Z (fromList xs) (lam - xs.length))

theorem codes_makeVec (lam : Nat) (xs : List (T lam)) (h : xs.length ≤ lam) :
    codes (makeVec lam xs h) = xs.map code ++ List.replicate (lam - xs.length) Code.zero := by
  rw [makeVec, codes_length_cast (Nat.add_sub_of_le h), codes_extend, codes_fromList]

mutual
  def reify (lam : Nat) (s : Code) : T lam :=
    match s with
    | .zero => .Z
    | .p args tail =>
      if h : (values lam args).length ≤ lam then .P (makeVec lam (values lam args) h) (reify lam tail)
      else .Z
  termination_by sizeOf s

  def values (lam : Nat) (xs : List Code) : List (T lam) :=
    match xs with
    | [] => []
    | x :: xs => reify lam x :: values lam xs
  termination_by sizeOf xs
end

theorem values_length (lam : Nat) (xs : List Code) : (values lam xs).length = xs.length := by
  induction xs with
  | nil => rw [values]; rfl
  | cons a xs ih => simp only [values, List.length_cons, ih]

theorem trim_append_zeros (xs : List Code) (k : Nat) : trim (xs ++ List.replicate k .zero) = trim xs := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, ← List.singleton_append, ← List.append_assoc, ih,
      FiniteCorrespondence.trim_append_zero]

mutual

  theorem code_reify (lam : Nat) (s : Code) (h : width s ≤ lam) : code (reify lam s) = normalize s := by
    cases s with
    | zero => simp only [reify, code, normalize]
    | p args tail =>
      simp only [width, Nat.max_le] at h
      rw [reify, dite_eq_left (by rw [values_length]; exact h.1), code, codes_makeVec,
        values_code lam args h.2.1, trim_append_zeros, code_reify lam tail h.2.2, normalize]
  termination_by sizeOf s

  theorem values_code (lam : Nat) (xs : List Code) (h : argsWidth xs ≤ lam) :
      (values lam xs).map code = normalizeArgs xs := by
    cases xs with
    | nil => rw [values, normalizeArgs]; rfl
    | cons a xs =>
      simp only [argsWidth, Nat.max_le] at h
      rw [values, List.map_cons, code_reify lam a h.1, values_code lam xs h.2, normalizeArgs]
  termination_by sizeOf xs
end

theorem trim_normal_eq (xs : List Code) (h : noTrailingZero xs = true) : trim xs = xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => cases a <;> simp [trim, Code.isZero, noTrailingZero] at h ⊢
    | cons b xs =>
      have he := trim_normal_eq (b :: xs) h
      change (match trim (b :: xs) with
        | [] => if a.isZero then [] else [a]
        | y :: ys => a :: y :: ys) = a :: b :: xs
      rw [he]
termination_by xs.length

mutual
  theorem normalize_eq (s : Code) (h : s.normal) : normalize s = s := by
    cases s with
    | zero => rw [normalize]
    | p args tail =>
      rw [Code.normal] at h
      rw [normalize, normalizeArgs_eq args h.2.1, trim_normal_eq args h.1, normalize_eq tail h.2.2]
  termination_by sizeOf s

  theorem normalizeArgs_eq (xs : List Code) (h : ∀ x ∈ xs, x.normal) : normalizeArgs xs = xs := by
    cases xs with
    | nil => rw [normalizeArgs]
    | cons a xs =>
      rw [normalizeArgs, normalize_eq a (h a (List.mem_cons_self)),
        normalizeArgs_eq xs (fun x hx => h x (List.mem_cons_of_mem a hx))]
  termination_by sizeOf xs
end

theorem code_reify_normal (lam : Nat) (s : Code) (hn : s.normal) (h : width s ≤ lam) :
    code (reify lam s) = s := by rw [code_reify lam s h, normalize_eq s hn]

end Support.CodeReification

namespace Support.DimensionImage

open OCF.Jaeger Support.OTQuotient Support.BinaryTranslation

def lower : Nat → List Term → Term → Term
  | 0, _, h => h
  | k + 1, xs, h =>
    let a := xs[k]?.getD .zero
    let t := if h = .zero then
        if k = 0 then .psi Term.bigOmega a
        else if a = .zero then .zero else .psi (.inacc k .zero) (dropOne a)
      else if a = .zero then h
      else .psi (.inacc k (succTerm h)) (dropOne a)
    lower k xs t

def principal (d : Nat) (xs : List Term) : Term :=
  if d ≤ 2 then OT2.principal (xs[0]?.getD .zero) (xs[1]?.getD .zero)
  else
    let high := xs[d - 1]?.getD .zero
    let middle := xs[d - 2]?.getD .zero
    let h := if middle = .zero then
        if high = .zero then .zero else .inacc (d - 2) (dropOne high)
      else .psi (.inacc (d - 2) (if high = .zero then .zero else succTerm (dropOne high)))
        (dropOne middle)
    lower (d - 2) xs h

mutual
  def convert (d : Nat) : Code → Term
    | .zero => .zero
    | .p xs b => OT2.assemble (principal d (arguments d xs)) (convert d b)
  termination_by s => sizeOf s

  def arguments (d : Nat) : List Code → List Term
    | [] => []
    | x :: xs => convert d x :: arguments d xs
  termination_by xs => sizeOf xs
end

end Support.DimensionImage

namespace Support.CodeReification

open new Support.OTQuotient Support.CountableSource Support.GeneralTranslation

theorem reify_outer {k : Nat} (c : Code) (ho : OuterForm c) (hw : width c ≤ k + 1) :
    Outer (reify (k + 1) c) := by
  cases c with
  | zero => rw [reify]; exact Outer.zero
  | p args tail =>
    rw [OuterForm] at ho
    have hw0 := hw
    simp only [width, Nat.max_le] at hw
    have hb := reify_outer tail ho.2 hw.2.2
    cases args with
    | nil =>
      have he : reify (k + 1) (.p [] tail) = .P (lowVec k .Z) (reify (k + 1) tail) := by
        apply code_injective
        rw [code_reify (k + 1) _ hw0,
          code, trim_codes_lowVec, code_reify (k + 1) tail hw.2.2]
        simp only [normalize, normalizeArgs, code, trim, Code.isZero, ↓reduceIte]
      rw [he]
      exact Outer.cons _ _ hb
    | cons a args =>
      cases args with
      | nil =>
        have ha : width a ≤ k + 1 := (argsWidth_le _ _).mp hw.2.1 a (by simp)
        have he : reify (k + 1) (.p [a] tail) =
            .P (lowVec k (reify (k + 1) a)) (reify (k + 1) tail) := by
          apply code_injective
          rw [code_reify (k + 1) _ hw0,
            code, trim_codes_lowVec, code_reify (k + 1) a ha, code_reify (k + 1) tail hw.2.2]
          rw [normalize, normalizeArgs, normalizeArgs]
        rw [he]
        exact Outer.cons _ _ hb
      | cons b args => simp only [List.length_cons] at ho; omega
termination_by sizeOf c
decreasing_by all_goals simp_all only [Code.p.sizeOf_spec]; omega

theorem fitting_outer_below_boundary (k : Nat) (c : Code) (hn : c.normal)
    (ho : OuterForm c) (hw : width c ≤ k + 1) :
    compareCode c (code (dimensionBound k)) = .lt := by
  let u := reify (k + 1) c
  have hu : code u = c := code_reify_normal (k + 1) c hn hw
  rw [← hu, ← code_pad u, compareCode_code]
  exact DimensionCut.pad_outer_below_dimensionBound (reify_outer c ho hw)

theorem generated_reify (d lam : Nat) (s : T.OT d) (hw : width (code s.val) ≤ lam) :
    T.isOT lam (reify lam (code s.val)) := by
  induction d using Nat.strongRecOn generalizing lam with
  | ind d ih =>
    by_cases hd : d ≤ lam
    · have he : reify lam (code s.val) = (promoteOT hd s).val := by
        apply code_injective
        rw [code_reify_normal lam (code s.val) (code_normal s.val) hw]
        exact (code_promote hd s.val).symm
      rw [he]
      exact (promoteOT hd s).property
    · cases d with
      | zero => omega
      | succ d =>
        cases d with
        | zero =>
          have hl : lam = 0 := by omega
          subst lam
          obtain ⟨n, he⟩ := FiniteCorrespondence.zero_dimension_exhaustive (reify 0 (code s.val))
          rw [he]
          exact FiniteCorrespondence.ofNat_isOT_zero n
        | succ k =>
          have hlo : width (code s.val) ≤ k + 1 := Nat.le_trans hw (by omega)
          have ho : OuterForm (code s.val) := outer_code (isOT_outer s.property)
          have hs : compareT s.val (dimensionBound k) = .lt := by
            rw [← compareCode_code]
            exact fitting_outer_below_boundary k (code s.val) (code_normal s.val) ho hlo
          obtain ⟨u, hu⟩ := DimensionCut.isOT_below_dimensionBound s.property hs
          have hc : code u.val = code s.val := by
            have he := congrArg code hu
            simpa only [code_pad] using he
          have hwu : width (code u.val) ≤ lam := by rw [hc]; exact hw
          have h := ih (k + 1) (by omega) lam u hwu
          simpa only [hc] using h

theorem original_representative_iff (c : Code) (hn : c.normal) :
    (∃ s : AllOT, code s.2.val = c) ↔ T.isOT (width c) (reify (width c) c) := by
  constructor
  · rintro ⟨⟨d, s⟩, hs⟩
    have h := generated_reify d (width c) s (by rw [hs]; exact Nat.le_refl _)
    simpa only [hs] using h
  · intro h
    exact ⟨⟨width c, reify (width c) c, h⟩, code_reify_normal _ c hn (Nat.le_refl _)⟩

theorem representative_generated (q : Classes) :
    T.isOT (width (representative q)) (reify (width (representative q)) (representative q)) := by
  apply (original_representative_iff _ (representative_normal q)).mp
  obtain ⟨s, hs⟩ := exists_rep q
  exact ⟨s, congrArg representative hs⟩

def coordinateWitness (q : Classes) : AllOT :=
  ⟨width (representative q), reify (width (representative q)) (representative q), representative_generated q⟩

theorem coordinateWitness_spec (q : Classes) : classOf (coordinateWitness q) = q := by
  apply classCode_injective
  exact code_reify_normal _ (representative q) (representative_normal q) (Nat.le_refl _)

theorem minDimension_eq_width (q : Classes) : minDimension q = width (representative q) := by
  apply Nat.le_antisymm
  · exact dimensionWitness_minimal q (coordinateWitness q) (coordinateWitness_spec q)
  · have h := width_code (dimensionWitness q).2.val
    rw [representative_spec q] at h
    exact h

end Support.CodeReification

namespace Support.TargetIndexCuts

open OCF.Jaeger

universe u

def IndicesBelow (k : Nat) : Term → Prop
  | .zero => True
  | .add a b => IndicesBelow k a ∧ IndicesBelow k b
  | .inacc n b => n < k ∧ IndicesBelow k b
  | .psi v b => IndicesBelow k v ∧ IndicesBelow k b

theorem IndicesBelow.mono {j k : Nat} (hjk : j ≤ k) {t : Term}
    (ht : IndicesBelow j t) : IndicesBelow k t := by
  induction t with
  | zero => trivial
  | add a b iha ihb => exact ⟨iha ht.1, ihb ht.2⟩
  | inacc n b ih => exact ⟨Nat.lt_of_lt_of_le ht.1 hjk, ih ht.2⟩
  | psi v b ihv ihb => exact ⟨ihv ht.1, ihb ht.2⟩

def collapse (k : Nat) : Term := .psi (.inacc k .zero) .zero

def boundary (k : Nat) : Term := .psi Term.bigOmega (collapse k)

theorem collapse_wf (k : Nat) : Term.wf (collapse k) = true := by
  simp [collapse, Term.wf, Term.isRT, Term.isLimT, Term.isSucc,
    Term.fT, Term.H, Term.allLt]

theorem boundary_wf (k : Nat) (hk : 0 < k) : Term.wf (boundary k) = true := by
  simp [boundary, collapse, Term.wf, Term.isRT, Term.isLimT, Term.isSucc,
    Term.fT, Term.H, Term.predR, Term.bigOmega, Term.le, Term.lt,
    CountableTarget.lt_zero, Term.hOne, Term.one, Term.allLt, Nat.ne_of_gt hk]

theorem IndicesBelow.fT_lt {k : Nat} (hk : 0 < k) {t : Term}
    (ht : IndicesBelow k t) : Term.fT t < k := by
  induction t with
  | zero | add => exact hk
  | inacc n b => exact ht.1
  | psi v b ihv _ => exact ihv ht.1

theorem IndicesBelow.below_inacc {k : Nat} (hk : 0 < k) {t : Term}
    (ht : IndicesBelow k t) : Term.lt t (.inacc k .zero) = true := by
  induction t with
  | zero => simp [Term.lt]
  | add a b iha _ => simpa only [Term.lt] using iha ht.1
  | inacc n b ih => simpa [Term.lt, ht.1] using ih ht.2
  | psi v b ihv _ =>
    have hv := ht.1.fT_lt hk
    simp [Term.lt, Nat.not_lt.mpr (Nat.le_of_lt hv), Nat.le_of_lt hv, ihv ht.1]

theorem IndicesBelow.below_collapse {k : Nat} (hk : 0 < k) {t : Term}
    (ht : IndicesBelow k t) : Term.lt t (collapse k) = true := by
  induction t with
  | zero => simp [collapse, Term.lt]
  | add a b iha _ => simpa only [collapse, Term.lt] using iha ht.1
  | inacc n b ih =>
    simpa [collapse, Term.lt, Term.fT, ht.1, Nat.not_le.mpr ht.1] using ih ht.2
  | psi v b ihv _ =>
    rw [collapse, Term.lt]
    have hv := ht.1.below_inacc hk
    have hp := ihv ht.1
    unfold collapse at hp
    simp [hv, hp]

theorem outer_below_boundary {k : Nat} (hk : 0 < k) {t : Term}
    (ho : CountableTarget.Outer t) (ht : IndicesBelow k t) :
    Term.lt t (boundary k) = true := by
  cases ho with
  | zero => simp [boundary, Term.lt]
  | atom b =>
    simpa only [boundary, Unary.psi_omega_lt] using ht.2.below_collapse hk
  | cons a b _ =>
    simpa only [boundary, Term.lt, Unary.psi_omega_lt] using ht.1.2.below_collapse hk

theorem indicesBelow_below_boundary {k : Nat} (hk : 0 < k) (t : WFBelowOmega)
    (ht : IndicesBelow k t.val) : Term.lt t.val (boundary k) = true :=
  outer_below_boundary hk (CountableTarget.target_outer t) ht

private theorem wf_lt_trans [LargeCardinals.{u}] {a b c : Term}
    (ha : Term.wf a = true) (hb : Term.wf b = true) (hc : Term.wf c = true)
    (hab : Term.lt a b = true) (hbc : Term.lt b c = true) : Term.lt a c = true :=
  lemma_6_1.{u}.2.1 a b c ha hb hc hab hbc

private theorem head_lt_psi (t v b : Term) :
    Term.lt (Term.head t) (.psi v b) = Term.lt t (.psi v b) := by
  cases t <;> simp only [Term.head, Term.lt]

private theorem tail_below_psi [LargeCardinals.{u}] {a b v c : Term}
    (hw : Term.wf (.add a b) = true) (hp : Term.wf (.psi v c) = true)
    (hlt : Term.lt a (.psi v c) = true) : Term.lt b (.psi v c) = true := by
  have h := (Term.wf_add_iff a b).mp hw
  have hh := (CountableTarget.head_properties h.2.2.1 h.2.2.2.1).2
  have hl : Term.lt (Term.head b) (.psi v c) = true := by
    have he := h.2.2.2.2
    simp only [Term.le, Bool.or_eq_true, decide_eq_true_eq] at he
    rcases he with he | he
    · rw [he]; exact hlt
    · exact wf_lt_trans hh h.2.1 hp he hlt
  rwa [head_lt_psi] at hl

private theorem high_inacc_not_below_inacc {n k : Nat} (hn : k ≤ n) (a : Term) :
    Term.lt (.inacc n a) (.inacc k .zero) = false := by
  simp [Term.lt, Nat.not_lt.mpr hn, CountableTarget.lt_zero]

private theorem high_inacc_not_below_collapse {n k : Nat} (hn : k ≤ n) (a : Term) :
    Term.lt (.inacc n a) (collapse k) = false := by
  simp [collapse, Term.lt, Term.fT, Nat.not_lt.mpr hn,
    high_inacc_not_below_inacc hn]

private theorem high_psi_not_below_collapse {n k : Nat} (hn : k ≤ n) (a b : Term) :
    Term.lt (.psi (.inacc n a) b) (collapse k) = false := by
  have hp : Term.lt (.psi (.inacc n a) b) (.inacc k .zero) =
      decide ((.inacc n a : Term) = .inacc k .zero) := by
    by_cases hnk : n ≤ k
    · have he : n = k := Nat.le_antisymm hnk hn
      subst n
      simp [Term.lt, Term.fT, CountableTarget.lt_zero]
    · have hne : n ≠ k := by omega
      simp [Term.lt, Term.fT, Nat.not_lt.mpr hn, hnk, hne]
  rw [collapse, Term.lt]
  simp only [high_inacc_not_below_inacc hn, Bool.false_and,
    CountableTarget.lt_zero, Bool.and_false, Bool.false_or, hp]
  by_cases he : (.inacc n a : Term) = .inacc k .zero
  · rw [he, TargetArithmetic.lt_self]; simp
  · simp [he]

private theorem lower_psi_below_collapse_subscript [LargeCardinals.{u}]
    {n k : Nat} (hn : n < k) {a b : Term} (hw : Term.wf (.inacc n a) = true)
    (hlt : Term.lt (.psi (.inacc n a) b) (collapse k) = true) :
    Term.lt a (collapse k) = true := by
  rw [collapse, Term.lt] at hlt
  simp only [CountableTarget.lt_zero, Bool.and_false, Bool.or_false,
    Bool.or_eq_true, Bool.and_eq_true] at hlt
  rcases hlt with hlt | hlt
  · simpa [Term.lt, collapse, Term.fT, hn, Nat.not_le.mpr hn] using hlt.2
  · have hl : Term.lt (.inacc n a) (.inacc k .zero) = true := by
      simpa [Term.lt, Term.fT, Nat.not_lt.mpr (Nat.le_of_lt hn),
        Nat.le_of_lt hn, Nat.ne_of_lt hn] using hlt.2
    have hkw : Term.wf (.inacc k .zero) = true := by simp [Term.wf, Term.fT]
    have hself := wf_lt_trans hkw hw hkw hlt.1 hl
    rw [TargetArithmetic.lt_self] at hself
    cases hself

private theorem H_omega_inacc_psi (n : Nat) (a b : Term) :
    Term.H Term.bigOmega (.psi (.inacc n a) b) =
      b :: (Term.H Term.bigOmega b ++ Term.H Term.bigOmega (.inacc n a)) := by
  simp [Term.H, Term.predR, Term.bigOmega, Term.le, Term.lt, CountableTarget.lt_zero]

theorem indicesBelow_of_collapse_bounds [LargeCardinals.{u}] {k : Nat}
    (t : Term) : Term.wf t = true → Term.lt t (collapse k) = true →
    (∀ z, z ∈ Term.H Term.bigOmega t → Term.lt z (collapse k) = true) →
    IndicesBelow k t := by
  induction t with
  | zero => intro _ _ _; trivial
  | add a b iha ihb =>
    intro hw hlt hH
    have h := (Term.wf_add_iff a b).mp hw
    have ha : Term.lt a (collapse k) = true := by simpa only [collapse, Term.lt] using hlt
    have hb := tail_below_psi hw (collapse_wf k) ha
    exact ⟨iha h.2.1 ha (fun z hz => hH z (List.mem_append.mpr (Or.inl hz))),
      ihb h.2.2.1 hb (fun z hz => hH z (List.mem_append.mpr (Or.inr hz)))⟩
  | inacc n a iha =>
    intro hw hlt hH
    have hn : n < k := by
      by_cases hn : n < k
      · exact hn
      · rw [high_inacc_not_below_collapse (Nat.le_of_not_gt hn)] at hlt; cases hlt
    refine ⟨hn, iha ((Term.wf_inacc_iff n a).mp hw).1 ?_ ?_⟩
    · simpa [collapse, Term.lt, Term.fT, hn, Nat.not_le.mpr hn] using hlt
    · intro z hz
      exact hH z (by simp only [Term.H, List.mem_append]; exact Or.inr hz)
  | psi v b ihv ihb =>
    intro hw hlt hH
    have h := (Term.wf_psi_iff v b).mp hw
    cases v with
    | zero | add | psi => cases h.1
    | inacc n a =>
      have hn : n < k := by
        by_cases hn : n < k
        · exact hn
        · rw [high_psi_not_below_collapse (Nat.le_of_not_gt hn)] at hlt; cases hlt
      have ha := lower_psi_below_collapse_subscript hn h.2.1 hlt
      have hv : Term.lt (.inacc n a) (collapse k) = true := by
        simpa [collapse, Term.lt, Term.fT, hn, Nat.not_le.mpr hn] using ha
      have hHv : ∀ z, z ∈ Term.H Term.bigOmega (.inacc n a) →
          Term.lt z (collapse k) = true := by
        intro z hz
        exact hH z (by
          simp only [H_omega_inacc_psi, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inr hz))
      have hb := hH b (by simp [H_omega_inacc_psi])
      have hHb : ∀ z, z ∈ Term.H Term.bigOmega b → Term.lt z (collapse k) = true := by
        intro z hz
        exact hH z (by
          simp only [H_omega_inacc_psi, List.mem_cons, List.mem_append]
          exact Or.inr (Or.inl hz))
      exact ⟨ihv h.2.1 hv hHv, ihb h.2.2.1 hb hHb⟩

theorem wf_below_boundary_indicesBelow [LargeCardinals.{u}] {k : Nat} (hk : 0 < k)
    (t : Term) : Term.wf t = true → Term.lt t (boundary k) = true → IndicesBelow k t := by
  induction t with
  | zero => intro _ _; trivial
  | add a b iha ihb =>
    intro hw hlt
    have h := (Term.wf_add_iff a b).mp hw
    have ha : Term.lt a (boundary k) = true := by simpa only [boundary, Term.lt] using hlt
    have hb := tail_below_psi hw (boundary_wf k hk) ha
    exact ⟨iha h.2.1 ha, ihb h.2.2.1 hb⟩
  | inacc n a =>
    intro _ hlt
    rw [boundary, CountableTarget.inacc_not_below_psiOmega] at hlt
    cases hlt
  | psi v a =>
    intro hw hlt
    have h := (Term.wf_psi_iff v a).mp hw
    have he := CountableTarget.psi_lt_psiOmega_subscript h.1 hlt
    subst v
    have ha : Term.lt a (collapse k) = true := by
      simpa only [boundary, Unary.psi_omega_lt] using hlt
    have hH : ∀ z, z ∈ Term.H Term.bigOmega a → Term.lt z (collapse k) = true := by
      intro z hz
      have hzlt := (Term.allLt_iff _ _).mp h.2.2.2 z hz
      have hzwf := H_wf.{u} h.1 h.2.1 h.2.2.1 hz
      exact wf_lt_trans hzwf h.2.2.1 (collapse_wf k) hzlt ha
    exact ⟨⟨hk, trivial⟩, indicesBelow_of_collapse_bounds a h.2.2.1 ha hH⟩

theorem indicesBelow_iff_below_boundary [LargeCardinals.{u}] {k : Nat} (hk : 0 < k)
    (t : WFBelowOmega) : IndicesBelow k t.val ↔ Term.lt t.val (boundary k) = true :=
  ⟨indicesBelow_below_boundary hk t, wf_below_boundary_indicesBelow hk t.val t.property.1⟩

theorem indicesBelow_initial [LargeCardinals.{u}] {k : Nat} (hk : 0 < k)
    (s t : WFBelowOmega) (hst : Term.lt s.val t.val = true)
    (ht : IndicesBelow k t.val) : IndicesBelow k s.val := by
  apply (indicesBelow_iff_below_boundary hk s).mpr
  exact wf_lt_trans s.property.1 t.property.1 (boundary_wf k hk) hst
    (indicesBelow_below_boundary hk t ht)

end Support.TargetIndexCuts

namespace Support.DimensionImage

open OCF.Jaeger Support.OTQuotient Support.BinaryTranslation
open Support.DimensionCut Support.TargetIndexCuts

theorem indices_one {k : Nat} (hk : 0 < k) : IndicesBelow k Term.one := by
  simp [IndicesBelow, Term.one, Term.bigOmega, hk]

theorem indices_drop {k : Nat} {t : Term} (ht : IndicesBelow k t) :
    IndicesBelow k (dropOne t) := by
  cases t with
  | zero => trivial
  | add a b => simp only [dropOne]; split <;> simp_all [IndicesBelow]
  | inacc n b => exact ht
  | psi u b => simp only [dropOne]; split <;> simp_all [IndicesBelow]

theorem indices_succ {k : Nat} (hk : 0 < k) {t : Term} (ht : IndicesBelow k t) :
    IndicesBelow k (succTerm t) := by
  induction t with
  | zero => exact indices_one hk
  | add a b _ ih => exact ⟨ht.1, ih ht.2⟩
  | inacc n b | psi u b => exact ⟨ht, indices_one hk⟩

theorem indices_getD {k : Nat} (xs : List Term) (hs : ∀ t ∈ xs, IndicesBelow k t) (i : Nat) :
    IndicesBelow k (xs[i]?.getD .zero) := by
  induction xs generalizing i with
  | nil => simp [IndicesBelow]
  | cons a xs ih =>
    cases i with
    | zero => simpa using hs a (by simp)
    | succ i => simpa using ih (fun t ht => hs t (by simp [ht])) i

theorem indices_lower {k j : Nat} (hk : 0 < k) (hj : j ≤ k) (xs : List Term)
    (hs : ∀ t ∈ xs, IndicesBelow k t) (h : Term) (hh : IndicesBelow k h) :
    IndicesBelow k (lower j xs h) := by
  induction j generalizing h with
  | zero => exact hh
  | succ j ih =>
    rw [lower]
    apply ih (by omega)
    have ha := indices_getD xs hs j
    split
    · split
      · exact ⟨⟨by omega, trivial⟩, ha⟩
      · split
        · trivial
        · exact ⟨⟨by omega, trivial⟩, indices_drop ha⟩
    · split
      · exact hh
      · exact ⟨⟨by omega, indices_succ hk hh⟩, indices_drop ha⟩

theorem indices_principal {d : Nat} (hd : 2 ≤ d) (xs : List Term)
    (hs : ∀ t ∈ xs, IndicesBelow (d - 1) t) :
    IndicesBelow (d - 1) (principal d xs) := by
  have hk : 0 < d - 1 := by omega
  rw [principal]
  split
  · have ha := indices_getD xs hs 0
    have hb := indices_getD xs hs 1
    rw [OT2.principal]
    split
    · exact ⟨⟨by omega, trivial⟩, ha⟩
    · split
      · exact ⟨by omega, indices_drop hb⟩
      · exact ⟨⟨by omega, indices_succ hk (indices_drop hb)⟩, indices_drop ha⟩
  · apply indices_lower hk (by omega) xs hs
    have ha := indices_getD xs hs (d - 1)
    have hb := indices_getD xs hs (d - 2)
    split
    · split
      · trivial
      · exact ⟨by omega, indices_drop ha⟩
    · refine ⟨⟨by omega, ?_⟩, indices_drop hb⟩
      split
      · trivial
      · exact indices_succ hk (indices_drop ha)

theorem indices_assemble {k : Nat} {a b : Term} (ha : IndicesBelow k a) (hb : IndicesBelow k b) :
    IndicesBelow k (OT2.assemble a b) := by
  unfold OT2.assemble
  split
  · exact ha
  · exact ⟨ha, hb⟩

mutual
  theorem indices_convert (d : Nat) (hd : 2 ≤ d) (s : Code) :
      IndicesBelow (d - 1) (convert d s) := by
    cases s with
    | zero => simp [convert, IndicesBelow]
    | p xs b =>
      rw [convert]
      exact indices_assemble (indices_principal hd _ (indices_arguments d hd xs)) (indices_convert d hd b)
  termination_by sizeOf s

  theorem indices_arguments (d : Nat) (hd : 2 ≤ d) (xs : List Code) :
      ∀ t ∈ arguments d xs, IndicesBelow (d - 1) t := by
    cases xs with
    | nil => simp [arguments]
    | cons a xs =>
      intro t ht
      simp only [arguments, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact indices_convert d hd a
      · exact indices_arguments d hd xs t ht
  termination_by sizeOf xs
end

end Support.DimensionImage

namespace Support.SourceFundOrder

open new Support.OTQuotient Support.DimensionCut

theorem domOmega_fund_ne_zero {lam : Nat} (s t : T lam)
    {v : Vec (T lam) lam} (hd : T.dom s = .Omega v) : T.fund s t ≠ .Z := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte] at hd
      rw [T.fund]
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          simp only [hm] at hd
          by_cases hz : i.val = 0
          · simp only [hz, ↓reduceIte] at hd; cases hd
          · obtain ⟨m, him⟩ := i
            cases m with
            | zero => exact False.elim (hz rfl)
            | succ m => simp
        | Omega ys => simp only []; split <;> simp
    · simp only [T.fund, hb, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]

theorem iter_ofNat_succ {lam : Nat} (F : T lam → T lam) (n : Nat) :
    T.iter F (T.ofNat (n + 1)) = F (T.iter F (T.ofNat n)) := by
  simp only [T.ofNat, T.iter]

theorem domOmega_iter_lt_next {lam : Nat} (s : T lam) {v : Vec (T lam) lam}
    (hd : T.dom s = .Omega v) (n : Nat) :
    T.lt (T.iter (T.fund s) (T.ofNat n))
      (T.iter (T.fund s) (T.ofNat (n + 1))) := by
  induction n with
  | zero =>
    rw [iter_ofNat_succ]
    simp only [T.ofNat, T.iter]
    have hn := domOmega_fund_ne_zero s .Z hd
    cases he : T.fund s .Z with
    | Z => exact False.elim (hn he)
    | P => rfl
  | succ n ih =>
    rw [iter_ofNat_succ s.fund (n + 1), iter_ofNat_succ s.fund n]
    exact fund_mono s hd _ _ ih

theorem mul_principal_ofNat_succ {lam : Nat} (xs : Vec (T lam) lam) (n : Nat) :
    T.mul (.P xs .Z) (T.ofNat (n + 1)) = .P xs (T.mul (.P xs .Z) (T.ofNat n)) := by
  simp only [T.ofNat, T.mul, HAdd.hAdd, Add.add, T.oplus]

theorem mul_principal_ofNat_lt_next {lam : Nat} (xs : Vec (T lam) lam) (n : Nat) :
    T.lt (T.mul (.P xs .Z) (T.ofNat n))
      (T.mul (.P xs .Z) (T.ofNat (n + 1))) := by
  induction n with
  | zero => simp only [T.ofNat, T.mul, HAdd.hAdd, Add.add, T.oplus, T.lt, compareT]
  | succ n ih =>
    rw [mul_principal_ofNat_succ xs n, mul_principal_ofNat_succ xs (n + 1)]
    simpa only [T.lt, compareT, Vec_refl] using ih

theorem countable_fund_lt_next {lam : Nat} (s : T lam) (hd : T.dom s = .omega)
    (n : Nat) : T.lt (T.fund s (T.ofNat n)) (T.fund s (T.ofNat (n + 1))) := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte] at hd
      rw [T.fund.eq_def (.P xs .Z) (T.ofNat n),
        T.fund.eq_def (.P xs .Z) (T.ofNat (n + 1))]
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchild := (minIdx_spec xs hm).1.symm
        simp only [GetElem.getElem, Fin.eta]
        cases d with
        | zero => exact False.elim ((minIdx_spec xs hm).2.1 rfl)
        | one =>
          simp only [hm] at hd
          obtain ⟨m, him⟩ := i
          cases m with
          | zero => exact mul_principal_ofNat_lt_next _ n
          | succ m => simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero,
              and_false, ↓reduceIte, reduceCtorEq] at hd
        | omega =>
          have hi := countable_fund_lt_next (xs.idx i) hchild n
          change compareT (.P (xs.rplc i _) .Z) (.P (xs.rplc i _) .Z) = .lt
          simp only [compareT, compareVec_rplc_pair_lt xs i _ _ hi]
        | Omega ys =>
          simp only [hm] at hd
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte]
            have hi := fund_mono (xs.idx i) hchild _ _
              (domOmega_iter_lt_next (xs.idx i) hchild n)
            change compareT (.P (xs.rplc i _) .Z) (.P (xs.rplc i _) .Z) = .lt
            simp only [compareT, compareVec_rplc_pair_lt xs i _ _ hi]
          · simp only [hv, ↓reduceIte] at hd; cases hd
    · rw [T.dom, ite_eq_right hb] at hd
      rw [T.fund.eq_def (.P xs b) (T.ofNat n),
        T.fund.eq_def (.P xs b) (T.ofNat (n + 1))]
      simp only [hb, ↓reduceIte]
      have hi := countable_fund_lt_next b hd n
      simpa only [T.lt, compareT, Vec_refl] using hi
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

theorem dom_one_fund_constant {lam : Nat} (s : T lam) (hd : T.dom s = .one)
    (t u : T lam) : T.fund s t = T.fund s u := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [DimensionCut.dom_one_principal xs hd]
      simp only [T.fund, ↓reduceIte, zeros_minIdx]
    · rw [T.dom, ite_eq_right hb] at hd
      rw [T.fund.eq_def (.P xs b) t, T.fund.eq_def (.P xs b) u]
      simp only [hb, ↓reduceIte]
      rw [dom_one_fund_constant b hd t u]
termination_by T.size s
decreasing_by all_goals simp_all only [T.size]; all_goals omega

end Support.SourceFundOrder

namespace Support.DimensionImage

open OCF.Jaeger Support.OTQuotient Support.BinaryTranslation

universe u

theorem lower_keep (k : Nat) (xs : List Term) (h : Term) (hh : h ≠ .zero)
    (hz : ∀ i, i < k → xs[i]?.getD .zero = .zero) : lower k xs h = h := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lower]
    simp only [hz k (by omega), hh, ↓reduceIte]
    exact ih (fun i hi => hz i (by omega))

theorem lower_zero_context (k : Nat) (xs : List Term) (hk : 0 < k)
    (hz : ∀ i, 0 < i → i < k → xs[i]?.getD .zero = .zero) :
    lower k xs .zero = .psi Term.bigOmega (xs[0]?.getD .zero) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [lower]
    | succ k =>
      rw [lower]
      simp only [hz (k + 1) (by omega) (by omega), ↓reduceIte,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]
      exact ih (by omega) (fun i hi hik => hz i hi (by omega))

theorem principal_low (d : Nat) (xs : List Term)
    (hz : ∀ i, 0 < i → xs[i]?.getD .zero = .zero) :
    principal d xs = .psi Term.bigOmega (xs[0]?.getD .zero) := by
  rw [principal]
  split
  · simp [OT2.principal, hz 1 (by omega)]
  · rename_i hd
    have hhigh := hz (d - 1) (by omega)
    have hmiddle := hz (d - 2) (by omega)
    simp only [hhigh, hmiddle, ↓reduceIte]
    exact lower_zero_context (d - 2) xs (by omega) (fun i hi _ => hz i hi)

theorem principal_nil (d : Nat) : principal d [] = Term.one := by
  rw [principal_low d [] (by intro i hi; simp)]
  rfl

theorem principal_singleton (d : Nat) (a : Term) : principal d [a] = .psi Term.bigOmega a := by
  rw [principal_low d [a] (by intro i hi; cases i with | zero => omega | succ i => simp)]
  rfl

theorem convert_one (d : Nat) : convert d UserImage.oneCode = Term.one := by
  simp [UserImage.oneCode, convert, arguments, principal_nil, OT2.assemble]

theorem arguments_append (d : Nat) (xs ys : List Code) :
    arguments d (xs ++ ys) = arguments d xs ++ arguments d ys := by
  induction xs with
  | nil => simp [arguments]
  | cons a xs ih => simp [arguments, ih]

theorem arguments_zeros (d k : Nat) : arguments d (List.replicate k .zero) = List.replicate k Term.zero := by
  induction k with
  | zero => simp [arguments]
  | succ k ih => simp [arguments, List.replicate_succ, convert, ih]

end Support.DimensionImage

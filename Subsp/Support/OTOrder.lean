import Subsp.Support.Main

/-! The usual order `<` on OT is well-founded, and on OT it coincides with the order
`FundLT` generated (by `FundOrder.TransClosure`) from natural fundamental-sequence steps. -/

namespace Support.OTOrder

open new OCF.Jaeger Support.OTQuotient Support.GeneralImageEmbedding
open Support.DimensionCut Support.SourceFundOrder

universe u

/-! ### Well-foundedness -/

theorem lt_iff_classLT {lam : Nat} (s t : T.OT lam) :
    s.val < t.val ↔ ClassLT (classOf ⟨lam, s⟩) (classOf ⟨lam, t⟩) := by
  show compareT s.val t.val = .lt ↔ compareCode (code s.val) (code t.val) = .lt
  rw [compareCode_code]

theorem classLT_wellFounded [LargeCardinals.{u}] : WellFounded ClassLT := by
  have h := Support.GeneralImageUniformMain.global_certificate.{u}
  refine Subrelation.wf (r := InvImage (fun a b : OCF.Ordinal.{u} => a < b)
    (fun q => Term.V.{u} (classConversion q))) ?_ (InvImage.wf _ OCF.Ordinal.lt_wellFounded)
  intro q r hqr
  exact (lt_iff_V.{u} (h.wf q) (h.wf r)).mp ((h.order q r).mp hqr)

/-- The usual order on `T.OT lam` is well-founded. -/
theorem ot_lt_wellFounded [LargeCardinals.{u}] (lam : Nat) :
    WellFounded (fun s t : T.OT lam => s.val < t.val) :=
  Subrelation.wf (fun h => (lt_iff_classLT _ _).mp h)
    (InvImage.wf (fun s : T.OT lam => classOf ⟨lam, s⟩) classLT_wellFounded.{u})

/-! ### Vectors and the cases of `fund` -/

theorem zeros_idx {lam m : Nat} (j : Fin m) : (zeros (lam := lam) m).idx j = .Z := by
  rw [zeros, Vec.ofFn_idx]

theorem rplc_rplc {A : Type} {m : Nat} (xs : Vec A m) (i : Fin m) (a b : A) :
    (xs.rplc i a).rplc i b = xs.rplc i b := by
  apply vec_ext; intro j
  simp only [vec_rplc_idx]
  split <;> rfl

theorem rplc_eq_self {A : Type} {m : Nat} (xs : Vec A m) (i : Fin m) (a : A)
    (h : xs.idx i = a) : xs.rplc i a = xs := by
  apply vec_ext; intro j
  rw [vec_rplc_idx]
  split
  · rename_i hj; rw [Fin.ext hj, h]
  · rfl

theorem rplc_snoc {lam m : Nat} (xs : Vec (T lam) m) (x : T lam) (i : Fin (m + 1)) (a : T lam) :
    (Vec.snoc m xs x).rplc i a =
      if h : i.val < m then Vec.snoc m (xs.rplc ⟨i.val, h⟩ a) x else Vec.snoc m xs a := by
  by_cases hi : i.val < m
  · simp only [hi, ↓reduceDIte]
    apply vec_ext; intro j
    rw [vec_rplc_idx]
    by_cases hj : j.val < m
    · simp only [Vec.idx, hj, ↓reduceDIte, vec_rplc_idx]
    · have hji : j.val ≠ i.val := by omega
      simp only [Vec.idx, hj, ↓reduceDIte, hji, ite_false]
  · simp only [hi, ↓reduceDIte]
    apply vec_ext; intro j
    rw [vec_rplc_idx]
    by_cases hj : j.val < m
    · have hji : j.val ≠ i.val := by omega
      simp only [Vec.idx, hj, ↓reduceDIte, hji, ite_false]
    · have hji : j.val = i.val := by omega
      simp only [Vec.idx, hi, ↓reduceDIte, hji, ite_true]

theorem size_rplc {lam m : Nat} (xs : Vec (T lam) m) (i : Fin m) (a : T lam) :
    Vec.size (xs.rplc i a) + T.size (xs.idx i) = Vec.size xs + T.size a := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    rw [rplc_snoc]
    split
    · rename_i h
      have := ih ⟨i.val, h⟩
      simp only [Vec.size, Vec.idx, h, ↓reduceDIte]
      omega
    · rename_i h
      simp only [Vec.size, Vec.idx, h, ↓reduceDIte]
      omega

theorem minIdx_at {lam m : Nat} (xs : Vec (T lam) m) (i : Fin m)
    (hlow : ∀ j : Fin m, j.val < i.val → xs.idx j = .Z) (hi : xs.idx i ≠ .Z) :
    T.domVecMinIdx xs = some (i, T.dom (xs.idx i)) := by
  cases h : T.domVecMinIdx xs with
  | none =>
    rw [(minIdx_none_iff xs).mp h, zeros_idx] at hi
    exact absurd rfl hi
  | some p =>
    obtain ⟨i', d⟩ := p
    obtain ⟨hd, hd0, hlow'⟩ := minIdx_spec xs h
    have he : i' = i := by
      rcases Nat.lt_trichotomy i'.val i.val with hlt | heq | hgt
      · exact absurd (hd.trans ((dom_eq_zero_iff _).mpr (hlow i' hlt))) hd0
      · exact Fin.ext heq
      · exact absurd (hlow' i hgt) hi
    subst he; rw [hd]

theorem rplc_low {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (w : T lam)
    (hlow : ∀ j : Fin lam, j.val < i.val → xs.idx j = .Z) :
    ∀ j : Fin lam, j.val < i.val → (xs.rplc i w).idx j = .Z := by
  intro j hj
  rw [vec_rplc_idx, ite_eq_right (by omega)]
  exact hlow j hj

theorem minIdx_rplc {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (w : T lam)
    (hlow : ∀ j : Fin lam, j.val < i.val → xs.idx j = .Z) (hw : w ≠ .Z) :
    T.domVecMinIdx (xs.rplc i w) = some (i, T.dom w) := by
  have h := minIdx_at (xs.rplc i w) i (rplc_low xs i w hlow) (by rw [vec_rplc_idx, ite_eq_left rfl]; exact hw)
  rwa [vec_rplc_idx, ite_eq_left rfl] at h

theorem fund_tail {lam : Nat} (xs : Vec (T lam) lam) (b t : T lam) (hb : b ≠ .Z) :
    T.fund (.P xs b) t = .P xs (T.fund b t) := by
  rw [T.fund, ite_eq_right hb]

theorem dom_tail {lam : Nat} (xs : Vec (T lam) lam) (b : T lam) (hb : b ≠ .Z) :
    T.dom (.P xs b) = T.dom b := by
  rw [T.dom, ite_eq_right hb]

theorem fund_none {lam : Nat} (xs : Vec (T lam) lam) (t : T lam) (hm : T.domVecMinIdx xs = none) :
    T.fund (.P xs .Z) t = .Z := by
  simp only [T.fund, ↓reduceIte, hm]

theorem dom_none {lam : Nat} (xs : Vec (T lam) lam) (hm : T.domVecMinIdx xs = none) :
    T.dom (.P xs .Z) = .one := by
  simp only [T.dom, ↓reduceIte, hm]

theorem fund_one_zero {lam : Nat} (xs : Vec (T lam) lam) (h0 : 0 < lam) (t : T lam)
    (hm : T.domVecMinIdx xs = some (⟨0, h0⟩, .one)) :
    T.fund (.P xs .Z) t = T.mul (.P (xs.rplc ⟨0, h0⟩ (T.fund (xs.idx ⟨0, h0⟩) .Z)) .Z) t := by
  simp only [T.fund, ↓reduceIte, hm, GetElem.getElem]

theorem dom_one_zero {lam : Nat} (xs : Vec (T lam) lam) (h0 : 0 < lam)
    (hm : T.domVecMinIdx xs = some (⟨0, h0⟩, .one)) : T.dom (.P xs .Z) = .omega := by
  simp only [T.dom, ↓reduceIte, hm]

theorem fund_one_succ {lam : Nat} (xs : Vec (T lam) lam) (m : Nat) (hm1 : m + 1 < lam) (t : T lam)
    (hm : T.domVecMinIdx xs = some (⟨m + 1, hm1⟩, .one)) :
    T.fund (.P xs .Z) t =
      .P ((xs.rplc ⟨m + 1, hm1⟩ (T.fund (xs.idx ⟨m + 1, hm1⟩) .Z)).rplc ⟨m, by omega⟩ t) .Z := by
  simp only [T.fund, ↓reduceIte, hm, GetElem.getElem]

theorem dom_one_succ {lam : Nat} (xs : Vec (T lam) lam) (m : Nat) (hm1 : m + 1 < lam)
    (hm : T.domVecMinIdx xs = some (⟨m + 1, hm1⟩, .one)) : T.dom (.P xs .Z) = .Omega xs := by
  simp only [T.dom, ↓reduceIte, hm]; simp

theorem fund_omega {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (t : T lam)
    (hm : T.domVecMinIdx xs = some (i, .omega)) :
    T.fund (.P xs .Z) t = .P (xs.rplc i (T.fund (xs.idx i) t)) .Z := by
  simp only [T.fund, ↓reduceIte, hm, GetElem.getElem]

theorem dom_omega {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam)
    (hm : T.domVecMinIdx xs = some (i, .omega)) : T.dom (.P xs .Z) = .omega := by
  simp only [T.dom, ↓reduceIte, hm]

theorem fund_diag {lam : Nat} (xs q : Vec (T lam) lam) (i : Fin lam) (t : T lam)
    (hm : T.domVecMinIdx xs = some (i, .Omega q)) (hq : Vec.lt xs q) :
    T.fund (.P xs .Z) t =
      .P (xs.rplc i (T.fund (xs.idx i) (T.iter (T.fund (xs.idx i)) t))) .Z := by
  simp only [T.fund, ↓reduceIte, hm, hq, GetElem.getElem]

theorem dom_diag {lam : Nat} (xs q : Vec (T lam) lam) (i : Fin lam)
    (hm : T.domVecMinIdx xs = some (i, .Omega q)) (hq : Vec.lt xs q) :
    T.dom (.P xs .Z) = .omega := by
  simp only [T.dom, ↓reduceIte, hm, hq]

theorem fund_nondiag {lam : Nat} (xs q : Vec (T lam) lam) (i : Fin lam) (t : T lam)
    (hm : T.domVecMinIdx xs = some (i, .Omega q)) (hq : ¬ Vec.lt xs q) :
    T.fund (.P xs .Z) t = .P (xs.rplc i (T.fund (xs.idx i) t)) .Z := by
  simp only [T.fund, ↓reduceIte, hm, hq, GetElem.getElem]

theorem dom_nondiag {lam : Nat} (xs q : Vec (T lam) lam) (i : Fin lam)
    (hm : T.domVecMinIdx xs = some (i, .Omega q)) (hq : ¬ Vec.lt xs q) :
    T.dom (.P xs .Z) = .Omega q := by
  simp only [T.dom, ↓reduceIte, hm, hq]

/-- At a successor domain the fundamental sequence ignores its argument. -/
theorem fund_dom_one {lam : Nat} : ∀ (s : T lam), T.dom s = .one → ∀ t : T lam,
    T.fund s t = T.fund s .Z
  | .Z, _, _ => by simp only [T.fund]
  | .P xs b, hs, t => by
    by_cases hb : b = .Z
    · subst hb
      cases hm : T.domVecMinIdx xs with
      | none => rw [fund_none xs t hm, fund_none xs _ hm]
      | some p =>
        obtain ⟨i, d⟩ := p
        simp only [T.dom, ↓reduceIte, hm] at hs
        cases d <;> simp only [] at hs
        all_goals first | cases hs | (split at hs <;> cases hs)
    · rw [fund_tail xs b t hb, fund_tail xs b _ hb,
        fund_dom_one b (by rwa [dom_tail xs b hb] at hs) t]
termination_by s => T.size s
decreasing_by exact T.add_size_lt_P xs b

theorem mul_one {lam : Nat} (xs : Vec (T lam) lam) :
    T.mul (.P xs .Z) (T.ofNat 1) = .P xs .Z := by
  simp only [T.ofNat, T.mul, HAdd.hAdd, Add.add, T.oplus]

theorem mul_succ {lam : Nat} (xs : Vec (T lam) lam) (n : Nat) :
    T.mul (.P xs .Z) (T.ofNat (n + 1)) = .P xs (T.mul (.P xs .Z) (T.ofNat n)) := by
  simp only [T.ofNat, T.mul, HAdd.hAdd, Add.add, T.oplus]

theorem fund_ofNat_succ {lam : Nat} (n : Nat) (t : T lam) :
    T.fund (T.ofNat (n + 1)) t = T.ofNat n := by
  induction n with
  | zero => exact fund_one t
  | succ n ih =>
    rw [T.ofNat, fund_tail _ _ t (by simp [T.ofNat]), ih, T.ofNat]

/-! ### Reachability by steps that lift through contexts -/

/-- A step `u ↦ u[n]` from a nonzero `u` that uses index `0` unless `dom u = ω`. -/
def GoodStep {lam : Nat} (u v : T lam) : Prop :=
  u ≠ .Z ∧ (v = T.fund u .Z ∨ (T.dom u = .omega ∧ ∃ n : Nat, v = T.fund u (T.ofNat n)))

inductive Reach {lam : Nat} : T lam → T lam → Prop
  | refl (u : T lam) : Reach u u
  | tail {u v w : T lam} : Reach u v → GoodStep v w → Reach u w

theorem Reach.single {lam : Nat} {u v : T lam} (h : GoodStep u v) : Reach u v := .tail (.refl u) h

theorem Reach.trans {lam : Nat} {u v w : T lam} (h₁ : Reach u v) (h₂ : Reach v w) : Reach u w := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

theorem Reach.lift_tail {lam : Nat} (xs : Vec (T lam) lam) {e e' : T lam} (h : Reach e e') :
    Reach (.P xs e) (.P xs e') := by
  induction h with
  | refl => exact .refl _
  | @tail v w _ hs ih =>
    obtain ⟨hv, hw⟩ := hs
    refine .tail ih ⟨(by intro h; cases h), ?_⟩
    rcases hw with rfl | ⟨hd, n, rfl⟩
    · exact Or.inl (fund_tail xs v .Z hv).symm
    · exact Or.inr ⟨(dom_tail xs v hv).trans hd, n, (fund_tail xs v _ hv).symm⟩

theorem lift_step {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam)
    (hlow : ∀ j : Fin lam, j.val < i.val → xs.idx j = .Z) {v w : T lam} (hs : GoodStep v w) :
    Reach (.P (xs.rplc i v) .Z) (.P (xs.rplc i w) .Z) := by
  obtain ⟨hv, hw⟩ := hs
  have hm := minIdx_rplc xs i v hlow hv
  have hidx : (xs.rplc i v).idx i = v := by rw [vec_rplc_idx, ite_eq_left rfl]
  have hne : (T.P (xs.rplc i v) .Z) ≠ .Z := by intro h; cases h
  have hzero : T.dom v ≠ .omega → w = T.fund v .Z := by
    intro hd
    rcases hw with h | ⟨h, _⟩
    · exact h
    · exact absurd h hd
  cases hd : T.dom v with
  | zero => exact absurd ((dom_eq_zero_iff v).mp hd) hv
  | one =>
    rw [hzero (by rw [hd]; intro h; cases h)]
    rw [hd] at hm
    obtain ⟨iv, hi⟩ := i
    cases iv with
    | zero =>
      refine Reach.single ⟨hne, Or.inr ⟨dom_one_zero _ hi hm, 1, ?_⟩⟩
      rw [fund_one_zero _ hi _ hm, hidx, rplc_rplc, mul_one]
    | succ m =>
      refine Reach.single ⟨hne, Or.inl ?_⟩
      rw [fund_one_succ _ m hi _ hm, hidx, rplc_rplc,
        rplc_eq_self (xs.rplc ⟨m + 1, hi⟩ (T.fund v .Z)) ⟨m, by omega⟩ .Z (by
          rw [vec_rplc_idx, ite_eq_right (by simp)]
          exact hlow ⟨m, by omega⟩ (by simp))]
  | omega =>
    rw [hd] at hm
    have key : ∀ t, T.fund (T.P (xs.rplc i v) .Z) t = .P (xs.rplc i (T.fund v t)) .Z := by
      intro t; rw [fund_omega _ i t hm, hidx, rplc_rplc]
    rcases hw with rfl | ⟨_, n, rfl⟩
    · exact Reach.single ⟨hne, Or.inl (key _).symm⟩
    · exact Reach.single ⟨hne, Or.inr ⟨dom_omega _ i hm, n, (key _).symm⟩⟩
  | Omega q =>
    rw [hzero (by rw [hd]; intro h; cases h)]
    rw [hd] at hm
    refine Reach.single ⟨hne, Or.inl ?_⟩
    by_cases hq : Vec.lt (xs.rplc i v) q
    · rw [fund_diag _ q i _ hm hq, hidx, rplc_rplc]
      simp only [T.iter]
    · rw [fund_nondiag _ q i _ hm hq, hidx, rplc_rplc]

/-- Steps of the selected coordinate lift to steps of the principal term. -/
theorem Reach.lift_coord {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam)
    (hlow : ∀ j : Fin lam, j.val < i.val → xs.idx j = .Z) {w w' : T lam} (h : Reach w w') :
    Reach (.P (xs.rplc i w) .Z) (.P (xs.rplc i w') .Z) := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.trans (lift_step xs i hlow hs)

theorem size_pos {lam : Nat} {s : T lam} (h : s ≠ .Z) : 0 < T.size s := by
  cases s with
  | Z => exact absurd rfl h
  | P xs b => simp only [T.size]; omega

theorem size_rplc_zero_lt {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (hc : xs.idx i ≠ .Z) :
    T.size (.P (xs.rplc i .Z) .Z) < T.size (.P xs .Z) := by
  have h1 := size_rplc xs i .Z
  have h2 := size_pos hc
  simp only [T.size] at h1 ⊢
  omega

/-- Every term reaches `0`. -/
theorem reach_zero {lam : Nat} : ∀ u : T lam, Reach u .Z
  | .Z => .refl _
  | .P xs .Z => by
    cases hm : T.domVecMinIdx xs with
    | none => exact Reach.single ⟨(by intro h; cases h), Or.inl (fund_none xs _ hm).symm⟩
    | some p =>
      obtain ⟨i, d⟩ := p
      obtain ⟨hd, hd0, hlow⟩ := minIdx_spec xs hm
      have hc : xs.idx i ≠ .Z := fun h => hd0 (hd.trans ((dom_eq_zero_iff _).mpr h))
      have h1 := Reach.lift_coord xs i hlow (reach_zero (xs.idx i))
      rw [rplc_eq_self xs i _ rfl] at h1
      exact h1.trans (reach_zero (.P (xs.rplc i .Z) .Z))
  | .P xs (.P ys c) =>
    (Reach.lift_tail xs (reach_zero (.P ys c))).trans (reach_zero (.P xs .Z))
termination_by u => T.size u
decreasing_by
  all_goals first
    | exact T.idx_size_lt_P xs _ i
    | exact size_rplc_zero_lt xs i (by assumption)
    | exact T.add_size_lt_P xs _
    | (simp only [T.size]; omega)

/-- At an uncountable domain, reachability of arguments lifts to the fundamental sequence. -/
theorem reach_arg {lam : Nat} : ∀ (c : T lam) (q : Vec (T lam) lam), T.dom c = .Omega q →
    ∀ x y : T lam, Reach x y → Reach (T.fund c x) (T.fund c y)
  | .Z, q, hd, _, _, _ => by simp [T.dom] at hd
  | .P xs b, q, hd, x, y, hxy => by
    by_cases hb : b = .Z
    · subst hb
      cases hm : T.domVecMinIdx xs with
      | none => rw [dom_none xs hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        obtain ⟨hd', hd0, hlow⟩ := minIdx_spec xs hm
        cases d with
        | zero => exact absurd rfl hd0
        | one =>
          obtain ⟨iv, hi⟩ := i
          cases iv with
          | zero => rw [dom_one_zero xs hi hm] at hd; cases hd
          | succ m =>
            rw [fund_one_succ xs m hi x hm, fund_one_succ xs m hi y hm]
            refine Reach.lift_coord _ ⟨m, by omega⟩ ?_ hxy
            intro j hj
            rw [vec_rplc_idx, ite_eq_right (by simp at hj ⊢; omega)]
            exact hlow j (by simp at hj ⊢; omega)
        | omega => rw [dom_omega xs i hm] at hd; cases hd
        | Omega q' =>
          by_cases hq : Vec.lt xs q'
          · rw [dom_diag xs q' i hm hq] at hd; cases hd
          · rw [fund_nondiag xs q' i x hm hq, fund_nondiag xs q' i y hm hq]
            exact Reach.lift_coord xs i hlow (reach_arg (xs.idx i) q' hd'.symm x y hxy)
    · rw [fund_tail xs b x hb, fund_tail xs b y hb]
      exact Reach.lift_tail xs (reach_arg b q (by rwa [dom_tail xs b hb] at hd) x y hxy)
termination_by c => T.size c
decreasing_by
  all_goals first | exact T.idx_size_lt_P xs _ i | exact T.add_size_lt_P xs b

theorem reach_ofNat_succ {lam : Nat} (n : Nat) : Reach (T.ofNat (lam := lam) (n + 1)) (T.ofNat n) :=
  Reach.single ⟨by simp [T.ofNat], Or.inl (fund_ofNat_succ n .Z).symm⟩

theorem reach_iter {lam : Nat} (c : T lam) (q : Vec (T lam) lam) (hd : T.dom c = .Omega q) (n : Nat) :
    Reach (T.fund c (T.iter (T.fund c) (T.ofNat (n + 1)))) (T.fund c (T.iter (T.fund c) (T.ofNat n))) := by
  have key : ∀ n, Reach (T.iter (T.fund c) (T.ofNat (n + 1))) (T.iter (T.fund c) (T.ofNat n)) := by
    intro n
    induction n with
    | zero => simp only [T.ofNat, T.iter]; exact reach_zero _
    | succ n ih =>
      rw [iter_ofNat_succ _ (n + 1), iter_ofNat_succ _ n]
      exact reach_arg c q hd _ _ ih
  exact reach_arg c q hd _ _ (key n)

theorem reach_mul {lam : Nat} (ys : Vec (T lam) lam) (n : Nat) :
    Reach (.P ys (T.mul (.P ys .Z) (T.ofNat n))) (T.mul (.P ys .Z) (T.ofNat n)) := by
  induction n with
  | zero => simp only [T.ofNat, T.mul]; exact reach_zero _
  | succ n ih => rw [mul_succ]; exact Reach.lift_tail ys ih

/-- The chain property: `u[n + 1]` reaches `u[n]`. -/
theorem reach_fund_succ {lam : Nat} : ∀ (u : T lam) (n : Nat),
    Reach (T.fund u (T.ofNat (n + 1))) (T.fund u (T.ofNat n))
  | .Z, n => by simp only [T.fund]; exact .refl _
  | .P xs b, n => by
    by_cases hb : b = .Z
    · subst hb
      cases hm : T.domVecMinIdx xs with
      | none => rw [fund_none xs _ hm, fund_none xs _ hm]; exact .refl _
      | some p =>
        obtain ⟨i, d⟩ := p
        obtain ⟨hd', hd0, hlow⟩ := minIdx_spec xs hm
        cases d with
        | zero => exact absurd rfl hd0
        | one =>
          obtain ⟨iv, hi⟩ := i
          cases iv with
          | zero =>
            rw [fund_one_zero xs hi _ hm, fund_one_zero xs hi _ hm, mul_succ]
            exact reach_mul _ n
          | succ m =>
            rw [fund_one_succ xs m hi _ hm, fund_one_succ xs m hi _ hm]
            refine Reach.lift_coord _ ⟨m, by omega⟩ ?_ (reach_ofNat_succ n)
            intro j hj
            rw [vec_rplc_idx, ite_eq_right (by simp at hj ⊢; omega)]
            exact hlow j (by simp at hj ⊢; omega)
        | omega =>
          rw [fund_omega xs i _ hm, fund_omega xs i _ hm]
          exact Reach.lift_coord xs i hlow (reach_fund_succ (xs.idx i) n)
        | Omega q =>
          by_cases hq : Vec.lt xs q
          · rw [fund_diag xs q i _ hm hq, fund_diag xs q i _ hm hq]
            exact Reach.lift_coord xs i hlow (reach_iter (xs.idx i) q hd'.symm n)
          · rw [fund_nondiag xs q i _ hm hq, fund_nondiag xs q i _ hm hq]
            exact Reach.lift_coord xs i hlow
              (reach_arg (xs.idx i) q hd'.symm _ _ (reach_ofNat_succ n))
    · rw [fund_tail xs b _ hb, fund_tail xs b _ hb]
      exact Reach.lift_tail xs (reach_fund_succ b n)
termination_by u => T.size u
decreasing_by
  all_goals first | exact T.idx_size_lt_P xs _ i | exact T.add_size_lt_P xs b

theorem reach_fund_le {lam : Nat} (u : T lam) {a b : Nat} (h : a ≤ b) :
    Reach (T.fund u (T.ofNat b)) (T.fund u (T.ofNat a)) := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]; exact .refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with hlt | hge
    · exact (reach_fund_succ u b).trans (ih (by omega))
    · rw [Nat.le_antisymm h hge]; exact .refl _

/-! ### The order generated by fundamental-sequence steps -/

/-- One natural fundamental-sequence step: `a = b[n]` for a nonzero `b`. -/
def FundStep {lam : Nat} (a b : T lam) : Prop := b ≠ .Z ∧ ∃ n : Nat, a = T.fund b (T.ofNat n)

/-- The order generated from `FundStep` by `FundOrder.TransClosure`. -/
def FundLT {lam : Nat} (s t : T lam) : Prop := FundOrder.TransClosure FundStep s t

theorem lt_irrefl {lam : Nat} (s : T lam) : ¬ s < s := by
  intro h
  change compareT s s = .lt at h
  rw [T_refl] at h
  cases h

theorem fundLT_lt {lam : Nat} {s t : T lam} (h : FundLT s t) : s < t := by
  induction h with
  | single h => obtain ⟨hb, n, rfl⟩ := h; exact fund_lt _ _ hb
  | tail _ h ih => obtain ⟨hb, n, rfl⟩ := h; exact T_trans _ _ _ ih (fund_lt _ _ hb)

/-- Descent by arbitrary natural steps (`u` reaches `v`). -/
inductive Desc {lam : Nat} : T lam → T lam → Prop
  | refl (u : T lam) : Desc u u
  | step {u v : T lam} (n : Nat) : u ≠ .Z → Desc (T.fund u (T.ofNat n)) v → Desc u v

theorem Desc.trans {lam : Nat} {u v w : T lam} (h₁ : Desc u v) (h₂ : Desc v w) : Desc u w := by
  induction h₁ with
  | refl => exact h₂
  | step n hu _ ih => exact .step n hu (ih h₂)

theorem Desc.tail {lam : Nat} {u v : T lam} (h : Desc u v) (hv : v ≠ .Z) (n : Nat) :
    Desc u (T.fund v (T.ofNat n)) :=
  h.trans (.step n hv (.refl _))

theorem Reach.desc {lam : Nat} {u v : T lam} (h : Reach u v) : Desc u v := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    obtain ⟨hv, hw⟩ := hs
    rcases hw with rfl | ⟨_, n, rfl⟩
    · exact ih.tail hv 0
    · exact ih.tail hv n

theorem Desc.fundLT {lam : Nat} {u v : T lam} (h : Desc u v) : u = v ∨ FundLT v u := by
  induction h with
  | refl => exact Or.inl rfl
  | step n hu _ ih =>
    have hs : FundStep (T.fund _ (T.ofNat n)) _ := ⟨hu, n, rfl⟩
    rcases ih with he | h
    · rw [← he]; exact Or.inr (.single hs)
    · exact Or.inr (.tail h hs)

/-! ### Generators of OT -/

/-- The generators of `T.isOT lam`. -/
def base : (lam : Nat) → Nat → T lam
  | 0, n => T.LF 0 n
  | lam + 1, n => .P (Vec.ofFn (lam + 1) (fun i => if i.val = 0 then T.LF (lam + 1) n else .Z)) .Z

theorem base_isOT (lam n : Nat) : T.isOT lam (base lam n) := by
  cases lam with
  | zero => exact .base_0 n
  | succ lam => exact .base_succ lam n

theorem isOT_from_base {lam : Nat} {s : T lam} (h : T.isOT lam s) : ∃ n, Desc (base lam n) s := by
  induction h with
  | base_0 n => exact ⟨n, .refl _⟩
  | base_succ lam n => exact ⟨n, .refl _⟩
  | step lam s _ k ih =>
    obtain ⟨n, h⟩ := ih
    by_cases hz : s = .Z
    · subst hz; exact ⟨n, by simpa only [T.fund] using h⟩
    · exact ⟨n, h.tail hz k⟩

theorem ofFn_single {lam : Nat} (i : Fin lam) (a : T lam) :
    Vec.ofFn lam (fun j => if j.val = i.val then a else .Z) = (zeros lam).rplc i a := by
  apply vec_ext; intro j
  rw [Vec.ofFn_idx, vec_rplc_idx, zeros_idx]

theorem reach_LF {lam : Nat} (n : Nat) : Reach (T.LF lam (n + 1)) (T.LF lam n) := by
  cases lam with
  | zero =>
    induction n with
    | zero =>
      refine Reach.single ⟨by simp [T.LF], Or.inl ?_⟩
      simp only [T.LF, T.fund, ↓reduceIte, T.domVecMinIdx]
    | succ n ih =>
      have h := Reach.lift_tail Vec.nil ih
      simpa only [T.LF] using h
  | succ l =>
    have hlow : ∀ j : Fin (l + 1), j.val < (Fin.last l).val → (zeros (lam := l + 1) (l + 1)).idx j = .Z :=
      fun j _ => zeros_idx j
    have hLF : ∀ m, T.LF (l + 1) (m + 1) = .P ((zeros (l + 1)).rplc (Fin.last l) (T.LF (l + 1) m)) .Z := by
      intro m
      rw [T.LF, ← ofFn_single]
      rfl
    induction n with
    | zero =>
      rw [hLF]
      refine Reach.single ⟨(by intro h; cases h), Or.inl ?_⟩
      have hz : (zeros (lam := l + 1) (l + 1)).rplc (Fin.last l) (T.LF (l + 1) 0) = zeros (l + 1) :=
        rplc_eq_self _ _ _ (by rw [zeros_idx]; rfl)
      rw [hz, fund_none _ _ (zeros_minIdx _)]
      rfl
    | succ n ih =>
      have h := Reach.lift_coord _ _ hlow ih
      rw [← hLF (n + 1), ← hLF n] at h
      exact h

theorem reach_base {lam : Nat} (n : Nat) : Reach (base lam (n + 1)) (base lam n) := by
  cases lam with
  | zero => exact reach_LF n
  | succ l =>
    have h := Reach.lift_coord (zeros (l + 1)) ⟨0, by omega⟩ (fun j hj => by simp at hj)
      (reach_LF (lam := l + 1) n)
    simpa only [base, ← ofFn_single] using h

theorem desc_base {lam : Nat} {n N : Nat} (h : n ≤ N) : Desc (base lam N) (base lam n) := by
  induction N with
  | zero => rw [Nat.le_zero.mp h]; exact .refl _
  | succ N ih =>
    rcases Nat.lt_or_ge n (N + 1) with hlt | hge
    · exact (reach_base N).desc.trans (ih (by omega))
    · rw [Nat.le_antisymm h hge]; exact .refl _

/-! ### Main results -/

/-- Everything reachable from an OT element is linearly ordered by reachability. -/
theorem desc_total [LargeCardinals.{u}] {lam : Nat} (u : T.OT lam) :
    ∀ x y : T lam, Desc u.val x → Desc u.val y → Desc x y ∨ Desc y x := by
  refine (ot_lt_wellFounded.{u} lam).induction
    (C := fun u : T.OT lam => ∀ x y : T lam, Desc u.val x → Desc u.val y → Desc x y ∨ Desc y x) u ?_
  intro ⟨uv, huv⟩ ih x y hx hy
  cases hx with
  | refl => exact Or.inl hy
  | step a hu hx' =>
    cases hy with
    | refl => exact Or.inr (.step a hu hx')
    | step b _ hy' =>
      rcases Nat.le_total a b with hab | hba
      · exact ih ⟨_, .step _ _ huv b⟩ (fund_lt _ _ hu) x y
          ((reach_fund_le uv hab).desc.trans hx') hy'
      · exact ih ⟨_, .step _ _ huv a⟩ (fund_lt _ _ hu) x y hx'
          ((reach_fund_le uv hba).desc.trans hy')

/-- On OT, the usual order coincides with the order generated by natural
fundamental-sequence steps. -/
theorem lt_iff_fundLT [LargeCardinals.{u}] {lam : Nat} {s t : T lam}
    (hs : T.isOT lam s) (ht : T.isOT lam t) : s < t ↔ FundLT s t := by
  refine ⟨fun hlt => ?_, fundLT_lt⟩
  obtain ⟨n₁, h₁⟩ := isOT_from_base hs
  obtain ⟨n₂, h₂⟩ := isOT_from_base ht
  have hs' := (desc_base (lam := lam) (Nat.le_max_left n₁ n₂)).trans h₁
  have ht' := (desc_base (lam := lam) (Nat.le_max_right n₁ n₂)).trans h₂
  rcases desc_total.{u} ⟨_, base_isOT lam (max n₁ n₂)⟩ s t hs' ht' with h | h
  · rcases h.fundLT with he | h'
    · subst he; exact absurd hlt (lt_irrefl _)
    · exact absurd (T_trans _ _ _ hlt (fundLT_lt h')) (lt_irrefl _)
  · rcases h.fundLT with he | h'
    · subst he; exact absurd hlt (lt_irrefl _)
    · exact h'

/-- The fundamental-sequence order is well-founded on OT. -/
theorem fundLT_wellFounded [LargeCardinals.{u}] (lam : Nat) :
    WellFounded (fun s t : T.OT lam => FundLT s.val t.val) :=
  Subrelation.wf (fun h => fundLT_lt h) (ot_lt_wellFounded.{u} lam)

end Support.OTOrder

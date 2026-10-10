import Subsp.multi.kuma.Quotient

/-! Unfolding of the `multi` kumakuma system on fixed-dimension terms, dimension lifting of
source terms, target arithmetic, and dimension cuts (the `multi` version of
`Subsp/Support/Dimension.lean`). -/

namespace kumakuma.OTQuotient

open multi

/-! ### Vector updates -/

theorem set_of_ge (v : V multi.T) (i : Nat) (x : multi.T) (h : v.length ≤ i) : V.set v i x = v := by
  induction v with
  | emp => rfl
  | snoc b bx ih =>
    simp only [V.length] at h
    simp only [V.set, show i ≠ bx.length by omega, ite_false, ih (by omega)]

theorem set_eq_self (v : V multi.T) (i : Nat) (x : multi.T) (h : V.get0 v i = x) :
    V.set v i x = v := by
  by_cases hi : i < v.length
  · apply V.eq_of_get0 _ _ (V.length_set v i x)
    intro j
    rw [V.get0_set v i x j hi]
    split
    · rename_i hj; rw [hj, h]
    · rfl
  · exact set_of_ge v i x (Nat.le_of_not_lt hi)

theorem set_set (v : V multi.T) (i : Nat) (a b : multi.T) :
    V.set (V.set v i a) i b = V.set v i b := by
  by_cases hi : i < v.length
  · apply V.eq_of_get0 _ _ (by rw [V.length_set, V.length_set, V.length_set])
    intro j
    rw [V.get0_set _ i b j (by rw [V.length_set]; exact hi), V.get0_set v i b j hi,
      V.get0_set v i a j hi]
    split <;> rfl
  · rw [set_of_ge v i a (Nat.le_of_not_lt hi)]

/-! ### The first nonzero coordinate -/

theorem fnz_eq_some {v : V multi.T} {i : Nat} (hi : V.get0 v i ≠ .Z)
    (hlow : ∀ j, j < i → V.get0 v j = .Z) : V.fnz v = some i := by
  rcases h : V.fnz v with _ | k
  · exact absurd (V.fnz_none_spec v h i) hi
  · obtain ⟨hk, hklow⟩ := V.fnz_some_spec v k h
    rcases Nat.lt_trichotomy k i with hki | rfl | hik
    · exact absurd (hlow k hki) hk
    · rfl
    · exact absurd (hklow i hik) hi

theorem fnz_eq_none {v : V multi.T} (h : ∀ j, V.get0 v j = .Z) : V.fnz v = none := by
  rcases hf : V.fnz v with _ | k
  · rfl
  · exact absurd (h k) (V.fnz_some_spec v k hf).1

theorem fnz_none_iff (v : V multi.T) : V.fnz v = none ↔ ∀ j, V.get0 v j = .Z :=
  ⟨V.fnz_none_spec v, fnz_eq_none⟩

theorem fnz_set {v : V multi.T} {i : Nat} (hi : i < v.length)
    (hlow : ∀ j, j < i → V.get0 v j = .Z) {w : multi.T} (hw : w ≠ .Z) :
    V.fnz (V.set v i w) = some i := by
  apply fnz_eq_some
  · rw [V.get0_set_same v i w hi]; exact hw
  · intro j hj
    rw [V.get0_set_ne v i w j (Nat.ne_of_lt hj)]
    exact hlow j hj

theorem fnz_lt_length {v : V multi.T} {i : Nat} (h : V.fnz v = some i) : i < v.length :=
  V.lt_length_of_fnz v i h

/-! ### `dom` with full labels

`domF` is `T.dom` without normalizing the label of `Omega`; on fixed-dimension terms it is
the domain function of the fixed-dimension system. -/

/-- `T.dom` without normalizing the `Omega` label. -/
def domF (s : multi.T) : Dom :=
  match s with
  | .Z => .zero
  | .P li add =>
    if add = .Z then
      match V.fnz li with
      | none => .one
      | some i =>
        match domF (V.get0 li i) with
        | .one =>
          match i with
          | 0 => .omega
          | _ + 1 => .Omega li
        | .Omega ri => if li < ri then .omega else .Omega ri
        | _ => .omega
    else domF add
termination_by s.size
decreasing_by
  all_goals
    simp only [multi.T.size]
    first
    | omega
    | have := multi.V.size_get0_le li i; omega

/-- Normalization of the label of a domain. -/
def _root_.kumakuma.Dom.nrm : Dom → Dom
  | .zero => .zero
  | .one => .one
  | .omega => .omega
  | .Omega q => .Omega (V.norm q)

theorem domF_Z : domF .Z = .zero := by rw [domF]

theorem domF_tail (v : V multi.T) {a : multi.T} (ha : a ≠ .Z) : domF (.P v a) = domF a := by
  rw [domF, ite_eq_right ha]

theorem domF_none {v : V multi.T} (h : V.fnz v = none) : domF (.P v .Z) = .one := by
  rw [domF, ite_eq_left rfl, h]

theorem domF_one_zero {v : V multi.T} (h : V.fnz v = some 0) (hd : domF (V.get0 v 0) = .one) :
    domF (.P v .Z) = .omega := by
  rw [domF, ite_eq_left rfl, h]; simp only [hd]

theorem domF_one_succ {v : V multi.T} {m : Nat} (h : V.fnz v = some (m + 1))
    (hd : domF (V.get0 v (m + 1)) = .one) : domF (.P v .Z) = .Omega v := by
  rw [domF, ite_eq_left rfl, h]; simp only [hd]

theorem domF_omega {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .omega) : domF (.P v .Z) = .omega := by
  rw [domF, ite_eq_left rfl, h]; simp only [hd]

theorem domF_zero {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .zero) : domF (.P v .Z) = .omega := by
  rw [domF, ite_eq_left rfl, h]; simp only [hd]

theorem domF_diag {v : V multi.T} {i : Nat} {q : V multi.T} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .Omega q) (hq : v < q) : domF (.P v .Z) = .omega := by
  rw [domF, ite_eq_left rfl, h]; simp only [hd, hq, ↓reduceIte]

theorem domF_nondiag {v : V multi.T} {i : Nat} {q : V multi.T} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .Omega q) (hq : ¬ v < q) : domF (.P v .Z) = .Omega q := by
  rw [domF, ite_eq_left rfl, h]; simp only [hd, hq, ↓reduceIte]

theorem dom_eq_nrm : ∀ s : multi.T, T.dom s = (domF s).nrm
  | .Z => by rw [T.dom, domF]; rfl
  | .P v a => by
    by_cases ha : a = .Z
    · subst ha
      rw [T.dom, domF, ite_eq_left rfl, ite_eq_left rfl]
      rcases hf : V.fnz v with _ | i
      · rfl
      · simp only []
        rw [dom_eq_nrm (V.get0 v i)]
        cases hd : domF (V.get0 v i) with
        | zero => rfl
        | one => cases i <;> rfl
        | omega => rfl
        | Omega q =>
          have hq : v < V.norm q ↔ v < q := V.lt_congr rfl (V.norm_norm q)
          by_cases h : v < q
          · simp only [Dom.nrm, hq, h, ↓reduceIte]
          · simp only [Dom.nrm, hq, h, ↓reduceIte]
    · rw [T.dom, domF, ite_eq_right ha, ite_eq_right ha]
      exact dom_eq_nrm a
termination_by s => s.size
decreasing_by
  · exact multi.T.size_get0_lt_P _ _ _
  · exact multi.T.size_lt_P_right _ _

theorem domF_P_ne_zero : ∀ (a : multi.T) (v : V multi.T), domF (.P v a) ≠ .zero
  | .Z, v => by
    rcases hf : V.fnz v with _ | i
    · rw [domF_none hf]; intro h; cases h
    · cases hdi : domF (V.get0 v i) with
      | zero => rw [domF_zero hf hdi]; intro h; cases h
      | one =>
        cases i with
        | zero => rw [domF_one_zero hf hdi]; intro h; cases h
        | succ k => rw [domF_one_succ hf hdi]; intro h; cases h
      | omega => rw [domF_omega hf hdi]; intro h; cases h
      | Omega q =>
        by_cases hq : v < q
        · rw [domF_diag hf hdi hq]; intro h; cases h
        · rw [domF_nondiag hf hdi hq]; intro h; cases h
  | .P w b, v => by
    rw [domF_tail v (fun h => multi.T.noConfusion h)]
    exact domF_P_ne_zero b w

theorem domF_eq_zero_iff (s : multi.T) : domF s = .zero ↔ s = .Z := by
  cases s with
  | Z => exact ⟨fun _ => rfl, fun _ => domF_Z⟩
  | P v a => exact ⟨fun h => absurd h (domF_P_ne_zero a v), fun h => by cases h⟩

theorem domF_some_ne_one {v : V multi.T} {i : Nat} (hf : V.fnz v = some i) :
    domF (.P v .Z) ≠ .one := by
  cases hdi : domF (V.get0 v i) with
  | zero => rw [domF_zero hf hdi]; intro h; cases h
  | one =>
    cases i with
    | zero => rw [domF_one_zero hf hdi]; intro h; cases h
    | succ k => rw [domF_one_succ hf hdi]; intro h; cases h
  | omega => rw [domF_omega hf hdi]; intro h; cases h
  | Omega q =>
    by_cases hq : v < q
    · rw [domF_diag hf hdi hq]; intro h; cases h
    · rw [domF_nondiag hf hdi hq]; intro h; cases h

/-- A principal term with domain `1` has only zero coordinates. -/
theorem dom_one_principal {v : V multi.T} (h : domF (.P v .Z) = .one) : ∀ i, V.get0 v i = .Z := by
  rcases hf : V.fnz v with _ | i
  · exact V.fnz_none_spec v hf
  · exact absurd h (domF_some_ne_one hf)

/-! ### Unfolding `fund` -/

theorem fund_Z (t : multi.T) : T.fund .Z t = .Z := by rw [T.fund]

theorem fund_tail (v : V multi.T) {a : multi.T} (ha : a ≠ .Z) (t : multi.T) :
    T.fund (.P v a) t = .P v (T.fund a t) := by
  conv => lhs; rw [T.fund]
  rw [ite_eq_right ha]

theorem fund_none {v : V multi.T} (h : V.fnz v = none) (t : multi.T) :
    T.fund (.P v .Z) t = .Z := by
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]

theorem fund_one_zero {v : V multi.T} (h : V.fnz v = some 0) (hd : domF (V.get0 v 0) = .one)
    (t : multi.T) : T.fund (.P v .Z) t =
      multi.T.mul (.P (V.set v 0 (T.fund (V.get0 v 0) .Z)) .Z) t := by
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]; simp only [dom_eq_nrm, hd, Dom.nrm]

theorem fund_one_succ {v : V multi.T} {m : Nat} (h : V.fnz v = some (m + 1))
    (hd : domF (V.get0 v (m + 1)) = .one) (t : multi.T) :
    T.fund (.P v .Z) t =
      .P (V.set (V.set v (m + 1) (T.fund (V.get0 v (m + 1)) .Z)) m t) .Z := by
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]; simp only [dom_eq_nrm, hd, Dom.nrm]

theorem fund_omega {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .omega) (t : multi.T) :
    T.fund (.P v .Z) t = .P (V.set v i (T.fund (V.get0 v i) t)) .Z := by
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]; simp only [dom_eq_nrm, hd, Dom.nrm]

theorem fund_zero {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .zero) (t : multi.T) :
    T.fund (.P v .Z) t = .P (V.set v i (T.fund (V.get0 v i) t)) .Z := by
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]; simp only [dom_eq_nrm, hd, Dom.nrm]

theorem fund_diag {v : V multi.T} {i : Nat} {q : V multi.T} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .Omega q) (hq : v < q) (t : multi.T) :
    T.fund (.P v .Z) t =
      .P (V.set v i (T.fund (V.get0 v i) (multi.T.iter (T.fund (V.get0 v i)) t))) .Z := by
  have hq' : v < V.norm q := (V.lt_congr rfl (V.norm_norm q)).2 hq
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]; simp only [dom_eq_nrm, hd, Dom.nrm, hq', ↓reduceIte]

theorem fund_nondiag {v : V multi.T} {i : Nat} {q : V multi.T} (h : V.fnz v = some i)
    (hd : domF (V.get0 v i) = .Omega q) (hq : ¬ v < q) (t : multi.T) :
    T.fund (.P v .Z) t = .P (V.set v i (T.fund (V.get0 v i) t)) .Z := by
  have hq' : ¬ v < V.norm q := fun h' => hq ((V.lt_congr rfl (V.norm_norm q)).1 h')
  conv => lhs; rw [T.fund]
  rw [ite_eq_left rfl, h]; simp only [dom_eq_nrm, hd, Dom.nrm, hq', ↓reduceIte]

/-- At a successor domain the fundamental sequence ignores its argument. -/
theorem fund_dom_one : ∀ (s : multi.T), domF s = .one → ∀ t : multi.T, T.fund s t = T.fund s .Z
  | .Z, _, _ => by rw [fund_Z, fund_Z]
  | .P xs b, hs, t => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf, fund_none hf]
      · exact absurd hs (domF_some_ne_one hf)
    · rw [fund_tail xs hb, fund_tail xs hb,
        fund_dom_one b (by rwa [domF_tail xs hb] at hs) t]
termination_by s => s.size
decreasing_by exact multi.T.size_lt_P_right xs b

/-! ### Fixed dimension is preserved -/

theorem Dim_oplus {d : Nat} : ∀ {s t : multi.T}, Dim d s → Dim d t → Dim d (s + t)
  | .Z, _, _, ht => ht
  | .P _ a, t, hs, ht => by
    show Dim d (multi.T.P _ (a + t))
    exact Dim_P hs.length hs.coord (Dim_oplus hs.tail ht)

theorem Dim_mul {d : Nat} {s : multi.T} (hs : Dim d s) :
    ∀ {t : multi.T}, Dim d t → Dim d (multi.T.mul s t)
  | .Z, _ => Dim_Z d
  | .P _ b, ht => by
    show Dim d (s + multi.T.mul s b)
    exact Dim_oplus hs (Dim_mul hs ht.tail)

theorem Dim_iter {d : Nat} {F : multi.T → multi.T} (hF : ∀ x, Dim d x → Dim d (F x)) :
    ∀ {t : multi.T}, Dim d t → Dim d (multi.T.iter F t)
  | .Z, _ => Dim_Z d
  | .P _ b, ht => by
    show Dim d (F (multi.T.iter F b))
    exact hF _ (Dim_iter hF ht.tail)

theorem Dim_set {d : Nat} {v : V multi.T} {a : multi.T} (h : Dim d (multi.T.P v a)) (i : Nat)
    {x : multi.T} (hx : Dim d x) (b : multi.T) (hb : Dim d b) :
    Dim d (multi.T.P (V.set v i x) b) := by
  by_cases hi : i < v.length
  · refine Dim_P (by rw [V.length_set]; exact h.length) (fun j => ?_) hb
    rw [V.get0_set v i x j hi]
    split
    · exact hx
    · exact h.coord j
  · rw [set_of_ge v i x (Nat.le_of_not_lt hi)]
    exact Dim_P h.length h.coord hb

theorem Dim_fund {d : Nat} (s : multi.T) :
    ∀ (t : multi.T), Dim d s → Dim d t → Dim d (T.fund s t) := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro t hs ht
    cases s with
    | Z => rw [fund_Z]; exact Dim_Z d
    | P v a =>
      by_cases ha : a = .Z
      · subst ha
        rcases hf : V.fnz v with _ | i
        · rw [fund_none hf]; exact Dim_Z d
        · have hrec : ∀ u, Dim d u → Dim d (T.fund (V.get0 v i) u) :=
            fun u hu => ih _ (multi.T.size_get0_lt_P v i .Z) u (hs.coord i) hu
          cases hd : domF (V.get0 v i) with
          | zero => rw [fund_zero hf hd]; exact Dim_set hs i (hrec t ht) _ (Dim_Z d)
          | omega => rw [fund_omega hf hd]; exact Dim_set hs i (hrec t ht) _ (Dim_Z d)
          | one =>
            cases i with
            | zero =>
              rw [fund_one_zero hf hd]
              exact Dim_mul (Dim_set hs 0 (hrec _ (Dim_Z d)) _ (Dim_Z d)) ht
            | succ k =>
              rw [fund_one_succ hf hd]
              exact Dim_set (Dim_set hs (k + 1) (hrec _ (Dim_Z d)) _ (Dim_Z d)) k ht _ (Dim_Z d)
          | Omega q =>
            by_cases hq : v < q
            · rw [fund_diag hf hd hq]
              exact Dim_set hs i (hrec _ (Dim_iter hrec ht)) _ (Dim_Z d)
            · rw [fund_nondiag hf hd hq]
              exact Dim_set hs i (hrec t ht) _ (Dim_Z d)
      · rw [fund_tail v ha]
        exact Dim_P hs.length hs.coord (ih a (multi.T.size_lt_P_right v a) t hs.tail ht)

/-- The label of an `Omega` domain is a vector of the term. -/
theorem Dim_domF_Omega {d : Nat} : ∀ {s : multi.T} {q : V multi.T}, Dim d s →
    domF s = .Omega q → q.length = d ∧ ∀ i, Dim d (V.get0 q i)
  | .Z, q, _, h => by rw [domF_Z] at h; cases h
  | .P v a, q, hs, h => by
    by_cases ha : a = .Z
    · subst ha
      rcases hf : V.fnz v with _ | i
      · rw [domF_none hf] at h; cases h
      · cases hd : domF (V.get0 v i) with
        | zero => rw [domF_zero hf hd] at h; cases h
        | omega => rw [domF_omega hf hd] at h; cases h
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hd] at h; cases h
          | succ k =>
            rw [domF_one_succ hf hd] at h
            cases h
            exact ⟨hs.length, hs.coord⟩
        | Omega r =>
          by_cases hr : v < r
          · rw [domF_diag hf hd hr] at h; cases h
          · rw [domF_nondiag hf hd hr] at h
            cases h
            exact Dim_domF_Omega (hs.coord i) hd
    · rw [domF_tail v ha] at h
      exact Dim_domF_Omega hs.tail h
termination_by s => s.size
decreasing_by
  · exact multi.T.size_get0_lt_P _ _ _
  · exact multi.T.size_lt_P_right _ _

theorem DOT.dim {lam : Nat} {s : multi.T} (h : DOT lam s) : Dim lam s := by
  induction h with
  | base_0 n => exact Dim_towerD 0 n
  | base_succ lam n =>
    apply Dim_vOf _ _ (Dim_Z _)
    intro j _
    split
    · exact Dim_towerD _ _
    · exact Dim_Z _
  | step lam s _ n ih => exact Dim_fund s _ ih (Dim_ofNatD lam n)

/-! ### Moving between dimensions -/

theorem norm_padTo (d : Nat) (s : multi.T) : multi.T.norm (padTo d s) = multi.T.norm s :=
  (code_eq_iff _ _).1 (code_padTo d s)

theorem tWidth_le_of_Dim {d : Nat} : ∀ {s : multi.T}, Dim d s → tWidth s ≤ d
  | .Z, _ => by rw [tWidth]; exact Nat.zero_le _
  | .P v a, h => by
    rw [tWidth]
    refine Nat.max_le.2 ⟨Nat.le_trans (multi.V.length_trim_le v) (Nat.le_of_eq h.length),
      Nat.max_le.2 ⟨vWidth_le v d (fun i => tWidth_le_of_Dim (h.coord i)),
        tWidth_le_of_Dim h.tail⟩⟩
termination_by s => s.size
decreasing_by
  · exact multi.T.size_get0_lt_P _ _ _
  · exact multi.T.size_lt_P_right _ _

theorem tWidth_norm_le : ∀ s : multi.T, tWidth (multi.T.norm s) ≤ tWidth s
  | .Z => by rw [multi.T.norm]; exact Nat.le_refl _
  | .P v a => by
    rw [multi.T.norm_P, tWidth, tWidth]
    have hn : V.trim (V.norm v) = V.norm v := by rw [multi.V.norm, multi.V.trim_trim]
    have hl : (V.norm v).length = (V.trim v).length := by
      rw [multi.V.norm_eq, multi.V.length_mapNorm]
    rw [hn, hl]
    refine Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.max_le.2 ⟨?_, ?_⟩⟩
    · refine Nat.le_trans ?_ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      apply vWidth_le
      intro i
      rw [multi.V.get0_norm]
      exact Nat.le_trans (tWidth_norm_le (V.get0 v i)) (vWidth_get0 v i)
    · exact Nat.le_trans (tWidth_norm_le a)
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
termination_by s => s.size
decreasing_by
  · exact multi.T.size_get0_lt_P _ _ _
  · exact multi.T.size_lt_P_right _ _

theorem Dim_padTo {d : Nat} {s : multi.T} (h : tWidth s ≤ d) : Dim d (padTo d s) :=
  padN_Dim d (multi.T.norm s) (multi.T.norm_norm s) (Nat.le_trans (tWidth_norm_le s) h)

theorem Dim_padTo_of {e d : Nat} {s : multi.T} (hs : Dim e s) (h : e ≤ d) : Dim d (padTo d s) :=
  Dim_padTo (Nat.le_trans (tWidth_le_of_Dim hs) h)

theorem eq_of_norm_eq {d : Nat} {s t : multi.T} (hs : Dim d s) (ht : Dim d t)
    (h : multi.T.norm s = multi.T.norm t) : s = t :=
  eq_of_code_eq hs ht ((code_eq_iff s t).2 h)

theorem padTo_padTo (d e : Nat) (s : multi.T) : padTo d (padTo e s) = padTo d s :=
  padTo_congr (code_padTo e s)

theorem padTo_Z (d : Nat) : padTo d .Z = .Z := by
  rw [padTo, multi.T.norm, padN_Z]

theorem padTo_ofNatD (d e n : Nat) : padTo d (ofNatD e n) = ofNatD d n := by
  rw [← padTo_of_Dim (Dim_ofNatD d n)]
  apply padTo_congr
  rw [FiniteCorrespondence.code_ofNatD, FiniteCorrespondence.code_ofNatD]

theorem norm_ofNatD (d n : Nat) : multi.T.norm (ofNatD d n) = multi.T.ofNat n := by
  rw [← multi.T.ofNat_norm n]
  apply (code_eq_iff _ _).1
  rw [FiniteCorrespondence.code_ofNatD, FiniteCorrespondence.code_ofNat]

/-- `fund` commutes with padding to a larger dimension. -/
theorem fund_padTo {e d : Nat} {s t : multi.T} (hs : Dim e s) (ht : Dim e t) (hed : e ≤ d) :
    padTo d (T.fund s t) = T.fund (padTo d s) (padTo d t) := by
  apply eq_of_norm_eq (d := d) (Dim_padTo_of (Dim_fund s t hs ht) hed)
    (Dim_fund _ _ (Dim_padTo_of hs hed) (Dim_padTo_of ht hed))
  rw [norm_padTo]
  exact T.fund_congr _ _ _ _ (norm_padTo d s).symm (norm_padTo d t).symm

theorem code_P_congr {v w : V multi.T} {a b : multi.T}
    (hv : ∀ i, code (V.get0 v i) = code (V.get0 w i)) (hab : code a = code b) :
    code (multi.T.P v a) = code (multi.T.P w b) := by
  apply (code_eq_iff _ _).2
  rw [multi.T.norm_P, multi.T.norm_P, (code_eq_iff a b).1 hab]
  congr 1
  exact multi.V.norm_ext (fun i => (code_eq_iff _ _).1 (hv i))

end kumakuma.OTQuotient

namespace kumakuma.FirstLimit

open multi OTQuotient FiniteCorrespondence

def omegaSource : multi.T := .P (.snoc (ofNatD 1 1) .emp) .Z

theorem omegaSource_isOT : DOT 1 omegaSource := by
  have h := DOT.base_succ 0 1
  have he : baseD 0 1 = omegaSource := by
    rw [baseD, omegaSource]
    show multi.T.P (.snoc (if 0 = 0 then towerD 1 1 else .Z) .emp) .Z = _
    rw [ite_eq_left rfl, towerD]
    rfl
  rwa [he] at h

private theorem one_mul_nat : ∀ n : Nat, multi.T.mul (ofNatD 1 1) (ofNatD 1 n) = ofNatD 1 n
  | 0 => rfl
  | n + 1 => by
    show ofNatD 1 1 + multi.T.mul (ofNatD 1 1) (ofNatD 1 n) = ofNatD 1 (n + 1)
    rw [one_mul_nat n]
    rfl

theorem omegaSource_fund (n : Nat) : T.fund omegaSource (ofNatD 1 n) = ofNatD 1 n := by
  have hf : V.fnz (.snoc (ofNatD 1 1) .emp : V multi.T) = some 0 :=
    fnz_eq_some (by intro h; cases h) (fun j hj => absurd hj (Nat.not_lt_zero j))
  have hd : domF (V.get0 (.snoc (ofNatD 1 1) .emp : V multi.T) 0) = .one := by
    show domF (ofNatD 1 1) = .one
    exact domF_none (fnz_zeros 1)
  rw [omegaSource, fund_one_zero hf hd]
  have h1 : T.fund (V.get0 (.snoc (ofNatD 1 1) .emp : V multi.T) 0) .Z = .Z := by
    show T.fund (ofNatD 1 1) .Z = .Z
    exact fund_none (fnz_zeros 1) _
  rw [h1]
  exact one_mul_nat n

theorem ofNat_isOT_one (n : Nat) : DOT 1 (ofNatD 1 n) := by
  rw [← omegaSource_fund n]
  exact DOT.step 1 omegaSource omegaSource_isOT n

end kumakuma.FirstLimit

namespace kumakuma.CountableSource

open multi OTQuotient

/-- The vector of length `k + 1` with `a` at the lowest coordinate. -/
def lowVec (k : Nat) (a : multi.T) : V multi.T := vOf (fun i => if i = 0 then a else .Z) (k + 1)

theorem lowVec_length (k : Nat) (a : multi.T) : (lowVec k a).length = k + 1 := vOf_length _ _

theorem get0_lowVec (k : Nat) (a : multi.T) (i : Nat) :
    V.get0 (lowVec k a) i = if i = 0 then a else .Z := by
  rw [lowVec, get0_vOf]
  by_cases hi : i = 0
  · rw [ite_eq_left (by omega), ite_eq_left hi]
  · rw [ite_eq_right hi]; split <;> rfl

theorem lowVec_zero (a : multi.T) : lowVec 0 a = .snoc a .emp := by
  show V.snoc (if 0 = 0 then a else .Z) .emp = _
  rw [ite_eq_left rfl]

theorem lowVec_succ (k : Nat) (a : multi.T) : lowVec (k + 1) a = .snoc .Z (lowVec k a) := by
  show V.snoc (if k + 1 = 0 then a else .Z) (lowVec k a) = _
  rw [ite_eq_right (Nat.succ_ne_zero k)]

theorem lowVec_set_zero (k : Nat) (a b : multi.T) : V.set (lowVec k a) 0 b = lowVec k b := by
  apply V.eq_of_get0 _ _ (by rw [V.length_set, lowVec_length, lowVec_length])
  intro i
  rw [V.get0_set _ 0 b i (by rw [lowVec_length]; omega), get0_lowVec, get0_lowVec]
  split <;> rfl

theorem fnz_lowVec {k : Nat} {a : multi.T} (ha : a ≠ .Z) : V.fnz (lowVec k a) = some 0 :=
  fnz_eq_some (by rw [get0_lowVec, ite_eq_left rfl]; exact ha) (fun j hj => absurd hj (Nat.not_lt_zero j))

theorem fnz_lowVec_Z (k : Nat) : V.fnz (lowVec k .Z) = none :=
  fnz_eq_none (fun j => by rw [get0_lowVec]; split <;> rfl)

theorem lowVec_Z (k : Nat) : lowVec k .Z = zeros (k + 1) :=
  vOf_ext (fun j _ => by split <;> rfl)

theorem Dim_lowVec {k : Nat} {a b : multi.T} (ha : Dim (k + 1) a) (hb : Dim (k + 1) b) :
    Dim (k + 1) (.P (lowVec k a) b) :=
  Dim_vOf (fun j _ => by split; exact ha; exact Dim_Z _) b hb

inductive Outer (k : Nat) : multi.T → Prop
  | zero : Outer k .Z
  | cons (a b : multi.T) : Outer k b → Outer k (.P (lowVec k a) b)

theorem outer_oplus {k : Nat} {s t : multi.T} (hs : Outer k s) (ht : Outer k t) :
    Outer k (s + t) := by
  induction hs with
  | zero => exact ht
  | cons a b _ ih => exact Outer.cons a (b + t) ih

theorem outer_mul {k : Nat} {s : multi.T} (hs : Outer k s) : ∀ t : multi.T, Outer k (multi.T.mul s t)
  | .Z => Outer.zero
  | .P _ b => outer_oplus hs (outer_mul hs b)

theorem fund_lowVec_cases {k : Nat} (a t : multi.T) :
    T.fund (.P (lowVec k a) .Z) t = .Z ∨
      T.fund (.P (lowVec k a) .Z) t = multi.T.mul (.P (lowVec k (T.fund a .Z)) .Z) t ∨
      ∃ x, T.fund (.P (lowVec k a) .Z) t = .P (lowVec k (T.fund a x)) .Z := by
  by_cases ha : a = .Z
  · subst ha; exact Or.inl (fund_none (fnz_lowVec_Z k) t)
  · have hf := fnz_lowVec (k := k) ha
    have hg : V.get0 (lowVec k a) 0 = a := by rw [get0_lowVec, ite_eq_left rfl]
    cases hd : domF a with
    | zero =>
      refine Or.inr (Or.inr ⟨t, ?_⟩)
      rw [fund_zero hf (by rw [hg]; exact hd), hg, lowVec_set_zero]
    | one =>
      refine Or.inr (Or.inl ?_)
      rw [fund_one_zero hf (by rw [hg]; exact hd), hg, lowVec_set_zero]
    | omega =>
      refine Or.inr (Or.inr ⟨t, ?_⟩)
      rw [fund_omega hf (by rw [hg]; exact hd), hg, lowVec_set_zero]
    | Omega q =>
      refine Or.inr (Or.inr ?_)
      by_cases hq : lowVec k a < q
      · exact ⟨_, by rw [fund_diag hf (by rw [hg]; exact hd) hq, hg, lowVec_set_zero]⟩
      · exact ⟨t, by rw [fund_nondiag hf (by rw [hg]; exact hd) hq, hg, lowVec_set_zero]⟩

theorem fund_outer {k : Nat} {s : multi.T} (hs : Outer k s) (t : multi.T) :
    Outer k (T.fund s t) := by
  induction hs with
  | zero => rw [fund_Z]; exact Outer.zero
  | cons a b hb ih =>
    by_cases hz : b = .Z
    · subst hz
      rcases fund_lowVec_cases (k := k) a t with h | h | ⟨x, h⟩ <;> rw [h]
      · exact Outer.zero
      · exact outer_mul (Outer.cons _ _ Outer.zero) t
      · exact Outer.cons _ _ Outer.zero
    · rw [fund_tail _ hz]
      exact Outer.cons a _ ih

theorem isOT_outer_aux {lam : Nat} {s : multi.T} (h : DOT lam s) :
    ∀ k, lam = k + 1 → Outer k s := by
  induction h with
  | base_0 n => intro k e; omega
  | base_succ lam n =>
    intro k e
    obtain rfl : lam = k := by omega
    exact Outer.cons _ _ Outer.zero
  | step lam s _ n ih =>
    intro k e
    exact fund_outer (ih k e) _

theorem isOT_outer {k : Nat} {s : multi.T} (h : DOT (k + 1) s) : Outer k s :=
  isOT_outer_aux h k rfl

theorem trim_codes_lowVec (k : Nat) (a : multi.T) :
    trim (codes (lowVec k a)) = trim [code a] := by
  induction k with
  | zero => rw [lowVec_zero, codes_snoc, codes_emp]; rfl
  | succ k ih => rw [lowVec_succ, codes_snoc, code_Z, trim_append_zero, ih]

def OuterForm : Code → Prop
  | .zero => True
  | .p args b => args.length ≤ 1 ∧ OuterForm b

theorem outer_code {k : Nat} {s : multi.T} (hs : Outer k s) : OuterForm (code s) := by
  induction hs with
  | zero => rw [code_Z, OuterForm]; trivial
  | cons a b _ ih =>
    rw [code_P, trim_codes_lowVec, OuterForm]
    refine ⟨?_, ih⟩
    cases hc : code a with
    | zero => simp [trim, Code.isZero]
    | p xs c => simp [trim, Code.isZero]

theorem natCode_outer (n : Nat) : OuterForm (FiniteCorrespondence.natCode n) := by
  induction n with
  | zero => rw [FiniteCorrespondence.natCode, OuterForm]; trivial
  | succ n ih =>
    rw [FiniteCorrespondence.natCode, OuterForm]
    exact ⟨Nat.zero_le _, ih⟩

theorem allOT_outer (s : AllOT) : OuterForm (key s) := by
  obtain ⟨lam, s, hs⟩ := s
  cases lam with
  | zero =>
    obtain ⟨n, rfl⟩ := FiniteCorrespondence.zero_dimension_exhaustive s hs.dim
    show OuterForm (code (ofNatD 0 n))
    rw [FiniteCorrespondence.code_ofNatD]
    exact natCode_outer n
  | succ k => exact outer_code (isOT_outer hs)

theorem representative_outer (q : Classes) : OuterForm (representative q) := by
  induction q using Quotient.inductionOn with
  | h s => exact allOT_outer s

end kumakuma.CountableSource

namespace kumakuma.CountableTarget

open OCF.Jaeger

theorem lt_zero (t : Term) : Term.lt t .zero = false := by
  cases t <;> simp [Term.lt]

theorem inacc_not_below_omega (n : Nat) (a : Term) :
    Term.lt (.inacc n a) Term.bigOmega = false := by
  simp [Term.bigOmega, Term.lt, lt_zero]

theorem regular_not_below_omega {u : Term} (hu : Term.isRT u = true) :
    Term.lt u Term.bigOmega = false := by
  cases u with
  | zero | add | psi => cases hu
  | inacc n a => exact inacc_not_below_omega n a

theorem psi_below_omega_iff {u b : Term} (hu : Term.isRT u = true) :
    Term.lt (.psi u b) Term.bigOmega = true ↔ u = Term.bigOmega := by
  cases u with
  | zero | add | psi => cases hu
  | inacc n a => simp [Term.bigOmega, Term.lt, Term.fT, lt_zero]

theorem inacc_not_below_psiOmega (n : Nat) (a b : Term) :
    Term.lt (.inacc n a) (.psi Term.bigOmega b) = false := by
  simp only [Term.lt]
  simp [Term.bigOmega, Term.fT, Term.lt, lt_zero]

theorem psi_lt_psiOmega_subscript {u a b : Term} (hu : Term.isRT u = true)
    (h : Term.lt (.psi u a) (.psi Term.bigOmega b) = true) : u = Term.bigOmega := by
  rw [Term.lt] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · have hn := regular_not_below_omega hu
    rw [hn] at h
    cases h.1
  · exact h.1
  · exact (psi_below_omega_iff hu).mp h.2

theorem principal_below_omega {a : Term} (hp : Term.isPrin a = true)
    (hw : Term.wf a = true) (hlt : Term.lt a Term.bigOmega = true) :
    ∃ b, a = .psi Term.bigOmega b := by
  cases a with
  | zero | add => cases hp
  | inacc n b => rw [inacc_not_below_omega] at hlt; cases hlt
  | psi u b =>
    have hu := (Term.wf_psi_iff u b).mp hw
    exact ⟨b, congrArg (fun u => Term.psi u b) ((psi_below_omega_iff hu.1).mp hlt)⟩

theorem principal_le_psiOmega_below {a b : Term} (hp : Term.isPrin a = true)
    (hw : Term.wf a = true) (h : Term.le a (.psi Term.bigOmega b) = true) :
    Term.lt a Term.bigOmega = true := by
  simp only [Term.le, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | h
  · simp [Term.bigOmega, Term.lt, Term.fT]
  · cases a with
    | zero | add => cases hp
    | inacc n c => rw [inacc_not_below_psiOmega] at h; cases h
    | psi u c =>
      have hu := (Term.wf_psi_iff u c).mp hw
      exact (psi_below_omega_iff hu.1).mpr (psi_lt_psiOmega_subscript hu.1 h)

theorem head_properties {t : Term} (hw : Term.wf t = true) (hne : t ≠ .zero) :
    Term.isPrin (Term.head t) = true ∧ Term.wf (Term.head t) = true := by
  cases t with
  | zero => exact False.elim (hne rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    exact ⟨h.1, h.2.1⟩
  | inacc n a => exact ⟨rfl, hw⟩
  | psi u a => exact ⟨rfl, hw⟩

theorem head_below_omega (t : Term) :
    Term.lt (Term.head t) Term.bigOmega = Term.lt t Term.bigOmega := by
  cases t <;> simp [Term.head, Term.bigOmega, Term.lt]

inductive Outer : Term → Prop
  | zero : Outer .zero
  | atom (b : Term) : Outer (.psi Term.bigOmega b)
  | cons (a b : Term) : Outer b → Outer (.add (.psi Term.bigOmega a) b)

theorem wf_below_outer {t : Term} (hw : Term.wf t = true)
    (hlt : Term.lt t Term.bigOmega = true) : Outer t := by
  induction t with
  | zero => exact Outer.zero
  | inacc n a _ => rw [inacc_not_below_omega] at hlt; cases hlt
  | psi u a _ _ =>
    have hu := (Term.wf_psi_iff u a).mp hw
    have he := (psi_below_omega_iff hu.1).mp hlt
    rw [he]
    exact Outer.atom a
  | add a b _ ihb =>
    have h := (Term.wf_add_iff a b).mp hw
    have ha : Term.lt a Term.bigOmega = true := by simpa only [Term.bigOmega, Term.lt] using hlt
    obtain ⟨c, rfl⟩ := principal_below_omega h.1 h.2.1 ha
    have hb := head_properties h.2.2.1 h.2.2.2.1
    have hblt := principal_le_psiOmega_below hb.1 hb.2 h.2.2.2.2
    rw [head_below_omega] at hblt
    exact Outer.cons c b (ihb h.2.2.1 hblt)

theorem target_outer (t : kumakuma.WFBelowOmega) : Outer t.val :=
  wf_below_outer t.property.1 t.property.2

end kumakuma.CountableTarget

namespace kumakuma.TargetArithmetic

open OCF.Jaeger BinaryTranslation

theorem lt_self (t : Term) : Term.lt t t = false := by
  induction t with
  | zero => simp [Term.lt]
  | add a b iha ihb => simp [Term.lt, ihb]
  | inacc n b ih => simp [Term.lt, ih]
  | psi u b ihu ihb => simp [Term.lt, ihu, ihb]

theorem zero_lt_iff (t : Term) : Term.lt .zero t = true ↔ t ≠ .zero := by
  cases t <;> simp [Term.lt]

theorem one_le_principal {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.le Term.one t = true := by
  cases t with
  | zero | add => cases hp
  | inacc n b =>
    cases n <;> cases b <;> simp [Term.le, Term.one, Term.bigOmega, Term.lt, Term.fT]
  | psi u b =>
    have hu := ((Term.wf_psi_iff u b).mp hw).1
    cases u with
    | zero | add | psi => cases hu
    | inacc n c =>
      cases n <;> cases c <;> cases b <;>
        simp [Term.le, Term.one, Term.bigOmega, Term.lt, Term.fT, CountableTarget.lt_zero]

theorem principal_not_lt_one {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.lt t Term.one = false := by
  cases t with
  | zero | add => cases hp
  | inacc n b => exact CountableTarget.inacc_not_below_psiOmega n b .zero
  | psi u b =>
    have hu := ((Term.wf_psi_iff u b).mp hw).1
    by_cases he : u = Term.bigOmega
    · rw [he, Term.one, Unary.psi_omega_lt, CountableTarget.lt_zero]
    · have hn : Term.lt (.psi u b) Term.bigOmega = false := by
        cases h : Term.lt (.psi u b) Term.bigOmega with
        | false => rfl
        | true => exact False.elim (he ((CountableTarget.psi_below_omega_iff hu).mp h))
      rw [Term.one, Term.lt]
      simp [CountableTarget.regular_not_below_omega hu, he, hn]

theorem principal_le_one_iff {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.le t Term.one = true ↔ t = Term.one := by
  simp only [Term.le, principal_not_lt_one hp hw, Bool.or_false, decide_eq_true_eq]

theorem one_lt_principal_iff {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.lt Term.one t = true ↔ t ≠ Term.one := by
  constructor
  · intro h he
    rw [he, lt_self] at h
    cases h
  · intro he
    have h := one_le_principal hp hw
    simp only [Term.le, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact False.elim (he h.symm)
    · exact h

theorem dropOne_wf {t : Term} (hw : Term.wf t = true) : Term.wf (dropOne t) = true := by
  cases t with
  | zero => rfl
  | add a b =>
    simp only [dropOne]
    split
    · exact ((Term.wf_add_iff a b).mp hw).2.2.1
    · exact hw
  | inacc n b => exact hw
  | psi u b =>
    simp only [dropOne]
    split
    · rfl
    · exact hw

theorem succTerm_ne_zero (t : Term) : succTerm t ≠ .zero := by
  cases t <;> simp [succTerm, Term.one]

theorem head_succTerm {t : Term} (hne : t ≠ .zero) :
    Term.head (succTerm t) = Term.head t := by
  cases t with
  | zero => exact False.elim (hne rfl)
  | add | inacc | psi => rfl

theorem succTerm_wf {t : Term} (hw : Term.wf t = true) : Term.wf (succTerm t) = true := by
  induction t with
  | zero => exact Term.wf_one
  | add a b _ ihb =>
    have h := (Term.wf_add_iff a b).mp hw
    apply (Term.wf_add_iff _ _).mpr
    exact ⟨h.1, h.2.1, ihb h.2.2.1, succTerm_ne_zero b,
      by simpa only [head_succTerm h.2.2.2.1] using h.2.2.2.2⟩
  | inacc n b _ =>
    exact (Term.wf_add_iff _ _).mpr
      ⟨rfl, hw, Term.wf_one, by decide +kernel, one_le_principal rfl hw⟩
  | psi u b _ _ =>
    exact (Term.wf_add_iff _ _).mpr
      ⟨rfl, hw, Term.wf_one, by decide +kernel, one_le_principal rfl hw⟩

theorem succTerm_isSucc (t : Term) : Term.isSucc (succTerm t) = true := by
  induction t with
  | zero => decide +kernel
  | add a b _ ihb => exact ihb
  | inacc | psi => simp [succTerm, Term.isSucc, Term.one]

theorem succTerm_ne_one {t : Term} (hne : t ≠ .zero) : succTerm t ≠ Term.one := by
  cases t with
  | zero => exact False.elim (hne rfl)
  | add | inacc | psi => simp [succTerm, Term.one]

theorem predT_succTerm {t : Term} (hw : Term.wf t = true) : Term.predT (succTerm t) = t := by
  induction t with
  | zero => rfl
  | add a b _ ihb =>
    have h := (Term.wf_add_iff a b).mp hw
    simp only [succTerm, Term.predT, succTerm_ne_one h.2.2.2.1, ↓reduceIte, ihb h.2.2.1]
  | inacc | psi => simp [succTerm, Term.predT]

theorem succTerm_injective {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (h : succTerm s = succTerm t) : s = t := by
  have hp := congrArg Term.predT h
  simpa only [predT_succTerm hs, predT_succTerm ht] using hp

open FiniteCorrespondence

theorem head_one_nat {t : Term} (hw : Term.wf t = true) (hh : Term.head t = Term.one) :
    ∃ n, t = natTerm (n + 1) := by
  induction t with
  | zero => cases hh
  | add a b _ ihb =>
    have ha : a = Term.one := hh
    have h := (Term.wf_add_iff a b).mp hw
    have hb := CountableTarget.head_properties h.2.2.1 h.2.2.2.1
    have hhead := (principal_le_one_iff hb.1 hb.2).mp (ha ▸ h.2.2.2.2)
    obtain ⟨n, hn⟩ := ihb h.2.2.1 hhead
    exact ⟨n + 1, by simp only [natTerm, ha, hn]⟩
  | inacc => cases hh
  | psi u b _ _ => exact ⟨0, hh⟩

theorem dropOne_nat (n : Nat) : dropOne (natTerm (n + 1)) = natTerm n := by
  cases n <;> simp [natTerm, dropOne, Term.one]

theorem dropOne_of_head_ne {t : Term} (hh : Term.head t ≠ Term.one) : dropOne t = t := by
  cases t with
  | zero | inacc => rfl
  | add | psi => simp_all [Term.head, dropOne]

theorem nat_lt_of_head_ne {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero)
    (hh : Term.head t ≠ Term.one) (n : Nat) : Term.lt (natTerm n) t = true := by
  have hp := CountableTarget.head_properties hw hz
  have ho := (one_lt_principal_iff hp.1 hp.2).mpr hh
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have hae : Term.one ≠ a := fun h => hh h.symm
    change Term.lt Term.one a = true at ho
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n =>
      cases n with
      | zero =>
        have hae' : Term.psi Term.bigOmega .zero ≠ a := hae
        rw [natTerm, Term.one, Term.lt, ite_eq_right hae']; exact ho
      | succ n =>
        rw [natTerm, Term.lt, ite_eq_right hae]; exact ho
  | inacc k b =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simpa only [natTerm, Term.head, Term.lt] using ho
  | psi u b =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simpa only [natTerm, Term.head, Term.lt] using ho

theorem not_lt_nat_of_head_ne {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero)
    (hh : Term.head t ≠ Term.one) (n : Nat) : Term.lt t (natTerm n) = false := by
  have hp := CountableTarget.head_properties hw hz
  have ho := principal_not_lt_one hp.1 hp.2
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    change a ≠ Term.one at hh
    change Term.lt a Term.one = false at ho
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n =>
      cases n with
      | zero => rw [natTerm, Term.one, Term.lt]; exact ho
      | succ n =>
        rw [natTerm, Term.lt, ite_eq_right hh]; exact ho
  | inacc k b =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simpa [natTerm, Term.one, Term.head, Term.lt] using ho
  | psi u b =>
    change Term.psi u b ≠ Term.one at hh
    change Term.lt (.psi u b) Term.one = false at ho
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n =>
      cases n with
      | zero => exact ho
      | succ n =>
        rw [natTerm, Term.lt, ite_eq_right hh]; exact ho

theorem dropOne_order {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (hsz : s ≠ .zero) (htz : t ≠ .zero) :
    Term.lt (dropOne s) (dropOne t) = Term.lt s t := by
  by_cases hsh : Term.head s = Term.one <;> by_cases hth : Term.head t = Term.one
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    obtain ⟨n, rfl⟩ := head_one_nat ht hth
    apply Bool.eq_iff_iff.mpr
    simp only [dropOne_nat, natTerm_lt, Nat.add_lt_add_iff_right]
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    rw [dropOne_nat, dropOne_of_head_ne hth,
      nat_lt_of_head_ne ht htz hth, nat_lt_of_head_ne ht htz hth]
  · obtain ⟨n, rfl⟩ := head_one_nat ht hth
    rw [dropOne_nat, dropOne_of_head_ne hsh,
      not_lt_nat_of_head_ne hs hsz hsh, not_lt_nat_of_head_ne hs hsz hsh]
  · rw [dropOne_of_head_ne hsh, dropOne_of_head_ne hth]

theorem dropOne_injective {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (hsz : s ≠ .zero) (htz : t ≠ .zero) (he : dropOne s = dropOne t) : s = t := by
  by_cases hsh : Term.head s = Term.one <;> by_cases hth : Term.head t = Term.one
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    obtain ⟨n, rfl⟩ := head_one_nat ht hth
    rw [dropOne_nat, dropOne_nat] at he
    exact congrArg (fun n => natTerm (n + 1)) (natTerm_injective he)
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    rw [dropOne_nat, dropOne_of_head_ne hth] at he
    have hlt := nat_lt_of_head_ne ht htz hth m
    rw [he, lt_self] at hlt
    cases hlt
  · obtain ⟨n, rfl⟩ := head_one_nat ht hth
    rw [dropOne_nat, dropOne_of_head_ne hsh] at he
    have hlt := nat_lt_of_head_ne hs hsz hsh n
    rw [← he, lt_self] at hlt
    cases hlt
  · simpa only [dropOne_of_head_ne hsh, dropOne_of_head_ne hth] using he

theorem one_lt_add {a b : Term} (hp : Term.isPrin a = true) (hw : Term.wf a = true) :
    Term.lt Term.one (.add a b) = true := by
  have h := one_le_principal hp hw
  rw [Term.le] at h
  rw [Term.one, Term.lt]
  split
  · rfl
  · rename_i he
    have he' : Term.one ≠ a := he
    change Term.lt Term.one a = true
    simpa only [he', decide_false, Bool.false_or] using h

theorem one_lt_succTerm {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero) :
    Term.lt Term.one (succTerm t) = true := by
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    exact one_lt_add h.1 h.2.1
  | inacc | psi => exact one_lt_add rfl hw

theorem succTerm_not_lt_one {t : Term} (hw : Term.wf t = true) :
    Term.lt (succTerm t) Term.one = false := by
  cases t with
  | zero => exact lt_self Term.one
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    rw [succTerm, Term.one, Term.lt]
    exact principal_not_lt_one h.1 h.2.1
  | inacc | psi =>
    rw [succTerm, Term.one, Term.lt]
    exact principal_not_lt_one rfl hw

theorem add_one_order (s t : Term) :
    Term.lt (.add s Term.one) (.add t Term.one) = Term.lt s t := by
  rw [Term.lt]
  split
  · rename_i he
    subst t
    rw [lt_self, lt_self]
  · rfl

theorem succTerm_order {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true) :
    Term.lt (succTerm s) (succTerm t) = Term.lt s t := by
  induction s generalizing t with
  | zero =>
    cases t with
    | zero => simp only [succTerm, lt_self]
    | add | inacc | psi =>
      rw [show succTerm .zero = Term.one from rfl,
        one_lt_succTerm ht (by intro h; cases h)]
      simp [Term.lt]
  | add a b _ ihb =>
    have hsb := (Term.wf_add_iff a b).mp hs
    cases t with
    | zero => rw [succTerm, succTerm_not_lt_one hs, CountableTarget.lt_zero]
    | add c d =>
      have htd := (Term.wf_add_iff c d).mp ht
      simp only [succTerm, Term.lt]
      split
      · exact ihb hsb.2.2.1 htd.2.2.1
      · rfl
    | inacc n c =>
      rw [succTerm, succTerm, Term.lt, Term.lt]
      split
      · rename_i he
        rw [he, lt_self, succTerm_not_lt_one hsb.2.2.1]
      · rfl
    | psi u c =>
      rw [succTerm, succTerm, Term.lt, Term.lt]
      split
      · rename_i he
        rw [he, lt_self, succTerm_not_lt_one hsb.2.2.1]
      · rfl
  | inacc n a _ =>
    cases t with
    | zero => rw [succTerm, succTerm_not_lt_one hs, CountableTarget.lt_zero]
    | add c d =>
      have htd := (Term.wf_add_iff c d).mp ht
      simp only [succTerm, Term.lt]
      split
      · exact one_lt_succTerm htd.2.2.1 htd.2.2.2.1
      · rfl
    | inacc | psi => exact add_one_order _ _
  | psi u a _ _ =>
    cases t with
    | zero => rw [succTerm, succTerm_not_lt_one hs, CountableTarget.lt_zero]
    | add c d =>
      have htd := (Term.wf_add_iff c d).mp ht
      simp only [succTerm, Term.lt]
      split
      · exact one_lt_succTerm htd.2.2.1 htd.2.2.2.1
      · rfl
    | inacc | psi => exact add_one_order _ _

theorem one_le_of_ne_zero {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero) :
    Term.le Term.one t = true := by
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    rw [Term.le, one_lt_add h.1 h.2.1]
    simp
  | inacc | psi => exact one_le_principal rfl hw

theorem le_add_same (a b c : Term) :
    Term.le (.add a b) (.add a c) = Term.le b c := by
  simp [Term.le, Term.lt]

theorem not_lt_one {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero) :
    Term.lt t Term.one = false := by
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    rw [Term.one, Term.lt]
    exact principal_not_lt_one h.1 h.2.1
  | inacc | psi => exact principal_not_lt_one rfl hw

theorem succTerm_le_eq_lt {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true) :
    Term.le (succTerm s) t = Term.lt s t := by
  induction s generalizing t with
  | zero =>
    cases t with
    | zero => decide +kernel
    | add | inacc | psi =>
      rw [show succTerm .zero = Term.one from rfl,
        one_le_of_ne_zero ht (by intro h; cases h)]
      simp [Term.lt]
  | add a b _ ihb =>
    have hb := (Term.wf_add_iff a b).mp hs
    cases t with
    | zero => simp [succTerm, Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : a = c
      · subst c
        rw [succTerm, le_add_same, Term.lt]
        simpa only [↓reduceIte] using ihb hb.2.2.1 hd.2.2.1
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]
  | inacc n a _ =>
    cases t with
    | zero => simp [succTerm, Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : Term.inacc n a = c
      · subst c
        rw [succTerm, le_add_same, Term.lt]
        simp only [↓reduceIte, one_le_of_ne_zero hd.2.2.1 hd.2.2.2.1]
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]
  | psi u a _ _ =>
    cases t with
    | zero => simp [succTerm, Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : Term.psi u a = c
      · subst c
        rw [succTerm, le_add_same, Term.lt]
        simp only [↓reduceIte, one_le_of_ne_zero hd.2.2.1 hd.2.2.2.1]
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]

theorem lt_succTerm_eq_le {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true) :
    Term.lt s (succTerm t) = Term.le s t := by
  induction s generalizing t with
  | zero =>
    cases t <;> simp [succTerm, Term.le, Term.lt, Term.one]
  | add a b _ ihb =>
    have hb := (Term.wf_add_iff a b).mp hs
    cases t with
    | zero =>
      rw [show succTerm .zero = Term.one from rfl, not_lt_one hs (by intro h; cases h)]
      simp [Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : a = c
      · subst c
        simp only [succTerm, Term.lt, ↓reduceIte, Term.le, Term.add.injEq, true_and]
        exact ihb hb.2.2.1 hd.2.2.1
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc n c =>
      by_cases he : a = .inacc n c
      · subst a
        rw [succTerm, Term.lt]
        simp only [↓reduceIte, not_lt_one hb.2.2.1 hb.2.2.2.1, Term.le, reduceCtorEq,
          decide_false, Bool.false_or, Term.lt, lt_self]
      · simp [succTerm, Term.le, Term.lt, he]
    | psi u c =>
      by_cases he : a = .psi u c
      · subst a
        rw [succTerm, Term.lt]
        simp only [↓reduceIte, not_lt_one hb.2.2.1 hb.2.2.2.1, Term.le, reduceCtorEq,
          decide_false, Bool.false_or, Term.lt, lt_self]
      · simp [succTerm, Term.le, Term.lt, he]
  | inacc n a _ =>
    cases t with
    | zero =>
      rw [show succTerm .zero = Term.one from rfl, principal_not_lt_one rfl hs]
      simp [Term.le, Term.lt]
    | add c d => simp [succTerm, Term.le, Term.lt]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]

  | psi u a _ _ =>
    cases t with
    | zero =>
      rw [show succTerm .zero = Term.one from rfl, principal_not_lt_one rfl hs]
      simp [Term.le, Term.lt]
    | add c d => simp [succTerm, Term.le, Term.lt]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]

theorem dropOne_lt_of_lt {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (hlt : Term.lt s t = true) : Term.lt (dropOne s) t = true := by
  by_cases hs0 : s = .zero
  · simpa only [hs0, dropOne] using hlt
  · have ht0 : t ≠ .zero := by
      intro he
      rw [he, CountableTarget.lt_zero] at hlt
      cases hlt
    by_cases hsh : Term.head s = Term.one
    · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
      rw [dropOne_nat]
      by_cases hth : Term.head t = Term.one
      · obtain ⟨n, rfl⟩ := head_one_nat ht hth
        have hn := (natTerm_lt (m + 1) (n + 1)).mp hlt
        exact (natTerm_lt m (n + 1)).mpr (by omega)
      · exact nat_lt_of_head_ne ht ht0 hth m
    · simpa only [dropOne_of_head_ne hsh] using hlt

end kumakuma.TargetArithmetic

namespace kumakuma.OT2

open OCF.Jaeger
open kumakuma.BinaryTranslation (dropOne succTerm)
open kumakuma.TargetArithmetic

def principal (a b : Term) : Term :=
  if b = .zero then .psi Term.bigOmega a
  else if a = .zero then .inacc 0 (dropOne b)
  else .psi (.inacc 0 (succTerm (dropOne b))) (dropOne a)

def assemble (p t : Term) : Term := if t = .zero then p else .add p t

theorem principal_isPrin (a b : Term) : Term.isPrin (principal a b) = true := by
  unfold principal
  split
  · rfl
  · split <;> rfl

theorem assemble_injective {p q t u : Term} (hp : Term.isPrin p = true)
    (hq : Term.isPrin q = true) (he : assemble p t = assemble q u) : p = q ∧ t = u := by
  unfold assemble at he
  by_cases ht : t = .zero <;> by_cases hu : u = .zero
  · simpa only [ht, hu, ↓reduceIte, and_true] using he
  · simp only [ht, hu, ↓reduceIte] at he
    cases p <;> simp_all [Term.isPrin]
  · simp only [ht, hu, ↓reduceIte] at he
    cases q <;> simp_all [Term.isPrin]
  · simpa only [ht, hu, ↓reduceIte, Term.add.injEq] using he

theorem assemble_lt {p q t u : Term} (hp : Term.isPrin p = true)
    (hq : Term.isPrin q = true) :
    Term.lt (assemble p t) (assemble q u) =
      if p = q then Term.lt t u else Term.lt p q := by
  by_cases he : p = q
  · subst q
    by_cases ht : t = .zero <;> by_cases hu : u = .zero
    · simp [assemble, ht, hu, lt_self]
    · cases p <;> simp_all [Term.isPrin, assemble, Term.lt, (zero_lt_iff u).mpr hu]
    · cases p <;> simp_all [Term.isPrin, assemble, Term.lt, lt_self, CountableTarget.lt_zero]
    · simp [assemble, ht, hu, Term.lt]
  · by_cases ht : t = .zero <;> by_cases hu : u = .zero
    · simp [assemble, ht, hu, he]
    · cases p <;> simp_all [Term.isPrin, assemble, Term.lt]
    · cases q <;> simp_all [Term.isPrin, assemble, Term.lt]
    · simp [assemble, ht, hu, he, Term.lt]

theorem zero_le (t : Term) : Term.le .zero t = true := by
  cases t <;> simp [Term.le, Term.lt]

end kumakuma.OT2

namespace kumakuma.OT2

open OCF.Jaeger
open kumakuma.BinaryTranslation (dropOne succTerm)
open kumakuma.TargetArithmetic

theorem mem_H_dropOne {u t z : Term} (hz : z ∈ Term.H u (dropOne t)) :
    z ∈ Term.H u t := by
  cases t with
  | zero => exact hz
  | inacc => exact hz
  | add a b =>
    simp only [dropOne] at hz
    split at hz
    · exact List.mem_append_right _ hz
    · exact hz
  | psi v a =>
    simp only [dropOne] at hz
    split at hz
    · cases hz
    · exact hz

theorem H_succTerm (u t : Term) :
    Term.H u (succTerm t) = Term.H u t ++ Term.H u Term.one := by
  induction t with
  | zero => rfl
  | add a b _ ihb => simp [succTerm, Term.H, ihb, List.append_assoc]
  | inacc | psi => rfl

end kumakuma.OT2

namespace kumakuma.OTQuotient

open multi CountableSource FiniteCorrespondence

def lastVec (k : Nat) (a : multi.T) : V multi.T := .snoc a (zeros k)

theorem lastVec_length (k : Nat) (a : multi.T) : (lastVec k a).length = k + 1 := by
  show (zeros k).length + 1 = k + 1
  rw [zeros_length]

theorem get0_lastVec (k : Nat) (a : multi.T) (i : Nat) :
    V.get0 (lastVec k a) i = if i = k then a else .Z := by
  show (if i = (zeros k).length then a else V.get0 (zeros k) i) = _
  rw [zeros_length, get0_zeros]

theorem fnz_lastVec (k : Nat) {a : multi.T} (ha : a ≠ .Z) : V.fnz (lastVec k a) = some k :=
  fnz_eq_some (by rw [get0_lastVec, ite_eq_left rfl]; exact ha)
    (fun j hj => by rw [get0_lastVec, ite_eq_right (Nat.ne_of_lt hj)])

theorem LF_step (k n : Nat) :
    towerD (k + 1) (n + 1) = .P (lastVec k (towerD (k + 1) n)) .Z := by
  rw [towerD]
  congr 1
  show V.snoc (if k = k then towerD (k + 1) n else .Z)
    (vOf (fun i => if i = k then towerD (k + 1) n else .Z) k) = _
  rw [ite_eq_left rfl]
  congr 1
  exact vOf_ext (fun j hj => ite_eq_right (Nat.ne_of_lt hj))

theorem LF_one (k : Nat) : towerD (k + 1) 1 = ofNatD (k + 1) 1 := by
  rw [LF_step]
  rfl

theorem ofNatD_succ_ne (d n : Nat) : ofNatD d (n + 1) ≠ .Z := by
  rw [ofNatD]; intro h; cases h

theorem dom_one {d : Nat} : domF (ofNatD d 1) = .one := domF_none (fnz_zeros d)

theorem fund_one {d : Nat} (t : multi.T) : T.fund (ofNatD d 1) t = .Z := fund_none (fnz_zeros d) t

theorem code_P_snocZ (v : V multi.T) (a : multi.T) :
    code (.P (.snoc .Z v) a) = code (.P v a) := by
  rw [code_P, code_P, codes_snoc, code_Z, trim_append_zero]

theorem isOT_one (d : Nat) : DOT (d + 1) (ofNatD (d + 1) 1) := by
  have h := DOT.base_succ d 0
  have he : baseD d 0 = ofNatD (d + 1) 1 := by
    show multi.T.P _ .Z = multi.T.P (zeros (d + 1)) .Z
    congr 1
    exact vOf_ext (fun j _ => by split <;> rfl)
  rwa [he] at h

def dimensionTop (k : Nat) : multi.T := .P (lastVec (k + 1) (ofNatD (k + 2) 1)) .Z

theorem Dim_dimensionTop (k : Nat) : Dim (k + 2) (dimensionTop k) := by
  refine Dim_P (lastVec_length _ _) (fun i => ?_) (Dim_Z _)
  rw [get0_lastVec]
  split
  · exact Dim_ofNatD _ _
  · exact Dim_Z _

theorem dimensionTop_ne (k : Nat) : dimensionTop k ≠ .Z := by
  intro h; cases h

theorem dimensionTop_LF (k : Nat) : towerD (k + 2) 2 = dimensionTop k := by
  show towerD (k + 1 + 1) (1 + 1) = _
  rw [LF_step, LF_one]
  rfl

theorem dimensionTop_dom (k : Nat) :
    domF (dimensionTop k) = .Omega (lastVec (k + 1) (ofNatD (k + 2) 1)) :=
  domF_one_succ (fnz_lastVec (k + 1) (ofNatD_succ_ne _ _))
    (by rw [get0_lastVec, ite_eq_left rfl]; exact dom_one)

theorem dimensionTop_fund (k : Nat) (x : multi.T) :
    T.fund (dimensionTop k) x = .P (.snoc .Z (lastVec k x)) .Z := by
  rw [dimensionTop, fund_one_succ (fnz_lastVec (k + 1) (ofNatD_succ_ne _ _))
    (by rw [get0_lastVec, ite_eq_left rfl]; exact dom_one)]
  congr 1
  have hl : (lastVec (k + 1) (ofNatD (k + 2) 1)).length = k + 2 := lastVec_length _ _
  apply V.eq_of_get0 _ _
    (by rw [V.length_set, V.length_set, hl]; show k + 2 = (lastVec k x).length + 1; rw [lastVec_length])
  intro j
  rw [V.get0_set _ k x j (by rw [V.length_set, hl]; omega),
    V.get0_set _ (k + 1) _ j (by rw [hl]; omega)]
  show _ = if j = (lastVec k x).length then .Z else V.get0 (lastVec k x) j
  rw [lastVec_length]
  by_cases hjk : j = k
  · subst hjk; simp [get0_lastVec]
  · by_cases hj1 : j = k + 1
    · subst hj1; simp [get0_lastVec, fund_one]
    · simp [get0_lastVec, hjk, hj1]

theorem code_dimensionTop_fund (k : Nat) (x : multi.T) :
    code (T.fund (dimensionTop k) x) = code (.P (lastVec k x) .Z) := by
  rw [dimensionTop_fund, code_P_snocZ]

theorem dimensionTop_iter (k n : Nat) :
    multi.T.iter (T.fund (dimensionTop k)) (ofNatD (k + 2) n) = padTo (k + 2) (towerD (k + 1) n) := by
  induction n with
  | zero => exact (padTo_Z _).symm
  | succ n ih =>
    show T.fund (dimensionTop k) (multi.T.iter (T.fund (dimensionTop k)) (ofNatD (k + 2) n)) = _
    rw [ih]
    have hX : Dim (k + 2) (padTo (k + 2) (towerD (k + 1) n)) :=
      Dim_padTo_of (Dim_towerD (k + 1) n) (Nat.le_succ _)
    apply eq_of_code_eq (d := k + 2)
    · exact Dim_fund _ _ (Dim_dimensionTop k) hX
    · exact Dim_padTo_of (Dim_towerD (k + 1) (n + 1)) (Nat.le_succ _)
    · rw [code_dimensionTop_fund, code_padTo, LF_step]
      apply code_P_congr _ rfl
      intro i
      rw [get0_lastVec, get0_lastVec]
      split
      · exact code_padTo _ _
      · rfl

def lowerBase (k n : Nat) : multi.T := .P (lowVec k (towerD (k + 1) n)) .Z

def dimensionBound (k : Nat) : multi.T := .P (lowVec (k + 1) (dimensionTop k)) .Z

theorem lowerBase_isOT (k n : Nat) : DOT (k + 1) (lowerBase k n) := DOT.base_succ k n

theorem Dim_dimensionBound (k : Nat) : Dim (k + 2) (dimensionBound k) :=
  Dim_lowVec (Dim_dimensionTop k) (Dim_Z _)

theorem dimensionBound_isOT (k : Nat) : DOT (k + 2) (dimensionBound k) := by
  show DOT (k + 2) (.P (lowVec (k + 1) (dimensionTop k)) .Z)
  rw [← dimensionTop_LF k]
  exact DOT.base_succ (k + 1) 2

theorem lowVec_lt_lastVec (k : Nat) (a : multi.T) :
    lowVec (k + 1) a < lastVec (k + 1) (ofNatD (k + 2) 1) := by
  apply V.lt_of_pivot (k + 1)
  · intro j hj
    rw [V.get0_ge _ j (by rw [lowVec_length]; omega), V.get0_ge _ j (by rw [lastVec_length]; omega)]
    exact compareT_ZZ
  · rw [get0_lowVec, ite_eq_right (by omega), get0_lastVec, ite_eq_left rfl]
    exact T.Z_lt_P _ _

theorem dimensionBound_fund (k n : Nat) :
    T.fund (dimensionBound k) (ofNatD (k + 2) n) = padTo (k + 2) (lowerBase k (n + 1)) := by
  have hf : V.fnz (lowVec (k + 1) (dimensionTop k)) = some 0 := fnz_lowVec (dimensionTop_ne k)
  have hg : V.get0 (lowVec (k + 1) (dimensionTop k)) 0 = dimensionTop k := by
    rw [get0_lowVec, ite_eq_left rfl]
  rw [dimensionBound, fund_diag hf (by rw [hg]; exact dimensionTop_dom k) (lowVec_lt_lastVec k _),
    hg, lowVec_set_zero, dimensionTop_iter]
  have hX : Dim (k + 2) (padTo (k + 2) (towerD (k + 1) n)) :=
    Dim_padTo_of (Dim_towerD (k + 1) n) (Nat.le_succ _)
  apply eq_of_code_eq (d := k + 2)
  · exact Dim_lowVec (Dim_fund _ _ (Dim_dimensionTop k) hX) (Dim_Z _)
  · exact Dim_padTo_of (lowerBase_isOT k (n + 1)).dim (Nat.le_succ _)
  · rw [code_padTo, lowerBase, code_P, code_P, trim_codes_lowVec, trim_codes_lowVec,
      code_dimensionTop_fund, LF_step]
    congr 3
    apply code_P_congr _ rfl
    intro i
    rw [get0_lastVec, get0_lastVec]
    split
    · exact code_padTo _ _
    · rfl

theorem pad_lowerBase_isOT (k n : Nat) : DOT (k + 2) (padTo (k + 2) (lowerBase k n)) := by
  cases n with
  | zero =>
    have he : lowerBase k 0 = ofNatD (k + 1) 1 := by
      show multi.T.P (lowVec k .Z) .Z = _
      rw [lowVec_Z]; rfl
    rw [he, padTo_ofNatD]
    exact isOT_one (k + 1)
  | succ n =>
    rw [← dimensionBound_fund k n]
    exact DOT.step _ _ (dimensionBound_isOT k) n

theorem isOT_pad {lam : Nat} {s : multi.T} (hs : DOT lam s) :
    DOT (lam + 1) (padTo (lam + 1) s) := by
  induction hs with
  | base_0 n =>
    rw [← ofNatD_zero_eq_tower, padTo_ofNatD]
    exact FirstLimit.ofNat_isOT_one n
  | base_succ k n => exact pad_lowerBase_isOT k n
  | step lam s hs n ih =>
    rw [fund_padTo hs.dim (Dim_ofNatD lam n) (Nat.le_succ _), padTo_ofNatD]
    exact DOT.step _ _ ih n

theorem isOT_promote {lam m : Nat} (h : lam ≤ m) {s : multi.T} (hs : DOT lam s) :
    DOT m (padTo m s) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = lam + k := ⟨m - lam, by omega⟩
  induction k with
  | zero => rw [Nat.add_zero, padTo_of_Dim hs.dim]; exact hs
  | succ k ih =>
    rw [← padTo_padTo (lam + (k + 1)) (lam + k) s]
    exact isOT_pad (ih (Nat.le_add_right _ _))

def promoteOT {lam m : Nat} (h : lam ≤ m) (s : OTD lam) : OTD m :=
  ⟨padTo m s.val, isOT_promote h s.property⟩

theorem classOf_promoteOT {lam m : Nat} (h : lam ≤ m) (s : OTD lam) :
    classOf ⟨m, promoteOT h s⟩ = classOf ⟨lam, s⟩ :=
  (class_eq_iff _ _).mpr (code_padTo m s.val)

theorem isOT_ofNat (lam n : Nat) : DOT lam (ofNatD lam n) := by
  have h := isOT_promote (Nat.zero_le lam) (FiniteCorrespondence.ofNat_isOT_zero n)
  rwa [padTo_ofNatD] at h

def HasDimensionWitness (lam : Nat) (q : Classes) : Prop :=
  ∃ s : OTD lam, classOf ⟨lam, s⟩ = q

theorem hasDimensionWitness_mono {lam m : Nat} (h : lam ≤ m) {q : Classes}
    (hq : HasDimensionWitness lam q) : HasDimensionWitness m q := by
  obtain ⟨s, hs⟩ := hq
  exact ⟨promoteOT h s, (classOf_promoteOT h s).trans hs⟩

theorem hasDimensionWitness_iff (q : Classes) (lam : Nat) :
    HasDimensionWitness lam q ↔ minDimension q ≤ lam := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h
    exact dimensionWitness_minimal q ⟨lam, s⟩ hs
  · intro h
    exact hasDimensionWitness_mono h (minDimension_spec q)

end kumakuma.OTQuotient

namespace kumakuma.HigherBoundary

open multi OTQuotient CountableSource

theorem compare_lowVec (k : Nat) (a b : multi.T) :
    compareV (lowVec k a) (lowVec k b) = compareT a b := by
  rw [compareV_eq_cmpUpTo _ _ (k + 1) (Nat.le_of_eq (lowVec_length k a))
    (Nat.le_of_eq (lowVec_length k b))]
  have h := cmpUpTo_zeros (V.get0 (lowVec k a)) (V.get0 (lowVec k b)) 1 k
    (fun j hj => by rw [get0_lowVec, ite_eq_right (by omega)])
    (fun j hj => by rw [get0_lowVec, ite_eq_right (by omega)])
  rw [show k + 1 = 1 + k from Nat.add_comm k 1, h]
  show (compareT (V.get0 (lowVec k a) 0) (V.get0 (lowVec k b) 0)).then .eq = _
  rw [get0_lowVec, get0_lowVec, ite_eq_left rfl, ite_eq_left rfl, ordering_then_eq]

end kumakuma.HigherBoundary

namespace kumakuma.DimensionCut

open multi OTQuotient CountableSource

theorem fund_zero_of_dom_one {lam : Nat} {s : multi.T} (hs : Dim lam s)
    (hd : domF s = .one) (hf : T.fund s .Z = .Z) : s = ofNatD lam 1 := by
  cases s with
  | Z => rw [domF_Z] at hd; cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst hb
      have hz := dom_one_principal hd
      show multi.T.P xs .Z = multi.T.P (zeros lam) .Z
      congr 1
      exact V.eq_of_get0 _ _ (by rw [hs.length, zeros_length]) (fun i => by rw [hz, get0_zeros])
    · rw [fund_tail xs hb] at hf; cases hf

theorem not_lt_zeros (xs : V multi.T) {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) : ¬ xs < w := by
  intro h
  obtain ⟨i, _, hlt⟩ := (V.lt_iff_pivot xs w).1 h
  rw [hw i] at hlt
  exact T.not_lt_Z _ hlt

theorem lt_one_iff {s : multi.T} {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) :
    s < .P w .Z ↔ s = .Z := by
  constructor
  · intro h
    cases s with
    | Z => rfl
    | P u c =>
      rcases (T.P_lt_P_iff u w c .Z).1 h with h | ⟨_, h⟩
      · exact absurd h (not_lt_zeros u hw)
      · exact absurd h (T.not_lt_Z _)
  · rintro rfl; exact T.Z_lt_P _ _

theorem nonzero_not_below_one {d : Nat} {s : multi.T} (hs : s ≠ .Z) : ¬ s < ofNatD d 1 :=
  fun h => hs ((lt_one_iff (w := zeros d) (get0_zeros d)).1 h)

def RootLow (k : Nat) : multi.T → Prop
  | .Z => True
  | .P xs _ => V.get0 xs (k + 1) = .Z

theorem lt_dimensionTop_of {k : Nat} {xs : V multi.T} (b : multi.T) (hlen : xs.length ≤ k + 2)
    (hz : V.get0 xs (k + 1) = .Z) : multi.T.P xs b < dimensionTop k := by
  apply T.P_lt_P_of_vlt
  apply V.lt_of_pivot (k + 1)
  · intro j hj
    rw [V.get0_ge xs j (by omega), V.get0_ge _ j (by rw [lastVec_length]; omega)]
    exact compareT_ZZ
  · rw [hz, get0_lastVec, ite_eq_left rfl]
    exact T.Z_lt_P _ _

theorem below_dimensionTop_iff_rootLow {k : Nat} {s : multi.T} (hs : Dim (k + 2) s) :
    s < dimensionTop k ↔ RootLow k s := by
  cases s with
  | Z => exact ⟨fun _ => trivial, fun _ => T.Z_lt_P _ _⟩
  | P xs b =>
    constructor
    · intro h
      show V.get0 xs (k + 1) = .Z
      rcases (T.P_lt_P_iff xs (lastVec (k + 1) (ofNatD (k + 2) 1)) b .Z).1 h with h | ⟨_, h⟩
      · obtain ⟨i, _, hlt⟩ := (V.lt_iff_pivot _ _).1 h
        rw [get0_lastVec] at hlt
        by_cases hi : i = k + 1
        · subst hi
          rw [ite_eq_left rfl] at hlt
          exact (lt_one_iff (w := zeros (k + 2)) (get0_zeros _)).1 hlt
        · rw [ite_eq_right hi] at hlt; exact absurd hlt (T.not_lt_Z _)
      · exact absurd h (T.not_lt_Z _)
    · intro h
      exact lt_dimensionTop_of b (Nat.le_of_eq hs.length) h

theorem fund_cross_dimensionTop {k : Nat} {s t : multi.T} (hs' : Dim (k + 2) s)
    (ht' : Dim (k + 2) t) (hs : ¬ s < dimensionTop k) (hl : T.fund s t < dimensionTop k) :
    T.fund s t = .Z ∨ T.fund s t = ofNatD (k + 2) 1 ∨ s = dimensionTop k := by
  have hdim := Dim_fund s t hs' ht'
  cases s with
  | Z => exact absurd (T.Z_lt_P _ _) hs
  | P xs b =>
    have hx : V.get0 xs (k + 1) ≠ .Z := fun hz => hs ((below_dimensionTop_iff_rootLow hs').2 hz)
    have hlen := hs'.length
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · exact absurd (V.fnz_none_spec xs hf (k + 1)) hx
      · obtain ⟨_, hlow⟩ := V.fnz_some_spec xs i hf
        have hil : i < k + 2 := hlen ▸ fnz_lt_length hf
        have cross : ∀ y, T.fund (.P xs .Z) t = .P (V.set xs i y) .Z →
            T.fund (.P xs .Z) t = ofNatD (k + 2) 1 := by
          intro y he
          have hr := (below_dimensionTop_iff_rootLow hdim).1 hl
          rw [he] at hr ⊢
          change V.get0 (V.set xs i y) (k + 1) = .Z at hr
          by_cases hik : i = k + 1
          · subst hik
            rw [V.get0_set_same xs _ y (by omega)] at hr
            subst hr
            show multi.T.P (V.set xs (k + 1) .Z) .Z = multi.T.P (zeros (k + 2)) .Z
            congr 1
            apply V.eq_of_get0 _ _ (by rw [V.length_set, hlen, zeros_length])
            intro j
            rw [get0_zeros, V.get0_set xs (k + 1) .Z j (by omega)]
            split
            · rfl
            · by_cases hjl : j < k + 1
              · exact hlow j hjl
              · exact V.get0_ge xs j (by omega)
          · rw [V.get0_set_ne xs i y (k + 1) (Ne.symm hik)] at hr
            exact absurd hr hx
        cases hd : domF (V.get0 xs i) with
        | zero => exact Or.inr (Or.inl (cross _ (fund_zero hf hd t)))
        | omega => exact Or.inr (Or.inl (cross _ (fund_omega hf hd t)))
        | Omega q =>
          by_cases hq : xs < q
          · exact Or.inr (Or.inl (cross _ (fund_diag hf hd hq t)))
          · exact Or.inr (Or.inl (cross _ (fund_nondiag hf hd hq t)))
        | one =>
          cases i with
          | zero =>
            cases t with
            | Z => exact Or.inl (by rw [fund_one_zero hf hd]; rfl)
            | P ys c =>
              have hr := (below_dimensionTop_iff_rootLow hdim).1 hl
              rw [fund_one_zero hf hd] at hr
              change V.get0 (V.set xs 0 _) (k + 1) = .Z at hr
              rw [V.get0_set_ne xs 0 _ (k + 1) (by omega)] at hr
              exact absurd hr hx
          | succ m =>
            have hr := (below_dimensionTop_iff_rootLow hdim).1 hl
            rw [fund_one_succ hf hd] at hr
            change V.get0 (V.set (V.set xs (m + 1) _) m t) (k + 1) = .Z at hr
            rw [V.get0_set_ne _ m t (k + 1) (by omega)] at hr
            by_cases hmk : m + 1 = k + 1
            · obtain rfl : k = m := by omega
              rw [V.get0_set_same xs (k + 1) _ (by omega)] at hr
              have hone := fund_zero_of_dom_one (hs'.coord (k + 1)) hd hr
              refine Or.inr (Or.inr ?_)
              show multi.T.P xs .Z = multi.T.P (lastVec (k + 1) (ofNatD (k + 2) 1)) .Z
              congr 1
              apply V.eq_of_get0 _ _ (by rw [hlen, lastVec_length])
              intro j
              rw [get0_lastVec]
              split
              · rename_i hj; subst hj; exact hone
              · by_cases hjl : j < k + 1
                · exact hlow j hjl
                · exact V.get0_ge xs j (by omega)
            · rw [V.get0_set_ne xs (m + 1) _ (k + 1) (Ne.symm hmk)] at hr
              exact absurd hr hx
    · have hr := (below_dimensionTop_iff_rootLow hdim).1 hl
      rw [fund_tail xs hb] at hr
      exact absurd hr hx

theorem outer_below_dimensionBound_iff {k : Nat} (a b : multi.T) :
    multi.T.P (lowVec (k + 1) a) b < dimensionBound k ↔ a < dimensionTop k := by
  show compareT (.P (lowVec (k + 1) a) b) (.P (lowVec (k + 1) (dimensionTop k)) .Z) = .lt ↔
    compareT a (dimensionTop k) = .lt
  rw [compareT_PP, HigherBoundary.compare_lowVec]
  cases h : compareT a (dimensionTop k) with
  | lt => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | gt => exact ⟨fun h' => (by cases h'), fun h' => (by cases h')⟩
  | eq =>
    refine ⟨fun h' => ?_, fun h' => by cases h'⟩
    have h'' : compareT b .Z = .lt := h'
    cases b with
    | Z => rw [compareT_ZZ] at h''; cases h''
    | P _ _ => rw [compareT_PZ] at h''; cases h''

theorem dom_one_fund_not_cross {k : Nat} {s : multi.T} (hs' : Dim (k + 2) s)
    (hd : domF s = .one) (hs : ¬ s < dimensionTop k) : ¬ T.fund s .Z < dimensionTop k := by
  intro hl
  cases s with
  | Z => rw [domF_Z] at hd; cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst hb
      exact hs ((below_dimensionTop_iff_rootLow hs').2 (dom_one_principal hd (k + 1)))
    · have hdim := Dim_fund _ .Z hs' (Dim_Z _)
      have hr := (below_dimensionTop_iff_rootLow hdim).1 hl
      rw [fund_tail xs hb] at hr
      exact hs ((below_dimensionTop_iff_rootLow hs').2 hr)

theorem padded_small_argument {k : Nat} {a : multi.T} (ha : a = .Z ∨ a = ofNatD (k + 2) 1) :
    ∃ s, DOT (k + 1) s ∧ padTo (k + 2) s = .P (lowVec (k + 1) a) .Z := by
  rcases ha with rfl | rfl
  · refine ⟨ofNatD (k + 1) 1, isOT_ofNat _ _, ?_⟩
    rw [padTo_ofNatD, lowVec_Z]
    rfl
  · refine ⟨lowerBase k 1, lowerBase_isOT k 1, ?_⟩
    apply eq_of_code_eq (d := k + 2) (Dim_padTo_of (lowerBase_isOT k 1).dim (Nat.le_succ _))
      (Dim_lowVec (Dim_ofNatD _ _) (Dim_Z _))
    rw [code_padTo, lowerBase, code_P, code_P, trim_codes_lowVec, trim_codes_lowVec, LF_one,
      FiniteCorrespondence.code_ofNatD, FiniteCorrespondence.code_ofNatD]

theorem collapsed_argument_cross_padded {k : Nat} (a x : multi.T) (n : Nat)
    (ha' : Dim (k + 2) a) (hx' : Dim (k + 2) x) (ha : ¬ a < dimensionTop k)
    (he : T.fund (.P (lowVec (k + 1) a) .Z) (ofNatD (k + 2) n) =
      .P (lowVec (k + 1) (T.fund a x)) .Z)
    (hl : T.fund (.P (lowVec (k + 1) a) .Z) (ofNatD (k + 2) n) < dimensionBound k) :
    ∃ s, DOT (k + 1) s ∧ padTo (k + 2) s = T.fund (.P (lowVec (k + 1) a) .Z) (ofNatD (k + 2) n) := by
  have hl' : multi.T.P (lowVec (k + 1) (T.fund a x)) .Z < dimensionBound k := he ▸ hl
  have hx : T.fund a x < dimensionTop k := (outer_below_dimensionBound_iff _ _).1 hl'
  rcases fund_cross_dimensionTop ha' hx' ha hx with hf | hf | rfl
  · rw [he, hf]; exact padded_small_argument (Or.inl rfl)
  · rw [he, hf]; exact padded_small_argument (Or.inr rfl)
  · exact ⟨lowerBase k (n + 1), lowerBase_isOT k (n + 1), (dimensionBound_fund k n).symm⟩

theorem outer_step_cross_padded {k : Nat} {s : multi.T} (ho : Outer (k + 1) s)
    (hs' : Dim (k + 2) s) (n : Nat) (hs : ¬ s < dimensionBound k)
    (hl : T.fund s (ofNatD (k + 2) n) < dimensionBound k) :
    ∃ u, DOT (k + 1) u ∧ padTo (k + 2) u = T.fund s (ofNatD (k + 2) n) := by
  cases ho with
  | zero => exact absurd (T.Z_lt_P _ _) hs
  | cons a b hb =>
    have ha' : Dim (k + 2) a := by
      have := hs'.coord 0
      rwa [get0_lowVec, ite_eq_left rfl] at this
    have ha : ¬ a < dimensionTop k := fun h => hs ((outer_below_dimensionBound_iff a b).2 h)
    by_cases hb0 : b = .Z
    · subst hb0
      by_cases haz : a = .Z
      · subst haz
        refine ⟨ofNatD (k + 1) 0, isOT_ofNat _ _, ?_⟩
        rw [fund_none (fnz_lowVec_Z _)]
        exact padTo_Z _
      · have hf := fnz_lowVec (k := k + 1) haz
        have hg : V.get0 (lowVec (k + 1) a) 0 = a := by rw [get0_lowVec, ite_eq_left rfl]
        cases hd : domF a with
        | zero => exact absurd ((domF_eq_zero_iff a).1 hd) haz
        | one =>
          have he := fund_one_zero hf (by rw [hg]; exact hd) (ofNatD (k + 2) n)
          rw [hg, lowVec_set_zero] at he
          cases n with
          | zero => exact ⟨ofNatD (k + 1) 0, isOT_ofNat _ _, by rw [he]; exact padTo_Z _⟩
          | succ n =>
            rw [he] at hl
            have hl' : multi.T.P (lowVec (k + 1) (T.fund a .Z))
                (multi.T.mul (.P (lowVec (k + 1) (T.fund a .Z)) .Z) (ofNatD (k + 2) n)) <
                dimensionBound k := hl
            have hf' := (outer_below_dimensionBound_iff _ _).1 hl'
            exact absurd hf' (dom_one_fund_not_cross ha' hd ha)
        | omega =>
          have he := fund_omega hf (by rw [hg]; exact hd) (ofNatD (k + 2) n)
          rw [hg, lowVec_set_zero] at he
          exact collapsed_argument_cross_padded a _ n ha' (Dim_ofNatD _ _) ha he hl
        | Omega q =>
          by_cases hq : lowVec (k + 1) a < q
          · have he := fund_diag hf (by rw [hg]; exact hd) hq (ofNatD (k + 2) n)
            rw [hg, lowVec_set_zero] at he
            exact collapsed_argument_cross_padded a _ n ha'
              (Dim_iter (fun x hx => Dim_fund a x ha' hx) (Dim_ofNatD _ _)) ha he hl
          · have he := fund_nondiag hf (by rw [hg]; exact hd) hq (ofNatD (k + 2) n)
            rw [hg, lowVec_set_zero] at he
            exact collapsed_argument_cross_padded a _ n ha' (Dim_ofNatD _ _) ha he hl
    · rw [fund_tail _ hb0] at hl
      exact absurd ((outer_below_dimensionBound_iff _ _).1 hl) ha

theorem LF_positive (k n : Nat) : towerD (k + 1) (n + 1) ≠ .Z := by
  rw [LF_step]
  intro h; cases h

theorem generated_small_aux {lam : Nat} {s : multi.T} (h : DOT lam s) :
    ∀ k, lam = k + 2 → s < dimensionBound k → ∃ u, DOT (k + 1) u ∧ padTo (k + 2) u = s := by
  induction h with
  | base_0 n => intro k e; omega
  | base_succ lam n =>
    intro k e hl
    obtain rfl : lam = k + 1 := by omega
    match n with
    | 0 => exact padded_small_argument (a := towerD (k + 2) 0) (Or.inl rfl)
    | 1 => exact padded_small_argument (a := towerD (k + 2) 1) (Or.inr (LF_one (k + 1)))
    | n + 2 =>
      have ha := (outer_below_dimensionBound_iff (k := k) (towerD (k + 2) (n + 2)) .Z).1 hl
      have hr := (below_dimensionTop_iff_rootLow (Dim_towerD (k + 2) (n + 2))).1 ha
      have e : towerD (k + 2) (n + 2) = .P (lastVec (k + 1) (towerD (k + 2) (n + 1))) .Z :=
        LF_step (k + 1) (n + 1)
      rw [e] at hr
      change V.get0 (lastVec (k + 1) (towerD (k + 2) (n + 1))) (k + 1) = .Z at hr
      rw [get0_lastVec, ite_eq_left rfl] at hr
      exact absurd hr (LF_positive (k + 1) n)
  | step lam s hs n ih =>
    intro k e hl
    subst e
    by_cases hsmall : s < dimensionBound k
    · obtain ⟨u, hu, he⟩ := ih k rfl hsmall
      refine ⟨T.fund u (ofNatD (k + 1) n), DOT.step _ _ hu n, ?_⟩
      rw [fund_padTo hu.dim (Dim_ofNatD _ _) (Nat.le_succ _), padTo_ofNatD, he]
    · exact outer_step_cross_padded (isOT_outer hs) hs.dim n hsmall hl

theorem isOT_below_dimensionBound {k : Nat} {s : multi.T}
    (hs : DOT (k + 2) s) (hl : s < dimensionBound k) :
    ∃ u : OTD (k + 1), padTo (k + 2) u.val = s := by
  obtain ⟨u, hu, he⟩ := generated_small_aux hs k rfl hl
  exact ⟨⟨u, hu⟩, he⟩

def boundaryElement (k : Nat) : AllOT :=
  ⟨k + 2, dimensionBound k, dimensionBound_isOT k⟩

def boundaryClass (k : Nat) : Classes := classOf (boundaryElement k)

theorem outer_below_dimensionBound {k : Nat} {s : multi.T} (hs : Outer k s) (hd : Dim (k + 1) s) :
    s < dimensionBound k := by
  cases hs with
  | zero => exact T.Z_lt_P _ _
  | cons a b _ =>
    apply T.P_lt_P_of_vlt
    apply V.lt_of_pivot 0
    · intro j hj
      rw [get0_lowVec, get0_lowVec, ite_eq_right (by omega), ite_eq_right (by omega)]
      exact compareT_ZZ
    · rw [get0_lowVec, get0_lowVec, ite_eq_left rfl, ite_eq_left rfl]
      have ha : Dim (k + 1) a := by
        have := hd.coord 0
        rwa [get0_lowVec, ite_eq_left rfl] at this
      cases a with
      | Z => exact T.Z_lt_P _ _
      | P v c =>
        exact lt_dimensionTop_of c (by rw [ha.length]; omega) (V.get0_ge v _ (Nat.le_of_eq ha.length))

theorem dimension_witness_below_boundary {k : Nat} {q : Classes}
    (hq : HasDimensionWitness (k + 1) q) : ClassLT q (boundaryClass k) := by
  obtain ⟨s, rfl⟩ := hq
  show compareCode (code s.val) (code (dimensionBound k)) = .lt
  rw [compareCode_code]
  exact outer_below_dimensionBound (isOT_outer s.property) s.property.dim

theorem dimension_witness_iff_below_boundary (k : Nat) (q : Classes) :
    HasDimensionWitness (k + 1) q ↔ ClassLT q (boundaryClass k) := by
  constructor
  · exact dimension_witness_below_boundary
  · intro hq
    apply (hasDimensionWitness_iff q (k + 1)).mpr
    apply Nat.le_of_not_gt
    intro hn
    obtain ⟨s, hs⟩ := minDimension_spec q
    generalize hd : minDimension q = d at s hs
    cases d with
    | zero => omega
    | succ d =>
      cases d with
      | zero => omega
      | succ m =>
        have hkm : k ≤ m := by omega
        have hm : ClassLT q (boundaryClass m) := by
          by_cases he : k = m
          · simpa only [he] using hq
          · have hkdim : k + 2 ≤ m + 1 := by omega
            have hkw : HasDimensionWitness (m + 1) (boundaryClass k) :=
              hasDimensionWitness_mono hkdim ⟨(boundaryElement k).2, rfl⟩
            exact classLT_trans hq (dimension_witness_below_boundary hkw)
        rw [← hs] at hm
        change compareCode (code s.val) (code (dimensionBound m)) = .lt at hm
        rw [compareCode_code] at hm
        obtain ⟨u, hu⟩ := isOT_below_dimensionBound s.property hm
        have he : classOf ⟨m + 1, u⟩ = q := by
          rw [← hs]
          apply (class_eq_iff _ _).mpr
          show code u.val = code s.val
          rw [← hu, code_padTo]
        have hmin := dimensionWitness_minimal q ⟨m + 1, u⟩ he
        change minDimension q ≤ m + 1 at hmin
        omega

end kumakuma.DimensionCut

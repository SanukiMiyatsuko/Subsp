import Subsp.multi.kuma.Dimension

/-! Source fund order, codes, and the image map `DimensionImage.convert` (the `multi` version
of `Subsp/Support/Image.lean`). -/

namespace kumakuma.SourceFundOrder

open multi OTQuotient DimensionCut

theorem set_lt_set {v : V multi.T} {i : Nat} (hi : i < v.length) {a b : multi.T} (h : a < b) :
    V.set v i a < V.set v i b := by
  apply V.lt_of_pivot i
  · intro j hj
    rw [V.get0_set_ne v i a j (Nat.ne_of_gt hj), V.get0_set_ne v i b j (Nat.ne_of_gt hj)]
    exact T.eqv_refl _
  · rw [V.get0_set_same v i a hi, V.get0_set_same v i b hi]; exact h

theorem set_set_lower_lt {v : V multi.T} {m : Nat} (hm : m + 1 < v.length) {a : multi.T}
    (ha : a < V.get0 v (m + 1)) (b : multi.T) : V.set (V.set v (m + 1) a) m b < v := by
  apply V.lt_of_pivot (m + 1)
  · intro j hj
    rw [V.get0_set_ne _ m b j (by omega), V.get0_set_ne v (m + 1) a j (by omega)]
    exact T.eqv_refl _
  · rw [V.get0_set_ne _ m b (m + 1) (by omega), V.get0_set_same v (m + 1) a hm]; exact ha

theorem fund_lt : ∀ (s t : multi.T), s ≠ .Z → T.fund s t < s
  | .Z, _, hs => absurd rfl hs
  | .P xs b, t, _ => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf]; exact T.Z_lt_P _ _
      · have hn : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
        have hil := fnz_lt_length hf
        have hi : ∀ u, T.fund (V.get0 xs i) u < V.get0 xs i := fun u => fund_lt _ u hn
        cases hd : domF (V.get0 xs i) with
        | zero => rw [fund_zero hf hd]; exact T.P_lt_P_of_vlt _ _ (set_lt hil (hi _))
        | omega => rw [fund_omega hf hd]; exact T.P_lt_P_of_vlt _ _ (set_lt hil (hi _))
        | Omega q =>
          by_cases hq : xs < q
          · rw [fund_diag hf hd hq]; exact T.P_lt_P_of_vlt _ _ (set_lt hil (hi _))
          · rw [fund_nondiag hf hd hq]; exact T.P_lt_P_of_vlt _ _ (set_lt hil (hi _))
        | one =>
          cases i with
          | zero => rw [fund_one_zero hf hd]; exact mul_lt_of_vlt (set_lt hil (hi _)) t
          | succ m =>
            rw [fund_one_succ hf hd]
            exact T.P_lt_P_of_vlt _ _ (set_set_lower_lt hil (hi _) t)
    · rw [fund_tail xs hb]
      exact T.P_tail_lt xs (fund_lt b t hb)
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem fund_mono : ∀ (s : multi.T) {v : V multi.T}, domF s = .Omega v →
    ∀ (t u : multi.T), t < u → T.fund s t < T.fund s u
  | .Z, _, hd, _, _, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, v, hd, t, u, htu => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · have hil := fnz_lt_length hf
        cases hc : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hc] at hd; cases hd
        | omega => rw [domF_omega hf hc] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m =>
            rw [fund_one_succ hf hc, fund_one_succ hf hc]
            exact T.P_lt_P_of_vlt _ _ (set_lt_set (by rw [V.length_set]; omega) htu)
        | Omega q =>
          by_cases hq : xs < q
          · rw [domF_diag hf hc hq] at hd; cases hd
          · rw [fund_nondiag hf hc hq, fund_nondiag hf hc hq]
            exact T.P_lt_P_of_vlt _ _ (set_lt_set hil (fund_mono _ hc t u htu))
    · rw [domF_tail xs hb] at hd
      rw [fund_tail xs hb, fund_tail xs hb]
      exact T.P_tail_lt xs (fund_mono b hd t u htu)
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

def RegularVector (v : V multi.T) : Prop :=
  ∃ i, 0 < i ∧ V.fnz v = some i ∧ domF (V.get0 v i) = .one

theorem domOmega_regular : ∀ (s : multi.T) {v : V multi.T}, domF s = .Omega v → RegularVector v
  | .Z, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, v, hd => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hc : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hc] at hd; cases hd
        | omega => rw [domF_omega hf hc] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hc] at hd
            cases hd
            exact ⟨m + 1, Nat.succ_pos m, hf, hc⟩
        | Omega q =>
          by_cases hq : xs < q
          · rw [domF_diag hf hc hq] at hd; cases hd
          · rw [domF_nondiag hf hc hq] at hd
            cases hd
            exact domOmega_regular _ hc
    · rw [domF_tail xs hb] at hd
      exact domOmega_regular b hd
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem regularVector_dom {v : V multi.T} (hv : RegularVector v) : domF (.P v .Z) = .Omega v := by
  obtain ⟨i, hi, hf, hd⟩ := hv
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  exact domF_one_succ hf hd

theorem lowVec_below_positive (k : Nat) (a : multi.T) (v : V multi.T) (i : Nat) (hi : 0 < i)
    (hv : V.get0 v i ≠ .Z) : CountableSource.lowVec k a < v := by
  have hil : i < (V.trim v).length := by
    apply Nat.lt_of_not_le
    intro h
    exact hv (by rw [← V.get0_trim]; exact V.get0_ge _ i h)
  have htop := V.trim_eq_self_top (V.trim_trim v) (by omega)
  rw [V.get0_trim] at htop
  apply V.lt_of_pivot ((V.trim v).length - 1)
  · intro j hj
    rw [CountableSource.get0_lowVec, ite_eq_right (by omega), ← V.get0_trim v j,
      V.get0_ge _ j (by omega)]
    exact compareT_ZZ
  · rw [CountableSource.get0_lowVec, ite_eq_right (by omega)]
    exact T.Z_lt_of_ne htop

theorem lowVec_below_regular {k : Nat} (a : multi.T) (v : V multi.T) (i : Nat) (hi : 0 < i)
    (hf : V.fnz v = some i) : CountableSource.lowVec k a < v :=
  lowVec_below_positive k a v i hi (V.fnz_some_spec v i hf).1

theorem outer_not_Omega {k : Nat} {s : multi.T} (hs : CountableSource.Outer k s)
    (v : V multi.T) : domF s ≠ .Omega v := by
  induction hs with
  | zero => rw [domF_Z]; intro h; cases h
  | cons a b hb ih =>
    intro hd
    by_cases hz : b = .Z
    · subst hz
      by_cases ha : a = .Z
      · subst ha; rw [domF_none (CountableSource.fnz_lowVec_Z k)] at hd; cases hd
      · have hf := CountableSource.fnz_lowVec (k := k) ha
        have hg : V.get0 (CountableSource.lowVec k a) 0 = a := by
          rw [CountableSource.get0_lowVec, ite_eq_left rfl]
        cases hc : domF a with
        | zero => rw [domF_zero hf (by rw [hg]; exact hc)] at hd; cases hd
        | one => rw [domF_one_zero hf (by rw [hg]; exact hc)] at hd; cases hd
        | omega => rw [domF_omega hf (by rw [hg]; exact hc)] at hd; cases hd
        | Omega w =>
          obtain ⟨i, hi, hfw, _⟩ := domOmega_regular a hc
          have hlt := lowVec_below_regular (k := k) a w i hi hfw
          rw [domF_diag hf (by rw [hg]; exact hc) hlt] at hd; cases hd
    · rw [domF_tail _ hz] at hd
      exact ih hd

end kumakuma.SourceFundOrder

namespace kumakuma.SourceSummands

open multi OTQuotient

def tail : multi.T → multi.T
  | .Z => .Z
  | .P _ b => b

theorem tail_fund_isOT {lam : Nat} {s : multi.T} (hs : DOT lam s)
    (ht : DOT lam (tail s)) (n : Nat) : DOT lam (tail (T.fund s (ofNatD lam n))) := by
  cases s with
  | Z => rw [fund_Z]; exact ht
  | P xs b =>
    by_cases hb : b = .Z
    · subst hb
      have hz : DOT lam .Z := isOT_ofNat lam 0
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf]; exact hz
      · cases hd : domF (V.get0 xs i) with
        | zero => rw [fund_zero hf hd]; exact hz
        | omega => rw [fund_omega hf hd]; exact hz
        | Omega q =>
          by_cases hq : xs < q
          · rw [fund_diag hf hd hq]; exact hz
          · rw [fund_nondiag hf hd hq]; exact hz
        | one =>
          cases i with
          | succ m => rw [fund_one_succ hf hd]; exact hz
          | zero =>
            cases n with
            | zero => rw [fund_one_zero hf hd]; exact hz
            | succ n =>
              have h := DOT.step lam (.P xs .Z) hs n
              rw [fund_one_zero hf hd] at h ⊢
              exact h
    · rw [fund_tail xs hb]
      exact DOT.step lam b ht n

theorem tail_isOT {lam : Nat} {s : multi.T} (hs : DOT lam s) : DOT lam (tail s) := by
  induction hs with
  | base_0 n =>
    cases n with
    | zero => exact DOT.base_0 0
    | succ n => exact DOT.base_0 n
  | base_succ k n => exact isOT_ofNat (k + 1) 0
  | step lam s hs n ih => exact tail_fund_isOT hs ih n

end kumakuma.SourceSummands

namespace kumakuma.SourceDescending

open multi OTQuotient

theorem head_fund_le (s t : multi.T) : T.hd (T.fund s t) ≤ T.hd s := by
  by_cases hz : s = .Z
  · subst hz; rw [fund_Z]; exact T.le_refl _
  · exact T.hd_mono (SourceFundOrder.fund_lt s t hz)

def Descending : multi.T → Prop
  | .Z => True
  | .P xs b => Descending b ∧ T.hd b ≤ .P xs .Z

theorem principal_descending (xs : V multi.T) : Descending (.P xs .Z) := ⟨trivial, T.Z_le _⟩

theorem mul_principal_descending (xs : V multi.T) :
    ∀ t : multi.T, Descending (multi.T.mul (.P xs .Z) t)
  | .Z => trivial
  | .P _ b => by
    show Descending (.P xs (multi.T.mul (.P xs .Z) b))
    refine ⟨mul_principal_descending xs b, ?_⟩
    cases b with
    | Z => exact T.Z_le _
    | P zs c => exact T.le_refl _

theorem fund_descending : ∀ (s t : multi.T), Descending s → Descending (T.fund s t)
  | .Z, t, _ => by rw [fund_Z]; trivial
  | .P xs b, t, hs => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf]; trivial
      · cases hd : domF (V.get0 xs i) with
        | zero => rw [fund_zero hf hd]; exact principal_descending _
        | omega => rw [fund_omega hf hd]; exact principal_descending _
        | Omega q =>
          by_cases hq : xs < q
          · rw [fund_diag hf hd hq]; exact principal_descending _
          · rw [fund_nondiag hf hd hq]; exact principal_descending _
        | one =>
          cases i with
          | zero => rw [fund_one_zero hf hd]; exact mul_principal_descending _ t
          | succ m => rw [fund_one_succ hf hd]; exact principal_descending _
    · rw [fund_tail xs hb]
      exact ⟨fund_descending b t hs.1, T.le_trans (head_fund_le b t) hs.2⟩
termination_by s => s.size
decreasing_by exact multi.T.size_lt_P_right _ _

theorem ofNat_descending (lam n : Nat) : Descending (ofNatD lam n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    show Descending (.P (zeros lam) (ofNatD lam n))
    refine ⟨ih, ?_⟩
    cases n with
    | zero => exact T.Z_le _
    | succ n => exact T.le_refl _

theorem lt_one_iff_zero {lam : Nat} (s : multi.T) : s < ofNatD lam 1 ↔ s = .Z :=
  DimensionCut.lt_one_iff (w := zeros lam) (get0_zeros lam)

end kumakuma.SourceDescending

namespace kumakuma.SourceSuccessor

open multi OTQuotient

/-- The successor `s + 1` in dimension `lam`. -/
def succ (lam : Nat) (s : multi.T) : multi.T := s + ofNatD lam 1

theorem succ_ne_zero (lam : Nat) (s : multi.T) : succ lam s ≠ .Z := by
  cases s <;> intro h <;> cases h

theorem Dim_succ {lam : Nat} {s : multi.T} (h : Dim lam s) : Dim lam (succ lam s) :=
  Dim_oplus h (Dim_ofNatD lam 1)

theorem dom_succ (lam : Nat) : ∀ s : multi.T, domF (succ lam s) = .one
  | .Z => dom_one
  | .P xs b => by
    show domF (.P xs (succ lam b)) = .one
    rw [domF_tail xs (succ_ne_zero lam b)]
    exact dom_succ lam b

theorem fund_succ (lam : Nat) : ∀ s t : multi.T, T.fund (succ lam s) t = s
  | .Z, t => fund_one t
  | .P xs b, t => by
    show T.fund (.P xs (succ lam b)) t = .P xs b
    rw [fund_tail xs (succ_ne_zero lam b), fund_succ lam b t]

theorem lt_succ_iff_le (lam : Nat) : ∀ s t : multi.T, s < succ lam t ↔ s ≤ t
  | s, .Z => by
    show s < ofNatD lam 1 ↔ s ≤ .Z
    rw [SourceDescending.lt_one_iff_zero]
    constructor
    · rintro rfl; exact T.le_refl _
    · rintro (h | h)
      · exact absurd h (T.not_lt_Z _)
      · exact T.eqv_Z_iff.1 h
  | .Z, .P ys b => ⟨fun _ => T.Z_le _, fun _ => T.Z_lt_P _ _⟩
  | .P xs a, .P ys b => by
    show multi.T.P xs a < .P ys (succ lam b) ↔ multi.T.P xs a ≤ .P ys b
    rw [T.P_lt_P_iff, T.P_le_P_iff, lt_succ_iff_le lam a b]

theorem nat_succ (lam n : Nat) : succ lam (ofNatD lam n) = ofNatD lam (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (multi.T.P (zeros lam)) ih

end kumakuma.SourceSuccessor

namespace kumakuma.UserImage

open OTQuotient

def oneCode : Code := .p [] .zero

end kumakuma.UserImage

namespace kumakuma.CodeReification

open multi OTQuotient CountableSource

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

theorem argsWidth_append (xs ys : List Code) :
    argsWidth (xs ++ ys) = max (argsWidth xs) (argsWidth ys) := by
  induction xs with
  | nil => rw [List.nil_append, argsWidth, Nat.zero_max]
  | cons a xs ih => rw [List.cons_append, argsWidth, argsWidth, ih, Nat.max_assoc]

theorem argsWidth_singleton (c : Code) : argsWidth [c] = width c := by
  rw [argsWidth, argsWidth, Nat.max_zero]

theorem vWidth_trim : ∀ v : V multi.T, vWidth (V.trim v) = vWidth v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z =>
      show vWidth (V.trim ax) = max (tWidth .Z) (vWidth ax)
      rw [vWidth_trim ax, tWidth, Nat.zero_max]
    | P w c => rfl

theorem argsWidth_codes (v : V multi.T)
    (h : ∀ i, width (code (V.get0 v i)) = tWidth (V.get0 v i)) :
    argsWidth (codes v) = vWidth v := by
  induction v with
  | emp => rw [codes_emp, argsWidth, vWidth]
  | snoc x xs ih =>
    have hx := h xs.length
    rw [V.get0_snoc_top] at hx
    have hxs : ∀ i, width (code (V.get0 xs i)) = tWidth (V.get0 xs i) := by
      intro i
      by_cases hi : i < xs.length
      · have := h i; rwa [V.get0_snoc_low x xs i hi] at this
      · rw [V.get0_ge xs i (Nat.le_of_not_lt hi), code_Z, width, tWidth]
    rw [codes_snoc, argsWidth_append, argsWidth_singleton, ih hxs, hx, vWidth, Nat.max_comm]

/-- The width of the code of a term is its trimmed width. -/
theorem width_code : ∀ s : multi.T, width (code s) = tWidth s
  | .Z => by rw [code_Z, width, tWidth]
  | .P v a => by
    rw [code_P, width, tWidth, trim_codes, codes_length, width_code a,
      argsWidth_codes (V.trim v) (fun i => by rw [V.get0_trim]; exact width_code _), vWidth_trim]
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem width_code_le {d : Nat} {s : multi.T} (h : Dim d s) : width (code s) ≤ d := by
  rw [width_code]; exact tWidth_le_of_Dim h

theorem Dim_padTo_width {d : Nat} {s : multi.T} (h : width (code s) ≤ d) : Dim d (padTo d s) :=
  Dim_padTo (by rwa [← width_code])

theorem tWidth_coord_le (v : V multi.T) (a : multi.T) (i : Nat) :
    tWidth (V.get0 v i) ≤ tWidth (.P v a) := by
  rw [tWidth]
  exact Nat.le_trans (vWidth_get0 v i)
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))

theorem outer_fit_below {k : Nat} {s : multi.T} (hs : Outer (k + 1) s) (hd : Dim (k + 2) s)
    (hw : width (code s) ≤ k + 1) : s < dimensionBound k := by
  cases hs with
  | zero => exact T.Z_lt_P _ _
  | cons a b _ =>
    apply (DimensionCut.outer_below_dimensionBound_iff a b).2
    have ha : Dim (k + 2) a := by
      have := hd.coord 0
      rwa [get0_lowVec, ite_eq_left rfl] at this
    have hwa : tWidth a ≤ k + 1 := by
      have := tWidth_coord_le (lowVec (k + 1) a) b 0
      rw [get0_lowVec, ite_eq_left rfl] at this
      rw [width_code] at hw
      omega
    cases a with
    | Z => exact T.Z_lt_P _ _
    | P w c =>
      apply DimensionCut.lt_dimensionTop_of c (Nat.le_of_eq ha.length)
      rw [← V.get0_trim]
      apply V.get0_ge
      rw [tWidth] at hwa
      have := Nat.le_max_left (V.trim w).length (max (vWidth w) (tWidth c))
      omega

theorem generated_reify (d lam : Nat) (s : OTD d) (hw : width (code s.val) ≤ lam) :
    DOT lam (padTo lam s.val) := by
  induction d using Nat.strongRecOn generalizing lam with
  | ind d ih =>
    by_cases hd : d ≤ lam
    · exact isOT_promote hd s.property
    · cases d with
      | zero => omega
      | succ d =>
        cases d with
        | zero =>
          have hl : lam = 0 := by omega
          subst lam
          obtain ⟨n, he⟩ :=
            FiniteCorrespondence.zero_dimension_exhaustive (padTo 0 s.val) (Dim_padTo_width hw)
          rw [he]
          exact FiniteCorrespondence.ofNat_isOT_zero n
        | succ k =>
          have hlo : width (code s.val) ≤ k + 1 := Nat.le_trans hw (by omega)
          have hs : s.val < dimensionBound k :=
            outer_fit_below (isOT_outer s.property) s.property.dim hlo
          obtain ⟨u, hu⟩ := DimensionCut.isOT_below_dimensionBound s.property hs
          have hc : code u.val = code s.val := by rw [← hu, code_padTo]
          have hwu : width (code u.val) ≤ lam := by rw [hc]; exact hw
          have h := ih (k + 1) (by omega) lam u hwu
          rwa [padTo_congr hc] at h

noncomputable def coordinateWitness (q : Classes) : AllOT :=
  ⟨width (representative q), padTo (width (representative q)) (dimensionWitness q).2.val,
    generated_reify _ _ (dimensionWitness q).2 (Nat.le_of_eq (by rw [representative_spec]))⟩

theorem coordinateWitness_spec (q : Classes) : classOf (coordinateWitness q) = q := by
  apply classCode_injective
  show code (padTo _ (dimensionWitness q).2.val) = classCode q
  rw [code_padTo]
  exact representative_spec q

theorem minDimension_eq_width (q : Classes) : minDimension q = width (representative q) := by
  apply Nat.le_antisymm
  · exact dimensionWitness_minimal q (coordinateWitness q) (coordinateWitness_spec q)
  · have h := width_code_le (dimensionWitness q).2.property.dim
    rw [representative_spec q] at h
    exact h

end kumakuma.CodeReification

namespace kumakuma.DimensionImage

open OCF.Jaeger kumakuma.OTQuotient kumakuma.BinaryTranslation

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

end kumakuma.DimensionImage

namespace kumakuma.TargetIndexCuts

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

end kumakuma.TargetIndexCuts

namespace kumakuma.DimensionImage

open OCF.Jaeger kumakuma.OTQuotient kumakuma.BinaryTranslation
open kumakuma.DimensionCut kumakuma.TargetIndexCuts

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

end kumakuma.DimensionImage

namespace kumakuma.SourceFundOrder

open multi OTQuotient DimensionCut

theorem domOmega_fund_ne_zero : ∀ (s t : multi.T) {v : V multi.T}, domF s = .Omega v →
    T.fund s t ≠ .Z
  | .Z, _, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, t, v, hd => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hc : domF (V.get0 xs i) with
        | zero => rw [fund_zero hf hc]; intro h; cases h
        | omega => rw [fund_omega hf hc]; intro h; cases h
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m => rw [fund_one_succ hf hc]; intro h; cases h
        | Omega q =>
          by_cases hq : xs < q
          · rw [fund_diag hf hc hq]; intro h; cases h
          · rw [fund_nondiag hf hc hq]; intro h; cases h
    · rw [fund_tail xs hb]; intro h; cases h

theorem iter_ofNat_succ (F : multi.T → multi.T) (lam n : Nat) :
    multi.T.iter F (ofNatD lam (n + 1)) = F (multi.T.iter F (ofNatD lam n)) := rfl

theorem domOmega_iter_lt_next (s : multi.T) {v : V multi.T} (hd : domF s = .Omega v) (lam : Nat) :
    ∀ n : Nat, multi.T.iter (T.fund s) (ofNatD lam n) <
      multi.T.iter (T.fund s) (ofNatD lam (n + 1))
  | 0 => by
    show multi.T.Z < T.fund s (multi.T.iter (T.fund s) .Z)
    exact T.Z_lt_of_ne (domOmega_fund_ne_zero s _ hd)
  | n + 1 => by
    rw [iter_ofNat_succ _ lam (n + 1), iter_ofNat_succ _ lam n]
    exact fund_mono s hd _ _ (domOmega_iter_lt_next s hd lam n)

theorem mul_principal_ofNat_succ (xs : V multi.T) (lam n : Nat) :
    multi.T.mul (.P xs .Z) (ofNatD lam (n + 1)) = .P xs (multi.T.mul (.P xs .Z) (ofNatD lam n)) :=
  rfl

theorem mul_principal_ofNat_lt_next (xs : V multi.T) (lam : Nat) :
    ∀ n : Nat, multi.T.mul (.P xs .Z) (ofNatD lam n) < multi.T.mul (.P xs .Z) (ofNatD lam (n + 1))
  | 0 => T.Z_lt_P _ _
  | n + 1 => by
    rw [mul_principal_ofNat_succ xs lam n, mul_principal_ofNat_succ xs lam (n + 1)]
    exact T.P_tail_lt xs (mul_principal_ofNat_lt_next xs lam n)

theorem countable_fund_lt_next : ∀ (s : multi.T), domF s = .omega → ∀ (lam n : Nat),
    T.fund s (ofNatD lam n) < T.fund s (ofNatD lam (n + 1))
  | .Z, hd, _, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, hd, lam, n => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · have hil := fnz_lt_length hf
        have hn : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
        cases hc : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hc) hn
        | one =>
          cases i with
          | zero =>
            rw [fund_one_zero hf hc, fund_one_zero hf hc]
            exact mul_principal_ofNat_lt_next _ lam n
          | succ m => rw [domF_one_succ hf hc] at hd; cases hd
        | omega =>
          rw [fund_omega hf hc, fund_omega hf hc]
          exact T.P_lt_P_of_vlt _ _
            (set_lt_set hil (countable_fund_lt_next _ hc lam n))
        | Omega q =>
          by_cases hq : xs < q
          · rw [fund_diag hf hc hq, fund_diag hf hc hq]
            exact T.P_lt_P_of_vlt _ _ (set_lt_set hil
              (fund_mono _ hc _ _ (domOmega_iter_lt_next _ hc lam n)))
          · rw [domF_nondiag hf hc hq] at hd; cases hd
    · rw [domF_tail xs hb] at hd
      rw [fund_tail xs hb, fund_tail xs hb]
      exact T.P_tail_lt xs (countable_fund_lt_next b hd lam n)
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem dom_one_fund_constant (s : multi.T) (hd : domF s = .one) (t u : multi.T) :
    T.fund s t = T.fund s u := by
  rw [fund_dom_one s hd t, fund_dom_one s hd u]

end kumakuma.SourceFundOrder

namespace kumakuma.DimensionImage

open OCF.Jaeger kumakuma.OTQuotient kumakuma.BinaryTranslation

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

end kumakuma.DimensionImage

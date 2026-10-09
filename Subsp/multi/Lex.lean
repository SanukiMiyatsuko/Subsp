import Subsp.multi.Base

/-! Source-side order infrastructure shared by the multi-variable systems.

Vectors are compared through their coordinates `get0`: two vectors are
equivalent when all coordinates are equivalent, and `v < w` holds exactly when
there is a pivot coordinate below which nothing matters, above which the
coordinates agree, and at which `v` is smaller. -/

namespace multi

open T

/-! ### Basic order facts -/

theorem T.eqv_refl (a : T) : compareT a a = .eq := compareT_self a

theorem T.eqv_symm {a b : T} (h : compareT a b = .eq) : compareT b a = .eq :=
  (compareT_eq_iff b a).2 ((compareT_eq_iff a b).1 h).symm

theorem T.eqv_trans {a b c : T} (h1 : compareT a b = .eq) (h2 : compareT b c = .eq) :
    compareT a c = .eq :=
  (compareT_cons a b c).2.2.2 h1 h2

theorem T.lt_of_lt_of_eqv {a b c : T} (h1 : a < b) (h2 : compareT b c = .eq) : a < c :=
  (compareT_cons a b c).2.1 h1 h2

theorem T.lt_of_eqv_of_lt {a b c : T} (h1 : compareT a b = .eq) (h2 : b < c) : a < c :=
  (compareT_cons a b c).2.2.1 h1 h2

theorem T.lt_of_lt_of_le {a b c : T} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  rcases h2 with h2 | h2
  · exact T.lt_trans h1 h2
  · exact T.lt_of_lt_of_eqv h1 h2

theorem T.lt_of_le_of_lt {a b c : T} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  rcases h1 with h1 | h1
  · exact T.lt_trans h1 h2
  · exact T.lt_of_eqv_of_lt h1 h2

theorem T.le_of_lt {a b : T} (h : a < b) : a ≤ b := Or.inl h

theorem T.le_of_eqv {a b : T} (h : compareT a b = .eq) : a ≤ b := Or.inr h

theorem T.not_lt_Z (a : T) : ¬ a < Z := by
  intro h
  have h : compareT a Z = .lt := h
  cases a with
  | Z => rw [compareT_ZZ] at h; cases h
  | P _ _ => rw [compareT_PZ] at h; cases h

theorem T.Z_lt_P (v : V T) (a : T) : Z < P v a := compareT_ZP v a

theorem T.Z_le (a : T) : Z ≤ a := by
  cases a with
  | Z => exact Or.inr compareT_ZZ
  | P v b => exact Or.inl (compareT_ZP v b)

theorem T.eqv_Z_iff {a : T} : compareT a Z = .eq ↔ a = Z := by
  rw [compareT_eq_iff]
  constructor
  · intro h; exact T.norm_eq_Z.1 (by simpa [T.norm] using h)
  · intro h; subst h; rfl

theorem T.Z_lt_of_ne {a : T} (h : a ≠ Z) : Z < a := by
  cases a with
  | Z => exact absurd rfl h
  | P v b => exact compareT_ZP v b

theorem T.ne_Z_of_lt {a b : T} (h : a < b) : b ≠ Z := by
  intro hb; subst hb; exact T.not_lt_Z a h

theorem T.lt_or_eqv_of_le {a b : T} (h : a ≤ b) : a < b ∨ compareT a b = .eq := h

theorem T.le_of_not_lt {a b : T} (h : ¬ a < b) : b ≤ a := T.not_lt.1 h

theorem T.P_lt_P_iff (v w : V T) (a b : T) :
    P v a < P w b ↔ v < w ∨ (compareV v w = .eq ∧ a < b) := by
  show compareT (P v a) (P w b) = .lt ↔ compareV v w = .lt ∨ (_ ∧ compareT a b = .lt)
  rw [compareT_PP]
  cases compareV v w <;> simp [Ordering.then]

theorem T.P_lt_P_of_vlt {v w : V T} (a b : T) (h : v < w) : P v a < P w b :=
  (T.P_lt_P_iff v w a b).2 (Or.inl h)

theorem T.P_lt_P_of_eqv {v w : V T} {a b : T} (hv : compareV v w = .eq) (h : a < b) :
    P v a < P w b :=
  (T.P_lt_P_iff v w a b).2 (Or.inr ⟨hv, h⟩)

theorem T.P_tail_lt (v : V T) {a b : T} (h : a < b) : P v a < P v b :=
  T.P_lt_P_of_eqv (compareV_self v) h

theorem T.P_eqv_iff (v w : V T) (a b : T) :
    compareT (P v a) (P w b) = .eq ↔ compareV v w = .eq ∧ compareT a b = .eq := by
  rw [compareT_PP, Ordering.then_eq_eq]

theorem T.P_le_P_iff (v w : V T) (a b : T) :
    P v a ≤ P w b ↔ v < w ∨ (compareV v w = .eq ∧ a ≤ b) := by
  show (P v a < P w b ∨ compareT (P v a) (P w b) = .eq) ↔ _
  rw [T.P_lt_P_iff, T.P_eqv_iff]
  constructor
  · rintro ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr h2⟩
  · rintro (h | ⟨h1, h2 | h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr ⟨h1, h2⟩

theorem T.P_tail_le (v : V T) {a b : T} (h : a ≤ b) : P v a ≤ P v b :=
  (T.P_le_P_iff v v a b).2 (Or.inr ⟨compareV_self v, h⟩)

theorem V.lt_of_lt_of_eqv {a b c : V T} (h1 : a < b) (h2 : compareV b c = .eq) : a < c :=
  (compareV_cons a b c).2.1 h1 h2

theorem V.lt_of_eqv_of_lt {a b c : V T} (h1 : compareV a b = .eq) (h2 : b < c) : a < c :=
  (compareV_cons a b c).2.2.1 h1 h2

theorem V.eqv_symm {a b : V T} (h : compareV a b = .eq) : compareV b a = .eq :=
  (compareV_eq_iff b a).2 ((compareV_eq_iff a b).1 h).symm

theorem V.eqv_trans {a b c : V T} (h1 : compareV a b = .eq) (h2 : compareV b c = .eq) :
    compareV a c = .eq :=
  (compareV_cons a b c).2.2.2 h1 h2

/-! ### Coordinatewise lexicographic comparison -/

/-- Compare two coordinate functions on the indices below `k`, the highest index first. -/
def cmpUpTo (f g : Nat → T) : Nat → Ordering
  | 0 => .eq
  | k + 1 => (compareT (f k) (g k)).then (cmpUpTo f g k)

theorem cmpUpTo_congr {f f' g g' : Nat → T} :
    ∀ k : Nat, (∀ j, j < k → f j = f' j) → (∀ j, j < k → g j = g' j) →
      cmpUpTo f g k = cmpUpTo f' g' k
  | 0, _, _ => rfl
  | k + 1, hf, hg => by
    simp only [cmpUpTo]
    rw [hf k (Nat.lt_succ_self k), hg k (Nat.lt_succ_self k),
      cmpUpTo_congr k (fun j hj => hf j (Nat.lt_succ_of_lt hj))
        (fun j hj => hg j (Nat.lt_succ_of_lt hj))]

theorem cmpUpTo_zeros (f g : Nat → T) (k : Nat) :
    ∀ m : Nat, (∀ j, k ≤ j → f j = Z) → (∀ j, k ≤ j → g j = Z) →
      cmpUpTo f g (k + m) = cmpUpTo f g k
  | 0, _, _ => rfl
  | m + 1, hf, hg => by
    rw [show k + (m + 1) = (k + m) + 1 from rfl, cmpUpTo,
      hf (k + m) (Nat.le_add_right k m), hg (k + m) (Nat.le_add_right k m), compareT_ZZ,
      cmpUpTo_zeros f g k m hf hg]
    rfl

theorem cmpUpTo_eq_iff (f g : Nat → T) :
    ∀ k : Nat, cmpUpTo f g k = .eq ↔ ∀ j, j < k → compareT (f j) (g j) = .eq
  | 0 => by simp [cmpUpTo]
  | k + 1 => by
    rw [cmpUpTo, Ordering.then_eq_eq, cmpUpTo_eq_iff f g k]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h | h
      · exact h2 j h
      · subst h; exact h1
    · intro h
      exact ⟨h k (Nat.lt_succ_self k), fun j hj => h j (Nat.lt_succ_of_lt hj)⟩

theorem cmpUpTo_lt_iff (f g : Nat → T) :
    ∀ k : Nat, cmpUpTo f g k = .lt ↔
      ∃ i, i < k ∧ (∀ j, i < j → j < k → compareT (f j) (g j) = .eq) ∧ f i < g i
  | 0 => by
    simp only [cmpUpTo, reduceCtorEq, false_iff]
    rintro ⟨i, hi, _⟩
    exact Nat.not_lt_zero i hi
  | k + 1 => by
    rw [cmpUpTo]
    constructor
    · intro h
      cases hc : compareT (f k) (g k) with
      | lt => exact ⟨k, Nat.lt_succ_self k, fun j hkj hj => absurd hj (by omega), hc⟩
      | gt => rw [hc] at h; cases h
      | eq =>
        rw [hc] at h
        obtain ⟨i, hi, heq, hlt⟩ := (cmpUpTo_lt_iff f g k).1 h
        refine ⟨i, Nat.lt_succ_of_lt hi, fun j hij hj => ?_, hlt⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h' | h'
        · exact heq j hij h'
        · subst h'; exact hc
    · rintro ⟨i, hi, heq, hlt⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h' | h'
      · rw [heq k h' (Nat.lt_succ_self k)]
        exact (cmpUpTo_lt_iff f g k).2 ⟨i, h', fun j hij hj => heq j hij (Nat.lt_succ_of_lt hj), hlt⟩
      · subst h'
        have hlt : compareT (f i) (g i) = .lt := hlt
        rw [hlt]; rfl

theorem V.get0_snoc_top (a : T) (ax : V T) : V.get0 (.snoc a ax) ax.length = a := by
  simp [V.get0]

theorem V.get0_snoc_low (a : T) (ax : V T) (j : Nat) (hj : j < ax.length) :
    V.get0 (.snoc a ax) j = V.get0 ax j := by
  simp [V.get0, Nat.ne_of_lt hj]

theorem V.trim_eq_self_top {v : V T} (hv : V.trim v = v) (hpos : 0 < v.length) :
    V.get0 v (v.length - 1) ≠ Z := by
  cases v with
  | emp => exact absurd hpos (Nat.lt_irrefl 0)
  | snoc a ax =>
    have hne := V.trim_snoc_ne hv
    simp only [V.length, Nat.add_sub_cancel]
    rw [V.get0_snoc_top]
    exact hne

theorem compareV'_same_length :
    ∀ (a b : V T), a.length = b.length →
      compareV' a b = cmpUpTo (V.get0 a) (V.get0 b) a.length
  | .emp, .emp, _ => by rw [compareV'_ee]; rfl
  | .emp, .snoc _ _, h => absurd h.symm (Nat.succ_ne_zero _)
  | .snoc _ _, .emp, h => absurd h (Nat.succ_ne_zero _)
  | .snoc x ax, .snoc y bx, h => by
    simp only [V.length, Nat.add_right_cancel_iff] at h
    rw [compareV'_ss, compareV'_same_length ax bx h]
    simp only [V.length, cmpUpTo, V.get0_snoc_top]
    rw [show V.get0 (.snoc y bx) ax.length = y by rw [h]; exact V.get0_snoc_top y bx]
    congr 1
    apply cmpUpTo_congr
    · intro j hj; exact (V.get0_snoc_low x ax j hj).symm
    · intro j hj; rw [h] at hj; exact (V.get0_snoc_low y bx j hj).symm

theorem cmpUpTo_trimmed (a b : V T) (ha : V.trim a = a) (hb : V.trim b = b)
    (N : Nat) (hNa : a.length ≤ N) (hNb : b.length ≤ N) :
    (lenCmp a.length b.length).then (compareV' a b) = cmpUpTo (V.get0 a) (V.get0 b) N := by
  rcases Nat.lt_trichotomy a.length b.length with hab | hab | hab
  · rw [lenCmp_of_lt hab]
    obtain ⟨m, hm⟩ : ∃ m, N = b.length + m := ⟨N - b.length, by omega⟩
    rw [hm, cmpUpTo_zeros _ _ _ m (fun j hj => V.get0_ge a j (by omega))
      (fun j hj => V.get0_ge b j hj)]
    obtain ⟨k, hk⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by omega⟩
    have htop := V.trim_eq_self_top hb (by omega)
    rw [hk] at htop ⊢
    simp only [Nat.add_sub_cancel] at htop
    rw [cmpUpTo, V.get0_ge a k (by omega)]
    cases hbk : V.get0 b k with
    | Z => exact absurd hbk htop
    | P _ _ => rw [compareT_ZP]; rfl
  · rw [lenCmp_of_eq hab, compareV'_same_length a b hab]
    obtain ⟨m, hm⟩ : ∃ m, N = a.length + m := ⟨N - a.length, by omega⟩
    rw [hm, cmpUpTo_zeros _ _ _ m (fun j hj => V.get0_ge a j hj)
      (fun j hj => V.get0_ge b j (by omega))]
    rfl
  · rw [lenCmp_of_gt hab]
    obtain ⟨m, hm⟩ : ∃ m, N = a.length + m := ⟨N - a.length, by omega⟩
    rw [hm, cmpUpTo_zeros _ _ _ m (fun j hj => V.get0_ge a j hj)
      (fun j hj => V.get0_ge b j (by omega))]
    obtain ⟨k, hk⟩ : ∃ k, a.length = k + 1 := ⟨a.length - 1, by omega⟩
    have htop := V.trim_eq_self_top ha (by omega)
    rw [hk] at htop ⊢
    simp only [Nat.add_sub_cancel] at htop
    rw [cmpUpTo, V.get0_ge b k (by omega)]
    cases hak : V.get0 a k with
    | Z => exact absurd hak htop
    | P _ _ => rw [compareT_PZ]; rfl

/-- The vector comparison as a coordinatewise lexicographic comparison. -/
theorem compareV_eq_cmpUpTo (a b : V T) (N : Nat) (hNa : a.length ≤ N) (hNb : b.length ≤ N) :
    compareV a b = cmpUpTo (V.get0 a) (V.get0 b) N := by
  rw [compareV_eq, cmpUpTo_trimmed (V.trim a) (V.trim b) (V.trim_trim a) (V.trim_trim b) N
    (Nat.le_trans (V.length_trim_le a) hNa) (Nat.le_trans (V.length_trim_le b) hNb)]
  apply cmpUpTo_congr
  · intro j _; exact V.get0_trim a j
  · intro j _; exact V.get0_trim b j

theorem V.eqv_iff_get0 (a b : V T) :
    compareV a b = .eq ↔ ∀ j, compareT (V.get0 a j) (V.get0 b j) = .eq := by
  rw [compareV_eq_cmpUpTo a b (a.length + b.length) (Nat.le_add_right _ _)
    (Nat.le_add_left _ _), cmpUpTo_eq_iff]
  constructor
  · intro h j
    by_cases hj : j < a.length + b.length
    · exact h j hj
    · rw [V.get0_ge a j (by omega), V.get0_ge b j (by omega)]; exact compareT_ZZ
  · intro h j _; exact h j

/-- The pivot characterization of the vector order. -/
theorem V.lt_iff_pivot (a b : V T) :
    a < b ↔ ∃ i, (∀ j, i < j → compareT (V.get0 a j) (V.get0 b j) = .eq) ∧
      V.get0 a i < V.get0 b i := by
  show compareV a b = .lt ↔ _
  rw [compareV_eq_cmpUpTo a b (a.length + b.length) (Nat.le_add_right _ _)
    (Nat.le_add_left _ _), cmpUpTo_lt_iff]
  constructor
  · rintro ⟨i, _, heq, hlt⟩
    refine ⟨i, fun j hij => ?_, hlt⟩
    by_cases hj : j < a.length + b.length
    · exact heq j hij hj
    · rw [V.get0_ge a j (by omega), V.get0_ge b j (by omega)]; exact compareT_ZZ
  · rintro ⟨i, heq, hlt⟩
    refine ⟨i, ?_, fun j hij _ => heq j hij, hlt⟩
    apply Nat.lt_of_not_le
    intro hi
    rw [V.get0_ge b i (by omega)] at hlt
    exact T.not_lt_Z _ hlt

theorem V.lt_of_pivot {a b : V T} (i : Nat)
    (heq : ∀ j, i < j → compareT (V.get0 a j) (V.get0 b j) = .eq)
    (hlt : V.get0 a i < V.get0 b i) : a < b :=
  (V.lt_iff_pivot a b).2 ⟨i, heq, hlt⟩

/-! ### Coordinates after `set` and the first nonzero coordinate -/

theorem V.get0_set_same (v : V T) (i : Nat) (x : T) (hi : i < v.length) :
    V.get0 (V.set v i x) i = x := by
  rw [V.get0_set v i x i hi]; simp

theorem V.get0_set_ne (v : V T) (i : Nat) (x : T) (j : Nat) (hj : j ≠ i) :
    V.get0 (V.set v i x) j = V.get0 v j := by
  by_cases hi : i < v.length
  · rw [V.get0_set v i x j hi]; simp [hj]
  · have hs : ∀ (w : V T), ¬ i < w.length → V.set w i x = w := by
      intro w
      induction w with
      | emp => intro _; rfl
      | snoc b bx ih =>
        intro hw
        simp only [V.length] at hw
        simp only [V.set, show i ≠ bx.length by omega, ite_false, ih (by omega)]
    rw [hs v hi]

theorem V.fnz_some_spec : ∀ (v : V T) (i : Nat), V.fnz v = some i →
    V.get0 v i ≠ Z ∧ ∀ j, j < i → V.get0 v j = Z
  | .emp, i, h => by simp [V.fnz] at h
  | .snoc a ax, i, h => by
    simp only [V.fnz] at h
    rcases hr : V.fnz ax with _ | k
    · rw [hr] at h
      by_cases ha : a = Z
      · simp [ha] at h
      · simp only [ne_eq, ha, not_false_eq_true, ite_true, Option.some.injEq] at h
        subst h
        refine ⟨by rw [V.get0_snoc_top]; exact ha, fun j hj => ?_⟩
        rw [V.get0_snoc_low a ax j hj]
        have hnone : ∀ (w : V T), V.fnz w = none → ∀ j, V.get0 w j = Z := by
          intro w
          induction w with
          | emp => intro _ j; rfl
          | snoc b bx ih =>
            intro hw j
            simp only [V.fnz] at hw
            rcases hb : V.fnz bx with _ | m
            · rw [hb] at hw
              by_cases hbz : b = Z
              · simp only [V.get0]
                split
                · exact hbz
                · exact ih hb j
              · simp [hbz] at hw
            · rw [hb] at hw; simp at hw
        exact hnone ax hr j
    · rw [hr] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := V.fnz_some_spec ax k hr
      have hk := V.lt_length_of_fnz ax k hr
      refine ⟨by rw [V.get0_snoc_low a ax k hk]; exact h1, fun j hj => ?_⟩
      rw [V.get0_snoc_low a ax j (Nat.lt_trans hj hk)]
      exact h2 j hj

theorem V.fnz_none_spec : ∀ (v : V T), V.fnz v = none → ∀ j, V.get0 v j = Z
  | .emp, _, j => rfl
  | .snoc b bx, hw, j => by
    simp only [V.fnz] at hw
    rcases hb : V.fnz bx with _ | m
    · rw [hb] at hw
      by_cases hbz : b = Z
      · simp only [V.get0]
        split
        · exact hbz
        · exact V.fnz_none_spec bx hb j
      · simp [hbz] at hw
    · rw [hb] at hw; simp at hw

/-! ### Sizes -/

theorem V.size_get0_lt_of_ne (v : V T) (i : Nat) (add : T) :
    (V.get0 v i).size < (P v add).size := T.size_get0_lt_P v i add

/-! ### Heads -/

/-- The leading summand of a term. -/
def T.hd : T → T
  | Z => Z
  | P v _ => P v Z

theorem T.hd_le_self (s : T) : T.hd s ≤ s := by
  cases s with
  | Z => exact T.le_refl Z
  | P v a => exact T.P_tail_le v (T.Z_le a)

theorem T.hd_mono {a b : T} (h : a < b) : T.hd a ≤ T.hd b := by
  cases a with
  | Z => exact T.Z_le _
  | P v x =>
    cases b with
    | Z => exact absurd h (T.not_lt_Z _)
    | P w y =>
      rcases (T.P_lt_P_iff v w x y).1 h with h | ⟨h, _⟩
      · exact Or.inl (T.P_lt_P_of_vlt Z Z h)
      · exact Or.inr ((T.P_eqv_iff v w Z Z).2 ⟨h, compareT_ZZ⟩)

theorem T.hd_mono_le {a b : T} (h : a ≤ b) : T.hd a ≤ T.hd b := by
  rcases h with h | h
  · exact T.hd_mono h
  · cases a with
    | Z => exact T.Z_le _
    | P v x =>
      cases b with
      | Z => rw [compareT_PZ] at h; cases h
      | P w y =>
        exact Or.inr ((T.P_eqv_iff v w Z Z).2 ⟨((T.P_eqv_iff v w x y).1 h).1, compareT_ZZ⟩)

/-! ### Sums, multiples and iterates -/

theorem T.P_add (v : V T) (a t : T) : P v a + t = P v (a + t) := rfl

theorem T.Z_add (t : T) : Z + t = t := rfl

theorem T.mul_ofNat_succ (s : T) (n : Nat) : T.mul s (T.ofNat (n + 1)) = s + T.mul s (T.ofNat n) :=
  rfl

theorem T.iter_ofNat_succ (F : T → T) (n : Nat) :
    T.iter F (T.ofNat (n + 1)) = F (T.iter F (T.ofNat n)) := rfl

/-! ### Sizes of normal forms

Proper subterms are never equivalent to the whole term: their normal forms are smaller. -/

/-- The size of the normal form. -/
def T.nsize (x : T) : Nat := (T.norm x).size

theorem T.nsize_get0_lt (v : V T) (j : Nat) (a : T) : T.nsize (V.get0 v j) < T.nsize (P v a) := by
  unfold T.nsize
  rw [T.norm_P, ← V.get0_norm]
  have := V.size_get0_le (V.norm v) j
  simp only [T.size]
  omega

theorem T.nsize_tail_lt (v : V T) (a : T) : T.nsize a < T.nsize (P v a) := by
  unfold T.nsize
  rw [T.norm_P]
  simp only [T.size]
  omega

theorem T.nsize_congr {a b : T} (h : compareT a b = .eq) : T.nsize a = T.nsize b := by
  unfold T.nsize
  rw [(compareT_eq_iff a b).1 h]

theorem T.not_eqv_of_nsize_lt {a b : T} (h : T.nsize a < T.nsize b) : compareT a b ≠ .eq :=
  fun he => Nat.ne_of_lt h (T.nsize_congr he)

/-! ### Moving a pivot comparison to related vectors -/

theorem V.pivot_ge {a b : V T} (h : a < b) (k : Nat)
    (hk : compareT (V.get0 a k) (V.get0 b k) ≠ .eq) :
    ∃ p, k ≤ p ∧ (∀ j, p < j → compareT (V.get0 a j) (V.get0 b j) = .eq) ∧
      V.get0 a p < V.get0 b p := by
  obtain ⟨p, heq, hlt⟩ := (V.lt_iff_pivot a b).1 h
  refine ⟨p, ?_, heq, hlt⟩
  apply Nat.le_of_not_lt
  intro hpk
  exact hk (heq k hpk)

/-- A comparison whose pivot lies at or above `k` transfers to vectors agreeing at and above
`k`. -/
theorem V.lt_transfer {a b a' b' : V T} (h : a < b) (k : Nat)
    (hk : compareT (V.get0 a k) (V.get0 b k) ≠ .eq)
    (ha : ∀ j, k ≤ j → compareT (V.get0 a' j) (V.get0 a j) = .eq)
    (hb : ∀ j, k ≤ j → compareT (V.get0 b' j) (V.get0 b j) = .eq) : a' < b' := by
  obtain ⟨p, hkp, heq, hlt⟩ := V.pivot_ge h k hk
  apply V.lt_of_pivot p
  · intro j hj
    exact T.eqv_trans (ha j (by omega)) (T.eqv_trans (heq j hj) (T.eqv_symm (hb j (by omega))))
  · exact T.lt_of_eqv_of_lt (ha p hkp) (T.lt_of_lt_of_eqv hlt (T.eqv_symm (hb p hkp)))

/-- If `v` vanishes below `i`, a vector below `v` is below every `w` agreeing with `v` above `i`
whose `i`-th coordinate exceeds that of the smaller vector. -/
theorem V.lt_of_zero_below {y v w : V T} (h : y < v) (i : Nat)
    (hz : ∀ j, j < i → V.get0 v j = Z)
    (hw : ∀ j, i < j → compareT (V.get0 w j) (V.get0 v j) = .eq)
    (hi : V.get0 y i < V.get0 w i) : y < w := by
  obtain ⟨p, heq, hlt⟩ := (V.lt_iff_pivot y v).1 h
  have hip : i ≤ p := by
    apply Nat.le_of_not_lt
    intro hp
    rw [hz p hp] at hlt
    exact T.not_lt_Z _ hlt
  rcases Nat.lt_or_eq_of_le hip with hip | rfl
  · apply V.lt_of_pivot p
    · intro j hj; exact T.eqv_trans (heq j hj) (T.eqv_symm (hw j (by omega)))
    · exact T.lt_of_lt_of_eqv hlt (T.eqv_symm (hw p hip))
  · apply V.lt_of_pivot i
    · intro j hj; exact T.eqv_trans (heq j hj) (T.eqv_symm (hw j hj))
    · exact hi

/-- A coordinate below its term stays below after changing coordinates under it only. -/
theorem T.get0_lt_P_of_agree {v v' : V T} {j : Nat} (h : V.get0 v j < P v Z)
    (hv : ∀ m, j ≤ m → compareT (V.get0 v' m) (V.get0 v m) = .eq) : V.get0 v j < P v' Z := by
  cases hx : V.get0 v j with
  | Z => exact T.Z_lt_P _ _
  | P y e =>
    rw [hx] at h
    rcases (T.P_lt_P_iff y v e Z).1 h with hy | ⟨_, he⟩
    · apply T.P_lt_P_of_vlt
      apply V.lt_transfer hy j _ (fun m _ => T.eqv_refl _) hv
      rw [hx]
      exact T.not_eqv_of_nsize_lt (T.nsize_get0_lt y j e)
    · exact absurd he (T.not_lt_Z _)

theorem V.get0_set_eqv_above (v : V T) (i : Nat) (x : T) (j : Nat) (hj : i < j) :
    compareT (V.get0 (V.set v i x) j) (V.get0 v j) = .eq := by
  rw [V.get0_set_ne v i x j (Nat.ne_of_gt hj)]
  exact T.eqv_refl _

theorem T.ofNat_norm : ∀ n : Nat, T.norm (T.ofNat n) = T.ofNat n
  | 0 => rfl
  | n + 1 => by
    rw [T.ofNat, T.norm_P, T.ofNat_norm n]
    rfl

theorem T.rep_ofNat (n : Nat) : (T.rep (T.ofNat n)).1 = T.ofNat n := T.ofNat_norm n

theorem T.lt_norm_iff (a b : T) : a < b ↔ T.norm a < T.norm b := by
  have ha : compareT (T.norm a) a = .eq := (compareT_eq_iff _ _).2 (T.norm_norm a)
  have hb : compareT (T.norm b) b = .eq := (compareT_eq_iff _ _).2 (T.norm_norm b)
  constructor
  · intro h
    exact T.lt_of_eqv_of_lt ha (T.lt_of_lt_of_eqv h (T.eqv_symm hb))
  · intro h
    exact T.lt_of_eqv_of_lt (T.eqv_symm ha) (T.lt_of_lt_of_eqv h hb)

theorem T.le_norm_iff (a b : T) : a ≤ b ↔ T.norm a ≤ T.norm b := by
  show (a < b ∨ compareT a b = .eq) ↔ (T.norm a < T.norm b ∨ compareT (T.norm a) (T.norm b) = .eq)
  rw [T.lt_norm_iff, compareT_eq_iff, compareT_eq_iff, T.norm_norm, T.norm_norm]


/-! ### Vector updates, multiples and appends -/

theorem mul_lt_of_vlt {v' v : V multi.T} (h : v' < v) (t : multi.T) :
    T.mul (P v' Z) t < P v Z := by
  cases t with
  | Z => exact T.Z_lt_P _ _
  | P _ t' => exact T.P_lt_P_of_vlt _ _ h

theorem set_lt {v : V multi.T} {i : Nat} (hi : i < v.length) {x : multi.T} (h : x < V.get0 v i) :
    V.set v i x < v := by
  apply V.lt_of_pivot i
  · intro j hj; exact V.get0_set_eqv_above v i x j hj
  · rw [V.get0_set_same v i x hi]; exact h

theorem vlt_of_P_lt {y v : V multi.T} {e : multi.T} (h : P y e < P v Z) : y < v := by
  rcases (T.P_lt_P_iff y v e Z).1 h with h | ⟨_, h⟩
  · exact h
  · exact absurd h (T.not_lt_Z _)

theorem pivot_above_zero {y v : V multi.T} {i p : Nat} (hzero : ∀ j, j < i → V.get0 v j = Z)
    (hp : V.get0 y p < V.get0 v p) : i ≤ p := by
  apply Nat.le_of_not_lt
  intro h
  rw [hzero p h] at hp
  exact T.not_lt_Z _ hp


theorem V.length_append (u w : V multi.T) : (V.append u w).length = u.length + w.length := by
  induction u with
  | emp => simp [V.append, V.length]
  | snoc a ax ih => simp only [V.append, V.length, ih]; omega

theorem V.get0_append (u w : V multi.T) (j : Nat) :
    V.get0 (V.append u w) j = if j < w.length then V.get0 w j else V.get0 u (j - w.length) := by
  induction u with
  | emp =>
    simp only [V.append]
    by_cases hj : j < w.length
    · simp [hj]
    · simp only [hj, ite_false]; rw [V.get0_ge w j (by omega)]; rfl
  | snoc a ax ih =>
    show (if j = (V.append ax w).length then a else V.get0 (V.append ax w) j) = _
    rw [V.length_append, ih]
    by_cases hj : j < w.length
    · rw [ite_eq_right (show ¬ j = ax.length + w.length by omega), ite_eq_left hj,
        ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj]
      show _ = (if j - w.length = ax.length then a else V.get0 ax (j - w.length))
      by_cases hj' : j = ax.length + w.length
      · rw [ite_eq_left hj', ite_eq_left (show j - w.length = ax.length by omega)]
      · rw [ite_eq_right hj', ite_eq_right (show ¬ j - w.length = ax.length by omega)]

end multi

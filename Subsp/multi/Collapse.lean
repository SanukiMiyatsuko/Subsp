import Subsp.Buchholz.Rank1

/-! Buchholz-side operations shared by the translations of the multi-variable systems.

* `MT.part s` splits a sum into its uncountable prefix (summands `ψ_ν` with `ν ≠ 0`) and its
  countable remainder.
* `MT.collapse s` is the logarithm of `ψ_0(s)`: when `s` has an uncountable prefix `h` and a
  countable remainder `l`, it is `ψ_0(h) + l` with the summands of `l` that are absorbed removed.
* `MT.card n s` multiplies a countable sum `s` by `Ω^n`. -/

namespace MT

open T

/-- Remove the summands of a sum that violate the normal-form head condition. -/
def stand : T → T
  | Z => Z
  | P s0 s1 s2 =>
    if T.head (stand s2) ≤ P s0 s1 Z then P s0 s1 (stand s2) else stand s2

/-- Split a sum into the prefix of positive-index summands and the remainder. -/
def part : T → T × T
  | Z => (Z, Z)
  | P s0 s1 s2 =>
    if s0 = 0 then (Z, P s0 s1 s2)
    else (P s0 s1 (part s2).1, (part s2).2)

/-- The exponent `e` with `ψ_0(s) = ω^e`. -/
def collapse (s : T) : T :=
  if (part s).1 = Z then s else stand (P 0 (part s).1 (part s).2)

/-- `Ω^n` times a sum of index-zero summands. -/
def card (n : Nat) : T → T
  | Z => Z
  | P s0 s1 s2 =>
    match n with
    | 0 => P s0 s1 s2
    | k + 1 =>
      (if s0 = 0 then P 1 (T.add (T.mul (P 1 Z Z) (T.ofNat k)) (collapse s1)) Z
        else P 1 (T.add (T.mul (P 1 Z Z) (T.ofNat (k + 1))) s1) Z) + card (k + 1) s2

/-- `Ω·k + c`. -/
def shift (k : Nat) (c : T) : T := T.add (T.mul (P 1 Z Z) (T.ofNat k)) c

/-! ### Sums -/

theorem add_Z_left (a : T) : T.add Z a = a := rfl

theorem hadd_eq (a b : T) : a + b = T.add a b := rfl

theorem add_assoc (a b c : T) : T.add (T.add a b) c = T.add a (T.add b c) :=
  Rank1Termination.add_assoc a b c

theorem add_self_le (a z : T) : a ≤ T.add a z := by
  induction a with
  | Z => exact T.Z_le z
  | P p x y _ ih =>
    rw [T.P_add_eq]
    exact ih.imp (T.Lt.p_tail _ _ _ _) (congrArg (P p x))

theorem add_left_lt (p : T) {a b : T} (h : a < b) : T.add p a < T.add p b := by
  induction p with
  | Z => exact h
  | P p0 p1 p2 _ ih => rw [T.P_add_eq, T.P_add_eq]; exact T.Lt.p_tail _ _ _ _ ih

theorem add_left_le (p : T) {a b : T} (h : a ≤ b) : T.add p a ≤ T.add p b :=
  h.imp (add_left_lt p) (congrArg (T.add p))

theorem G1_add (u : Nat) (a b : T) : T.G1 u (T.add a b) = T.G1 u a ++ T.G1 u b := by
  induction a with
  | Z => rfl
  | P p x y _ ih =>
    rw [T.P_add_eq]
    by_cases h : u ≤ p <;> simp [T.G1, h, ih, List.append_assoc]

theorem isNF1_add_right {a b : T} (h : T.isNF1 (T.add a b)) : T.isNF1 b := by
  induction a with
  | Z => exact h
  | P a0 a1 a2 _ ih =>
    rw [T.P_add_eq] at h
    exact ih (T.isNF1_P_inv a0 a1 _ h).2.1

theorem isNF1_add_left {a b : T} (h : T.isNF1 (T.add a b)) : T.isNF1 a := by
  induction a with
  | Z => exact T.isNF1.z
  | P a0 a1 a2 _ ih =>
    rw [T.P_add_eq] at h
    obtain ⟨ha1, ht, hg, hh⟩ := T.isNF1_P_inv a0 a1 _ h
    refine T.isNF1.p _ _ _ ha1 (ih ht) hg ?_
    cases a2 with
    | Z => exact T.Z_le _
    | P c0 c1 c2 => simpa [T.head_add_ne_Z] using hh

theorem head_le_self (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P p a b => exact (T.Z_le b).imp (T.Lt.p_tail p a _ _) (congrArg (P p a))

theorem head_add_ne_Z (a b : T) (ha : a ≠ Z) : T.head (T.add a b) = T.head a := by
  cases a with
  | Z => exact absurd rfl ha
  | P p c d => exact T.head_add_ne_Z p c d b

theorem tail_lt_of_NF1 {p : Nat} {a b : T} (h : T.isNF1 (P p a b)) : b < P p a b := by
  rcases T.isNF1_tail_le (P p a b) h p a b rfl with hlt | heq
  · exact hlt
  · exact absurd (congrArg T.size heq) (Nat.ne_of_lt (T.size_lt_size_P_right p a b))

theorem lt_of_not_le {a b : T} (h : ¬ a ≤ b) : b < a := by
  rcases lt_total_thm a b with hab | hba | heq
  · exact absurd (Or.inl hab) h
  · exact hba
  · exact absurd (Or.inr heq) h

theorem lt_add_left_of_size_lt (a b x : T) (ha : a ≠ Z) (hsize : T.size x < T.size a)
    (h : x < T.add a b) : x < a := by
  induction a generalizing x with
  | Z => exact absurd rfl ha
  | P a0 a1 a2 _ ih =>
    rw [T.P_add_eq] at h
    cases h with
    | Z_lt_P => exact T.Lt.Z_lt_P _ _ _
    | p_head _ _ _ _ _ _ h => exact T.Lt.p_head _ _ _ _ _ _ h
    | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
    | p_tail _ _ x2 _ h =>
      have hsz : T.size x2 < T.size a2 := by simp only [T.size] at hsize; omega
      have hne : a2 ≠ Z := by intro he; subst he; exact Nat.not_lt_zero _ hsz
      exact T.Lt.p_tail _ _ _ _ (ih x2 hne hsz h)

/-- Prefixes of a strong normal form are strong normal forms. -/
theorem strong_add_prefix (a b : T) (ha : a ≠ Z) (hnf : T.isNF1 (T.add a b))
    (hg : ∀ x, x ∈ T.G1 0 (T.add a b) → x < T.add a b) :
    T.isNF1 a ∧ ∀ x, x ∈ T.G1 0 a → x < a :=
  ⟨isNF1_add_left hnf, fun x hx => lt_add_left_of_size_lt a b x ha (G1_size_lt 0 a x hx)
    (hg x (by rw [G1_add]; exact List.mem_append_left _ hx))⟩

/-- A term whose summands have index at most `k` and whose level-`k` support lies below it
is below its `ψ_k`-wrapper. -/
theorem lt_wrap (k : Nat) (a b : T) (hi : T.index_Prop1 k a)
    (hg : ∀ x, x ∈ T.G1 k a → x < a) : a < P k a b := by
  cases hi with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p c d hp _ =>
    rcases Nat.eq_or_lt_of_le hp with rfl | hp
    · exact T.Lt.p_mid _ _ _ _ _ (hg c (by simp [T.G1]))
    · exact T.Lt.p_head _ _ _ _ _ _ hp

theorem P0_head_mid_le {a e f : T} (h : T.head (P 0 e f) ≤ P 0 a Z) : e ≤ a := by
  rcases h with h | h
  · cases h with
    | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
    | p_mid _ _ _ _ _ h => exact Or.inl h
    | p_tail _ _ _ _ h => cases h
  · cases h; exact Or.inr rfl

theorem lift_le (p : Nat) {a b : T} (h : a ≤ b) : P p a Z ≤ P p b Z :=
  h.imp (T.Lt.p_mid _ _ _ _ _) (congrArg (fun x => P p x Z))

theorem Z_lt_of_ne {a : T} (h : a ≠ Z) : Z < a := by
  cases a with
  | Z => exact absurd rfl h
  | P _ _ _ => exact T.Lt.Z_lt_P _ _ _

theorem lt_one_eq_Z {x : T} (h : x < P 0 Z Z) : x = Z := by
  cases h with
  | Z_lt_P => rfl
  | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
  | p_mid _ _ _ _ _ h => cases h
  | p_tail _ _ _ _ h => cases h

theorem G1_P_mem {u p : Nat} {c d x : T} (h : u ≤ p) :
    x ∈ T.G1 u (T.P p c d) ↔ x = c ∨ x ∈ T.G1 u c ∨ x ∈ T.G1 u d := by
  simp only [T.G1, h, ite_true, List.mem_append, List.mem_singleton, or_assoc]

theorem G1_one_P0 (c d : T) : T.G1 1 (T.P 0 c d) = T.G1 1 d := by
  simp only [T.G1, show ¬ (1 ≤ 0) from by omega, ite_false]

/-! ### `stand` and `part` -/

theorem stand_of_NF1 {s : T} (hs : T.isNF1 s) : stand s = s := by
  induction hs with
  | z => rw [stand]
  | p s0 s1 s2 _ _ _ hhead _ ih2 => rw [stand, ih2, ite_eq_left hhead]

theorem stand_ne_Z {s : T} (hs : s ≠ Z) : stand s ≠ Z := by
  induction s with
  | Z => exact absurd rfl hs
  | P p a b _ ih =>
    rw [stand]
    split
    · intro h; cases h
    · apply ih
      intro he
      subst b
      exact ‹¬ T.head (stand Z) ≤ P p a Z› (T.Z_le _)

theorem part_add (s : T) : T.add (part s).1 (part s).2 = s := by
  induction s with
  | Z => rfl
  | P p a b _ ih => by_cases hp : p = 0 <;> simp [part, hp, T.P_add_eq, T.add.eq_1, ih]

theorem part_snd_shape (s : T) : (part s).2 = Z ∨ ∃ c d, (part s).2 = P 0 c d := by
  induction s with
  | Z => exact Or.inl rfl
  | P p c d _ ih =>
    by_cases h0 : p = 0
    · subst p; exact Or.inr ⟨c, d, by simp [part]⟩
    · simpa [part, h0] using ih

theorem part_NF1 {s : T} (hs : T.isNF1 s) : T.isNF1 (part s).1 ∧ T.isNF1 (part s).2 := by
  have hnf : T.isNF1 (T.add (part s).1 (part s).2) := (part_add s).symm ▸ hs
  exact ⟨isNF1_add_left hnf, isNF1_add_right hnf⟩

theorem part_snd_index0 {s : T} (hs : T.isNF1 s) : T.index_Prop1 0 (part s).2 := by
  rcases part_snd_shape s with h | ⟨c, d, h⟩
  · rw [h]; exact T.index_Prop1.z
  · have hb := (part_NF1 hs).2
    rw [h] at hb ⊢
    exact isNF1_index 0 0 c d hb (Nat.le_refl 0)

theorem part_fst_fixed (s : T) : part (part s).1 = ((part s).1, Z) := by
  induction s with
  | Z => rfl
  | P p a b _ ih => by_cases hp : p = 0 <;> simp [part, hp, ih]

theorem part_snd_fixed (s : T) : part (part s).2 = (Z, (part s).2) := by
  induction s with
  | Z => rfl
  | P p a b _ ih => by_cases hp : p = 0 <;> simp [part, hp, ih]

theorem part_of_index0 {s : T} (hi : T.index_Prop1 0 s) : part s = (Z, s) := by
  cases hi with
  | z => rfl
  | p p a b hp _ => simp [part, Nat.eq_zero_of_le_zero hp]

theorem part_lt_cases {s t : T} (h : s < t) :
    (part s).1 < (part t).1 ∨ ((part s).1 = (part t).1 ∧ (part s).2 < (part t).2) := by
  induction h with
  | Z_lt_P q u v =>
    rw [part, part]
    split
    · exact Or.inr ⟨rfl, T.Lt.Z_lt_P _ _ _⟩
    · exact Or.inl (T.Lt.Z_lt_P _ _ _)
  | p_head p q x u y v hpq =>
    have hq : q ≠ 0 := by omega
    by_cases hp : p = 0
    · simp only [part, ite_eq_left hp, ite_eq_right hq]
      exact Or.inl (T.Lt.Z_lt_P _ _ _)
    · simp only [part, ite_eq_right hp, ite_eq_right hq]
      exact Or.inl (T.Lt.p_head _ _ _ _ _ _ hpq)
  | p_mid p x u y v h _ =>
    by_cases hp : p = 0
    · simp only [part, ite_eq_left hp]
      exact Or.inr ⟨trivial, T.Lt.p_mid _ _ _ _ _ h⟩
    · simp only [part, ite_eq_right hp]
      exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
  | p_tail p x y v h ih =>
    by_cases hp : p = 0
    · simp only [part, ite_eq_left hp]
      exact Or.inr ⟨trivial, T.Lt.p_tail _ _ _ _ h⟩
    · simp only [part, ite_eq_right hp]
      rcases ih with h | ⟨he, h⟩
      · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
      · exact Or.inr ⟨congrArg (P p x) he, h⟩

theorem lt_of_part_cases {s t : T}
    (h : (part s).1 < (part t).1 ∨ ((part s).1 = (part t).1 ∧ (part s).2 < (part t).2)) :
    s < t := by
  rcases lt_total_thm s t with hst | hts | rfl
  · exact hst
  · have hr := part_lt_cases hts
    rcases h with h | ⟨he, h⟩ <;> rcases hr with hr | ⟨hre, hr⟩
    · exact absurd (lt_trans_thm _ _ _ h hr) (lt_irrefl_thm _)
    · rw [hre] at h; exact absurd h (lt_irrefl_thm _)
    · rw [he] at hr; exact absurd hr (lt_irrefl_thm _)
    · exact absurd (lt_trans_thm _ _ _ h hr) (lt_irrefl_thm _)
  · rcases h with h | ⟨_, h⟩ <;> exact absurd h (lt_irrefl_thm _)

theorem part_fst_le_self (s : T) : (part s).1 ≤ s := by
  by_cases hb : (part s).2 = Z
  · exact Or.inr (by simpa [hb, T.add_Z] using part_add s)
  · apply Or.inl
    apply lt_of_part_cases
    rw [part_fst_fixed]
    refine Or.inr ⟨rfl, ?_⟩
    rcases T.Z_le (part s).2 with h | h
    · exact h
    · exact absurd h.symm hb

theorem part_prefix_upper {s t : T} (h : (part s).1 < (part t).1) : s < (part t).1 := by
  apply lt_of_part_cases
  rw [part_fst_fixed]
  exact Or.inl h

theorem remainder_mid_lt {s c d : T} (hp : (part s).2 = P 0 c d)
    (hg : ∀ x, x ∈ T.G1 0 s → x < s) : c < s := by
  apply hg
  rw [← part_add s, hp, G1_add]
  exact List.mem_append_right _ (by simp [T.G1])

/-! ### Collapse -/

theorem collapse_eq (s : T) (hb : T.isNF1 (part s).2) :
    collapse s = if (part s).1 = Z then (part s).2
      else if T.head (part s).2 ≤ P 0 (part s).1 Z then P 0 (part s).1 (part s).2
      else (part s).2 := by
  rw [collapse]
  by_cases ha : (part s).1 = Z
  · have he : (part s).2 = s := by simpa [ha, T.add] using part_add s
    simp [ha, he]
  · simp [ha, stand, stand_of_NF1 hb]

theorem collapse_Z : collapse T.Z = T.Z := by rw [collapse]; rfl

theorem collapse_ne_Z {s : T} (hs : s ≠ Z) : collapse s ≠ Z := by
  rw [collapse]
  split
  · exact hs
  · exact stand_ne_Z (by intro h; cases h)

theorem collapse_of_index0 {s : T} (hi : T.index_Prop1 0 s) : collapse s = s := by
  rw [collapse, part_of_index0 hi]; rfl

theorem collapse_closed {s : T} (hs : T.isNF1 s) (hg : ∀ x, x ∈ T.G1 0 s → x < s) :
    T.isNF1 (collapse s) ∧ T.index_Prop1 0 (collapse s) := by
  cases s with
  | Z => exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P s0 s1 s2 =>
    by_cases hs0 : s0 = 0
    · subst s0
      have hi := isNF1_index 0 0 s1 s2 hs (Nat.le_refl 0)
      rw [collapse_of_index0 hi]
      exact ⟨hs, hi⟩
    · have hnf2 := (T.isNF1_P_inv s0 s1 s2 hs).2.1
      have hwhole : T.add (P s0 s1 (part s2).1) (part s2).2 = P s0 s1 s2 := by
        simp only [T.P_add_eq, part_add]
      have hpStrong := strong_add_prefix (P s0 s1 (part s2).1) (part s2).2
        (fun h => T.noConfusion h) (hwhole.symm ▸ hs) (hwhole.symm ▸ hg)
      have hbNF := (part_NF1 hnf2).2
      have hbIdx := part_snd_index0 hnf2
      have hec : collapse (P s0 s1 s2) = stand (P 0 (P s0 s1 (part s2).1) (part s2).2) := by
        simp [collapse, part, hs0]
      rw [hec, stand, stand_of_NF1 hbNF]
      split
      · exact ⟨T.isNF1.p _ _ _ hpStrong.1 hbNF hpStrong.2 ‹_›,
          T.index_Prop1.p _ _ _ (Nat.le_refl 0) hbIdx⟩
      · exact ⟨hbNF, hbIdx⟩

theorem collapse_G1_one {s : T} (hs : T.isNF1 s) (hg : ∀ x, x ∈ T.G1 0 s → x < s) :
    ∀ x, x ∈ T.G1 1 (collapse s) → x < collapse s := by
  rw [index_Prop1_G1_empty 0 _ (collapse_closed hs hg).2 1 (by omega)]
  intro x hx; cases hx

theorem collapse_upper {s c : T} (hs : T.isNF1 s) (hg : ∀ x, x ∈ T.G1 0 s → x < s)
    (hsc : s < c) : collapse s < P 0 c Z := by
  have hb : T.isNF1 (part s).2 := (part_NF1 hs).2
  have hbc : (part s).2 < P 0 c Z := by
    rcases part_snd_shape s with h | ⟨e, f, h⟩
    · rw [h]; exact T.Lt.Z_lt_P _ _ _
    · rw [h]; exact T.Lt.p_mid _ _ _ _ _ (lt_trans_thm _ _ _ (remainder_mid_lt h hg) hsc)
  rw [collapse_eq s hb]
  split
  · exact hbc
  · split
    · exact T.Lt.p_mid _ _ _ _ _ (lt_of_le_of_lt_thm T _ _ _ (part_fst_le_self s) hsc)
    · exact hbc

theorem collapse_ge_base {t : T} (ht : T.isNF1 t) (hc : (part t).1 ≠ Z) :
    P 0 (part t).1 Z ≤ collapse t := by
  rw [collapse_eq t (part_NF1 ht).2, ite_eq_right hc]
  split
  · exact head_le_self (P 0 (part t).1 (part t).2)
  · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (lt_of_not_le ‹_›) (head_le_self _))

theorem stand_P0_lt {a b d : T} (hb : T.isNF1 b) (hd : T.isNF1 d) (hpd : part d = (Z, d))
    (hbd : b < d) : stand (P 0 a b) < stand (P 0 a d) := by
  rw [stand, stand_of_NF1 hb, stand, stand_of_NF1 hd]
  by_cases hba : T.head b ≤ P 0 a Z
  · rw [ite_eq_left hba]
    by_cases hda : T.head d ≤ P 0 a Z
    · rw [ite_eq_left hda]
      exact T.Lt.p_tail _ _ _ _ hbd
    · rw [ite_eq_right hda]
      have hshape := part_snd_shape d
      rw [hpd] at hshape
      rcases hshape with h | ⟨f, g, h⟩
      · subst h; exact absurd (T.Z_le _) hda
      · subst h
        have hh : P 0 a Z < P 0 f Z := lt_of_not_le hda
        cases hh with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
        | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
        | p_tail _ _ _ _ h => cases h
  · by_cases hda : T.head d ≤ P 0 a Z
    · exact absurd (partial_order.trans _ _ _ (T.head_mono hbd) hda) hba
    · simpa [hba, hda] using hbd

theorem collapse_lt {s t : T} (hs : T.isNF1 s) (hsg : ∀ x, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t) (hst : s < t) : collapse s < collapse t := by
  rcases part_lt_cases hst with hac | ⟨he, hbd⟩
  · have hc : (part t).1 ≠ Z := by intro h; rw [h] at hac; exact lt_Z_inv hac
    exact lt_of_lt_of_le_thm T _ _ _ (collapse_upper hs hsg (part_prefix_upper hac))
      (collapse_ge_base ht hc)
  · by_cases ha : (part s).1 = Z
    · rw [collapse, ite_eq_left ha, collapse, ite_eq_left (he ▸ ha)]
      exact hst
    · rw [collapse, ite_eq_right ha, collapse, ← he, ite_eq_right ha]
      exact stand_P0_lt (part_NF1 hs).2 (part_NF1 ht).2 (part_snd_fixed t) hbd

theorem collapse_le {s t : T} (hs : T.isNF1 s) (hsg : ∀ x, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t) (hst : s ≤ t) : collapse s ≤ collapse t :=
  hst.imp (collapse_lt hs hsg ht) (congrArg collapse)

/-- The support of a collapse is bounded by the collapsed term. -/
theorem collapse_G1_le {s : T} (hs : T.isNF1 s) (hg : ∀ x, x ∈ T.G1 0 s → x < s) :
    ∀ x, x ∈ T.G1 0 (collapse s) → x ≤ s := by
  intro x hx
  have hb := (part_NF1 hs).2
  have hmem : ∀ x, x ∈ T.G1 0 (part s).1 ++ T.G1 0 (part s).2 → x < s := by
    intro x hx
    apply hg
    rwa [← part_add s, G1_add]
  rw [collapse_eq s hb] at hx
  split at hx
  · exact Or.inl (hmem x (List.mem_append_right _ hx))
  · split at hx
    · simp only [T.G1, Nat.zero_le, ite_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | hx) | hx
      · exact part_fst_le_self s
      · exact Or.inl (hmem x (List.mem_append_left _ hx))
      · exact Or.inl (hmem x (List.mem_append_right _ hx))
    · exact Or.inl (hmem x (List.mem_append_right _ hx))

/-- A finer support bound: every support element of a collapse is the uncountable prefix, a
support element of the prefix, or a support element of the countable remainder. -/
theorem collapse_G1_cases {s : T} (hs : T.isNF1 s) :
    ∀ x, x ∈ T.G1 0 (collapse s) →
      ((part s).1 ≠ Z ∧ x = (part s).1) ∨ x ∈ T.G1 0 (part s).1 ∨ x ∈ T.G1 0 (part s).2 := by
  intro x hx
  rw [collapse_eq s (part_NF1 hs).2] at hx
  split at hx
  · exact Or.inr (Or.inr hx)
  · split at hx
    · simp only [T.G1, Nat.zero_le, ite_true, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | hx) | hx
      · exact Or.inl ⟨‹_›, rfl⟩
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
    · exact Or.inr (Or.inr hx)

/-! ### Shifts `Ω·k + c` -/

theorem shift_zero (c : T) : shift 0 c = c := rfl

theorem shift_succ (k : Nat) (c : T) : shift (k + 1) c = P 1 Z (shift k c) := by
  rw [shift, shift, mul_succ_shape, T.P_add_eq]

theorem shift_head_le (k : Nat) {c : T} (hc : T.index_Prop1 0 c) :
    T.head (shift k c) ≤ P 1 Z Z := by
  cases k with
  | zero =>
    cases hc with
    | z => exact T.Z_le _
    | p p a b hp _ => exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (by omega))
  | succ k => rw [shift_succ]; exact Or.inr rfl

theorem shift_NF (k : Nat) {c : T} (hnf : T.isNF1 c) (hc : T.index_Prop1 0 c) :
    T.isNF1 (shift k c) := by
  induction k with
  | zero => exact hnf
  | succ k ih =>
    rw [shift_succ]
    exact T.isNF1.p _ _ _ T.isNF1.z ih (by intro x hx; cases hx) (shift_head_le k hc)

theorem shift_lt_P1Z (k : Nat) {c : T} (hc : T.index_Prop1 0 c) :
    shift k c < P 1 Z (shift k c) := by
  induction k with
  | zero =>
    cases hc with
    | z => exact T.Lt.Z_lt_P _ _ _
    | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  | succ k ih => rw [shift_succ]; exact T.Lt.p_tail _ _ _ _ ih

theorem shift_G1_one (k : Nat) {c : T} (hc : T.index_Prop1 0 c) :
    ∀ x, x ∈ T.G1 1 (shift k c) → x < shift k c := by
  induction k with
  | zero =>
    simp only [shift_zero, index_Prop1_G1_empty 0 c hc 1 (by omega)]
    intro x hx; cases hx
  | succ k ih =>
    intro x hx
    rw [shift_succ] at hx ⊢
    simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx
    · exact T.Lt.Z_lt_P _ _ _
    · exact lt_trans_thm _ _ _ (ih x hx) (shift_lt_P1Z k hc)

theorem shift_lt_wrap (k : Nat) {c : T} (tail : T) (hc : T.index_Prop1 0 c) :
    shift k c < P 1 (shift k c) tail := by
  cases k with
  | zero =>
    cases hc with
    | z => exact T.Lt.Z_lt_P _ _ _
    | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  | succ k =>
    rw [shift_succ]
    exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)

theorem shift_level_lt : ∀ k l : Nat, k < l → ∀ {x y : T}, T.index_Prop1 0 x →
    shift k x < shift l y := by
  intro k
  induction k with
  | zero =>
    intro l hkl x y hx
    cases l with
    | zero => exact absurd hkl (Nat.lt_irrefl _)
    | succ l =>
      rw [shift_succ, shift_zero]
      cases hx with
      | z => exact T.Lt.Z_lt_P _ _ _
      | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  | succ k ih =>
    intro l hkl x y hx
    cases l with
    | zero => exact absurd hkl (Nat.not_lt_zero _)
    | succ l =>
      rw [shift_succ, shift_succ]
      exact T.Lt.p_tail _ _ _ _ (ih l (Nat.lt_of_succ_lt_succ hkl) hx)

theorem shift_lt_right (k : Nat) {x y : T} (h : x < y) : shift k x < shift k y := by
  induction k with
  | zero => exact h
  | succ k ih => rw [shift_succ, shift_succ]; exact T.Lt.p_tail _ _ _ _ ih

theorem shift_G1_zero (k : Nat) (c : T) :
    ∀ x, x ∈ T.G1 0 (shift k c) → x = Z ∨ x ∈ T.G1 0 c := by
  induction k with
  | zero => exact fun x hx => Or.inr hx
  | succ k ih =>
    intro x hx
    rw [shift_succ] at hx
    simp only [T.G1, Nat.zero_le, ite_true, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact ih x hx

/-! ### Multiplication by `Ω^n` -/

theorem card_zero (c : T) : card 0 c = c := by cases c <;> rfl

theorem card_Z (n : Nat) : card n Z = Z := by cases n <;> rfl

theorem card_P0 (k : Nat) (a b : T) :
    card (k + 1) (P 0 a b) = P 1 (shift k (collapse a)) (card (k + 1) b) := by
  simp [card, shift, hadd_eq, T.P_add_eq, T.add.eq_1]

theorem card_P0_add (k : Nat) (a b y : T) :
    T.add (card (k + 1) (P 0 a b)) y = P 1 (shift k (collapse a)) (T.add (card (k + 1) b) y) := by
  rw [card_P0, T.P_add_eq]

theorem card_ne_Z (n : Nat) {s : T} (hs : s ≠ Z) : card n s ≠ Z := by
  cases s with
  | Z => exact absurd rfl hs
  | P p a b =>
    cases n with
    | zero => intro h; cases h
    | succ n =>
      rw [card]
      split <;> rw [hadd_eq, T.P_add_eq] <;> intro h <;> cases h

theorem card_add (n : Nat) {a : T} (b : T) (ha : T.index_Prop1 0 a) :
    card n (T.add a b) = T.add (card n a) (card n b) := by
  induction ha with
  | z => rw [card_Z]; rfl
  | p p x y hp _ ih =>
    have hp0 : p = 0 := by omega
    subst p
    cases n with
    | zero => rw [card_zero, card_zero, card_zero]
    | succ k => rw [T.P_add_eq, card_P0, card_P0, ih, T.P_add_eq]

/-- Normal form of `Ω^n · c` followed by a smaller summand `y`. -/
theorem card_append_closed (k : Nat) :
    ∀ {c : T} (y : T), T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 y → T.index_Prop1 1 y → (∀ x, x ∈ T.G1 1 y → x < y) →
      (∀ z, T.isNF1 z → T.index_Prop1 0 z → z ≠ Z → y < card (k + 1) z) →
      T.isNF1 (T.add (card (k + 1) c) y) ∧ T.index_Prop1 1 (T.add (card (k + 1) c) y) ∧
        (∀ x, x ∈ T.G1 1 (T.add (card (k + 1) c) y) → x < T.add (card (k + 1) c) y) := by
  intro c y hcNF hcIdx hyNF hyIdx hyG hbound
  induction hcIdx with
  | z => exact ⟨hyNF, hyIdx, hyG⟩
  | p p a b hp hb ih =>
    have hp0 : p = 0 := by omega
    subst p
    obtain ⟨haNF, hbNF, haG, hhead⟩ := T.isNF1_P_inv _ _ _ hcNF
    have hec := collapse_closed haNF haG
    let M := shift k (collapse a)
    let R := T.add (card (k + 1) b) y
    have hr := ih hbNF
    have hheadR : T.head R ≤ P 1 M Z := by
      cases hb with
      | z =>
        have hy := hbound (P 0 a Z) hcNF (T.index_Prop1.p _ _ _ (Nat.le_refl _) T.index_Prop1.z)
          (by intro h; cases h)
        rw [card_P0, card_Z] at hy
        have h2 := T.head_mono hy
        simpa only [R, card_Z, add_Z_left, T.head] using h2
      | p q e f hq _ =>
        have hq0 : q = 0 := by omega
        subst q
        have he := T.isNF1_P_inv _ _ _ hbNF
        simp only [R, card_P0_add, T.head]
        exact lift_le 1 (by
          show shift k (collapse e) ≤ shift k (collapse a)
          rcases collapse_le he.1 he.2.2.1 haNF (P0_head_mid_le hhead) with h | h
          · exact Or.inl (shift_lt_right k h)
          · exact Or.inr (congrArg (shift k) h))
    have hMG := shift_G1_one k hec.2
    have hnf := T.isNF1.p 1 M R (shift_NF k hec.1 hec.2) hr.1 hMG hheadR
    rw [card_P0_add]
    refine ⟨hnf, T.index_Prop1.p _ _ _ (Nat.le_refl _) hr.2.1, ?_⟩
    intro x hx
    have hM := shift_lt_wrap k R hec.2
    simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | hx) | hx
    · exact hM
    · exact lt_trans_thm _ _ _ (hMG x hx) hM
    · exact lt_of_lt_of_le_thm T _ _ _ (hr.2.2 x hx) (T.isNF1_tail_le _ hnf _ _ _ rfl)

theorem card_closed (n : Nat) {c : T} (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) :
    T.isNF1 (card n c) ∧ T.index_Prop1 1 (card n c) ∧
      (∀ x, x ∈ T.G1 1 (card n c) → x < card n c) := by
  cases n with
  | zero =>
    rw [card_zero]
    exact ⟨hcNF, Rank1Termination.index_mono (by omega) _ hcIdx,
      by simp [index_Prop1_G1_empty 0 _ hcIdx 1 (by omega)]⟩
  | succ k =>
    have h := card_append_closed k Z hcNF hcIdx T.isNF1.z T.index_Prop1.z
      (by intro x hx; cases hx) (fun z _ _ hz => Z_lt_of_ne (card_ne_Z _ hz))
    rwa [T.add_Z] at h

/-- Lexicographic comparison of `Ω^n · c + y` against `Ω^n · d + z` when `c < d`. -/
theorem card_append_lt (n : Nat) :
    ∀ {c d : T} (y z : T), T.isNF1 c → T.index_Prop1 0 c → T.isNF1 d → T.index_Prop1 0 d →
      c < d → (∀ q, T.isNF1 q → T.index_Prop1 0 q → q ≠ Z → y < card n q) →
      T.add (card n c) y < T.add (card n d) z := by
  intro c d y z hcNF hcIdx hdNF hdIdx hcd hy
  induction hcd with
  | Z_lt_P q e f =>
    exact lt_of_lt_of_le_thm T _ _ _ (hy _ hdNF hdIdx (by intro h; cases h)) (add_self_le _ z)
  | p_head p q a e b f hpq =>
    cases hcIdx; cases hdIdx
    exfalso; omega
  | p_mid p a e b f hae _ =>
    cases hcIdx with
    | p _ _ _ hp _ =>
      have hp0 : p = 0 := by omega
      subst p
      cases n with
      | zero =>
        rw [card_zero, card_zero, T.P_add_eq, T.P_add_eq]
        exact T.Lt.p_mid _ _ _ _ _ hae
      | succ k =>
        rw [card_P0_add, card_P0_add]
        exact T.Lt.p_mid _ _ _ _ _ (shift_lt_right k
          (collapse_lt (T.isNF1_P_inv _ _ _ hcNF).1 (T.isNF1_P_inv _ _ _ hcNF).2.2.1
            (T.isNF1_P_inv _ _ _ hdNF).1 hae))
  | p_tail p a b f hbf ih =>
    cases hcIdx with
    | p _ _ _ hp hb =>
      cases hdIdx with
      | p _ _ _ _ hf =>
        have hr := ih (T.isNF1_P_inv _ _ _ hcNF).2.1 hb (T.isNF1_P_inv _ _ _ hdNF).2.1 hf
        have hp0 : p = 0 := by omega
        subst p
        cases n with
        | zero =>
          rw [card_zero, card_zero] at hr ⊢
          rw [T.P_add_eq, T.P_add_eq]
          exact T.Lt.p_tail _ _ _ _ hr
        | succ k =>
          rw [card_P0_add, card_P0_add]
          exact T.Lt.p_tail _ _ _ _ hr

theorem card_lt (n : Nat) {c d : T} (hc : T.isNF1 c) (hi : T.index_Prop1 0 c)
    (hd : T.isNF1 d) (hj : T.index_Prop1 0 d) (h : c < d) : card n c < card n d := by
  have := card_append_lt n Z Z hc hi hd hj h
    (fun q _ _ hn => Z_lt_of_ne (card_ne_Z n hn))
  rwa [T.add_Z, T.add_Z] at this

theorem card_le (n : Nat) {c d : T} (hc : T.isNF1 c) (hi : T.index_Prop1 0 c)
    (hd : T.isNF1 d) (hj : T.index_Prop1 0 d) (h : c ≤ d) : card n c ≤ card n d :=
  h.imp (card_lt n hc hi hd hj) (congrArg (card n))

/-- A level-`m` block followed by anything is below a nonzero level-`n` block, for `m < n`. -/
theorem card_level_lt {m n : Nat} {c d : T} (y : T) (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ Z) :
    T.add (card m c) y < card n d := by
  cases hcIdx with
  | z => exact absurd rfl hcne
  | p p a b hp _ =>
    cases hdIdx with
    | z => exact absurd rfl hdne
    | p q e f hq _ =>
      have hp0 : p = 0 := by omega
      have hq0 : q = 0 := by omega
      subst p; subst q
      have ha := T.isNF1_P_inv _ _ _ hcNF
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero _)
      | succ l =>
        rw [card_P0]
        cases m with
        | zero =>
          rw [card_zero, T.P_add_eq]
          exact T.Lt.p_head _ _ _ _ _ _ (by omega)
        | succ k =>
          rw [card_P0_add]
          exact T.Lt.p_mid _ _ _ _ _
            (shift_level_lt k l (by omega) (collapse_closed ha.1 ha.2.2.1).2)

/-! ### Shapes below a principal term -/

theorem lt_P_of_head_lt {x : T} {q : Nat} {b : T} (h : T.head x < T.P q b T.Z) :
    x < T.P q b T.Z := by
  cases x with
  | Z => exact T.Lt.Z_lt_P _ _ _
  | P p c d =>
    cases h with
    | p_head _ _ _ _ _ _ h => exact T.Lt.p_head _ _ _ _ _ _ h
    | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
    | p_tail _ _ _ _ h => cases h

theorem shift_decomp_omega : ∀ a : T, T.isNF1 a → a < T.P 1 (T.P 0 T.Z T.Z) T.Z →
    ∃ k e, a = shift k e ∧ T.index_Prop1 0 e
  | .Z, _, _ => ⟨0, T.Z, rfl, T.index_Prop1.z⟩
  | .P p c d, ha, h => by
    cases h with
    | p_head _ _ _ _ _ _ hp =>
      have hp0 : p = 0 := by omega
      subst p
      exact ⟨0, T.P 0 c d, rfl, isNF1_index 0 0 c d ha (Nat.le_refl 0)⟩
    | p_mid _ _ _ _ _ hc =>
      have hcz := lt_one_eq_Z hc
      subst hcz
      obtain ⟨_, hdNF, _, hdh⟩ := T.isNF1_P_inv _ _ _ ha
      have hd : d < T.P 1 (T.P 0 T.Z T.Z) T.Z :=
        lt_P_of_head_lt (lt_of_le_of_lt_thm T _ _ _ hdh (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)))
      obtain ⟨k, e, rfl, he⟩ := shift_decomp_omega d hdNF hd
      exact ⟨k + 1, e, (shift_succ k e).symm, he⟩
    | p_tail _ _ _ _ h => cases h

end MT

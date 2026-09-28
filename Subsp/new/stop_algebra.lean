import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans

/-! Algebraic lemmas for collapse, cardinal operations, and translation vectors. -/

/-! Basic normal-form and support properties. -/

section BasicOperations

open T

/-- A term with index and support bounded at level `k` lies below its `k`-wrapper. -/
theorem bridge_good_index_lt_wrap (k : Nat) (a b : T) (hi : T.index_Prop1 k a)
    (hg : ∀ x : T, x ∈ T.G1 k a → x < a) : a < T.P k a b := by
  cases hi with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p c d hp _ =>
      rcases Nat.eq_or_lt_of_le hp with rfl | hp
      · exact T.Lt.p_mid _ _ _ _ _ (hg c (by simp [T.G1]))
      · exact T.Lt.p_head _ _ _ _ _ _ hp

theorem bridge_stand_eq_self_of_NF1 (s : T) (hs : T.isNF1 s) : T.stand s = s := by
  induction hs with
  | z => rw [T.stand]
  | p s0 s1 s2 hs1 hs2 hG hhead _ ih2 =>
    rw [T.stand, ih2, ite_eq_left hhead]

theorem bridge_lt_add_left_of_size_lt (a b x : T)
    (ha : a ≠ T.Z) (hsize : T.size x < T.size a)
    (h : x < T.add a b) : x < a := by
  induction a generalizing x with
  | Z => exact False.elim (ha rfl)
  | P a0 a1 a2 _ ih =>
      rw [T.P_add_eq] at h
      cases h with
      | Z_lt_P => exact T.Lt.Z_lt_P _ _ _
      | p_head _ _ _ _ _ _ h => exact T.Lt.p_head _ _ _ _ _ _ h
      | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
      | p_tail _ _ x2 _ h =>
          have hsz : T.size x2 < T.size a2 := by simp only [T.size] at hsize; omega
          have hne : a2 ≠ T.Z := by intro he; simp [he, T.size] at hsz
          exact T.Lt.p_tail _ _ _ _ (ih x2 hne hsz h)

theorem bridge_G1_add_eq (u : Nat) (a b : T) :
    T.G1 u (T.add a b) = T.G1 u a ++ T.G1 u b := by
  induction a with
  | Z => rfl
  | P p x y _ ih =>
      rw [T.P_add_eq]
      by_cases h : u ≤ p <;> simp [T.G1, h, ih, List.append_assoc]

 theorem bridge_G1_add_left {u : Nat} (a b x : T) (hx : x ∈ T.G1 u a) :
    x ∈ T.G1 u (T.add a b) := by
  rw [bridge_G1_add_eq]
  exact List.mem_append_left _ hx

 theorem bridge_isNF1_add_inv_right (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 b := by
  induction a with
  | Z => exact h
  | P a0 a1 a2 _ ih =>
      rw [T.P_add_eq] at h
      exact ih (T.isNF1_P_inv a0 a1 _ h).2.1

 theorem bridge_isNF1_add_inv_left (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 a := by
  induction a with
  | Z => exact T.isNF1.z
  | P a0 a1 a2 _ ih =>
      rw [T.P_add_eq] at h
      obtain ⟨ha1, ht, hg, hh⟩ := T.isNF1_P_inv a0 a1 _ h
      refine T.isNF1.p _ _ _ ha1 (ih ht) hg ?_
      cases a2 with
      | Z => exact T.Z_le _
      | P c0 c1 c2 => simpa [T.head_add_ne_Z] using hh

 theorem bridge_strong_add_prefix (a b : T)
    (ha : a ≠ T.Z)
    (hnf : T.isNF1 (T.add a b))
    (hg : ∀ x : T, x ∈ T.G1 0 (T.add a b) → x < T.add a b) :
    T.isNF1 a ∧ ∀ x : T, x ∈ T.G1 0 a → x < a := by
  refine ⟨bridge_isNF1_add_inv_left a b hnf, ?_⟩
  intro x hx
  exact bridge_lt_add_left_of_size_lt a b x ha (G1_size_lt 0 a x hx)
    (hg x (bridge_G1_add_left a b x hx))

 theorem bridge_part_add (s : T) : T.add (T.part s).1 (T.part s).2 = s := by
  induction s with
  | Z => rfl
  | P p a b _ ih =>
      by_cases hp : p = 0 <;> simp [T.part, hp, T.P_add_eq, T.add.eq_1, ih]

theorem bridge_part_second_shape (s a b : T) (hp : T.part s = (a, b)) :
    b = T.Z ∨ ∃ c d : T, b = T.P 0 c d := by
  induction s generalizing a b with
  | Z => cases hp; exact Or.inl rfl
  | P p c d _ ih =>
      by_cases h0 : p = 0
      · rw [T.part, ite_eq_left h0] at hp
        cases hp; subst p
        exact Or.inr ⟨c, d, rfl⟩
      · rw [T.part, ite_eq_right h0] at hp
        have hb : (T.part d).2 = b := congrArg Prod.snd hp
        exact ih (T.part d).1 b (Prod.ext rfl hb)

theorem bridge_part_second_index0 (s a b : T)
    (hs : T.isNF1 s) (hp : T.part s = (a, b)) :
    T.index_Prop1 0 b := by
  have hsum : T.add a b = s := by simpa [hp] using bridge_part_add s
  have hb := bridge_isNF1_add_inv_right a b (hsum.symm ▸ hs)
  rcases bridge_part_second_shape s a b hp with rfl | ⟨c, d, rfl⟩
  · exact T.index_Prop1.z
  · exact isNF1_index 0 0 c d hb (Nat.le_refl 0)

theorem bridge_stand_ne_Z (s : T) (hs : s ≠ T.Z) :
    T.stand s ≠ T.Z := by
  induction s with
  | Z => exact False.elim (hs rfl)
  | P p a b _ ih =>
      rw [T.stand]
      split
      · intro h; cases h
      · apply ih
        intro he
        subst b
        exact ‹¬ T.head (T.stand T.Z) ≤ T.P p a T.Z› (T.Z_le _)

theorem bridge_early_collapse_ne_Z (s : T) (hs : s ≠ T.Z) :
    T.early_collapse s ≠ T.Z := by
  dsimp only [T.early_collapse]
  split
  · exact hs
  · exact bridge_stand_ne_Z _ (by intro h; cases h)

theorem bridge_card_times_ne_Z (n : Nat) (s : T) (hs : s ≠ T.Z) :
    T.card_times n s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P p a b =>
      cases n with
      | zero => intro h; cases h
      | succ n =>
          rw [T.card_times]
          split <;> cases T.card_times (n + 1) b <;> intro h <;> cases h

end BasicOperations

/-! Collapse, cardinal arithmetic, and lexicographic translation. -/

section TranslationAlgebra

open T

theorem bridge_early_collapse_closed (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    T.isNF1 (T.early_collapse s) ∧
      T.index_Prop1 0 (T.early_collapse s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.early_collapse s) → x < T.early_collapse s) := by
  suffices hh : T.isNF1 (T.early_collapse s) ∧ T.index_Prop1 0 (T.early_collapse s) by
    refine ⟨hh.1, hh.2, ?_⟩
    rw [index_Prop1_G1_empty 0 _ hh.2 1 (by omega)]
    simp
  cases s with
  | Z => exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P s0 s1 s2 =>
      by_cases hs0 : s0 = 0
      · subst s0
        simpa [T.early_collapse, T.part] using
          (show T.isNF1 (T.P 0 s1 s2) ∧ T.index_Prop1 0 (T.P 0 s1 s2) from
            ⟨hs, isNF1_index 0 0 s1 s2 hs (Nat.le_refl 0)⟩)
      · rcases hp : T.part s2 with ⟨a, b⟩
        have hsum : T.add a b = s2 := by simpa [hp] using bridge_part_add s2
        let p := T.P s0 s1 a
        have hwhole : T.add p b = T.P s0 s1 s2 := by simp [p, T.P_add_eq, hsum]
        have hnf : T.isNF1 (T.add p b) := hwhole.symm ▸ hs
        have hgood : ∀ x ∈ T.G1 0 (T.add p b), x < T.add p b := hwhole.symm ▸ hg
        have hpStrong := bridge_strong_add_prefix p b (by dsimp [p]; intro h; cases h) hnf hgood
        have hbNF := bridge_isNF1_add_inv_right p b hnf
        have hbIndex := bridge_part_second_index0 s2 a b (T.isNF1_P_inv s0 s1 s2 hs).2.1 hp
        have hec : T.early_collapse (T.P s0 s1 s2) = T.stand (T.P 0 p b) := by
          simp [T.early_collapse, T.part, hs0, hp, p]
        rw [hec, T.stand, bridge_stand_eq_self_of_NF1 b hbNF]
        split
        · exact ⟨T.isNF1.p _ _ _ hpStrong.1 hbNF hpStrong.2 ‹_›,
            T.index_Prop1.p _ _ _ (Nat.le_refl 0) hbIndex⟩
        · exact ⟨hbNF, hbIndex⟩

theorem bridge_add_left_lt (p a b : T) (h : a < b) :
    T.add p a < T.add p b := by
  induction p with
  | Z => exact h
  | P p0 p1 p2 _ ih =>
      rw [T.P_add_eq, T.P_add_eq]
      exact T.Lt.p_tail _ _ _ _ ih

theorem bridge_shift_head_le (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.head (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) ≤
      T.P 1 T.Z T.Z := by
  cases k with
  | zero =>
      cases hc with
      | z => exact T.Z_le _
      | p p a b hp _ => exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (by omega))
  | succ k => rw [mul_succ_shape, T.P_add_eq]; exact Or.inr rfl

theorem bridge_shift_NF (k : Nat) (c : T)
    (hnf : T.isNF1 c) (hc : T.index_Prop1 0 c) :
    T.isNF1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  induction k with
  | zero => exact hnf
  | succ k ih =>
      rw [mul_succ_shape, T.P_add_eq]
      exact T.isNF1.p _ _ _ T.isNF1.z ih (by intro x hx; cases hx) (bridge_shift_head_le k c hc)

theorem bridge_shift_lt_wrap (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 T.Z
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  induction k with
  | zero =>
      cases hc with
      | z => exact T.Lt.Z_lt_P _ _ _
      | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  | succ k ih =>
      rw [mul_succ_shape, T.P_add_eq]
      exact T.Lt.p_tail _ _ _ _ ih

theorem bridge_shift_strong1 (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    ∀ x : T,
      x ∈ T.G1 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) →
      x < T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c := by
  induction k with
  | zero => simp [T.ofNat, T.mul, T.add, index_Prop1_G1_empty 0 c hc 1 (by omega)]
  | succ k ih =>
      intro x hx
      rw [mul_succ_shape, T.P_add_eq] at hx ⊢
      simp [T.G1] at hx
      rcases hx with rfl | hx
      · exact T.Lt.Z_lt_P _ _ _
      · exact lt_trans_thm _ _ _ (ih x hx) (bridge_shift_lt_wrap k c hc)

theorem bridge_part_fst_head_le (s : T) :
    T.head (T.part s).1 ≤ T.head s := by
  cases s with
  | Z => exact Or.inr rfl
  | P p a b =>
      rw [T.part]
      split
      · exact T.Z_le _
      · exact Or.inr rfl

theorem bridge_part_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part s).1 ∧ T.isNF1 (T.part s).2 := by
  have hnf : T.isNF1 (T.add (T.part s).1 (T.part s).2) := (bridge_part_add s).symm ▸ hs
  exact ⟨bridge_isNF1_add_inv_left _ _ hnf, bridge_isNF1_add_inv_right _ _ hnf⟩

theorem part_lt_cases : ∀ s t : T, s < t →
    (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2) := by
  intro s t h
  induction h with
  | Z_lt_P q u v =>
      rw [T.part, T.part]
      split
      · exact Or.inr ⟨rfl, T.Lt.Z_lt_P _ _ _⟩
      · exact Or.inl (T.Lt.Z_lt_P _ _ _)
  | p_head p q x u y v hpq =>
      have hq : q ≠ 0 := by omega
      by_cases hp : p = 0
      · simp only [T.part, ite_eq_left hp, ite_eq_right hq]
        exact Or.inl (T.Lt.Z_lt_P _ _ _)
      · simp only [T.part, ite_eq_right hp, ite_eq_right hq]
        exact Or.inl (T.Lt.p_head _ _ _ _ _ _ hpq)
  | p_mid p x u y v h _ =>
      by_cases hp : p = 0
      · simp only [T.part, ite_eq_left hp]
        exact Or.inr ⟨trivial, T.Lt.p_mid _ _ _ _ _ h⟩
      · simp only [T.part, ite_eq_right hp]
        exact Or.inl (T.Lt.p_mid _ _ _ _ _ h)
  | p_tail p x y v h ih =>
      by_cases hp : p = 0
      · simp only [T.part, ite_eq_left hp]
        exact Or.inr ⟨trivial, T.Lt.p_tail _ _ _ _ h⟩
      · simp only [T.part, ite_eq_right hp]
        rcases ih with h | ⟨he, h⟩
        · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
        · exact Or.inr ⟨congrArg (T.P p x) he, h⟩

theorem bridge_early_collapse_part (s a b : T)
    (hp : T.part s = (a, b)) (hb : T.isNF1 b) :
    T.early_collapse s =
      if a = T.Z then b
      else if T.head b ≤ T.P 0 a T.Z then T.P 0 a b else b := by
  rw [T.early_collapse, hp]
  by_cases ha : a = T.Z
  · have he : b = s := by simpa [hp, ha, T.add] using bridge_part_add s
    simp [ha, he]
  · simp [ha, T.stand, bridge_stand_eq_self_of_NF1 b hb]

theorem bridge_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b _ ih => by_cases hp : p = 0 <;> simp [T.part, hp, ih]

theorem bridge_part_snd_fixed (s : T) :
    T.part (T.part s).2 = (T.Z, (T.part s).2) := by
  induction s with
  | Z => rfl
  | P p a b _ ih => by_cases hp : p = 0 <;> simp [T.part, hp, ih]

theorem bridge_part_lt_of_cases (s t : T)
    (h : (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2)) :
    s < t := by
  rcases lt_total_thm s t with hst | hts | rfl
  · exact hst
  · have hr := part_lt_cases t s hts
    rcases h with h | ⟨he, h⟩ <;> rcases hr with hr | ⟨hre, hr⟩ <;>
      simp_all [show ∀ x : T, ¬ x < x from lt_irrefl_thm, lt_asymm_thm]
  · rcases h with h | ⟨_, h⟩ <;> exact False.elim (lt_irrefl_thm _ h)

theorem bridge_lt_of_not_le (a b : T) (h : ¬ a ≤ b) : b < a := by
  rcases lt_total_thm a b with hab | (hba | heq)
  · exact False.elim (h (Or.inl hab))
  · exact hba
  · exact False.elim (h (Or.inr heq))

theorem bridge_part_prefix_upper (s t : T)
    (h : (T.part s).1 < (T.part t).1) :
    s < (T.part t).1 := by
  apply bridge_part_lt_of_cases
  rw [bridge_part_fst_fixed]
  exact Or.inl h

theorem bridge_insert_lt (a b d : T)
    (hb : T.isNF1 b) (hd : T.isNF1 d)
    (hpb : T.part b = (T.Z, b))
    (hpd : T.part d = (T.Z, d))
    (hbd : b < d) :
    T.stand (T.P 0 a b) < T.stand (T.P 0 a d) := by
  rw [T.stand, bridge_stand_eq_self_of_NF1 b hb, T.stand, bridge_stand_eq_self_of_NF1 d hd]
  by_cases hba : T.head b ≤ T.P 0 a T.Z
  · rw [ite_eq_left hba]
    by_cases hda : T.head d ≤ T.P 0 a T.Z
    · rw [ite_eq_left hda]
      exact T.Lt.p_tail _ _ _ _ hbd
    · rw [ite_eq_right hda]
      rcases bridge_part_second_shape d T.Z d hpd with rfl | ⟨f, g, rfl⟩
      · exact False.elim (hda (T.Z_le _))
      · have hh : T.P 0 a T.Z < T.P 0 f T.Z := bridge_lt_of_not_le _ _ hda
        cases hh with
        | p_head _ _ _ _ _ _ h => exact False.elim (Nat.lt_irrefl _ h)
        | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
        | p_tail _ _ _ _ h => cases h
  · by_cases hda : T.head d ≤ T.P 0 a T.Z
    · exact False.elim (hba (partial_order.trans _ _ _ (T.head_mono hbd) hda))
    · simpa [hba, hda] using hbd

theorem bridge_head_le_self (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P p a b => exact (T.Z_le b).imp (T.Lt.p_tail p a _ _) (congrArg (T.P p a))

theorem bridge_part_fst_le_self (s : T) : (T.part s).1 ≤ s := by
  by_cases hb : (T.part s).2 = T.Z
  · exact Or.inr (by simpa [hb, T.add_Z] using bridge_part_add s)
  · apply Or.inl ∘ bridge_part_lt_of_cases _ _
    rw [bridge_part_fst_fixed]
    refine Or.inr ⟨rfl, ?_⟩
    rcases T.Z_le (T.part s).2 with h | h
    · exact h
    · exact False.elim (hb h.symm)

theorem bridge_mid_mem_G1_zero (a b : T) :
    a ∈ T.G1 0 (T.P 0 a b) := by
  simp [T.G1]

theorem bridge_remainder_member_lt (s a c d : T)
    (hp : T.part s = (a, T.P 0 c d))
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    c < s := by
  apply hg
  rw [← bridge_part_add s, hp, bridge_G1_add_eq]
  exact List.mem_append_right _ (bridge_mid_mem_G1_zero c d)

theorem bridge_early_collapse_upper (s c : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (hsc : s < c) :
    T.early_collapse s < T.P 0 c T.Z := by
  rcases hp : T.part s with ⟨a, b⟩
  have hb : T.isNF1 b := by simpa [hp] using (bridge_part_NF1 s hs).2
  have hbc : b < T.P 0 c T.Z := by
    rcases bridge_part_second_shape s a b hp with rfl | ⟨e, f, rfl⟩
    · exact T.Lt.Z_lt_P _ _ _
    · exact T.Lt.p_mid _ _ _ _ _ (lt_trans_thm _ _ _ (bridge_remainder_member_lt s a e f hp hg) hsc)
  rw [bridge_early_collapse_part s a b hp hb]
  split
  · exact hbc
  · split
    · have has : a ≤ s := by simpa [hp] using bridge_part_fst_le_self s
      exact T.Lt.p_mid _ _ _ _ _ (lt_of_le_of_lt_thm T _ _ _ has hsc)
    · exact hbc

theorem bridge_part_base_le_early_collapse (t : T)
    (ht : T.isNF1 t) (hc : (T.part t).1 ≠ T.Z) :
    T.P 0 (T.part t).1 T.Z ≤ T.early_collapse t := by
  rcases hp : T.part t with ⟨c, d⟩
  have hd : T.isNF1 d := by simpa [hp] using (bridge_part_NF1 t ht).2
  simp only [hp] at hc ⊢
  rw [bridge_early_collapse_part t c d hp hd, ite_eq_right hc]
  split
  · exact bridge_head_le_self (T.P 0 c d)
  · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (bridge_lt_of_not_le _ _ ‹_›) (bridge_head_le_self d))

theorem bridge_early_collapse_lt (s t : T)
    (hs : T.isNF1 s)
    (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
    (hst : s < t) :
    T.early_collapse s < T.early_collapse t := by
  rcases hparts : part_lt_cases s t hst with hac | ⟨he, hbd⟩
  · have hc : (T.part t).1 ≠ T.Z := by intro h; rw [h] at hac; exact lt_Z_inv hac
    exact lt_of_lt_of_le_thm T _ _ _
      (bridge_early_collapse_upper s _ hs hsg (bridge_part_prefix_upper s t hac))
      (bridge_part_base_le_early_collapse t ht hc)
  · by_cases ha : (T.part s).1 = T.Z
    · rw [T.early_collapse, ite_eq_left ha, T.early_collapse, ite_eq_left (he ▸ ha)]
      exact hst
    · rw [T.early_collapse, ite_eq_right ha, T.early_collapse, ← he, ite_eq_right ha]
      exact bridge_insert_lt _ _ _ (bridge_part_NF1 s hs).2 (bridge_part_NF1 t ht).2
        (bridge_part_snd_fixed s) (bridge_part_snd_fixed t) hbd

theorem tc_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c <;> rfl

theorem wt_add_self_le (a z : T) : a ≤ T.add a z := by
  induction a with
  | Z => exact T.Z_le z
  | P p x y _ ih =>
      rw [T.P_add_eq]
      exact ih.imp (T.Lt.p_tail _ _ _ _) (congrArg (T.P p x))

theorem wt_expand_card_succ_add (k : Nat) (a b y : T) :
    T.add (T.card_times (k + 1) (T.P 0 a b)) y =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a))
        (T.add (T.card_times (k + 1) b) y) := by
  simp [T.card_times, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]

theorem wt_card_append_lt (n : Nat) :
    ∀ c d y z : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d →
      (∀ q : T, T.isNF1 q → T.index_Prop1 0 q → q ≠ T.Z →
        y < T.card_times n q) →
      T.add (T.card_times n c) y < T.add (T.card_times n d) z := by
  intro c d y z hcNF hcIdx hdNF hdIdx hcd hy
  induction hcd with
  | Z_lt_P q e f =>
      exact lt_of_lt_of_le_thm T _ _ _ (hy _ hdNF hdIdx (by intro h; cases h)) (wt_add_self_le _ z)
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
              simp only [T.card_times, T.P_add_eq]
              exact T.Lt.p_mid _ _ _ _ _ hae
          | succ k =>
              rw [wt_expand_card_succ_add, wt_expand_card_succ_add]
              exact T.Lt.p_mid _ _ _ _ _ (bridge_add_left_lt _ _ _
                (bridge_early_collapse_lt a e (T.isNF1_P_inv _ _ _ hcNF).1
                  (T.isNF1_P_inv _ _ _ hcNF).2.2.1 (T.isNF1_P_inv _ _ _ hdNF).1 hae))
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
                  simp only [T.card_times, T.P_add_eq]
                  rw [tc_card_times_zero, tc_card_times_zero] at hr
                  exact T.Lt.p_tail _ _ _ _ hr
              | succ k =>
                  rw [wt_expand_card_succ_add, wt_expand_card_succ_add]
                  exact T.Lt.p_tail _ _ _ _ hr

theorem bridge_card_times_lt_same (n : Nat) :
    ∀ c d : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d → T.card_times n c < T.card_times n d := by
  intro c d hc hi hd hj h
  suffices T.add (T.card_times n c) T.Z < T.add (T.card_times n d) T.Z by simpa [T.add_Z] using this
  apply wt_card_append_lt n c d T.Z T.Z hc hi hd hj h
  intro q _ _ hn
  rcases T.Z_le (T.card_times n q) with h | h
  · exact h
  · exact False.elim (bridge_card_times_ne_Z n q hn h.symm)

theorem bridge_shift_level_lt : ∀ k l : Nat, k < l →
    ∀ x y : T, T.index_Prop1 0 x → T.index_Prop1 0 y →
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) x <
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) y := by
  intro k
  induction k with
  | zero =>
      intro l hkl x y hx _
      cases l with
      | zero => exact False.elim (Nat.lt_irrefl _ hkl)
      | succ l =>
          rw [T.ofNat, T.mul, T.add, mul_succ_shape, T.P_add_eq]
          cases hx with
          | z => exact T.Lt.Z_lt_P _ _ _
          | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  | succ k ih =>
      intro l hkl x y hx hy
      cases l with
      | zero => exact False.elim (Nat.not_lt_zero _ hkl)
      | succ l =>
          rw [mul_succ_shape, T.P_add_eq, mul_succ_shape, T.P_add_eq]
          exact T.Lt.p_tail _ _ _ _ (ih l (Nat.lt_of_succ_lt_succ hkl) x y hx hy)

theorem bridge_card_times_add_level_lt (m n : Nat) (c d y : T)
    (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ T.Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ T.Z) :
    T.add (T.card_times m c) y < T.card_times n d := by
  cases hcIdx with
  | z => exact False.elim (hcne rfl)
  | p p a b hp _ =>
      cases hdIdx with
      | z => exact False.elim (hdne rfl)
      | p q e f hq _ =>
          have hp0 : p = 0 := by omega
          have hq0 : q = 0 := by omega
          subst p; subst q
          have ha := T.isNF1_P_inv _ _ _ hcNF
          have he := T.isNF1_P_inv _ _ _ hdNF
          cases n with
          | zero => exact False.elim (Nat.not_lt_zero _ hmn)
          | succ l =>
              cases m with
              | zero =>
                  simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
                  exact T.Lt.p_head _ _ _ _ _ _ (by omega)
              | succ k =>
                  simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
                  exact T.Lt.p_mid _ _ _ _ _ (bridge_shift_level_lt k l (by omega) _ _
                    (bridge_early_collapse_closed a ha.1 ha.2.2.1).2.1
                    (bridge_early_collapse_closed e he.1 he.2.2.1).2.1)

theorem bridge_card_times_level_lt (m n : Nat) (c d : T)
    (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ T.Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ T.Z) :
    T.card_times m c < T.card_times n d := by
  simpa [T.add_Z] using bridge_card_times_add_level_lt m n c d T.Z hmn hcNF hcIdx hcne hdNF hdIdx hdne

theorem bridge_add_left_le (p a b : T) (h : a ≤ b) :
    T.add p a ≤ T.add p b := by
  exact h.imp (bridge_add_left_lt p a b) (congrArg (T.add p))

theorem bridge_shift_lt_outer (k : Nat) (c tail : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail := by
  cases k with
  | zero =>
      cases hc with
      | z => exact T.Lt.Z_lt_P _ _ _
      | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  | succ k =>
      rw [mul_succ_shape, T.P_add_eq]
      exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)

theorem bridge_early_collapse_le (s t : T)
    (hs : T.isNF1 s) (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
    (hst : s ≤ t) : T.early_collapse s ≤ T.early_collapse t := by
  exact hst.imp (bridge_early_collapse_lt s t hs hsg ht) (congrArg T.early_collapse)

theorem bridge_P0_head_mid_le (a e f : T)
    (h : T.head (T.P 0 e f) ≤ T.P 0 a T.Z) : e ≤ a := by
  rcases h with h | h
  · cases h with
    | p_head _ _ _ _ _ _ h => exact False.elim (Nat.lt_irrefl _ h)
    | p_mid _ _ _ _ _ h => exact Or.inl h
    | p_tail _ _ _ _ h => cases h
  · cases h; exact Or.inr rfl

theorem bridge_lift_P1_le (a b : T) (h : a ≤ b) :
    T.P 1 a T.Z ≤ T.P 1 b T.Z := by
  exact h.imp (T.Lt.p_mid _ _ _ _ _) (congrArg (fun x => T.P 1 x T.Z))

theorem bridge_card_times_closed (n : Nat) :
    ∀ c : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 (T.card_times n c) ∧
        T.index_Prop1 1 (T.card_times n c) ∧
        (∀ x : T, x ∈ T.G1 1 (T.card_times n c) →
          x < T.card_times n c) := by
  intro c hcNF hcIdx
  induction hcIdx with
  | z => exact ⟨T.isNF1.z, T.index_Prop1.z, by intro x hx; cases hx⟩
  | p p a b hp hb ih =>
      have hp0 : p = 0 := by omega
      subst p
      obtain ⟨haNF, hbNF, haG, hhead⟩ := T.isNF1_P_inv _ _ _ hcNF
      cases n with
      | zero =>
          have hi := T.index_Prop1.p 0 a b (Nat.le_refl 0) hb
          exact ⟨hcNF, Rank1Termination.index_mono (by omega) _ hi,
            by simp [T.card_times, index_Prop1_G1_empty 0 _ hi 1 (by omega)]⟩
      | succ k =>
          simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
          let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)
          let R := T.card_times (k + 1) b
          have hec := bridge_early_collapse_closed a haNF haG
          have hMG := bridge_shift_strong1 k _ hec.2.1
          have hr := ih hbNF
          have hheadR : T.head R ≤ T.P 1 M T.Z := by
            cases hb with
            | z => exact T.Z_le _
            | p q e f hq _ =>
                have hq0 : q = 0 := by omega
                subst q
                have he := T.isNF1_P_inv _ _ _ hbNF
                simp only [R, T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1, T.head]
                exact bridge_lift_P1_le _ _ (bridge_add_left_le _ _ _
                  (bridge_early_collapse_le e a he.1 he.2.2.1 haNF (bridge_P0_head_mid_le a e f hhead)))
          have hnf := T.isNF1.p 1 M R (bridge_shift_NF k _ hec.1 hec.2.1) hr.1 hMG hheadR
          refine ⟨hnf, T.index_Prop1.p _ _ _ (Nat.le_refl _) hr.2.1, ?_⟩
          intro x hx
          have hM := bridge_shift_lt_outer k _ R hec.2.1
          simp [T.G1] at hx
          rcases hx with rfl | hx | hx
          · exact hM
          · exact lt_trans_thm _ _ _ (hMG x hx) hM
          · exact lt_of_lt_of_le_thm T _ _ _ (hr.2.2 x hx) (T.isNF1_tail_le _ hnf _ _ _ rfl)

theorem bridge_head_add_ne_Z (a b : T) (ha : a ≠ T.Z) :
    T.head (T.add a b) = T.head a := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d => exact T.head_add_ne_Z p c d b

theorem bridge_card_times_succ_append (k : Nat) :
    ∀ c y : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 y → T.index_Prop1 1 y →
      (∀ x : T, x ∈ T.G1 1 y → x < y) →
      (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
        y < T.card_times (k + 1) z) →
      T.isNF1 (T.add (T.card_times (k + 1) c) y) ∧
        T.index_Prop1 1 (T.add (T.card_times (k + 1) c) y) ∧
        (∀ x : T,
          x ∈ T.G1 1 (T.add (T.card_times (k + 1) c) y) →
          x < T.add (T.card_times (k + 1) c) y) := by
  intro c y hcNF hcIdx hyNF hyIdx hyG hbound
  induction hcIdx with
  | z => exact ⟨hyNF, hyIdx, hyG⟩
  | p p a b hp hb ih =>
      have hp0 : p = 0 := by omega
      subst p
      obtain ⟨haNF, hbNF, haG, _⟩ := T.isNF1_P_inv _ _ _ hcNF
      have hec := bridge_early_collapse_closed a haNF haG
      let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)
      let R := T.add (T.card_times (k + 1) b) y
      have hMG := bridge_shift_strong1 k _ hec.2.1
      have hr := ih hbNF
      have hheadR : T.head R ≤ T.P 1 M T.Z := by
        cases b with
        | Z =>
            have hy := hbound (T.P 0 a T.Z) hcNF (T.index_Prop1.p _ _ _ (Nat.le_refl _) hb)
              (by intro h; cases h)
            simpa [T.card_times, ← add_eq_hAdd, T.add_Z, T.add.eq_1, T.head, M, R] using T.head_mono hy
        | P q e f =>
            dsimp only [R]
            rw [bridge_head_add_ne_Z _ y (bridge_card_times_ne_Z _ _ (by intro h; cases h))]
            have hnf := (bridge_card_times_closed (k + 1) _ hcNF (T.index_Prop1.p _ _ _ (Nat.le_refl _) hb)).1
            simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1] at hnf
            exact (T.isNF1_P_inv _ _ _ hnf).2.2.2
      have hnf := T.isNF1.p 1 M R (bridge_shift_NF k _ hec.1 hec.2.1) hr.1 hMG hheadR
      simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
      refine ⟨hnf, T.index_Prop1.p _ _ _ (Nat.le_refl _) hr.2.1, ?_⟩
      intro x hx
      have hM := bridge_shift_lt_outer k _ R hec.2.1
      simp [T.G1] at hx
      rcases hx with rfl | hx | hx
      · exact hM
      · exact lt_trans_thm _ _ _ (hMG x hx) hM
      · exact lt_of_lt_of_le_thm T _ _ _ (hr.2.2 x hx) (T.isNF1_tail_le _ hnf _ _ _ rfl)

theorem bridge_lt_P0ZZ_eq_Z (x : T) (h : x < T.P 0 T.Z T.Z) : x = T.Z := by
  cases h with
  | Z_lt_P => rfl
  | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
  | p_mid _ _ _ _ _ h => cases h
  | p_tail _ _ _ _ h => cases h

-- From AuxBridge.lean

-- From TransCore.lean

theorem tc_trans_P_add {lam : Nat} (ls : new.Vec (new.T lam) lam) (a : new.T lam) :
    trans (new.T.P ls a) = T.add (trans (new.T.P ls new.T.Z)) (trans a) := by
  rw [_root_.trans.eq_2, _root_.trans.eq_2, _root_.trans.eq_1]
  rcases transAux ls with ⟨found, sum, a0⟩
  cases found <;> by_cases h : a0 = T.Z <;> simp [h, T.P_add_eq, T.add.eq_1]

theorem tc_trans_head {lam : Nat} (s : new.T lam) :
    trans (new.T.head s) = T.head (trans s) := by
  cases s with
  | Z => rfl
  | P ls a =>
      rw [new.T.head, _root_.trans.eq_2, _root_.trans.eq_2, _root_.trans.eq_1]
      rcases transAux ls with ⟨found, sum, a0⟩
      cases found <;> by_cases h : a0 = T.Z <;> simp [h, T.head]

-- From AuxCore.lean

theorem tc_trans_ne_Z_of_ne_Z {lam : Nat} (s : new.T lam)
    (hs : s ≠ new.T.Z) : trans s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P ls a =>
      rw [_root_.trans.eq_2]
      rcases transAux ls with ⟨found, sum, a0⟩
      cases found <;> by_cases h : a0 = T.Z <;> simp [h]

theorem tc_Z_lt_of_ne (x : T) (hx : x ≠ T.Z) : T.Z < x := by
  rcases T.Z_le x with h | h
  · exact h
  · exact False.elim (hx h.symm)

theorem tc_add_ne_Z_left (a b : T) (ha : a ≠ T.Z) : a + b ≠ T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d =>
    cases b <;> intro h <;> cases h

theorem co_len1_sum_zero {lam : Nat}
    (v : new.Vec (new.T lam) 1) (f : Bool) (s a0 : T)
    (h : transAux v = (f, s, a0)) : s = T.Z := by
  cases v with
  | snoc _ xs a => cases xs; cases h; rfl

theorem tc_transAux_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 a0 ∧
          (∀ y : T, y ∈ T.G1 0 a0 → y < a0) ∧
          T.isNF1 sum ∧
          T.index_Prop1 1 sum ∧
          (∀ y : T, y ∈ T.G1 1 sum → y < sum) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              sum < T.card_times k c) ∧
          (found = true → sum ≠ T.Z) ∧
          (found = false → sum = T.Z) := by
  intro k
  induction k with
  | zero =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc _ xs a =>
          cases xs; cases haux
          have ha := hcomp a (by simp [new.Vec.toList])
          refine ⟨ha.1, ha.2, T.isNF1.z, T.index_Prop1.z, ?_, ?_, ?_, ?_⟩
          · intro y hy; cases hy
          · intro c _ _ hcne
            simpa [tc_card_times_zero] using tc_Z_lt_of_ne c hcne
          · intro h; cases h
          · intro _; rfl
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc _ xs a =>
          have hrest := fun x hx => hcomp x (List.mem_append_left [a] hx)
          have ha := hcomp a (by simp [new.Vec.toList])
          rcases hxs : transAux xs with ⟨fr, sr, ar⟩
          obtain ⟨har, hGar, hsr, hisr, hGsr, hbound, htrue, hfalse⟩ := ih xs hrest fr sr ar hxs
          rw [transAux.eq_3, hxs] at haux
          cases a with
          | Z =>
              change (fr, sr, ar) = (found, sum, a0) at haux
              cases haux
              refine ⟨har, hGar, hsr, hisr, hGsr, ?_, htrue, hfalse⟩
              intro c hnf hi hn
              exact lt_trans_thm _ _ _ (hbound c hnf hi hn)
                (bridge_card_times_level_lt m (m + 1) c c (by omega) hnf hi hn hnf hi hn)
          | P ls b =>
              have hec := bridge_early_collapse_closed _ ha.1 ha.2
              have hn := bridge_early_collapse_ne_Z _ (tc_trans_ne_Z_of_ne_Z (new.T.P ls b) (by intro h; cases h))
              change (true, T.card_times m (T.early_collapse (trans (new.T.P ls b))) + sr, ar) = (found, sum, a0) at haux
              cases haux
              have hnext := fun c hnf hi hc => bridge_card_times_add_level_lt m (m + 1) _ c sr
                (Nat.lt_succ_self m) hec.1 hec.2.1 hn hnf hi hc
              have hclosed : T.isNF1 (T.card_times m (T.early_collapse (trans (new.T.P ls b))) + sr) ∧
                  T.index_Prop1 1 (T.card_times m (T.early_collapse (trans (new.T.P ls b))) + sr) ∧
                  (∀ x ∈ T.G1 1 (T.card_times m (T.early_collapse (trans (new.T.P ls b))) + sr),
                    x < T.card_times m (T.early_collapse (trans (new.T.P ls b))) + sr) := by
                cases m with
                | zero =>
                    simpa [co_len1_sum_zero xs fr sr a0 hxs, tc_card_times_zero, ← add_eq_hAdd, T.add_Z] using
                      And.intro hec.1 (And.intro (Rank1Termination.index_mono (Nat.zero_le 1) _ hec.2.1) hec.2.2)
                | succ j => exact bridge_card_times_succ_append j _ sr hec.1 hec.2.1 hsr hisr hGsr hbound
              exact ⟨har, hGar, hclosed.1, hclosed.2.1, hclosed.2.2, hnext,
                fun _ => tc_add_ne_Z_left _ sr (bridge_card_times_ne_Z m _ hn), by intro h; cases h⟩

-- From CardAlg.lean

theorem ca_card_times_add (n : Nat) (a b : T) :
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  cases n with
  | zero => simp only [tc_card_times_zero]
  | succ k =>
      induction a with
      | Z => rfl
      | P p x y _ ih =>
          rw [T.P_add_eq, T.card_times.eq_3, T.card_times.eq_3, ih]
          exact (Rank1Termination.add_assoc _ _ _).symm

theorem ca_mul_P1_ofNat_succ (k : Nat) :
    T.add (T.P 1 T.Z T.Z)
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) =
    T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
  rw [mul_succ_shape, T.P_add_eq, T.add.eq_1]

theorem ca_PZ_add (p : Nat) (a b : T) :
    T.P p a T.Z + b = T.P p a b := by
  rw [← add_eq_hAdd, T.P_add_eq, T.add.eq_1]

theorem ca_mul_P1_one :
    T.mul (T.P 1 T.Z T.Z) (T.ofNat 1) = T.P 1 T.Z T.Z := by
  rfl

theorem ca_card_times_one_comp (m : Nat) (c : T) :
    T.card_times 1 (T.card_times m c) = T.card_times (m + 1) c := by
  induction c with
  | Z => rfl
  | P p a b _ ih =>
      cases m with
      | zero => rw [tc_card_times_zero]
      | succ k =>
          rw [T.card_times.eq_3]
          change T.card_times 1 (T.add _ _) = _
          rw [ca_card_times_add, ih]
          by_cases hp : p = 0 <;>
            simp [hp, T.card_times, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1,
              ca_mul_P1_one, ← Rank1Termination.add_assoc] <;>
            simp only [mul_succ_shape, T.P_add_eq]

-- From Weighted.lean

-- From AuxOrder.lean

theorem ao_transAux_lex {lam : Nat} :
    ∀ {k : Nat} (v w : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x : new.T lam, x ∈ new.Vec.toList w →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x y : new.T lam,
        x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
        x < y → trans x < trans y) →
      new.compareVec v w = Ordering.lt →
      ∀ fv fw : Bool, ∀ sv av sw aw : T,
        transAux v = (fv, sv, av) →
        transAux w = (fw, sw, aw) →
        sv < sw ∨ (sv = sw ∧ av < aw) := by
  intro k
  induction k with
  | zero =>
      intro v w _ _ hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | snoc _ xs a =>
          cases xs
          cases w with
          | snoc _ ys b =>
              cases ys; cases hav; cases haw
              apply Or.inr ∘ And.intro rfl
              apply hmono a b (by simp [new.Vec.toList]) (by simp [new.Vec.toList])
              change new.compareT a b = .lt
              cases hc : new.compareT a b <;> simp_all [new.compareVec]
  | succ m ih =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | snoc _ xs a =>
          cases w with
          | snoc _ ys b =>
              have hvr := fun x hx => hv x (List.mem_append_left [a] hx)
              have hwr := fun x hx => hw x (List.mem_append_left [b] hx)
              have ha := hv a (by simp [new.Vec.toList])
              have hb := hw b (by simp [new.Vec.toList])
              have hmr := fun x y hx hy => hmono x y (List.mem_append_left [a] hx) (List.mem_append_left [b] hy)
              rcases hxs : transAux xs with ⟨fx, sx, ax⟩
              rcases hys : transAux ys with ⟨fy, sy, ay⟩
              rw [transAux.eq_3, hxs] at hav
              rw [transAux.eq_3, hys] at haw
              cases hc : new.compareT a b with
              | gt => simp [new.compareVec, hc] at hcmp
              | lt =>
                  have hab := hmono a b (by simp [new.Vec.toList]) (by simp [new.Vec.toList]) hc
                  have hea := bridge_early_collapse_closed _ ha.1 ha.2
                  have heb := bridge_early_collapse_closed _ hb.1 hb.2
                  have hbound := (tc_transAux_inv xs hvr fx sx ax hxs).2.2.2.2.2.1
                  cases hav; cases haw
                  exact Or.inl (wt_card_append_lt m _ _ _ _ hea.1 hea.2.1 heb.1 heb.2.1
                    (bridge_early_collapse_lt _ _ ha.1 ha.2 hb.1 hab) hbound)
              | eq =>
                  have he := new.T_eq_sound a b hc
                  subst b
                  have hr := ih xs ys hvr hwr hmr (by simpa [new.compareVec, hc] using hcmp)
                    fx fy sx ax sy ay hxs hys
                  cases hav; cases haw
                  rcases hr with h | ⟨h, hmid⟩
                  · exact Or.inl (bridge_add_left_lt _ _ _ h)
                  · exact Or.inr ⟨congrArg (T.add _) h, hmid⟩

-- From CardAux.lean

theorem sc_transAux_card1_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 (T.card_times 1 sum) ∧
          T.index_Prop1 1 (T.card_times 1 sum) ∧
          (∀ y : T, y ∈ T.G1 1 (T.card_times 1 sum) →
            y < T.card_times 1 sum) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              T.card_times 1 sum < T.card_times (k + 1) c) := by
  intro k
  induction k with
  | zero =>
      intro v _ found sum a0 haux
      rw [co_len1_sum_zero v found sum a0 haux]
      refine ⟨T.isNF1.z, T.index_Prop1.z, ?_, ?_⟩
      · intro y hy; cases hy
      · intro c _ _ hn
        exact tc_Z_lt_of_ne _ (bridge_card_times_ne_Z 1 c hn)
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc _ xs a =>
          have hr := fun x hx => hcomp x (List.mem_append_left [a] hx)
          have ha := hcomp a (by simp [new.Vec.toList])
          rcases hxs : transAux xs with ⟨fr, sr, ar⟩
          obtain ⟨hnf, hi, hg, hbound⟩ := ih xs hr fr sr ar hxs
          rw [transAux.eq_3, hxs] at haux
          cases a with
          | Z =>
              change (fr, sr, ar) = (found, sum, a0) at haux
              cases haux
              refine ⟨hnf, hi, hg, ?_⟩
              intro c hcnf hci hn
              exact lt_trans_thm _ _ _ (hbound c hcnf hci hn)
                (bridge_card_times_level_lt (m + 1) (m + 2) c c (by omega) hcnf hci hn hcnf hci hn)
          | P ls b =>
              have hec := bridge_early_collapse_closed _ ha.1 ha.2
              have hn := bridge_early_collapse_ne_Z _ (tc_trans_ne_Z_of_ne_Z (new.T.P ls b) (by intro h; cases h))
              cases haux
              simp only [← add_eq_hAdd, ca_card_times_add, ca_card_times_one_comp]
              have happ := bridge_card_times_succ_append m _ _ hec.1 hec.2.1 hnf hi hg hbound
              refine ⟨happ.1, happ.2.1, happ.2.2, ?_⟩
              intro c hcnf hci hcn
              exact bridge_card_times_add_level_lt (m + 1) (m + 2) _ c _ (by omega) hec.1 hec.2.1 hn hcnf hci hcn

-- From CardOrder_fixed.lean

theorem c1_p0 (a b : T) :
    T.card_times 1 (T.P 0 a b) =
      T.P 1 (T.early_collapse a) (T.card_times 1 b) := by
  simp [T.card_times, T.ofNat, T.mul, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]

theorem c1_p1 (a b : T) :
    T.card_times 1 (T.P 1 a b) =
      T.P 1 (T.P 1 T.Z a) (T.card_times 1 b) := by
  simp [T.card_times, T.ofNat, T.mul, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]

theorem c1_idx0_lt_outer1 (x m y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 m y := by
  cases hx with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)

theorem c1_idx0_lt_P1 (x y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 T.Z y := by
  exact c1_idx0_lt_outer1 x T.Z y hx

theorem c1_card_append_lt_index1 :
    ∀ s t x y : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.index_Prop1 0 x →
      T.add (T.card_times 1 s) x < T.add (T.card_times 1 t) y := by
  intro s t x y hsNF hsIdx htNF htIdx hst hx
  induction hst with
  | Z_lt_P q e f =>
      cases htIdx with
      | p _ _ _ hq _ =>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl <;>
            simp only [T.card_times.eq_1, T.add.eq_1, c1_p0, c1_p1, T.P_add_eq] <;>
            exact c1_idx0_lt_outer1 _ _ _ hx
  | p_head p q a e b f hpq =>
      cases hsIdx with
      | p _ _ _ hp _ =>
          cases htIdx with
          | p _ _ _ hq _ =>
              have hp0 : p = 0 := by omega
              have hq1 : q = 1 := by omega
              subst p; subst q
              have ha := T.isNF1_P_inv _ _ _ hsNF
              rw [c1_p0, c1_p1, T.P_add_eq, T.P_add_eq]
              exact T.Lt.p_mid _ _ _ _ _ (c1_idx0_lt_P1 _ _ (bridge_early_collapse_closed a ha.1 ha.2.2.1).2.1)
  | p_mid p a e b f h _ =>
      cases hsIdx with
      | p _ _ _ hp _ =>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
          · rw [c1_p0, c1_p0, T.P_add_eq, T.P_add_eq]
            exact T.Lt.p_mid _ _ _ _ _ (bridge_early_collapse_lt a e (T.isNF1_P_inv _ _ _ hsNF).1
              (T.isNF1_P_inv _ _ _ hsNF).2.2.1 (T.isNF1_P_inv _ _ _ htNF).1 h)
          · rw [c1_p1, c1_p1, T.P_add_eq, T.P_add_eq]
            exact T.Lt.p_mid _ _ _ _ _ (T.Lt.p_tail _ _ _ _ h)
  | p_tail p a b f h ih =>
      cases hsIdx with
      | p _ _ _ hp hb =>
          cases htIdx with
          | p _ _ _ _ hf =>
              have hr := ih (T.isNF1_P_inv _ _ _ hsNF).2.1 hb (T.isNF1_P_inv _ _ _ htNF).2.1 hf
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl <;>
                simp only [c1_p0, c1_p1, T.P_add_eq] <;> exact T.Lt.p_tail _ _ _ _ hr

theorem c1_card_times_mono_index1 :
    ∀ s t : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.card_times 1 s < T.card_times 1 t := by
  intro s t hs hi ht hj h
  simpa only [T.add_Z] using c1_card_append_lt_index1 s t T.Z T.Z hs hi ht hj h T.index_Prop1.z

theorem co_transAux_card1_lex {lam : Nat} :
    ∀ {k : Nat} (v w : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x : new.T lam, x ∈ new.Vec.toList w →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x y : new.T lam,
        x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
        x < y → trans x < trans y) →
      new.compareVec v w = Ordering.lt →
      ∀ fv fw : Bool, ∀ sv av sw aw : T,
        transAux v = (fv, sv, av) →
        transAux w = (fw, sw, aw) →
        T.card_times 1 sv < T.card_times 1 sw ∨
          (T.card_times 1 sv = T.card_times 1 sw ∧ av < aw) := by
  intro k v w hv hw hm hc fv fw sv av sw aw hav haw
  have hiv := tc_transAux_inv v hv fv sv av hav
  have hiw := tc_transAux_inv w hw fw sw aw haw
  rcases ao_transAux_lex v w hv hw hm hc fv fw sv av sw aw hav haw with h | ⟨h, hmid⟩
  · exact Or.inl (c1_card_times_mono_index1 _ _ hiv.2.2.1 hiv.2.2.2.1 hiw.2.2.1 hiw.2.2.2.1 h)
  · exact Or.inr ⟨congrArg (T.card_times 1) h, hmid⟩

theorem ec_part_snd_index0 (s : T) (hs : T.isNF1 s) :
    T.index_Prop1 0 (T.part s).2 := by
  exact bridge_part_second_index0 s _ _ hs rfl

theorem ec_index0_lt_posfixed (b c : T)
    (hb : T.index_Prop1 0 b)
    (hc : T.part c = (c, T.Z))
    (hcne : c ≠ T.Z) :
    b < c := by
  cases c with
  | Z => exact False.elim (hcne rfl)
  | P q u v =>
      have hq : q ≠ 0 := by intro h; simp [T.part, h] at hc
      cases hb with
      | z => exact T.Lt.Z_lt_P _ _ _
      | p p a d hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)

theorem ec_add_index0_lt_pos_of_lt : ∀ a c b : T,
    T.part a = (a, T.Z) →
    T.part c = (c, T.Z) →
    T.index_Prop1 0 b →
    a < c →
    T.add a b < c := by
  intro a c b ha hc hb hlt
  induction hlt with
  | Z_lt_P q u v =>
      exact ec_index0_lt_posfixed b _ hb hc (by intro h; cases h)
  | p_head p q x u y v h => rw [T.P_add_eq]; exact T.Lt.p_head _ _ _ _ _ _ h
  | p_mid p x u y v h _ => rw [T.P_add_eq]; exact T.Lt.p_mid _ _ _ _ _ h
  | p_tail p x y v h ih =>
      have hp : p ≠ 0 := by intro h; simp [T.part, h] at ha
      have hy : T.part y = (y, T.Z) := by simpa [T.part, hp, Prod.ext_iff] using ha
      have hv : T.part v = (v, T.Z) := by simpa [T.part, hp, Prod.ext_iff] using hc
      rw [T.P_add_eq]
      exact T.Lt.p_tail _ _ _ _ (ih hy hv)

theorem ec_pair_formula (s a b : T)
    (hs : T.isNF1 s) (hp : T.part s = (a, b)) :
    T.early_collapse s =
      if a = T.Z then s
      else if T.head b ≤ T.P 0 a T.Z then T.P 0 a b else b := by
  have hb : T.isNF1 b := by simpa [hp] using (bridge_part_NF1 s hs).2
  simp [T.early_collapse, hp, T.stand, bridge_stand_eq_self_of_NF1 b hb]

theorem ec_part_snd_middle_mem (s a e f : T)
    (hp : T.part s = (a, T.P 0 e f)) :
    e ∈ T.G1 0 s := by
  rw [← bridge_part_add s, hp, bridge_G1_add_eq]
  exact List.mem_append_right _ (bridge_mid_mem_G1_zero e f)

theorem ec_index0_lt_P0 (b c : T)
    (hb : T.index_Prop1 0 b)
    (hmid : ∀ e f : T, b = T.P 0 e f → e < c) :
    b < T.P 0 c T.Z := by
  cases hb with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p e f hp _ =>
      have hp0 : p = 0 := by omega
      subst p
      exact T.Lt.p_mid _ _ _ _ _ (hmid e f rfl)

theorem ec_one_del_NF_index_good1 (s : T)
    (hs : T.isNF1 s)
    (hi : T.index_Prop1 0 s)
    (_hg : ∀ x : T, x ∈ T.G1 1 s → x < s) :
    T.isNF1 (T.one_del s) ∧
      T.index_Prop1 0 (T.one_del s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.one_del s) → x < T.one_del s) := by
  cases hi with
  | z => exact ⟨hs, T.index_Prop1.z, _hg⟩
  | p p a b hp hb =>
      have hp0 : p = 0 := by omega
      subst p
      cases a with
      | Z => exact ⟨(T.isNF1_P_inv _ _ _ hs).2.1, hb, by simp [T.one_del, index_Prop1_G1_empty 0 b hb 1 (by omega)]⟩
      | P q c d => exact ⟨hs, T.index_Prop1.p _ _ _ (Nat.le_refl _) hb, _hg⟩

end TranslationAlgebra

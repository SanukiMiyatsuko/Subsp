import Subsp.old.stop_translation

/-! Normal-form lemmas for the legacy collapse at an arbitrary cardinal index. -/

namespace LegacyTranslation

open T

theorem stand_eq_self (s : T) (hs : T.isNF1 s) : T.stand s = s := by
  induction hs with
  | z => rfl
  | p p a b _ _ _ hh _ ih => rw [T.stand, ih, ite_eq_left hh]

theorem part_of_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) :
    T.part n s = (T.Z, s) := by
  induction hs with
  | z => rfl
  | p p a b hp _ ih => simp only [T.part, ih, hp, ite_true]

theorem part_add (n : Nat) (s : T) (hs : T.isNF1 s) :
    T.add (T.part n s).1 (T.part n s).2 = s := by
  induction hs with
  | z => rfl
  | p p a b ha hb hg hh _ ih =>
      by_cases hp : p ≤ n
      · rw [part_of_index n _ (isNF1_index n p a b (.p p a b ha hb hg hh) hp)]
        exact zero_add _
      · simp only [T.part, hp, ite_false, T.P_add_eq, ih]

theorem part_second_index (n : Nat) (s : T) : T.index_Prop1 n (T.part n s).2 := by
  induction s with
  | Z => exact .z
  | P p a b _ ih =>
      rw [T.part]
      split
      · exact .p p a _ ‹p ≤ n› ih
      · exact ih

theorem isNF1_add_inv (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 a ∧ T.isNF1 b := by
  induction a with
  | Z => exact ⟨.z, h⟩
  | P p a c _ ih =>
      rw [T.P_add_eq] at h
      obtain ⟨ha, hc, hg, hh⟩ := T.isNF1_P_inv p a _ h
      refine ⟨.p p a c ha (ih hc).1 hg ?_, (ih hc).2⟩
      cases c with
      | Z => exact T.Z_le _
      | P q d e => simpa only [T.head_add_ne_Z] using hh

theorem add_right_le_of_NF (a b : T)
    (h : T.isNF1 (T.add a b)) : b ≤ T.add a b := by
  induction a with
  | Z => exact Or.inr rfl
  | P p c d _ ih =>
      rw [T.P_add_eq] at h ⊢
      have htailNF := (T.isNF1_P_inv p c (T.add d b) h).2.1
      exact partial_order.trans _ _ _
        (ih htailNF)
        (T.isNF1_tail_le _ h p c (T.add d b) rfl)

theorem part_NF (n : Nat) (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part n s).1 ∧ T.isNF1 (T.part n s).2 :=
  isNF1_add_inv _ _ ((part_add n s hs).symm ▸ hs)

theorem G1_add (n : Nat) (a b : T) :
    T.G1 n (T.add a b) = T.G1 n a ++ T.G1 n b := by
  induction a with
  | Z => rfl
  | P p a c _ ih =>
      rw [T.P_add_eq]
      by_cases hp : n ≤ p <;> simp [T.G1, hp, ih, List.append_assoc]

theorem lt_prefix_of_size_lt (a b x : T) (ha : a ≠ T.Z)
    (hsize : T.size x < T.size a) (h : x < T.add a b) : x < a := by
  induction a generalizing x with
  | Z => exact False.elim (ha rfl)
  | P p a c _ ih =>
      rw [T.P_add_eq] at h
      cases h with
      | Z_lt_P => exact .Z_lt_P _ _ _
      | p_head _ _ _ _ _ _ h => exact .p_head _ _ _ _ _ _ h
      | p_mid _ _ _ _ _ h => exact .p_mid _ _ _ _ _ h
      | p_tail _ _ d _ h =>
          have hsize' : T.size d < T.size c := by simp only [T.size] at hsize; omega
          have hc : c ≠ T.Z := by intro he; simp [he, T.size] at hsize'
          exact .p_tail _ _ _ _ (ih d hc hsize' h)

theorem support_prefix (n : Nat) (a b : T) (ha : a ≠ T.Z)
    (hg : ∀ x ∈ T.G1 n (T.add a b), x < T.add a b) :
    ∀ x ∈ T.G1 n a, x < a := fun x hx =>
  lt_prefix_of_size_lt a b x ha (G1_size_lt n a x hx) (hg x ((G1_add n a b).symm ▸ List.mem_append_left _ hx))

theorem early_collapse_of_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) :
    T.early_collapse n s = s := by
  simp only [T.early_collapse, part_of_index n s hs, ite_true]

theorem early_collapse_closed (n : Nat) (s : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) :
    T.isNF1 (T.early_collapse n s) ∧ T.index_Prop1 n (T.early_collapse n s) := by
  obtain ⟨ha, hb⟩ := part_NF n s hs
  have he := part_add n s hs
  have hi := part_second_index n s
  dsimp only [T.early_collapse]
  split
  · exact ⟨hb, hi⟩
  · have hga : ∀ x ∈ T.G1 n (T.part n s).1, x < (T.part n s).1 :=
      support_prefix n _ _ ‹_› (he.symm ▸ hg)
    rw [T.stand, stand_eq_self _ hb]
    split
    · exact ⟨.p n _ _ ha hb hga ‹_›, .p n _ _ (Nat.le_refl n) hi⟩
    · exact ⟨hb, hi⟩

theorem add_self_le (a b : T) : a ≤ T.add a b := by
  induction a with
  | Z => exact T.Z_le b
  | P p a c _ ih =>
      rw [T.P_add_eq]
      exact ih.imp (T.Lt.p_tail _ _ _ _) (congrArg (T.P p a))

theorem part_first_le (n : Nat) (s : T) (hs : T.isNF1 s) : (T.part n s).1 ≤ s := by
  have h := add_self_le (T.part n s).1 (T.part n s).2
  rwa [part_add n s hs] at h

theorem part_first_head_gt (n p : Nat) (s a b : T)
    (h : (T.part n s).1 = T.P p a b) : n < p := by
  induction s with
  | Z => cases h
  | P q c d _ ih =>
      by_cases hq : q ≤ n
      · simp only [T.part, hq, ite_true] at h
        exact ih h
      · simp only [T.part, hq, ite_false] at h
        cases h
        omega

theorem part_first_fixed (n : Nat) (s : T) :
    T.part n (T.part n s).1 = ((T.part n s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b _ ih => by_cases hp : p ≤ n <;> simp [T.part, hp, ih]

theorem part_lt_cases (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (h : s < t) :
    (T.part n s).1 < (T.part n t).1 ∨
      ((T.part n s).1 = (T.part n t).1 ∧ (T.part n s).2 < (T.part n t).2) := by
  induction h with
  | Z_lt_P q a b =>
      by_cases hq : q ≤ n
      · rw [part_of_index n _ (isNF1_index n q a b ht hq)]
        exact Or.inr ⟨rfl, .Z_lt_P _ _ _⟩
      · simp only [T.part, hq, ite_false]
        exact Or.inl (.Z_lt_P _ _ _)
  | p_head p q a c b d hpq =>
      by_cases hp : p ≤ n
      · rw [part_of_index n _ (isNF1_index n p a b hs hp)]
        by_cases hq : q ≤ n
        · rw [part_of_index n _ (isNF1_index n q c d ht hq)]
          exact Or.inr ⟨rfl, .p_head _ _ _ _ _ _ hpq⟩
        · simp only [T.part, hq, ite_false]
          exact Or.inl (.Z_lt_P _ _ _)
      · have hq : ¬ q ≤ n := by omega
        simp only [T.part, hp, hq, ite_false]
        exact Or.inl (.p_head _ _ _ _ _ _ hpq)
  | p_mid p a c b d hac _ =>
      by_cases hp : p ≤ n
      · rw [part_of_index n _ (isNF1_index n p a b hs hp),
          part_of_index n _ (isNF1_index n p c d ht hp)]
        exact Or.inr ⟨rfl, .p_mid _ _ _ _ _ hac⟩
      · simp only [T.part, hp, ite_false]
        exact Or.inl (.p_mid _ _ _ _ _ hac)
  | p_tail p a b d hbd ih =>
      by_cases hp : p ≤ n
      · rw [part_of_index n _ (isNF1_index n p a b hs hp),
          part_of_index n _ (isNF1_index n p a d ht hp)]
        exact Or.inr ⟨rfl, .p_tail _ _ _ _ hbd⟩
      · simp only [T.part, hp, ite_false]
        rcases ih (T.isNF1_P_inv _ _ _ hs).2.1 (T.isNF1_P_inv _ _ _ ht).2.1 with h | ⟨he, h⟩
        · exact Or.inl (.p_tail _ _ _ _ h)
        · exact Or.inr ⟨congrArg (T.P p a) he, h⟩

theorem lt_of_part_lt_cases (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (h : (T.part n s).1 < (T.part n t).1 ∨
      ((T.part n s).1 = (T.part n t).1 ∧ (T.part n s).2 < (T.part n t).2)) :
    s < t := by
  rcases lt_total_thm s t with hst | hts | rfl
  · exact hst
  · have hr := part_lt_cases n t s ht hs hts
    rcases h with h | ⟨he, h⟩ <;> rcases hr with hr | ⟨hre, hr⟩ <;>
      simp_all [show ∀ x : T, ¬ x < x from lt_irrefl_thm, lt_asymm_thm]
  · rcases h with h | ⟨_, h⟩ <;> exact False.elim (lt_irrefl_thm _ h)

theorem head_le_self (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P p a b => exact (T.Z_le b).imp (T.Lt.p_tail p a _ _) (congrArg (T.P p a))

theorem lt_of_not_le (a b : T) (h : ¬ a ≤ b) : b < a := by
  rcases lt_total_thm a b with hab | hba | he
  · exact False.elim (h (Or.inl hab))
  · exact hba
  · exact False.elim (h (Or.inr he))

theorem lt_of_head_lt (s t : T) (h : T.head s < T.head t) : s < t := by
  cases s <;> cases t <;> cases h
  · exact .Z_lt_P _ _ _
  · exact .p_head _ _ _ _ _ _ ‹_›
  · exact .p_mid _ _ _ _ _ ‹_›
  · exact False.elim (lt_Z_inv ‹T.Z < T.Z›)

theorem stand_insert_lt (n : Nat) (a b d : T) (hb : T.isNF1 b) (hd : T.isNF1 d)
    (hbd : b < d) : T.stand (T.P n a b) < T.stand (T.P n a d) := by
  rw [T.stand, stand_eq_self b hb, T.stand, stand_eq_self d hd]
  by_cases hba : T.head b ≤ T.P n a T.Z
  · rw [ite_eq_left hba]
    split
    · exact .p_tail _ _ _ _ hbd
    · exact lt_of_head_lt _ _ (lt_of_not_le _ _ ‹_›)
  · have hda : ¬ T.head d ≤ T.P n a T.Z :=
      fun h => hba (partial_order.trans _ _ _ (T.head_mono hbd) h)
    simpa only [hba, hda, ite_false] using hbd

/-- The low part of a good term is below the principal term it wraps. -/
theorem part_snd_lt_wrap (K : Nat) (X b : T) (hX : T.isNF1 X) (hg : ∀ y ∈ T.G1 K X, y < X) :
    (T.part K X).2 < T.P K X b := by
  have hi := part_second_index K X
  cases hp : (T.part K X).2 with
  | Z => exact T.Lt.Z_lt_P _ _ _
  | P q d e =>
      rw [hp] at hi
      cases hi with
      | p _ _ _ hq _ =>
          rcases Nat.eq_or_lt_of_le hq with rfl | hq
          · apply T.Lt.p_mid
            apply hg d
            rw [← part_add q X hX, G1_add, hp]
            exact List.mem_append_right _ (by simp [T.G1])
          · exact T.Lt.p_head _ _ _ _ _ _ hq

theorem early_collapse_upper (n : Nat) (s c : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) (hsc : s < c) :
    T.early_collapse n s < T.P n c T.Z := by
  have hb := (part_NF n s hs).2
  have hbc : (T.part n s).2 < T.P n c T.Z :=
    lt_trans_thm _ _ _ (part_snd_lt_wrap n s T.Z hs hg) (.p_mid _ _ _ _ _ hsc)
  dsimp only [T.early_collapse]
  split
  · exact hbc
  · rw [T.stand, stand_eq_self _ hb]
    split
    · exact .p_mid _ _ _ _ _ (lt_of_le_of_lt_thm T _ _ _ (part_first_le n s hs) hsc)
    · exact hbc

theorem part_base_le_early_collapse (n : Nat) (t : T) (ht : T.isNF1 t)
    (hne : (T.part n t).1 ≠ T.Z) :
    T.P n (T.part n t).1 T.Z ≤ T.early_collapse n t := by
  rw [T.early_collapse, ite_eq_right hne, T.stand, stand_eq_self _ (part_NF n t ht).2]
  split
  · exact head_le_self (T.P n _ _)
  · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (lt_of_not_le _ _ ‹_›) (head_le_self _))

theorem early_collapse_lt (n : Nat) (s t : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) (ht : T.isNF1 t) (hst : s < t) :
    T.early_collapse n s < T.early_collapse n t := by
  rcases part_lt_cases n s t hs ht hst with h | ⟨he, h⟩
  · have hne : (T.part n t).1 ≠ T.Z := by
      intro hz; rw [hz] at h; exact lt_Z_inv h
    exact lt_of_lt_of_le_thm T _ _ _
      (early_collapse_upper n s _ hs hg (lt_of_part_lt_cases n s _ hs (part_NF n t ht).1
        (by rw [part_first_fixed]; exact Or.inl h)))
      (part_base_le_early_collapse n t ht hne)
  · by_cases hz : (T.part n s).1 = T.Z
    · rw [T.early_collapse, ite_eq_left hz, T.early_collapse, ite_eq_left (he ▸ hz)]
      exact h
    · rw [T.early_collapse, ite_eq_right hz, T.early_collapse, ← he, ite_eq_right hz]
      exact stand_insert_lt n _ _ _ (part_NF n s hs).2 (part_NF n t ht).2 h

end LegacyTranslation

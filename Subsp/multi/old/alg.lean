import Subsp.multi.Collapse

/-! Buchholz-side algebra for the translation of `old`.

* `OB.part n s` splits a sum into the summands of index above `n` and the rest.
* `OB.ec n s` collapses `s` at index `n`: the exponent `e` with `ψ_n(s) = Ω_n·ω^e`-style
  normal forms, of index at most `n`.
* `OB.ct n s` multiplies a sum by `Ω_n`, summand by summand (`OB.cardArg`). -/

namespace OB

open T

/-- Split a sum into its summands of index above `n` and those of index at most `n`. -/
def part (n : Nat) : T → T × T
  | Z => (Z, Z)
  | P p a b =>
    if p ≤ n then ((part n b).1, P p a (part n b).2) else (P p a (part n b).1, (part n b).2)

theorem part_P_le {n p : Nat} (a b : T) (hp : p ≤ n) :
    part n (P p a b) = ((part n b).1, P p a (part n b).2) := by
  rw [part, ite_eq_left hp]

theorem part_P_gt {n p : Nat} (a b : T) (hp : ¬ p ≤ n) :
    part n (P p a b) = (P p a (part n b).1, (part n b).2) := by
  rw [part, ite_eq_right hp]

/-- Collapse at index `n`. -/
def ec (n : Nat) (s : T) : T :=
  if (part n s).1 = Z then (part n s).2 else MT.stand (P n (part n s).1 (part n s).2)

/-- Remove a leading summand `ψ_0(0) = 1`. -/
def oneDel : T → T
  | P 0 Z b => b
  | s => s

/-- The argument of a summand `ψ_p(a)` after multiplication by `Ω_n`. -/
def cardArg (n p : Nat) (a : T) : T :=
  if p < n then
    if p = 0 then ec p a else MT.stand (P p Z (ec p a))
  else if p = n ∧ a < P n (P 0 Z Z) Z then P n Z a
  else a

/-- Multiplication of a sum by `Ω_n`. -/
def ct (n : Nat) : T → T
  | Z => Z
  | P p a b => P (max p n) (cardArg n p a) (ct n b)

/-! ### Sums -/

theorem zero_add (t : T) : T.add Z t = t := rfl

theorem p_zero_add (p : Nat) (a y : T) : T.add (P p a Z) y = P p a y := by
  cases y <;> rfl

theorem add_right_le_of_NF (a b : T) (h : T.isNF1 (T.add a b)) : b ≤ T.add a b := by
  induction a with
  | Z => exact Or.inr rfl
  | P p c d _ ih =>
    rw [T.P_add_eq] at h ⊢
    exact partial_order.trans _ _ _ (ih (T.isNF1_P_inv p c _ h).2.1)
      (T.isNF1_tail_le _ h p c (T.add d b) rfl)

theorem lt_of_head_lt (s t : T) (h : T.head s < T.head t) : s < t := by
  cases s <;> cases t <;> cases h
  · exact T.Lt.Z_lt_P _ _ _
  · exact T.Lt.p_head _ _ _ _ _ _ ‹_›
  · exact T.Lt.p_mid _ _ _ _ _ ‹_›
  · exact False.elim (lt_Z_inv ‹T.Z < T.Z›)

/-! ### Parts -/

theorem part_of_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) : part n s = (Z, s) := by
  induction hs with
  | z => rfl
  | p p a b hp _ ih => rw [part_P_le a b hp, ih]

theorem part_add (n : Nat) (s : T) (hs : T.isNF1 s) : T.add (part n s).1 (part n s).2 = s := by
  induction hs with
  | z => rfl
  | p p a b ha hb hg hh _ ih =>
    by_cases hp : p ≤ n
    · rw [part_of_index n _ (isNF1_index n p a b (T.isNF1.p p a b ha hb hg hh) hp)]; rfl
    · rw [part_P_gt a b hp]
      show T.add (P p a (part n b).1) (part n b).2 = P p a b
      rw [T.P_add_eq, ih]

theorem part_second_index (n : Nat) (s : T) : T.index_Prop1 n (part n s).2 := by
  induction s with
  | Z => exact T.index_Prop1.z
  | P p a b _ ih =>
    rw [part]
    by_cases hp : p ≤ n
    · rw [ite_eq_left hp]; exact T.index_Prop1.p p a _ hp ih
    · rw [ite_eq_right hp]; exact ih

theorem part_NF (n : Nat) (s : T) (hs : T.isNF1 s) :
    T.isNF1 (part n s).1 ∧ T.isNF1 (part n s).2 := by
  have h := part_add n s hs
  rw [← h] at hs
  exact ⟨MT.isNF1_add_left hs, MT.isNF1_add_right hs⟩

theorem part_first_le (n : Nat) (s : T) (hs : T.isNF1 s) : (part n s).1 ≤ s := by
  have h := MT.add_self_le (part n s).1 (part n s).2
  rwa [part_add n s hs] at h

theorem part_first_head_gt (n p : Nat) (s a b : T) (h : (part n s).1 = P p a b) : n < p := by
  induction s with
  | Z => cases h
  | P q c d _ ih =>
    rw [part] at h
    by_cases hq : q ≤ n
    · rw [ite_eq_left hq] at h; exact ih h
    · rw [ite_eq_right hq] at h
      cases h
      exact Nat.lt_of_not_le hq

theorem part_first_fixed (n : Nat) (s : T) : part n (part n s).1 = ((part n s).1, Z) := by
  induction s with
  | Z => rfl
  | P p a b _ ih =>
    by_cases hp : p ≤ n
    · rw [part_P_le a b hp]; exact ih
    · rw [part_P_gt a b hp]
      show part n (P p a (part n b).1) = (P p a (part n b).1, Z)
      rw [part_P_gt a _ hp, ih]

theorem part_snd_of_fst_Z (n : Nat) : ∀ b : T, (part n b).1 = Z → (part n b).2 = b
  | Z, _ => rfl
  | P p a r, h => by
    by_cases hp : p ≤ n
    · rw [part_P_le a r hp] at h ⊢
      show P p a (part n r).2 = P p a r
      rw [part_snd_of_fst_Z n r h]
    · rw [part_P_gt a r hp] at h; cases h

theorem part_lt_cases (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t) (h : s < t) :
    (part n s).1 < (part n t).1 ∨ ((part n s).1 = (part n t).1 ∧ (part n s).2 < (part n t).2) := by
  induction h with
  | Z_lt_P q a b =>
    by_cases hq : q ≤ n
    · rw [part_of_index n _ (isNF1_index n q a b ht hq)]
      exact Or.inr ⟨rfl, T.Lt.Z_lt_P _ _ _⟩
    · rw [part_P_gt a b hq]
      exact Or.inl (T.Lt.Z_lt_P _ _ _)
  | p_head p q a c b d hpq =>
    by_cases hp : p ≤ n
    · rw [part_of_index n _ (isNF1_index n p a b hs hp)]
      by_cases hq : q ≤ n
      · rw [part_of_index n _ (isNF1_index n q c d ht hq)]
        exact Or.inr ⟨rfl, T.Lt.p_head _ _ _ _ _ _ hpq⟩
      · rw [part_P_gt c d hq]
        exact Or.inl (T.Lt.Z_lt_P _ _ _)
    · have hq : ¬ q ≤ n := fun h => hp (Nat.le_trans (Nat.le_of_lt hpq) h)
      rw [part_P_gt a b hp, part_P_gt c d hq]
      exact Or.inl (T.Lt.p_head _ _ _ _ _ _ hpq)
  | p_mid p a c b d hac =>
    by_cases hp : p ≤ n
    · rw [part_of_index n _ (isNF1_index n p a b hs hp),
        part_of_index n _ (isNF1_index n p c d ht hp)]
      exact Or.inr ⟨rfl, T.Lt.p_mid _ _ _ _ _ hac⟩
    · rw [part_P_gt a b hp, part_P_gt c d hp]
      exact Or.inl (T.Lt.p_mid _ _ _ _ _ hac)
  | p_tail p a b d hbd ih =>
    by_cases hp : p ≤ n
    · rw [part_of_index n _ (isNF1_index n p a b hs hp),
        part_of_index n _ (isNF1_index n p a d ht hp)]
      exact Or.inr ⟨rfl, T.Lt.p_tail _ _ _ _ hbd⟩
    · rw [part_P_gt a b hp, part_P_gt a d hp]
      rcases ih (T.isNF1_P_inv _ _ _ hs).2.1 (T.isNF1_P_inv _ _ _ ht).2.1 with h | ⟨he, h⟩
      · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
      · exact Or.inr ⟨congrArg (P p a) he, h⟩

theorem lt_of_part_lt_cases (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (h : (part n s).1 < (part n t).1 ∨
      ((part n s).1 = (part n t).1 ∧ (part n s).2 < (part n t).2)) : s < t := by
  rcases lt_total_thm s t with hst | hts | rfl
  · exact hst
  · exfalso
    rcases part_lt_cases n t s ht hs hts with hr | ⟨hre, hr⟩
    · rcases h with h | ⟨he, _⟩
      · exact lt_asymm_thm h hr
      · rw [he] at hr; exact lt_irrefl_thm _ hr
    · rcases h with h | ⟨_, h⟩
      · rw [hre] at h; exact lt_irrefl_thm _ h
      · exact lt_asymm_thm h hr
  · exfalso
    rcases h with h | ⟨_, h⟩ <;> exact lt_irrefl_thm _ h

theorem part_add_distrib (n : Nat) : ∀ a b : T,
    part n (T.add a b) = (T.add (part n a).1 (part n b).1, T.add (part n a).2 (part n b).2)
  | Z, b => rfl
  | P p c r, b => by
    rw [T.P_add_eq]
    have ih := part_add_distrib n r b
    by_cases hp : p ≤ n
    · rw [part_P_le c _ hp, part_P_le c r hp, ih, T.P_add_eq]
    · rw [part_P_gt c _ hp, part_P_gt c r hp, ih, T.P_add_eq]

theorem part_add_split (n : Nat) (a b : T) (ha : part n a = (a, Z)) (hb : (part n b).1 = Z) :
    part n (T.add a b) = (a, b) := by
  rw [part_add_distrib, ha, hb, part_snd_of_fst_Z n b hb, T.add_Z]; rfl

theorem part_part (n m : Nat) (hnm : n ≤ m) : ∀ s : T,
    (part m (part n s).1).1 = (part m s).1 ∧ (part n (part m s).2).2 = (part n s).2 ∧
      (part m (part n s).1).2 = (part n (part m s).2).1
  | Z => ⟨rfl, rfl, rfl⟩
  | P p a r => by
    obtain ⟨ih1, ih2, ih3⟩ := part_part n m hnm r
    by_cases hpn : p ≤ n
    · have hpm : p ≤ m := Nat.le_trans hpn hnm
      rw [part_P_le a r hpn, part_P_le a r hpm]
      refine ⟨ih1, ?_, ?_⟩
      · show (part n (P p a (part m r).2)).2 = P p a (part n r).2
        rw [part_P_le a _ hpn]
        show P p a (part n (part m r).2).2 = P p a (part n r).2
        rw [ih2]
      · show (part m (part n r).1).2 = (part n (P p a (part m r).2)).1
        rw [part_P_le a _ hpn]
        exact ih3
    · by_cases hpm : p ≤ m
      · rw [part_P_gt a r hpn, part_P_le a r hpm]
        refine ⟨?_, ?_, ?_⟩
        · show (part m (P p a (part n r).1)).1 = (part m r).1
          rw [part_P_le a _ hpm]
          exact ih1
        · show (part n (P p a (part m r).2)).2 = (part n r).2
          rw [part_P_gt a _ hpn]
          exact ih2
        · show (part m (P p a (part n r).1)).2 = (part n (P p a (part m r).2)).1
          rw [part_P_le a _ hpm, part_P_gt a _ hpn]
          show P p a (part m (part n r).1).2 = P p a (part n (part m r).2).1
          rw [ih3]
      · rw [part_P_gt a r hpn, part_P_gt a r hpm]
        refine ⟨?_, ih2, ?_⟩
        · show (part m (P p a (part n r).1)).1 = P p a (part m r).1
          rw [part_P_gt a _ hpm]
          show P p a (part m (part n r).1).1 = P p a (part m r).1
          rw [ih1]
        · show (part m (P p a (part n r).1)).2 = (part n (part m r).2).1
          rw [part_P_gt a _ hpm]
          exact ih3

/-! ### Collapse at an index -/

theorem support_prefix (n : Nat) (a b : T) (ha : a ≠ Z)
    (hg : ∀ x ∈ T.G1 n (T.add a b), x < T.add a b) : ∀ x ∈ T.G1 n a, x < a := fun x hx =>
  MT.lt_add_left_of_size_lt a b x ha (G1_size_lt n a x hx)
    (hg x (by rw [MT.G1_add]; exact List.mem_append_left _ hx))

theorem ec_of_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) : ec n s = s := by
  rw [ec, part_of_index n s hs]; rfl

theorem ec_closed (n : Nat) (s : T) (hs : T.isNF1 s) (hg : ∀ x ∈ T.G1 n s, x < s) :
    T.isNF1 (ec n s) ∧ T.index_Prop1 n (ec n s) := by
  obtain ⟨ha, hb⟩ := part_NF n s hs
  have he := part_add n s hs
  have hi := part_second_index n s
  rw [ec]
  by_cases hz : (part n s).1 = Z
  · rw [ite_eq_left hz]; exact ⟨hb, hi⟩
  · rw [ite_eq_right hz]
    have hga : ∀ x ∈ T.G1 n (part n s).1, x < (part n s).1 :=
      support_prefix n _ _ hz (by rw [he]; exact hg)
    rw [MT.stand, MT.stand_of_NF1 hb]
    by_cases hh : T.head (part n s).2 ≤ P n (part n s).1 Z
    · rw [ite_eq_left hh]
      exact ⟨T.isNF1.p n _ _ ha hb hga hh, T.index_Prop1.p n _ _ (Nat.le_refl n) hi⟩
    · rw [ite_eq_right hh]; exact ⟨hb, hi⟩

theorem stand_insert_lt (n : Nat) (a b d : T) (hb : T.isNF1 b) (hd : T.isNF1 d) (hbd : b < d) :
    MT.stand (P n a b) < MT.stand (P n a d) := by
  rw [MT.stand, MT.stand_of_NF1 hb, MT.stand, MT.stand_of_NF1 hd]
  by_cases hba : T.head b ≤ P n a Z
  · rw [ite_eq_left hba]
    by_cases hda : T.head d ≤ P n a Z
    · rw [ite_eq_left hda]; exact T.Lt.p_tail _ _ _ _ hbd
    · rw [ite_eq_right hda]
      exact lt_of_head_lt _ _ (MT.lt_of_not_le hda)
  · have hda : ¬ T.head d ≤ P n a Z :=
      fun h => hba (partial_order.trans _ _ _ (T.head_mono hbd) h)
    rw [ite_eq_right hba, ite_eq_right hda]
    exact hbd

/-- The low part of a good term is below the principal term it wraps. -/
theorem part_snd_lt_wrap (K : Nat) (X b : T) (hX : T.isNF1 X) (hg : ∀ y ∈ T.G1 K X, y < X) :
    (part K X).2 < P K X b := by
  have hi := part_second_index K X
  cases hp : (part K X).2 with
  | Z => exact T.Lt.Z_lt_P _ _ _
  | P q d e =>
    rw [hp] at hi
    cases hi with
    | p _ _ _ hq _ =>
      rcases Nat.eq_or_lt_of_le hq with rfl | hq
      · apply T.Lt.p_mid
        apply hg d
        rw [← part_add q X hX, MT.G1_add, hp]
        exact List.mem_append_right _ ((MT.G1_P_mem (Nat.le_refl q)).2 (Or.inl rfl))
      · exact T.Lt.p_head _ _ _ _ _ _ hq

theorem ec_upper (n : Nat) (s c : T) (hs : T.isNF1 s) (hg : ∀ x ∈ T.G1 n s, x < s) (hsc : s < c) :
    ec n s < P n c Z := by
  have hb := (part_NF n s hs).2
  have hbc : (part n s).2 < P n c Z :=
    lt_trans_thm _ _ _ (part_snd_lt_wrap n s Z hs hg) (T.Lt.p_mid _ _ _ _ _ hsc)
  rw [ec]
  by_cases hz : (part n s).1 = Z
  · rw [ite_eq_left hz]; exact hbc
  · rw [ite_eq_right hz, MT.stand, MT.stand_of_NF1 hb]
    by_cases hh : T.head (part n s).2 ≤ P n (part n s).1 Z
    · rw [ite_eq_left hh]
      exact T.Lt.p_mid _ _ _ _ _ (lt_of_le_of_lt_thm T _ _ _ (part_first_le n s hs) hsc)
    · rw [ite_eq_right hh]; exact hbc

theorem part_base_le_ec (n : Nat) (t : T) (ht : T.isNF1 t) (hne : (part n t).1 ≠ Z) :
    P n (part n t).1 Z ≤ ec n t := by
  rw [ec, ite_eq_right hne, MT.stand, MT.stand_of_NF1 (part_NF n t ht).2]
  by_cases hh : T.head (part n t).2 ≤ P n (part n t).1 Z
  · rw [ite_eq_left hh]; exact MT.head_le_self (P n _ _)
  · rw [ite_eq_right hh]
    exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (MT.lt_of_not_le hh) (MT.head_le_self _))

theorem ec_lt (n : Nat) (s t : T) (hs : T.isNF1 s) (hg : ∀ x ∈ T.G1 n s, x < s) (ht : T.isNF1 t)
    (hst : s < t) : ec n s < ec n t := by
  rcases part_lt_cases n s t hs ht hst with h | ⟨he, h⟩
  · have hne : (part n t).1 ≠ Z := by
      intro hz; rw [hz] at h; exact lt_Z_inv h
    exact lt_of_lt_of_le_thm T _ _ _
      (ec_upper n s _ hs hg (lt_of_part_lt_cases n s _ hs (part_NF n t ht).1
        (by rw [part_first_fixed]; exact Or.inl h)))
      (part_base_le_ec n t ht hne)
  · by_cases hz : (part n s).1 = Z
    · rw [ec, ite_eq_left hz, ec, ite_eq_left (he ▸ hz)]
      exact h
    · rw [ec, ite_eq_right hz, ec, ← he, ite_eq_right hz]
      exact stand_insert_lt n _ _ _ (part_NF n s hs).2 (part_NF n t ht).2 h

/-! ### Removing a leading `1` -/

theorem oneDel_P0Z (b : T) : oneDel (P 0 Z b) = b := rfl

theorem oneDel_cases (s : T) : oneDel s = s ∨ ∃ b, s = P 0 Z b ∧ oneDel s = b := by
  match s with
  | P 0 Z b => exact Or.inr ⟨b, rfl, rfl⟩
  | Z => exact Or.inl rfl
  | P (_ + 1) _ _ => exact Or.inl rfl
  | P 0 (P _ _ _) _ => exact Or.inl rfl

theorem oneDel_NF (s : T) (hs : T.isNF1 s) : T.isNF1 (oneDel s) := by
  rcases oneDel_cases s with h | ⟨b, rfl, h⟩
  · rw [h]; exact hs
  · rw [h]; exact (T.isNF1_P_inv 0 Z b hs).2.1

theorem oneDel_le (s : T) (hs : T.isNF1 s) : oneDel s ≤ s := by
  rcases oneDel_cases s with h | ⟨b, rfl, h⟩
  · rw [h]; exact Or.inr rfl
  · rw [h]; exact T.isNF1_tail_le _ hs _ _ _ rfl

theorem oneDel_lt (s t : T) (hs : T.isNF1 s) (hne : s ≠ Z) (h : s < t) : oneDel s < oneDel t := by
  cases h with
  | Z_lt_P => exact absurd rfl hne
  | p_head p q a c b d hpq =>
    cases q with
    | zero => exact absurd hpq (Nat.not_lt_zero _)
    | succ q => exact lt_of_le_of_lt_thm T _ _ _ (oneDel_le _ hs) (T.Lt.p_head _ _ _ _ _ _ hpq)
  | p_mid p a c b d hac =>
    cases p with
    | zero =>
      cases c with
      | Z => exact absurd hac lt_Z_inv
      | P q e f => exact lt_of_le_of_lt_thm T _ _ _ (oneDel_le _ hs) (T.Lt.p_mid _ _ _ _ _ hac)
    | succ p => exact T.Lt.p_mid _ _ _ _ _ hac
  | p_tail p a b d hbd =>
    cases p with
    | zero =>
      cases a with
      | Z => exact hbd
      | P _ _ _ => exact T.Lt.p_tail _ _ _ _ hbd
    | succ _ => exact T.Lt.p_tail _ _ _ _ hbd

theorem oneDel_good_pos (n : Nat) (hn : 0 < n) (s : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) : ∀ x ∈ T.G1 n (oneDel s), x < oneDel s := by
  rcases oneDel_cases s with h | ⟨b, rfl, h⟩
  · rw [h]; exact hg
  · rw [h]
    cases isNF1_index 0 0 Z b hs (Nat.le_refl 0) with
    | p _ _ _ _ hb =>
      intro x hx
      rw [index_Prop1_G1_empty 0 b hb n hn] at hx
      cases hx

theorem part_oneDel_fst (n : Nat) (t : T) : (part n (oneDel t)).1 = (part n t).1 := by
  rcases oneDel_cases t with h | ⟨b, rfl, h⟩
  · rw [h]
  · rw [h, part, ite_eq_left (Nat.zero_le n)]

/-! ### Multiplication by `Ω_n` -/

theorem ct_P (n p : Nat) (a b : T) : ct n (P p a b) = P (max p n) (cardArg n p a) (ct n b) := rfl

theorem stand_insert_closed (n : Nat) (a b : T) (ha : T.isNF1 a) (hg : ∀ x ∈ T.G1 n a, x < a)
    (hb : T.isNF1 b) : T.isNF1 (MT.stand (P n a b)) := by
  rw [MT.stand, MT.stand_of_NF1 hb]
  by_cases hh : T.head b ≤ P n a Z
  · rw [ite_eq_left hh]; exact T.isNF1.p n a b ha hb hg hh
  · rw [ite_eq_right hh]; exact hb

theorem stand_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) : T.index_Prop1 n (MT.stand s) := by
  induction hs with
  | z => exact T.index_Prop1.z
  | p p a b hp _ ih =>
    rw [MT.stand]
    by_cases hh : T.head (MT.stand b) ≤ P p a Z
    · rw [ite_eq_left hh]; exact T.index_Prop1.p p a _ hp ih
    · rw [ite_eq_right hh]; exact ih

theorem stand_insert_base_le (n : Nat) (a b : T) (hb : T.isNF1 b) :
    P n a Z ≤ MT.stand (P n a b) := by
  rw [MT.stand, MT.stand_of_NF1 hb]
  by_cases hh : T.head b ≤ P n a Z
  · rw [ite_eq_left hh]; exact MT.head_le_self (P n a b)
  · rw [ite_eq_right hh]
    exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (MT.lt_of_not_le hh) (MT.head_le_self b))

theorem head_le_card_of_lt (n : Nat) (a : T) (ha : a < P n (P 0 Z Z) Z) : T.head a ≤ P n Z Z := by
  cases ha with
  | Z_lt_P => exact T.Z_le _
  | p_head _ _ _ _ _ _ h => exact Or.inl (T.Lt.p_head _ _ _ _ _ _ h)
  | p_mid _ a _ _ _ h => rw [MT.lt_one_eq_Z h]; exact Or.inr rfl
  | p_tail _ _ _ _ h => cases h

theorem card_prefix_lt (n : Nat) (a : T) (ha : T.isNF1 a) (hh : T.head a ≤ P n Z Z) :
    a < P n Z a := by
  cases a with
  | Z => exact T.Lt.Z_lt_P _ _ _
  | P p b c =>
    rcases hh with hh | hh
    · cases hh with
      | p_head _ _ _ _ _ _ h => exact T.Lt.p_head _ _ _ _ _ _ h
      | p_mid _ _ _ _ _ h => cases h
      | p_tail _ _ _ _ h => cases h
    · cases hh
      exact T.Lt.p_tail _ _ _ _ (MT.tail_lt_of_NF1 ha)

theorem cardArg_lt_case (n p : Nat) (a : T) (hpn : p < n) :
    cardArg n p a = if p = 0 then ec p a else MT.stand (P p Z (ec p a)) := by
  rw [cardArg, ite_eq_left hpn]

theorem cardArg_eq_self (n p : Nat) (a : T) (hpn : ¬ p < n)
    (hc : ¬ (p = n ∧ a < P n (P 0 Z Z) Z)) : cardArg n p a = a := by
  rw [cardArg, ite_eq_right hpn, ite_eq_right hc]

theorem cardArg_same_small (n : Nat) (a : T) (ha : a < P n (P 0 Z Z) Z) :
    cardArg n n a = P n Z a := by
  rw [cardArg, ite_eq_right (Nat.lt_irrefl n), ite_eq_left ⟨rfl, ha⟩]

theorem cardArg_above (n p : Nat) (a : T) (hnp : n < p) : cardArg n p a = a :=
  cardArg_eq_self n p a (fun h => Nat.lt_asymm h hnp) (fun h => Nat.ne_of_gt hnp h.1)

theorem cardArg_closed (n p : Nat) (a : T) (ha : T.isNF1 a) (hg : ∀ x ∈ T.G1 p a, x < a) :
    T.isNF1 (cardArg n p a) ∧ (∀ x ∈ T.G1 (max p n) (cardArg n p a), x < cardArg n p a) := by
  by_cases hpn : p < n
  · have hm : max p n = n := Nat.max_eq_right (Nat.le_of_lt hpn)
    obtain ⟨heNF, heIdx⟩ := ec_closed p a ha hg
    rw [cardArg_lt_case n p a hpn, hm]
    by_cases hp0 : p = 0
    · rw [ite_eq_left hp0]
      refine ⟨heNF, ?_⟩
      rw [index_Prop1_G1_empty p _ heIdx n hpn]
      intro x hx; cases hx
    · rw [ite_eq_right hp0]
      have hnf := stand_insert_closed p Z _ T.isNF1.z (fun x hx => by cases hx) heNF
      have hi := stand_index p _ (T.index_Prop1.p p Z _ (Nat.le_refl p) heIdx)
      refine ⟨hnf, ?_⟩
      rw [index_Prop1_G1_empty p _ hi n hpn]
      intro x hx; cases hx
  · by_cases hc : p = n ∧ a < P n (P 0 Z Z) Z
    · obtain ⟨rfl, halt⟩ := hc
      rw [cardArg_same_small p a halt, Nat.max_self]
      have hh := head_le_card_of_lt p a halt
      refine ⟨T.isNF1.p p Z a T.isNF1.z ha (fun x hx => by cases hx) hh, ?_⟩
      intro x hx
      rcases (MT.G1_P_mem (Nat.le_refl p)).1 hx with rfl | hx | hx
      · exact T.Lt.Z_lt_P _ _ _
      · cases hx
      · exact lt_trans_thm _ _ _ (hg x hx) (card_prefix_lt p a ha hh)
    · have hnp : n ≤ p := Nat.le_of_not_gt hpn
      rw [cardArg_eq_self n p a hpn hc, Nat.max_eq_left hnp]
      exact ⟨ha, hg⟩

theorem cardArg_index_of_lt (n p : Nat) (a : T) (ha : T.isNF1 a) (hg : ∀ x ∈ T.G1 p a, x < a)
    (hpn : p < n) : T.index_Prop1 p (cardArg n p a) := by
  rw [cardArg_lt_case n p a hpn]
  have hi := (ec_closed p a ha hg).2
  by_cases hp0 : p = 0
  · rw [ite_eq_left hp0]; exact hi
  · rw [ite_eq_right hp0]; exact stand_index p _ (T.index_Prop1.p p Z _ (Nat.le_refl p) hi)

theorem cardArg_lower (n p : Nat) (a : T) (ha : T.isNF1 a) (hg : ∀ x ∈ T.G1 p a, x < a)
    (hp : 0 < p) (hpn : p ≤ n) : P p Z Z ≤ cardArg n p a := by
  by_cases hlt : p < n
  · rw [cardArg_lt_case n p a hlt, ite_eq_right (Nat.ne_of_gt hp)]
    exact stand_insert_base_le p Z _ (ec_closed p a ha hg).1
  · have he : p = n := Nat.le_antisymm hpn (Nat.le_of_not_gt hlt)
    subst he
    by_cases hal : a < P p (P 0 Z Z) Z
    · rw [cardArg_same_small p a hal]; exact MT.head_le_self (P p Z a)
    · rw [cardArg_eq_self p p a hlt (fun h => hal h.2)]
      rcases lt_total_thm a (P p (P 0 Z Z) Z) with h | h | h
      · exact absurd h hal
      · exact Or.inl (lt_trans_thm _ _ _ (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)) h)
      · subst h; exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))

theorem cardArg_lt_same (n p : Nat) (a b : T) (ha : T.isNF1 a) (hga : ∀ x ∈ T.G1 p a, x < a)
    (hb : T.isNF1 b) (hgb : ∀ x ∈ T.G1 p b, x < b) (hab : a < b) :
    cardArg n p a < cardArg n p b := by
  by_cases hpn : p < n
  · rw [cardArg_lt_case n p a hpn, cardArg_lt_case n p b hpn]
    have he := ec_lt p a b ha hga hb hab
    by_cases hp0 : p = 0
    · rw [ite_eq_left hp0, ite_eq_left hp0]; exact he
    · rw [ite_eq_right hp0, ite_eq_right hp0]
      exact stand_insert_lt p Z _ _ (ec_closed p a ha hga).1 (ec_closed p b hb hgb).1 he
  · by_cases hp : p = n
    · subst hp
      by_cases hal : a < P p (P 0 Z Z) Z
      · rw [cardArg_same_small p a hal]
        by_cases hbl : b < P p (P 0 Z Z) Z
        · rw [cardArg_same_small p b hbl]; exact T.Lt.p_tail _ _ _ _ hab
        · rw [cardArg_eq_self p p b hpn (fun h => hbl h.2)]
          rcases lt_total_thm b (P p (P 0 Z Z) Z) with h | h | h
          · exact absurd h hbl
          · exact lt_trans_thm _ _ _ (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)) h
          · subst h; exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)
      · have hbl : ¬ b < P p (P 0 Z Z) Z := fun h => hal (lt_trans_thm _ _ _ hab h)
        rw [cardArg_eq_self p p a hpn (fun h => hal h.2), cardArg_eq_self p p b hpn (fun h => hbl h.2)]
        exact hab
    · rw [cardArg_eq_self n p a hpn (fun h => hp h.1), cardArg_eq_self n p b hpn (fun h => hp h.1)]
      exact hab

theorem index_lt_level (p q : Nat) (a : T) (ha : T.index_Prop1 p a) (hpq : p < q) :
    a < P q Z Z := by
  cases ha with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p r a b hr _ => exact T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hr hpq)

theorem card_heads_lt (n p q : Nat) (a b c d : T) (hpq : p < q)
    (ha : T.isNF1 a) (hga : ∀ x ∈ T.G1 p a, x < a)
    (hb : T.isNF1 b) (hgb : ∀ x ∈ T.G1 q b, x < b) :
    P (max p n) (cardArg n p a) c < P (max q n) (cardArg n q b) d := by
  by_cases hqn : q ≤ n
  · have hpn : p < n := Nat.lt_of_lt_of_le hpq hqn
    rw [Nat.max_eq_right (Nat.le_of_lt hpn), Nat.max_eq_right hqn]
    exact T.Lt.p_mid _ _ _ _ _ (lt_of_lt_of_le_thm T _ _ _
      (index_lt_level p q _ (cardArg_index_of_lt n p a ha hga hpn) hpq)
      (cardArg_lower n q b hb hgb (Nat.lt_of_le_of_lt (Nat.zero_le p) hpq) hqn))
  · apply T.Lt.p_head
    have h1 : max q n = q := Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hqn))
    rw [h1]
    by_cases hpn : p ≤ n
    · rw [Nat.max_eq_right hpn]; exact Nat.lt_of_not_le hqn
    · rw [Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hpn))]; exact hpq

theorem ct_lt (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t) (h : s < t) :
    ct n s < ct n t := by
  induction h with
  | Z_lt_P q a b => exact T.Lt.Z_lt_P _ _ _
  | p_head p q a c b d hpq =>
    obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
    obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
    exact card_heads_lt n p q a c _ _ hpq ha hga hc hgc
  | p_mid p a c b d hac =>
    obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
    obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
    exact T.Lt.p_mid _ _ _ _ _ (cardArg_lt_same n p a c ha hga hc hgc hac)
  | p_tail p a b d _ ih =>
    exact T.Lt.p_tail _ _ _ _ (ih (T.isNF1_P_inv _ _ _ hs).2.1 (T.isNF1_P_inv _ _ _ ht).2.1)

theorem ct_closed (n : Nat) (s : T) (hs : T.isNF1 s) : T.isNF1 (ct n s) := by
  induction hs with
  | z => exact T.isNF1.z
  | p p a b ha hb hg hh _ ih =>
    obtain ⟨harg, hsupport⟩ := cardArg_closed n p a ha hg
    refine T.isNF1.p _ _ _ harg ih hsupport ?_
    cases hb with
    | z => exact T.Z_le _
    | p q c d hc _ hgc _ =>
      change P q c Z ≤ P p a Z at hh
      have h := hh.imp (ct_lt n _ _ (T.isNF1.p q c Z hc T.isNF1.z hgc (T.Z_le _))
        (T.isNF1.p p a Z ha T.isNF1.z hg (T.Z_le _))) (congrArg (ct n))
      exact h

theorem ct_index (n u : Nat) (s : T) (hs : T.index_Prop1 u s) :
    T.index_Prop1 (max u n) (ct n s) := by
  induction hs with
  | z => exact T.index_Prop1.z
  | p p a b hp _ ih =>
    refine T.index_Prop1.p _ _ _ ?_ ih
    by_cases hpn : p ≤ n
    · rw [Nat.max_eq_right hpn]; exact Nat.le_max_right u n
    · rw [Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_le hpn))]
      exact Nat.le_trans hp (Nat.le_max_left u n)

theorem ct_index_self (n : Nat) (s : T) (hs : T.index_Prop1 n s) : T.index_Prop1 n (ct n s) := by
  have h := ct_index n n s hs
  rwa [Nat.max_self] at h

theorem head_base_le (n p : Nat) (a : T) (hnp : n ≤ p) : P n Z Z ≤ P p a Z := by
  rcases Nat.eq_or_lt_of_le hnp with rfl | hnp
  · exact (T.Z_le a).imp (T.Lt.p_mid _ _ _ _ _) (congrArg (fun x => P n x Z))
  · exact Or.inl (T.Lt.p_head _ _ _ _ _ _ hnp)

theorem ct_self_le (n : Nat) (s : T) (hs : T.isNF1 s) : s ≤ ct n s := by
  induction hs with
  | z => exact Or.inr rfl
  | p p a b ha _ _ _ _ ih =>
    rw [ct_P]
    by_cases hpn : p < n
    · refine Or.inl (T.Lt.p_head _ _ _ _ _ _ ?_)
      rw [Nat.max_eq_right (Nat.le_of_lt hpn)]; exact hpn
    · by_cases hc : p = n ∧ a < P n (P 0 Z Z) Z
      · obtain ⟨rfl, halt⟩ := hc
        rw [cardArg_same_small p a halt, Nat.max_self]
        exact Or.inl (T.Lt.p_mid _ _ _ _ _ (card_prefix_lt p a ha (head_le_card_of_lt p a halt)))
      · rw [cardArg_eq_self n p a hpn hc, Nat.max_eq_left (Nat.le_of_not_gt hpn)]
        exact ih.imp (T.Lt.p_tail _ _ _ _) (congrArg (P p a))

theorem ct_support (n : Nat) (s : T) (hs : T.isNF1 s) :
    ∀ x ∈ T.G1 n (ct n s), x < ct n s ∨ x ∈ T.G1 n s := by
  induction hs with
  | z => intro x hx; cases hx
  | p p a b ha hb hg hh _ ih =>
    have hnf := ct_closed n _ (T.isNF1.p p a b ha hb hg hh)
    rw [ct_P] at hnf ⊢
    have htail := MT.tail_lt_of_NF1 hnf
    intro x hx
    rcases (MT.G1_P_mem (Nat.le_max_right p n)).1 hx with rfl | hx | hx
    · by_cases hpn : p < n
      · apply Or.inl
        have hi := cardArg_index_of_lt n p a ha hg hpn
        exact lt_of_lt_of_le_thm T _ _ _ (index_lt_level p n _ hi hpn)
          (partial_order.trans _ _ _ (head_base_le n (max p n) _ (Nat.le_max_right p n))
            (MT.head_le_self (P (max p n) (cardArg n p a) (ct n b))))
      · by_cases hc : p = n ∧ a < P n (P 0 Z Z) Z
        · obtain ⟨rfl, halt⟩ := hc
          rw [cardArg_same_small p a halt, Nat.max_self]
          exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))
        · rw [cardArg_eq_self n p a hpn hc]
          exact Or.inr ((MT.G1_P_mem (Nat.le_of_not_gt hpn)).2 (Or.inl rfl))
    · by_cases hpn : p < n
      · rw [index_Prop1_G1_empty p _ (cardArg_index_of_lt n p a ha hg hpn) n hpn] at hx
        cases hx
      · have hnp : n ≤ p := Nat.le_of_not_gt hpn
        by_cases hc : p = n ∧ a < P n (P 0 Z Z) Z
        · obtain ⟨rfl, halt⟩ := hc
          rw [cardArg_same_small p a halt] at hx
          rcases (MT.G1_P_mem (Nat.le_refl p)).1 hx with rfl | hx | hx
          · exact Or.inl (T.Lt.Z_lt_P _ _ _)
          · cases hx
          · exact Or.inr ((MT.G1_P_mem (Nat.le_refl p)).2 (Or.inr (Or.inl hx)))
        · rw [cardArg_eq_self n p a hpn hc] at hx
          exact Or.inr ((MT.G1_P_mem hnp).2 (Or.inr (Or.inl hx)))
    · rcases ih x hx with h | h
      · exact Or.inl (lt_trans_thm _ _ _ h htail)
      · apply Or.inr
        by_cases hnp : n ≤ p
        · exact (MT.G1_P_mem hnp).2 (Or.inr (Or.inr h))
        · rw [T.G1, ite_eq_right hnp]; exact h

theorem ct_append_closed (n : Nat) (s b : T) (hs : T.isNF1 s) (hb : T.isNF1 b)
    (hbound : b < P n Z Z) : T.isNF1 (T.add (ct n s) b) := by
  induction hs with
  | z => exact hb
  | p p a c ha hc hg hh _ ih =>
    rw [ct_P, T.P_add_eq]
    obtain ⟨harg, hsupport⟩ := cardArg_closed n p a ha hg
    refine T.isNF1.p _ _ _ harg ih hsupport ?_
    cases c with
    | Z =>
      exact partial_order.trans _ _ _ (T.head_mono hbound)
        (head_base_le n (max p n) _ (Nat.le_max_right p n))
    | P q d e =>
      have hnf := ct_closed n _ (T.isNF1.p p a (P q d e) ha hc hg hh)
      rw [ct_P] at hnf
      have hhead := (T.isNF1_P_inv _ _ _ hnf).2.2.2
      rw [ct_P, T.head_add_ne_Z]
      exact hhead

theorem ct_append_good (n u : Nat) (hun : u < n) (s b : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) (hb : T.index_Prop1 u b) :
    ∀ x ∈ T.G1 n (T.add (ct n s) b), x < T.add (ct n s) b := by
  intro x hx
  rw [MT.G1_add, index_Prop1_G1_empty u b hb n hun, List.append_nil] at hx
  refine lt_of_lt_of_le_thm T _ _ _ ?_ (MT.add_self_le _ _)
  rcases ct_support n s hs x hx with h | h
  · exact h
  · exact lt_of_lt_of_le_thm T _ _ _ (hg x h) (ct_self_le n s hs)

theorem ct_append_lt (n : Nat) (s t l r : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hst : s < t) (hl : l < P n Z Z) : T.add (ct n s) l < T.add (ct n t) r := by
  induction hst with
  | Z_lt_P p a b =>
    rw [ct_P, T.P_add_eq]
    exact lt_of_lt_of_le_thm T _ _ _ hl
      (partial_order.trans _ _ _ (head_base_le n (max p n) _ (Nat.le_max_right p n))
        (MT.head_le_self (P (max p n) (cardArg n p a) (T.add (ct n b) r))))
  | p_head p q a c b d hpq =>
    rw [ct_P, ct_P, T.P_add_eq, T.P_add_eq]
    obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
    obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
    exact card_heads_lt n p q a c _ _ hpq ha hga hc hgc
  | p_mid p a c b d hac =>
    rw [ct_P, ct_P, T.P_add_eq, T.P_add_eq]
    obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
    obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
    exact T.Lt.p_mid _ _ _ _ _ (cardArg_lt_same n p a c ha hga hc hgc hac)
  | p_tail p a b d _ ih =>
    rw [ct_P, ct_P, T.P_add_eq, T.P_add_eq]
    exact T.Lt.p_tail _ _ _ _ (ih (T.isNF1_P_inv _ _ _ hs).2.1 (T.isNF1_P_inv _ _ _ ht).2.1)

theorem part_ct (n : Nat) : ∀ s : T,
    (part n (ct n s)).1 = (part n s).1 ∧ (part n (ct n s)).2 = ct n (part n s).2
  | Z => ⟨rfl, rfl⟩
  | P p a r => by
    have ih := part_ct n r
    rw [ct_P]
    by_cases hp : p ≤ n
    · have hm : max p n = n := Nat.max_eq_right hp
      rw [hm, part_P_le _ _ (Nat.le_refl n), part_P_le a r hp]
      refine ⟨ih.1, ?_⟩
      show P n (cardArg n p a) (part n (ct n r)).2 = ct n (P p a (part n r).2)
      rw [ih.2, ct_P, hm]
    · have hnp : n < p := Nat.lt_of_not_le hp
      have hm : max p n = p := Nat.max_eq_left (Nat.le_of_lt hnp)
      rw [hm, cardArg_above n p a hnp, part_P_gt a _ hp, part_P_gt a r hp]
      refine ⟨?_, ih.2⟩
      show P p a (part n (ct n r)).1 = P p a (part n r).1
      rw [ih.1]

end OB

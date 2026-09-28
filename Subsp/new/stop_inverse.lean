import Subsp.new.stop_nf_order

/-! Constructive inverses of collapse and cardinal operations, with depth and support bounds. -/

/-! The exponent-depth measure. -/

section InverseMeasure

open T

namespace StopSurjMeasure

-- Count nesting through exponents; appending a tail does not add a level.
def degree : T → Nat
  | T.Z => 0
  | T.P _ a b => max (degree a + 1) (degree b)

theorem degree_add (a b : T) : degree (T.add a b) = max (degree a) (degree b) := by
  induction a with
  | Z => simp [T.add, degree]
  | P p c d _ ih => simp only [T.P_add_eq, degree, ih, Nat.max_assoc]

theorem degree_part (a : T) : degree (T.part a).1 ≤ degree a ∧
    degree (T.part a).2 ≤ degree a := by
  have h := degree_add (T.part a).1 (T.part a).2
  rw [bridge_part_add] at h
  rw [h]
  exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

theorem degree_middle_lt (p : Nat) (a b : T) : degree a < degree (T.P p a b) := by
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (degree a)) (Nat.le_max_left _ _)

theorem degree_tail_le (p : Nat) (a b : T) : degree b ≤ degree (T.P p a b) := by
  exact Nat.le_max_right _ _

end StopSurjMeasure

end InverseMeasure

/-! Reconstruction before early collapse. -/

section InverseCollapse

open T

namespace StopUncollapse

open StopSurjMeasure

def Good (s : T) : Prop := ∀ x, x ∈ T.G1 0 s → x < s

theorem support_le_of_head (s a : T) (hs : T.isNF1 s)
    (hh : T.head s ≤ T.P 0 a T.Z) : ∀ x, x ∈ T.G1 0 s → x ≤ a := by
  induction hs with
  | z => intro x hx; cases hx
  | p p c d _ _ hg hhead _ ih =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero (head_le_index p 0 c a hh)
      subst p
      have hca := bridge_P0_head_mid_le a c d hh
      intro x hx
      simp [T.G1] at hx
      rcases hx with rfl | hx | hx
      · exact hca
      · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (hg x hx) hca)
      · exact ih (partial_order.trans _ _ _ hhead hh) x hx

theorem good_of_middle_lt (a b : T) (hs : T.isNF1 (T.P 0 a b))
    (ha : a < T.P 0 a b) : Good (T.P 0 a b) := by
  exact fun x hx => lt_of_le_of_lt_thm T _ _ _ (support_le_of_head _ a hs (Or.inr rfl) x hx) ha

theorem part_snd_lt_wrap (a : T) (hnf : T.isNF1 a) (hg : Good a) :
    (T.part a).2 < T.P 0 a T.Z := by
  apply ec_index0_lt_P0 _ a (ec_part_snd_index0 a hnf)
  intro e f he
  exact hg e (ec_part_snd_middle_mem a _ e f (Prod.ext rfl he))

theorem part_fixed_P_inv {p : Nat} {a b : T}
    (hfix : T.part (T.P p a b) = (T.P p a b, T.Z)) :
    p ≠ 0 ∧ T.part b = (b, T.Z) := by
  by_cases hp : p = 0
  · simp [T.part, hp] at hfix
  · simp [T.part, hp] at hfix
    exact ⟨hp, Prod.ext hfix.1 hfix.2⟩

theorem surj_part_add_fixed : ∀ a b : T,
    T.part a = (a, T.Z) → T.part b = (T.Z, b) →
      T.part (T.add a b) = (a, b) := by
  intro a
  induction a with
  | Z => exact fun b _ hb => hb
  | P p c d _ ih =>
      intro b hf hb
      have hi := part_fixed_P_inv hf
      simp [T.P_add_eq, T.part, hi.1, ih b hi.2 hb]

theorem surj_head_lt_pos_of_index0 (p : Nat) (c b : T)
    (hp : 0 < p) (hb : T.index_Prop1 0 b) :
    T.head b < T.P p c T.Z := by
  cases hb with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p q e f hq _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)

theorem surj_add_fixed_index0_NF : ∀ a b : T,
    T.isNF1 a → T.isNF1 b →
    T.part a = (a, T.Z) → T.index_Prop1 0 b →
      T.isNF1 (T.add a b) := by
  intro a b ha
  induction ha with
  | z => exact fun hb _ _ => hb
  | p p c d hc hd hg hh _ ih =>
      intro hb hf hi
      have hfix := part_fixed_P_inv hf
      rw [T.P_add_eq]
      refine T.isNF1.p _ _ _ hc (ih hb hfix.2 hi) hg ?_
      cases d with
      | Z => exact Or.inl (surj_head_lt_pos_of_index0 p c b (Nat.pos_of_ne_zero hfix.1) hi)
      | P q e f => simpa [T.P_add_eq, T.head] using hh

theorem part_of_index0 (s : T) (hi : T.index_Prop1 0 s) : T.part s = (T.Z, s) := by
  cases hi with
  | z => rfl
  | p p a b hp _ => simp [T.part, Nat.eq_zero_of_le_zero hp]

/-- Restore the positive-index prefix that `early_collapse` removed. When the
exponent has a nonzero low part, prepend its high part to the entire input;
`stand` then removes that prefix again. This also preserves the degree bound. -/
theorem exists_uncollapse (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    ∃ x : T, T.isNF1 x ∧ Good x ∧ T.early_collapse x = s ∧
      (∀ B : T, T.part B = (B, T.Z) →
        (∀ y, y ∈ T.G1 0 s → y < B) → s < B → x < B) ∧
      degree x ≤ degree s := by
  cases hi with
  | z => exact ⟨T.Z, hnf, (by intro x hx; cases hx), rfl, fun _ _ _ hb => hb, Nat.le_refl _⟩
  | p p a b hp hb =>
      have hp0 : p = 0 := by omega
      subst p
      have hn := T.isNF1_P_inv 0 a b hnf
      rcases hpart : T.part a with ⟨h, l⟩
      have hfix : T.part h = (h, T.Z) := by simpa [hpart] using bridge_part_fst_fixed a
      have hadd : T.add h l = a := by simpa [hpart] using bridge_part_add a
      have hparts : T.isNF1 h ∧ T.isNF1 l := by simpa [hpart] using bridge_part_NF1 a hn.1
      have hhgood : Good h := by simpa [hpart, Good] using sg_good0_part_fst a hn.2.2.1
      have hidx : T.index_Prop1 0 l := by simpa [hpart] using ec_part_snd_index0 a hn.1
      by_cases hz : h = T.Z
      · have hal : l = a := by simpa [hz, T.add.eq_1] using hadd
        have haidx : T.index_Prop1 0 a := hal ▸ hidx
        exact ⟨T.P 0 a b, hnf, good_of_middle_lt a b hnf (bridge_good_index_lt_wrap 0 a b haidx hn.2.2.1),
          rfl, fun _ _ _ hsB => hsB, Nat.le_refl _⟩
      · by_cases hlz : l = T.Z
        · have hha : h = a := by simpa [hlz, T.add_Z] using hadd
          subst h
          have hafix : T.part a = (a, T.Z) := by simpa [hlz] using hpart
          have hxNF := surj_add_fixed_index0_NF a b hn.1 hn.2.1 hafix hb
          refine ⟨T.add a b, hxNF, ?_, ?_, ?_, ?_⟩
          · intro y hy
            rw [bridge_G1_add_eq, List.mem_append] at hy
            rcases hy with hy | hy
            · exact lt_of_lt_of_le_thm T _ _ _ (hn.2.2.1 y hy) (wt_add_self_le a b)
            · have hbne : b ≠ T.Z := by intro h; simp [h, T.G1] at hy
              exact lt_of_le_of_lt_thm T _ _ _ (support_le_of_head b a hn.2.1 hn.2.2.2 y hy) (add_lt_add_of_ne_Z a b hbne)
          · rw [ec_pair_formula _ a b hxNF (surj_part_add_fixed a b hafix (part_of_index0 b hb)),
              ite_eq_right hz, ite_eq_left hn.2.2.2]
          · exact fun B hB hG _ => ec_add_index0_lt_pos_of_lt a B b hafix hB hb (hG a (bridge_mid_mem_G1_zero a b))
          · rw [degree_add, degree]
            exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
        · have hha : h < a := by rw [← hadd]; exact add_lt_add_of_ne_Z h l hlz
          have hl : l < T.P 0 a T.Z := by simpa [hpart] using part_snd_lt_wrap a hn.1 hn.2.2.1
          have has : a < T.add h (T.P 0 a b) := by
            have hh := bridge_add_left_lt h l (T.P 0 a b)
              (lt_of_lt_of_le_thm T _ _ _ hl (bridge_head_le_self (T.P 0 a b)))
            rwa [hadd] at hh
          have hsidx := T.index_Prop1.p 0 a b (Nat.le_refl 0) hb
          have hxNF := surj_add_fixed_index0_NF h _ hparts.1 hnf hfix hsidx
          refine ⟨T.add h (T.P 0 a b), hxNF, ?_, ?_, ?_, ?_⟩
          · intro y hy
            rw [bridge_G1_add_eq, List.mem_append] at hy
            rcases hy with hy | hy
            · exact lt_of_lt_of_le_thm T _ _ _ (hhgood y hy) (wt_add_self_le _ _)
            · exact lt_of_le_of_lt_thm T _ _ _ (support_le_of_head _ a hnf (Or.inr rfl) y hy) has
          · rw [ec_pair_formula _ h (T.P 0 a b) hxNF (surj_part_add_fixed h _ hfix rfl), ite_eq_right hz]
            apply ite_eq_right
            intro hh
            exact lt_irrefl_thm h (lt_of_lt_of_le_thm T _ _ _ hha (bridge_P0_head_mid_le h a b hh))
          · exact fun B hB hG _ => ec_add_index0_lt_pos_of_lt h B _ hfix hB hsidx
              (lt_trans_thm _ _ _ hha (hG a (bridge_mid_mem_G1_zero a b)))
          · have hd : degree h ≤ degree a := by simpa [hpart] using (degree_part a).1
            rw [degree_add]
            exact Nat.max_le.mpr ⟨Nat.le_trans hd (Nat.le_of_lt (degree_middle_lt 0 a b)), Nat.le_refl _⟩

end StopUncollapse

end InverseCollapse

/-! Reconstruction before cardinal multiplication. -/

section InverseCardinal

open T

namespace StopSurjCard

open StopSurjMeasure

def Small (B s : T) : Prop := s < B ∧ ∀ y, y ∈ T.G1 0 s → y < B

theorem small_inv (B : T) (p : Nat) (a b : T) (hnf : T.isNF1 (T.P p a b))
    (h : Small B (T.P p a b)) : Small B a ∧ Small B b := by
  have hG : a < B ∧ ∀ y, y ∈ T.G1 0 a ∨ y ∈ T.G1 0 b → y < B := by
    simpa [T.G1] using h.2
  exact ⟨⟨hG.1, fun y hy => hG.2 y (Or.inl hy)⟩,
    lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 p a b hnf) h.1,
    fun y hy => hG.2 y (Or.inr hy)⟩

def Good1 (s : T) : Prop := ∀ y, y ∈ T.G1 1 s → y < s

def OneChain : T → Prop
  | T.Z => True
  | T.P p _ b => p = 1 ∧ OneChain b

theorem card_head (s : T) : T.card_times 1 (T.head s) = T.head (T.card_times 1 s) := by
  cases s with
  | Z => rfl
  | P p a b =>
      by_cases hp : p = 0 <;>
        simp [T.head, T.card_times, hp, ← add_eq_hAdd, T.P_add_eq, T.add_Z]

theorem head_nf (s : T) (hs : T.isNF1 s) : T.isNF1 (T.head s) := by
  cases hs with
  | z => exact T.isNF1.z
  | p p a b ha hb hg hh =>
      exact T.isNF1.p p a T.Z ha T.isNF1.z hg (T.Z_le _)

theorem head_idx (s : T) (hs : T.index_Prop1 1 s) : T.index_Prop1 1 (T.head s) := by
  cases hs with
  | z => exact T.index_Prop1.z
  | p p a b hp hb => exact T.index_Prop1.p p a T.Z hp T.index_Prop1.z

theorem card_reflect_le (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hsi : T.index_Prop1 1 s) (hti : T.index_Prop1 1 t)
    (h : T.card_times 1 s ≤ T.card_times 1 t) : s ≤ t := by
  rcases lt_total_thm s t with hst | (hts | he)
  · exact Or.inl hst
  · have hc := c1_card_times_mono_index1 t s ht hti hs hsi hts
    exact False.elim (lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ hc h))
  · exact Or.inr he

theorem below_mul_support (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) :
    T.index_Prop1 1 a ∧ ∀ y, y ∈ T.G1 1 a → y = T.Z := by
  induction k generalizing a with
  | zero => exact False.elim (lt_Z_inv ha)
  | succ k ih =>
      rw [mul_succ_shape] at ha
      cases ha with
      | Z_lt_P => exact ⟨T.index_Prop1.z, by intro y hy; cases hy⟩
      | p_head p _ c _ d _ hp =>
          have hp0 : p = 0 := by omega
          subst p
          have hi := isNF1_index 0 0 c d hnf (Nat.le_refl 0)
          exact ⟨Rank1Termination.index_mono (Nat.zero_le 1) _ hi,
            by simp [index_Prop1_G1_empty 0 _ hi 1 (by omega)]⟩
      | p_mid _ _ _ _ _ h => cases h
      | p_tail _ _ d _ h =>
          have hd := ih d (T.isNF1_P_inv _ _ _ hnf).2.1 h
          refine ⟨T.index_Prop1.p _ _ _ (Nat.le_refl _) hd.1, ?_⟩
          simpa [T.G1] using hd.2

theorem below_mul_good (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) : Good1 a := by
  intro y hy
  rw [(below_mul_support a hnf k ha).2 y hy]
  exact tc_Z_lt_of_ne a (by rintro rfl; cases hy)

theorem principal_inverse (q : T) (hnf : T.isNF1 q) (k : Nat)
    (hq : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) :
    ∃ p a, p ≤ 1 ∧ T.isNF1 a ∧
      (∀ y, y ∈ T.G1 p a → y < a) ∧
      (p = 1 → T.index_Prop1 1 a ∧ Good1 a) ∧
      T.card_times 1 (T.P p a T.Z) = T.P 1 q T.Z ∧
      (∀ b, T.P p a b < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z) ∧
      degree a ≤ degree q ∧ (p = 1 → a < q) ∧
      ∀ B, T.part B = (B, T.Z) → Small B q → Small B a := by
  rw [mul_succ_shape] at hq
  cases hq with
  | Z_lt_P =>
      refine ⟨0, T.Z, Nat.zero_le 1, T.isNF1.z, ?_, ?_, rfl, ?_, Nat.le_refl 0, ?_, ?_⟩
      · intro y hy; cases hy
      · intro h; cases h
      · exact fun b => T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
      · intro h; cases h
      · exact fun _ _ h => h
  | p_head p _ a _ b _ hp =>
      have hp0 : p = 0 := by omega
      subst p
      obtain ⟨x, hnf, hg, hec, hbound, hd⟩ := StopUncollapse.exists_uncollapse _ hnf (isNF1_index 0 0 a b hnf (Nat.le_refl 0))
      refine ⟨0, x, Nat.zero_le 1, hnf, hg, ?_, ?_, ?_, hd, ?_, ?_⟩
      · intro h; cases h
      · rw [c1_p0, hec]; rfl
      · exact fun tail => T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
      · intro h; cases h
      · intro B hf hs
        have hx := hbound B hf hs.2 hs.1
        exact ⟨hx, fun y hy => lt_trans_thm _ _ _ (hg y hy) hx⟩
  | p_mid _ _ _ _ _ h => cases h
  | p_tail _ _ b _ h =>
      have hb := (T.isNF1_P_inv _ _ _ hnf).2.1
      have hi := (below_mul_support b hb k h).1
      have hg := below_mul_good b hb k h
      exact ⟨1, b, Nat.le_refl 1, hb, hg, fun _ => ⟨hi, hg⟩,
        c1_p1 b T.Z, fun tail => T.Lt.p_mid _ _ _ _ _ h, degree_tail_le 1 T.Z b,
        fun _ => gc_tail_lt_of_NF1 _ _ _ hnf, fun B _ hs => (small_inv B _ _ _ hnf hs).2⟩

theorem card_append (p : Nat) (a b : T) :
    T.card_times 1 (T.P p a b) = T.add (T.card_times 1 (T.P p a T.Z)) (T.card_times 1 b) := by
  simpa only [T.P_add_eq, T.add.eq_1] using ca_card_times_add 1 (T.P p a T.Z) b

theorem exists_uncard (h : T) (hnf : T.isNF1 h) (hc : OneChain h) (k : Nat)
    (hb : h < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z) :
    ∃ s, T.isNF1 s ∧ T.index_Prop1 1 s ∧ Good1 s ∧ T.card_times 1 s = h ∧
      s < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z ∧
      degree s ≤ degree h ∧
      ∀ B, T.part B = (B, T.Z) → Small B h → Small B s := by
  induction h with
  | Z =>
      exact ⟨T.Z, hnf, T.index_Prop1.z, (by intro y hy; cases hy), rfl,
        T.Lt.Z_lt_P _ _ _, Nat.le_refl _, fun _ _ hs => hs⟩
  | P p q r _ ih =>
      obtain ⟨rfl, hcr⟩ := hc
      have hn := T.isNF1_P_inv 1 q r hnf
      have hqb : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
        cases hb with
        | p_head _ _ _ _ _ _ h => exact False.elim (Nat.lt_irrefl _ h)
        | p_mid _ _ _ _ _ h => exact h
        | p_tail _ _ _ _ h => cases h
      obtain ⟨sr, hrNF, hrIdx, hrG, hrcard, hrlt, hrdeg, hrsmall⟩ :=
        ih hn.2.1 hcr (lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 _ _ _ hnf) hb)
      obtain ⟨j, a, hj, haNF, haG, hagood, hacard, halt, hadeg, haq, hasmall⟩ := principal_inverse q hn.1 k hqb
      have hheadNF := T.isNF1.p j a T.Z haNF T.isNF1.z haG (T.Z_le _)
      have hheadIdx := T.index_Prop1.p j a T.Z hj T.index_Prop1.z
      have hhead := card_reflect_le (T.head sr) _ (head_nf sr hrNF) hheadNF (head_idx sr hrIdx) hheadIdx
        (by rw [card_head, hrcard, hacard]; exact hn.2.2.2)
      have hsNF := T.isNF1.p j a sr haNF hrNF haG hhead
      refine ⟨T.P j a sr, hsNF, T.index_Prop1.p _ _ _ hj hrIdx, ?_, ?_, halt sr, ?_, ?_⟩
      · intro y hy
        have htail := gc_tail_lt_of_NF1 _ _ _ hsNF
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
        · exact lt_trans_thm _ _ _ (hrG y hy) htail
        · have ha := hagood rfl
          have hawrap := bridge_good_index_lt_wrap 1 a sr ha.1 ha.2
          simp [T.G1] at hy
          rcases hy with rfl | hy | hy
          · exact hawrap
          · exact lt_trans_thm _ _ _ (ha.2 y hy) hawrap
          · exact lt_trans_thm _ _ _ (hrG y hy) htail
      · rw [card_append, hacard, hrcard, T.P_add_eq, T.add.eq_1]
      · exact Nat.max_le.mpr
          ⟨Nat.le_trans (Nat.add_le_add_right hadeg 1) (Nat.le_max_left _ _), Nat.le_trans hrdeg (Nat.le_max_right _ _)⟩
      · intro B hf hs
        have hi := small_inv B _ _ _ hnf hs
        have ha := hasmall B hf hi.1
        have hr := hrsmall B hf hi.2
        constructor
        · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
          · exact ec_index0_lt_posfixed _ B (isNF1_index 0 0 a sr hsNF (Nat.le_refl 0)) hf
              (by intro h; rw [h] at hs; exact lt_Z_inv hs.1)
          · exact lt_trans_thm _ _ _ (T.Lt.p_mid _ _ _ _ _ (haq rfl)) hs.1
        · intro y hy
          simp [T.G1] at hy
          rcases hy with rfl | hy | hy
          · exact ha.1
          · exact ha.2 y hy
          · exact hr.2 y hy

end StopSurjCard

end InverseCardinal

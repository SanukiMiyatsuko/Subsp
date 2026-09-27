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
  | Z =>
      rw [T.add.eq_1, degree, Nat.zero_max]
  | P p c d _ ihd =>
      rw [T.P_add_eq, degree, ihd, degree, Nat.max_assoc]

theorem degree_part (a : T) : degree (T.part a).1 ≤ degree a ∧
    degree (T.part a).2 ≤ degree a := by
  induction a with
  | Z => exact ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | P p c d _ ihd =>
      by_cases hp : p = 0
      · rw [T.part, ite_eq_left hp]
        exact ⟨Nat.zero_le _, Nat.le_refl _⟩
      · rw [T.part, ite_eq_right hp]
        constructor
        · change max (degree c + 1) (degree (T.part d).1) ≤ max (degree c + 1) (degree d)
          exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ihd.1 (Nat.le_max_right _ _)⟩
        · exact Nat.le_trans ihd.2 (Nat.le_max_right _ _)

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
  | z =>
      intro x hx
      cases hx
  | p p c d _ _ hg hhead _ ihd =>
      have hp : p ≤ 0 := head_le_index p 0 c a hh
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      cases hp0
      have hca : c ≤ a := bridge_P0_head_mid_le a c d hh
      intro x hx
      rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 0)] at hx
      rcases List.mem_append.mp hx with hl | hxd
      · cases List.mem_append.mp hl with
        | inl heq =>
            rw [List.mem_singleton.mp heq]
            exact hca
        | inr hxc => exact Or.inl (lt_of_lt_of_le_thm T x c a (hg x hxc) hca)
      · have hda : T.head d ≤ T.P 0 a T.Z := by
          have hpc : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
            rcases hca with h | h
            · exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z h)
            · rw [h]; exact Or.inr rfl
          rcases hhead with h | h
          · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h hpc)
          · rw [h]; exact hpc
        exact ihd hda x hxd

theorem good_of_middle_lt (a b : T) (hs : T.isNF1 (T.P 0 a b))
    (ha : a < T.P 0 a b) : Good (T.P 0 a b) := by
  intro x hx
  have hle := support_le_of_head (T.P 0 a b) a hs (Or.inr rfl) x hx
  exact lt_of_le_of_lt_thm T x a (T.P 0 a b) hle ha

theorem part_snd_lt_wrap (a : T) (hnf : T.isNF1 a) (hg : Good a) :
    (T.part a).2 < T.P 0 a T.Z := by
  have hi := ec_part_snd_index0 a hnf
  apply ec_index0_lt_P0 _ a hi
  intro e f he
  have hp : T.part a = ((T.part a).1, T.P 0 e f) := by
    rw [← he]
  exact hg e (ec_part_snd_middle_mem a (T.part a).1 e f hp)

theorem part_fixed_P_inv {p : Nat} {a b : T}
    (hfix : T.part (T.P p a b) = (T.P p a b, T.Z)) :
    p ≠ 0 ∧ T.part b = (b, T.Z) := by
  have hp : p ≠ 0 := by
    intro hp
    rw [T.part, ite_eq_left hp] at hfix
    have hbad := congrArg Prod.fst hfix
    cases hbad
  rw [T.part, ite_eq_right hp] at hfix
  have hf : (T.part b).1 = b := (T.P.inj (congrArg Prod.fst hfix)).2.2
  have hs : (T.part b).2 = T.Z := congrArg Prod.snd hfix
  exact ⟨hp, Prod.ext hf hs⟩

theorem surj_part_add_fixed : ∀ a b : T,
    T.part a = (a, T.Z) → T.part b = (T.Z, b) →
      T.part (T.add a b) = (a, b) := by
  intro a
  induction a with
  | Z =>
      intro b _ hb
      rw [T.add]
      exact hb
  | P p c d _ ihd =>
      intro b hfix hb
      have hi := part_fixed_P_inv hfix
      rw [T.P_add_eq, T.part, ite_eq_right hi.1, ihd b hi.2 hb]

theorem surj_head_lt_pos_of_index0 (p : Nat) (c b : T)
    (hp : 0 < p) (hb : T.index_Prop1 0 b) :
    T.head b < T.P p c T.Z := by
  cases b with
  | Z =>
      rw [T.head]
      exact T.Lt.Z_lt_P p c T.Z
  | P q e f =>
      cases hb with
      | p _ _ _ hq htail =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          cases hq0
          rw [T.head]
          exact T.Lt.p_head 0 p e c T.Z T.Z hp

theorem surj_add_fixed_index0_NF : ∀ a b : T,
    T.isNF1 a → T.isNF1 b →
    T.part a = (a, T.Z) → T.index_Prop1 0 b →
      T.isNF1 (T.add a b) := by
  intro a
  induction a with
  | Z =>
      intro b _ hb _ _
      rw [T.add]
      exact hb
  | P p c d _ ihd =>
      intro b ha hb hfix hidx
      have hfixInv := part_fixed_P_inv hfix
      have hp : 0 < p := Nat.pos_of_ne_zero hfixInv.1
      have hinv := T.isNF1_P_inv p c d ha
      have htailNF : T.isNF1 (T.add d b) :=
        ihd b hinv.2.1 hb hfixInv.2 hidx
      have hhead : T.head (T.add d b) ≤ T.P p c T.Z := by
        cases d with
        | Z =>
            rw [T.add]
            exact Or.inl (surj_head_lt_pos_of_index0 p c b hp hidx)
        | P q e f =>
            rw [T.P_add_eq]
            exact hinv.2.2.2
      rw [T.P_add_eq]
      exact T.isNF1.p p c (T.add d b)
        hinv.1 htailNF hinv.2.2.1 hhead

theorem part_of_index0 (s : T) (hi : T.index_Prop1 0 s) : T.part s = (T.Z, s) := by
  cases s with
  | Z => rfl
  | P p a b =>
      cases hi with
      | p _ _ _ hp hb =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          rw [T.part, ite_eq_left hp0]

/-- Restore the positive-index prefix that `early_collapse` removed. When the
exponent has a nonzero low part, prepend its high part to the entire input;
`stand` then removes that prefix again. This also preserves the degree bound. -/
theorem exists_uncollapse (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    ∃ x : T, T.isNF1 x ∧ Good x ∧ T.early_collapse x = s ∧
      (∀ B : T, T.part B = (B, T.Z) →
        (∀ y, y ∈ T.G1 0 s → y < B) → s < B → x < B) ∧
      degree x ≤ degree s := by
  cases s with
  | Z =>
      refine ⟨T.Z, T.isNF1.z, ?_, rfl, ?_, Nat.le_refl 0⟩
      · intro x hx
        cases hx
      · intro B _ _ hb
        exact hb
  | P p a b =>
      cases hi with
      | p _ _ _ hp hbIdx =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          cases hp0
          have hn := T.isNF1_P_inv 0 a b hnf
          have haMem : a ∈ T.G1 0 (T.P 0 a b) := by
            rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 0)]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))
          have hbPart := part_of_index0 b hbIdx
          cases hpart : T.part a with
          | mk h l =>
              have hfix : T.part h = (h, T.Z) := by
                have hh := bridge_part_fst_fixed a
                rw [hpart] at hh
                exact hh
              have hadd : T.add h l = a := by
                have hh := bridge_part_add a
                rw [hpart] at hh
                exact hh
              have hparts := bridge_part_NF1 a hn.1
              rw [hpart] at hparts
              have hhGood : Good h := by
                have hh := sg_good0_part_fst a hn.2.2.1
                rw [hpart] at hh
                exact hh
              have hidx := ec_part_snd_index0 a hn.1
              rw [hpart] at hidx
              apply Decidable.byCases (p := h = T.Z)
              · intro hz
                have hal : l = a := by
                  rw [hz, T.add.eq_1] at hadd
                  exact hadd
                have haIdx : T.index_Prop1 0 a := by
                  rw [hal] at hidx
                  exact hidx
                refine ⟨T.P 0 a b, hnf, ?_, rfl, ?_, Nat.le_refl _⟩
                · exact good_of_middle_lt a b hnf (bridge_good_index_lt_wrap 0 a b haIdx hn.2.2.1)
                · intro B _ _ hsB
                  exact hsB
              · intro hne
                apply Decidable.byCases (p := l = T.Z)
                · intro hlz
                  have hha : h = a := by
                    rw [hlz, T.add_Z] at hadd
                    exact hadd
                  have hafix : T.part a = (a, T.Z) := by
                    rw [hpart, hha, hlz]
                  have hxNF := surj_add_fixed_index0_NF a b hn.1 hn.2.1 hafix hbIdx
                  refine ⟨T.add a b, hxNF, ?_, ?_, ?_, ?_⟩
                  · intro y hy
                    rw [bridge_G1_add_eq] at hy
                    rcases List.mem_append.mp hy with hya | hyb
                    · exact lt_of_lt_of_le_thm T y a (T.add a b)
                        (hn.2.2.1 y hya) (wt_add_self_le a b)
                    · have hya := support_le_of_head b a hn.2.1 hn.2.2.2 y hyb
                      have hbne : b ≠ T.Z := by
                        intro hbz
                        rw [hbz, T.G1.eq_1] at hyb
                        cases hyb
                      exact lt_of_le_of_lt_thm T y a (T.add a b)
                        hya (add_lt_add_of_ne_Z a b hbne)
                  · have hxPart := surj_part_add_fixed a b hafix hbPart
                    rw [ec_pair_formula (T.add a b) a b hxNF hxPart]
                    have hane : a ≠ T.Z := by
                      rw [← hha]
                      exact hne
                    rw [ite_eq_right hane, ite_eq_left hn.2.2.2]
                  · intro B hB hG _
                    exact ec_add_index0_lt_pos_of_lt a B b hafix hB hbIdx (hG a haMem)
                  · rw [degree_add, degree]
                    exact Nat.max_le.mpr
                      ⟨Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _),
                        Nat.le_max_right _ _⟩
                · intro hlne
                  have hha : h < a := by
                    rw [← hadd]
                    exact add_lt_add_of_ne_Z h l hlne
                  have hlwrap : l < T.P 0 a T.Z := by
                    have hh := part_snd_lt_wrap a hn.1 hn.2.2.1
                    rw [hpart] at hh
                    exact hh
                  have hwraple : T.P 0 a T.Z ≤ T.P 0 a b := by
                    have hh := wt_add_self_le (T.P 0 a T.Z) b
                    rw [T.P_add_eq, T.add.eq_1] at hh
                    exact hh
                  have hls : l < T.P 0 a b := lt_of_lt_of_le_thm T _ _ _ hlwrap hwraple
                  have has : a < T.add h (T.P 0 a b) := by
                    have hh := bridge_add_left_lt h l (T.P 0 a b) hls
                    rw [hadd] at hh
                    exact hh
                  have hsIdx : T.index_Prop1 0 (T.P 0 a b) :=
                    T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx
                  have hxNF := surj_add_fixed_index0_NF h (T.P 0 a b)
                    hparts.1 hnf hfix hsIdx
                  refine ⟨T.add h (T.P 0 a b), hxNF, ?_, ?_, ?_, ?_⟩
                  · intro y hy
                    rw [bridge_G1_add_eq] at hy
                    rcases List.mem_append.mp hy with hyh | hys
                    · exact lt_of_lt_of_le_thm T y h (T.add h (T.P 0 a b))
                        (hhGood y hyh) (wt_add_self_le h (T.P 0 a b))
                    · have hya := support_le_of_head (T.P 0 a b) a hnf (Or.inr rfl) y hys
                      exact lt_of_le_of_lt_thm T _ _ _ hya has
                  · have hxPart := surj_part_add_fixed h (T.P 0 a b) hfix rfl
                    rw [ec_pair_formula _ h (T.P 0 a b) hxNF hxPart, ite_eq_right hne]
                    have hnhead : ¬ T.head (T.P 0 a b) ≤ T.P 0 h T.Z := by
                      intro hh
                      have hah := bridge_P0_head_mid_le h a b hh
                      exact lt_irrefl_thm h (lt_of_lt_of_le_thm T h a h hha hah)
                    rw [ite_eq_right hnhead]
                  · intro B hB hG _
                    have hhB : h < B := lt_trans_thm h a B hha (hG a haMem)
                    exact ec_add_index0_lt_pos_of_lt h B (T.P 0 a b) hfix hB hsIdx hhB
                  · have hhdeg := (degree_part a).1
                    rw [hpart] at hhdeg
                    rw [degree_add]
                    exact Nat.max_le.mpr
                      ⟨Nat.le_trans hhdeg (Nat.le_of_lt (degree_middle_lt 0 a b)),
                        Nat.le_refl _⟩

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
  have hmem : a ∈ T.G1 0 (T.P p a b) := by
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))
  constructor
  · refine ⟨h.2 a hmem, ?_⟩
    intro y hy
    apply h.2 y
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_left _ (List.mem_append_right _ hy)
  · refine ⟨lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 p a b hnf) h.1, ?_⟩
    intro y hy
    apply h.2 y
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_right _ hy

def Good1 (s : T) : Prop := ∀ y, y ∈ T.G1 1 s → y < s

def OneChain : T → Prop
  | T.Z => True
  | T.P p _ b => p = 1 ∧ OneChain b

theorem card_head (s : T) : T.card_times 1 (T.head s) = T.head (T.card_times 1 s) := by
  cases s with
  | Z => rfl
  | P p a b =>
      rw [T.head, T.card_times.eq_3, T.card_times.eq_3]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        change T.add (T.P 1 _ T.Z) T.Z = T.head (T.add (T.P 1 _ T.Z) _)
        rw [T.add_Z, T.P_add_eq, T.head]
      · rw [ite_eq_right hp]
        change T.add (T.P 1 _ T.Z) T.Z = T.head (T.add (T.P 1 _ T.Z) _)
        rw [T.add_Z, T.P_add_eq, T.head]

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
  induction a generalizing k with
  | Z =>
      refine ⟨T.index_Prop1.z, ?_⟩
      intro y hy
      cases hy
  | P p c d ihc ihd =>
      cases k with
      | zero => exact False.elim (lt_Z_inv ha)
      | succ k =>
          rw [mul_succ_shape 1 T.Z k] at ha
          have hn := T.isNF1_P_inv p c d hnf
          rcases lt_inv p c d 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) ha with hp | (hm | ht)
          · have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
            cases hp0
            have hi := isNF1_index 0 0 c d hnf (Nat.le_refl 0)
            refine ⟨Rank1Termination.index_mono (Nat.zero_le 1) _ hi, ?_⟩
            intro y hy
            rw [index_Prop1_G1_empty 0 _ hi 1 (Nat.zero_lt_succ 0)] at hy
            cases hy
          · exact False.elim (lt_Z_inv hm.2)
          · have hp1 := ht.1
            have hc0 := ht.2.1
            cases hp1
            cases hc0
            have hd := ihd hn.2.1 k ht.2.2
            refine ⟨T.index_Prop1.p 1 T.Z d (Nat.le_refl 1) hd.1, ?_⟩
            intro y hy
            rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1)] at hy
            rcases List.mem_append.mp hy with hl | he
            · cases List.mem_append.mp hl with
              | inl he => exact List.mem_singleton.mp he
              | inr he => cases he
            · exact hd.2 y he

theorem below_mul_good (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) : Good1 a := by
  intro y hy
  have he := (below_mul_support a hnf k ha).2 y hy
  rw [he]
  cases a with
  | Z => cases hy
  | P p c d => exact T.Lt.Z_lt_P p c d

theorem principal_inverse (q : T) (hnf : T.isNF1 q) (k : Nat)
    (hq : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) :
    ∃ p a, p ≤ 1 ∧ T.isNF1 a ∧
      (∀ y, y ∈ T.G1 p a → y < a) ∧
      (p = 1 → T.index_Prop1 1 a ∧ Good1 a) ∧
      T.card_times 1 (T.P p a T.Z) = T.P 1 q T.Z ∧
      (∀ b, T.P p a b < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z) ∧
      degree a ≤ degree q ∧ (p = 1 → a < q) ∧
      ∀ B, T.part B = (B, T.Z) → Small B q → Small B a := by
  rw [mul_succ_shape 1 T.Z k] at hq
  cases q with
  | Z =>
      refine ⟨0, T.Z, Nat.zero_le 1, T.isNF1.z, ?_, ?_, rfl, ?_, Nat.le_refl 0, ?_, ?_⟩
      · intro y hy
        cases hy
      · intro h
        cases h
      · intro b
        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
      · intro h
        cases h
      · intro B _ hsmall
        exact hsmall
  | P p a b =>
      rcases lt_inv p a b 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) hq with hp | (hm | ht)
      · have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
        cases hp0
        have hi := isNF1_index 0 0 a b hnf (Nat.le_refl 0)
        obtain ⟨x, hx⟩ := StopUncollapse.exists_uncollapse (T.P 0 a b) hnf hi
        refine ⟨0, x, Nat.zero_le 1, hx.1, hx.2.1, ?_, ?_, ?_, hx.2.2.2.2, ?_, ?_⟩
        · intro h
          cases h
        · rw [T.card_times.eq_3, ite_eq_left rfl]
          change T.add (T.P 1 (T.early_collapse x) T.Z) T.Z = _
          rw [T.add_Z, hx.2.2.1]
        · intro tail
          exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
        · intro h
          cases h
        · intro B hfix hsmall
          have hxb := hx.2.2.2.1 B hfix hsmall.2 hsmall.1
          refine ⟨hxb, ?_⟩
          intro y hy
          exact lt_trans_thm _ _ _ (hx.2.1 y hy) hxb
      · exact False.elim (lt_Z_inv hm.2)
      · have hp1 := ht.1
        have ha0 := ht.2.1
        cases hp1
        cases ha0
        have hbNF := (T.isNF1_P_inv 1 T.Z b hnf).2.1
        have hbIdx := (below_mul_support b hbNF k ht.2.2).1
        have hbG := below_mul_good b hbNF k ht.2.2
        refine ⟨1, b, Nat.le_refl 1, hbNF, hbG, ?_, ?_, ?_,
          degree_tail_le 1 T.Z b, ?_, ?_⟩
        · intro _
          exact ⟨hbIdx, hbG⟩
        · rw [T.card_times.eq_3, ite_eq_right (by intro h; cases h)]
          change T.add (T.P 1 (T.add (T.P 1 T.Z T.Z) b) T.Z) T.Z = _
          rw [T.add_Z, T.P_add_eq, T.add.eq_1]
        · intro tail
          exact T.Lt.p_mid 1 _ _ _ _ ht.2.2
        · intro _
          exact gc_tail_lt_of_NF1 1 T.Z b hnf
        · intro B _ hsmall
          exact (small_inv B 1 T.Z b hnf hsmall).2

theorem card_append (p : Nat) (a b : T) :
    T.card_times 1 (T.P p a b) = T.add (T.card_times 1 (T.P p a T.Z)) (T.card_times 1 b) := by
  have hh := ca_card_times_add 1 (T.P p a T.Z) b
  rw [T.P_add_eq, T.add.eq_1] at hh
  exact hh

theorem exists_uncard (h : T) (hnf : T.isNF1 h) (hc : OneChain h) (k : Nat)
    (hb : h < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z) :
    ∃ s, T.isNF1 s ∧ T.index_Prop1 1 s ∧ Good1 s ∧ T.card_times 1 s = h ∧
      s < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z ∧
      degree s ≤ degree h ∧
      ∀ B, T.part B = (B, T.Z) → Small B h → Small B s := by
  induction h with
  | Z =>
      refine ⟨T.Z, T.isNF1.z, T.index_Prop1.z, ?_, rfl, T.Lt.Z_lt_P 1 _ T.Z,
        Nat.le_refl 0, ?_⟩
      · intro y hy
        cases hy
      · intro B _ hsmall
        exact hsmall
  | P p q r _ ihr =>
      have hp1 := hc.1
      cases hp1
      have hn := T.isNF1_P_inv 1 q r hnf
      have hrb : r < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z :=
        lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 1 q r hnf) hb
      have hqb : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
        rcases lt_inv 1 q r 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z hb with h | (hm | ht)
        · exact False.elim (Nat.lt_irrefl 1 h)
        · exact hm.2
        · exact False.elim (lt_Z_inv ht.2.2)
      obtain ⟨sr, hsr⟩ := ihr hn.2.1 hc.2 hrb
      obtain ⟨j, hj⟩ := principal_inverse q hn.1 k hqb
      obtain ⟨a, ha⟩ := hj
      have hheadNF : T.isNF1 (T.P j a T.Z) :=
        T.isNF1.p j a T.Z ha.2.1 T.isNF1.z ha.2.2.1 (T.Z_le _)
      have hheadIdx : T.index_Prop1 1 (T.P j a T.Z) :=
        T.index_Prop1.p j a T.Z ha.1 T.index_Prop1.z
      have hcardHead : T.card_times 1 (T.head sr) ≤
          T.card_times 1 (T.P j a T.Z) := by
        rw [card_head, hsr.2.2.2.1, ha.2.2.2.2.1]
        exact hn.2.2.2
      have hhead := card_reflect_le (T.head sr) (T.P j a T.Z)
        (head_nf sr hsr.1) hheadNF (head_idx sr hsr.2.1) hheadIdx hcardHead
      have hsNF : T.isNF1 (T.P j a sr) :=
        T.isNF1.p j a sr ha.2.1 hsr.1 ha.2.2.1 hhead
      refine ⟨T.P j a sr, hsNF, T.index_Prop1.p j a sr ha.1 hsr.2.1,
        ?_, ?_, ?_, ?_, ?_⟩
      · intro y hy
        have htail : sr < T.P j a sr := gc_tail_lt_of_NF1 j a sr hsNF
        cases j with
        | zero =>
            rw [T.G1.eq_2, ite_eq_right (Nat.not_succ_le_zero 0)] at hy
            exact lt_trans_thm _ _ _ (hsr.2.2.1 y hy) htail
        | succ j =>
            have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ ha.1)
            cases hj0
            have haGood := ha.2.2.2.1 rfl
            have halt := bridge_good_index_lt_wrap 1 a sr haGood.1 haGood.2
            rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1)] at hy
            rcases List.mem_append.mp hy with hl | he
            · cases List.mem_append.mp hl with
              | inl he =>
                  rw [List.mem_singleton.mp he]
                  exact halt
              | inr he => exact lt_trans_thm _ _ _ (haGood.2 y he) halt
            · exact lt_trans_thm _ _ _ (hsr.2.2.1 y he) htail
      · rw [card_append, ha.2.2.2.2.1, hsr.2.2.2.1, T.P_add_eq, T.add.eq_1]
      · exact ha.2.2.2.2.2.1 sr
      · have haDeg := ha.2.2.2.2.2.2.1
        have hsrDeg := hsr.2.2.2.2.2.1
        change max (degree a + 1) (degree sr) ≤ max (degree q + 1) (degree r)
        exact Nat.max_le.mpr
          ⟨Nat.le_trans (Nat.add_le_add_right haDeg 1) (Nat.le_max_left _ _),
            Nat.le_trans hsrDeg (Nat.le_max_right _ _)⟩
      · intro B hfix hsmall
        have hinv := small_inv B 1 q r hnf hsmall
        have hasmall := ha.2.2.2.2.2.2.2.2 B hfix hinv.1
        have hsrsmall := hsr.2.2.2.2.2.2 B hfix hinv.2
        constructor
        · cases j with
          | zero =>
              have hidx := isNF1_index 0 0 a sr hsNF (Nat.le_refl 0)
              have hBne : B ≠ T.Z := by
                intro hB
                rw [hB] at hsmall
                exact lt_Z_inv hsmall.1
              exact ec_index0_lt_posfixed _ B hidx hfix hBne
          | succ j =>
              have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ ha.1)
              cases hj0
              have haq := ha.2.2.2.2.2.2.2.1 rfl
              exact lt_trans_thm _ _ _ (T.Lt.p_mid 1 a q sr r haq) hsmall.1
        · intro y hy
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le j)] at hy
          rcases List.mem_append.mp hy with hl | he
          · cases List.mem_append.mp hl with
            | inl he =>
                rw [List.mem_singleton.mp he]
                exact hasmall.1
            | inr he => exact hasmall.2 y he
          · exact hsrsmall.2 y he

end StopSurjCard

end InverseCardinal

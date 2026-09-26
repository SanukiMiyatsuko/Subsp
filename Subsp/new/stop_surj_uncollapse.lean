import Subsp.new.stop_surj_measure

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
  | p p c d hc hd hg hhead ihc ihd =>
      have hp : p ≤ 0 := head_le_index p 0 c a hh
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      cases hp0
      have hca : c ≤ a := bridge_P0_head_mid_le a c d hh
      intro x hx
      rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 0)] at hx
      cases List.mem_append.mp hx with
      | inl hl =>
          cases List.mem_append.mp hl with
          | inl heq =>
              rw [List.mem_singleton.mp heq]
              exact hca
          | inr hxc => exact Or.inl (lt_of_lt_of_le_thm T x c a (hg x hxc) hca)
      | inr hxd =>
          have hda : T.head d ≤ T.P 0 a T.Z := by
            have hpc : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
              cases hca with
              | inl h => exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z h)
              | inr h => rw [h]; exact Or.inr rfl
            cases hhead with
            | inl h => exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h hpc)
            | inr h => rw [h]; exact hpc
          exact ihd hda x hxd

theorem good_of_middle_lt (a b : T) (hs : T.isNF1 (T.P 0 a b))
    (ha : a < T.P 0 a b) : Good (T.P 0 a b) := by
  intro x hx
  have hle := support_le_of_head (T.P 0 a b) a hs (Or.inr rfl) x hx
  exact lt_of_le_of_lt_thm T x a (T.P 0 a b) hle ha

theorem good_index0_lt (a : T) (hi : T.index_Prop1 0 a) (hg : Good a) (b : T) :
    a < T.P 0 a b := by
  cases a with
  | Z => exact T.Lt.Z_lt_P 0 T.Z b
  | P p c d =>
      cases hi with
      | p _ _ _ hp hd =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          cases hp0
          have hc : c ∈ T.G1 0 (T.P 0 c d) := by
            rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 0)]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self c))
          exact T.Lt.p_mid 0 c (T.P 0 c d) d b (hg c hc)

theorem part_snd_lt_wrap (a : T) (hnf : T.isNF1 a) (hg : Good a) :
    (T.part a).2 < T.P 0 a T.Z := by
  have hi := ec_part_snd_index0 a hnf
  apply ec_index0_lt_P0 _ a hi
  intro e f he
  have hp : T.part a = ((T.part a).1, T.P 0 e f) := by
    rw [← he]
  exact hg e (ec_part_snd_middle_mem a (T.part a).1 e f hp)

theorem surj_part_add_fixed : ∀ a b : T,
    T.part a = (a, T.Z) → T.part b = (T.Z, b) →
      T.part (T.add a b) = (a, b) := by
  intro a
  induction a with
  | Z =>
      intro b ha hb
      rw [T.add]
      exact hb
  | P p c d ihc ihd =>
      intro b hfix hb
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [T.part, ite_eq_left hp] at hfix
        have hbad : T.Z = T.P p c d := congrArg Prod.fst hfix
        cases hbad
      · intro hp
        rw [T.part, ite_eq_right hp] at hfix
        cases hdpart : T.part d with
        | mk x y =>
            rw [hdpart] at hfix
            have hx : x = d := by
              have heq : T.P p c x = T.P p c d := congrArg Prod.fst hfix
              cases heq
              rfl
            have hy : y = T.Z := congrArg Prod.snd hfix
            have hdFix : T.part d = (d, T.Z) := by
              rw [hdpart, hx, hy]
            have hrec := ihd b hdFix hb
            rw [T.P_add_eq]
            rw [T.part, ite_eq_right hp, hrec]


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
      intro b ha hb hfix hidx
      rw [T.add]
      exact hb
  | P p c d ihc ihd =>
      intro b ha hb hfix hidx
      have hpne : p ≠ 0 := by
        intro hp0
        rw [T.part, ite_eq_left hp0] at hfix
        have hbad : T.Z = T.P p c d := congrArg Prod.fst hfix
        cases hbad
      have hp : 0 < p := Nat.pos_of_ne_zero hpne
      have hinv := T.isNF1_P_inv p c d ha
      have hdFix : T.part d = (d, T.Z) := by
        rw [T.part, ite_eq_right hpne] at hfix
        cases hpart : T.part d with
        | mk x y =>
            rw [hpart] at hfix
            have hx : x = d := by
              have heq : T.P p c x = T.P p c d := congrArg Prod.fst hfix
              cases heq
              rfl
            have hy : y = T.Z := congrArg Prod.snd hfix
            exact Prod.ext hx hy
      have htailNF : T.isNF1 (T.add d b) :=
        ihd b hinv.2.1 hb hdFix hidx
      have hhead : T.head (T.add d b) ≤ T.P p c T.Z := by
        cases d with
        | Z =>
            rw [T.add]
            exact Or.inl (surj_head_lt_pos_of_index0 p c b hp hidx)
        | P q e f =>
            rw [T.P_add_eq]
            have heq : T.head (T.P q e (T.add f b)) =
                T.head (T.P q e f) := rfl
            rw [heq]
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
      · intro B hB hG hb
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
                have hh := ec_part_fst_fixed a
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
                · exact good_of_middle_lt a b hnf (good_index0_lt a haIdx hn.2.2.1 b)
                · intro B hB hG hsB
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
                    cases List.mem_append.mp hy with
                    | inl hya =>
                        exact lt_of_lt_of_le_thm T y a (T.add a b)
                          (hn.2.2.1 y hya) (wt_add_self_le a b)
                    | inr hyb =>
                        have hya := support_le_of_head b a hn.2.1 hn.2.2.2 y hyb
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
                  · intro B hB hG hsB
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
                    cases List.mem_append.mp hy with
                    | inl hyh =>
                        exact lt_of_lt_of_le_thm T y h (T.add h (T.P 0 a b))
                          (hhGood y hyh) (wt_add_self_le h (T.P 0 a b))
                    | inr hys =>
                        have hya := support_le_of_head (T.P 0 a b) a hnf (Or.inr rfl) y hys
                        exact lt_of_le_of_lt_thm T _ _ _ hya has
                  · have hxPart := surj_part_add_fixed h (T.P 0 a b) hfix rfl
                    rw [ec_pair_formula _ h (T.P 0 a b) hxNF hxPart, ite_eq_right hne]
                    have hnhead : ¬ T.head (T.P 0 a b) ≤ T.P 0 h T.Z := by
                      intro hh
                      have hah := bridge_P0_head_mid_le h a b hh
                      exact lt_irrefl_thm h (lt_of_lt_of_le_thm T h a h hha hah)
                    rw [ite_eq_right hnhead]
                  · intro B hB hG hsB
                    have hhB : h < B := lt_trans_thm h a B hha (hG a haMem)
                    exact ec_add_index0_lt_pos_of_lt h B (T.P 0 a b) hfix hB hsIdx hhB
                  · have hhdeg := (degree_part a).1
                    rw [hpart] at hhdeg
                    rw [degree_add]
                    exact Nat.max_le.mpr
                      ⟨Nat.le_trans hhdeg (Nat.le_of_lt (degree_middle_lt 0 a b)),
                        Nat.le_refl _⟩

#print axioms exists_uncollapse

end StopUncollapse

import Subsp.new.stop_progress_order
open T

theorem ec_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    by_cases hp : p = 0
    · rw [ite_eq_left hp]
      rfl
    · rw [ite_eq_right hp]
      cases hbpart : T.part b with
      | mk c d =>
        have ih := ihb
        rw [hbpart] at ih
        change T.part (T.P p a c) = (T.P p a c, T.Z)
        rw [T.part, ite_eq_right hp]
        rw [ih]

theorem ec_part_snd_index0 (s : T) (hs : T.isNF1 s) :
    T.index_Prop1 0 (T.part s).2 := by
  cases hp : T.part s with
  | mk a b =>
    change T.index_Prop1 0 b
    exact bridge_part_second_index0 s a b hs hp

theorem ec_index0_lt_posfixed (b c : T)
    (hb : T.index_Prop1 0 b)
    (hc : T.part c = (c, T.Z))
    (hcne : c ≠ T.Z) :
    b < c := by
  cases b with
  | Z =>
      cases c with
      | Z => exact False.elim (hcne rfl)
      | P q u v => exact T.Lt.Z_lt_P q u v
  | P p a d =>
      cases hb with
      | p _ _ _ hp htail =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        cases c with
        | Z => exact False.elim (hcne rfl)
        | P q u v =>
          have hqne : q ≠ 0 := by
            intro hq
            rw [T.part, ite_eq_left hq] at hc
            cases hc
          have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
          exact T.Lt.p_head 0 q a u d v hqpos

theorem ec_add_index0_lt_pos_of_lt : ∀ a c b : T,
    T.part a = (a, T.Z) →
    T.part c = (c, T.Z) →
    T.index_Prop1 0 b →
    a < c →
    T.add a b < c := by
  intro a
  induction a with
  | Z =>
    intro c b ha hc hb hlt
    rw [T.add]
    exact ec_index0_lt_posfixed b c hb hc (fun h => by rw [h] at hlt; cases hlt)
  | P p x y ihx ihy =>
    intro c b ha hc hb hlt
    have hpne : p ≠ 0 := by
      intro hp
      rw [T.part, ite_eq_left hp] at ha
      cases ha
    have hyfixed : T.part y = (y, T.Z) := by
      rw [T.part, ite_eq_right hpne] at ha
      cases hpy : T.part y with
      | mk r s =>
        rw [hpy] at ha
        injection ha with hr hs
        have hr' : r = y := by
          injection hr
        have hs' : s = T.Z := hs
        rw [← hr', ← hs']
    cases c with
    | Z => cases hlt
    | P q u v =>
      rw [T.P_add_eq]
      have hcinv : q ≠ 0 := by
        intro hq
        rw [T.part, ite_eq_left hq] at hc
        cases hc
      have hvfixed : T.part v = (v, T.Z) := by
        rw [T.part, ite_eq_right hcinv] at hc
        cases hpv : T.part v with
        | mk r s =>
          rw [hpv] at hc
          injection hc with hr hs
          have hr' : r = v := by
            injection hr
          have hs' : s = T.Z := hs
          rw [← hr', ← hs']
      cases lt_inv p x y q u v hlt with
      | inl hpq =>
          exact T.Lt.p_head p q x u (T.add y b) v hpq
      | inr hor =>
          cases hor with
          | inl hm =>
              cases hm.1
              exact T.Lt.p_mid p x u (T.add y b) v hm.2
          | inr ht =>
              cases ht.1
              cases ht.2.1
              have htail : T.add y b < v :=
                ihy v b hyfixed hvfixed hb ht.2.2
              exact T.Lt.p_tail p x (T.add y b) v htail

#print axioms ec_add_index0_lt_pos_of_lt

theorem ec_pair_formula (s a b : T)
    (hs : T.isNF1 s) (hp : T.part s = (a, b)) :
    T.early_collapse s =
      if a = T.Z then s
      else if T.head b ≤ T.P 0 a T.Z then T.P 0 a b else b := by
  rw [T.early_collapse, hp]
  by_cases ha : a = T.Z
  · rw [ite_eq_left ha, ite_eq_left ha]
  · rw [ite_eq_right ha, ite_eq_right ha]
    have hbnf : T.isNF1 b := by
      have hparts := bridge_part_NF1 s hs
      rw [hp] at hparts
      exact hparts.2
    rw [T.stand, bridge_stand_eq_self_of_NF1 b hbnf]

#print axioms ec_pair_formula

theorem ec_part_snd_middle_mem (s a e f : T)
    (hp : T.part s = (a, T.P 0 e f)) :
    e ∈ T.G1 0 s := by
  have hadd := bridge_part_add s
  rw [hp] at hadd
  have he : e ∈ T.G1 0 (T.P 0 e f) := by
    rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_singleton_self e))
  rw [← hadd, bridge_G1_add_eq]
  exact List.mem_append_right _ he

theorem ec_index0_lt_P0 (b c : T)
    (hb : T.index_Prop1 0 b)
    (hmid : ∀ e f : T, b = T.P 0 e f → e < c) :
    b < T.P 0 c T.Z := by
  cases b with
  | Z => exact T.Lt.Z_lt_P 0 c T.Z
  | P p e f =>
      cases hb with
      | p _ _ _ hp _ =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact T.Lt.p_mid 0 e c f T.Z (hmid e f rfl)

theorem ec_left_below_next_fst (s a b c : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (hp : T.part s = (a, b))
    (hcfix : T.part c = (c, T.Z))
    (hac : a < c) :
    T.early_collapse s < T.P 0 c T.Z := by
  have hbidx : T.index_Prop1 0 b := by
    exact bridge_part_second_index0 s a b hs hp
  have hafix : T.part a = (a, T.Z) := by
    have hh := ec_part_fst_fixed s
    rw [hp] at hh
    exact hh
  have hcne : c ≠ T.Z := by
    intro hc0
    rw [hc0] at hac
    exact False.elim (lt_Z_inv hac)
  have hsltc : s < c := by
    have hadd := bridge_part_add s
    rw [hp] at hadd
    rw [← hadd]
    exact ec_add_index0_lt_pos_of_lt a c b hafix hcfix hbidx hac
  rw [ec_pair_formula s a b hs hp]
  by_cases ha0 : a = T.Z
  · rw [ite_eq_left ha0]
    have hsb : s = b := by
      have hadd := bridge_part_add s
      rw [hp, ha0] at hadd
      exact hadd.symm
    rw [hsb]
    apply ec_index0_lt_P0 b c hbidx
    intro e f hbe
    have hmem : e ∈ T.G1 0 s := by
      rw [hbe] at hp
      exact ec_part_snd_middle_mem s a e f hp
    exact lt_trans_thm e s c (hg e hmem) hsltc
  · rw [ite_eq_right ha0]
    by_cases hkeep : T.head b ≤ T.P 0 a T.Z
    · rw [ite_eq_left hkeep]
      exact T.Lt.p_mid 0 a c b T.Z hac
    · rw [ite_eq_right hkeep]
      apply ec_index0_lt_P0 b c hbidx
      intro e f hbe
      have hmem : e ∈ T.G1 0 s := by
        rw [hbe] at hp
        exact ec_part_snd_middle_mem s a e f hp
      exact lt_trans_thm e s c (hg e hmem) hsltc

#print axioms ec_left_below_next_fst

theorem ec_wrap_fst_le (t c d : T)
    (ht : T.isNF1 t)
    (hp : T.part t = (c, d))
    (hc : c ≠ T.Z) :
    T.P 0 c T.Z ≤ T.early_collapse t := by
  rw [ec_pair_formula t c d ht hp, ite_eq_right hc]
  by_cases hkeep : T.head d ≤ T.P 0 c T.Z
  · rw [ite_eq_left hkeep]
    cases d with
    | Z => exact Or.inr rfl
    | P p e f =>
        exact Or.inl (T.Lt.p_tail 0 c T.Z (T.P p e f) (T.Lt.Z_lt_P p e f))
  · rw [ite_eq_right hkeep]
    have hdshape := bridge_part_second_shape t c d hp
    cases hdshape with
    | inl hd0 =>
        rw [hd0] at hkeep
        exact False.elim (hkeep (T.Z_le (T.P 0 c T.Z)))
    | inr hP =>
        obtain ⟨e, f, heq⟩ := hP
        rw [heq]
        have hce : c < e := by
          cases lt_total_thm c e with
          | inl hlt => exact hlt
          | inr hor =>
              cases hor with
              | inl hec =>
                  have hle : T.P 0 e T.Z ≤ T.P 0 c T.Z :=
                    Or.inl (T.Lt.p_mid 0 e c T.Z T.Z hec)
                  rw [heq] at hkeep
                  exact False.elim (hkeep hle)
              | inr hec =>
                  have hle : T.P 0 e T.Z ≤ T.P 0 c T.Z := by
                    rw [hec]
                    exact Or.inr rfl
                  rw [heq] at hkeep
                  exact False.elim (hkeep hle)
        exact Or.inl (T.Lt.p_mid 0 c e T.Z f hce)

#print axioms ec_wrap_fst_le

theorem ec_P0_lt_snd_of_not_head_le (t c d tail : T)
    (hp : T.part t = (c, d))
    (hnot : ¬ T.head d ≤ T.P 0 c T.Z) :
    T.P 0 c tail < d := by
  have hdshape := bridge_part_second_shape t c d hp
  cases hdshape with
  | inl hd0 =>
      rw [hd0] at hnot
      exact False.elim (hnot (T.Z_le (T.P 0 c T.Z)))
  | inr hP =>
      obtain ⟨e, f, heq⟩ := hP
      rw [heq]
      have hce : c < e := by
        cases lt_total_thm c e with
        | inl hlt => exact hlt
        | inr hor =>
            cases hor with
            | inl hec =>
                have hle : T.P 0 e T.Z ≤ T.P 0 c T.Z :=
                  Or.inl (T.Lt.p_mid 0 e c T.Z T.Z hec)
                rw [heq] at hnot
                exact False.elim (hnot hle)
            | inr hec =>
                have hle : T.P 0 e T.Z ≤ T.P 0 c T.Z := by
                  rw [hec]
                  exact Or.inr rfl
                rw [heq] at hnot
                exact False.elim (hnot hle)
      exact T.Lt.p_mid 0 c e tail f hce

theorem ec_same_fst_mono (s t a b d : T)
    (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hps : T.part s = (a, b))
    (hpt : T.part t = (a, d))
    (hbd : b < d) :
    T.early_collapse s < T.early_collapse t := by
  rw [ec_pair_formula s a b hs hps, ec_pair_formula t a d ht hpt]
  by_cases ha : a = T.Z
  · rw [ite_eq_left ha, ite_eq_left ha]
    have hsb : s = b := by
      have h := bridge_part_add s
      rw [hps, ha] at h
      exact h.symm
    have htd : t = d := by
      have h := bridge_part_add t
      rw [hpt, ha] at h
      exact h.symm
    rw [hsb, htd]
    exact hbd
  · rw [ite_eq_right ha, ite_eq_right ha]
    by_cases hbkeep : T.head b ≤ T.P 0 a T.Z
    · rw [ite_eq_left hbkeep]
      by_cases hdkeep : T.head d ≤ T.P 0 a T.Z
      · rw [ite_eq_left hdkeep]
        exact T.Lt.p_tail 0 a b d hbd
      · rw [ite_eq_right hdkeep]
        exact ec_P0_lt_snd_of_not_head_le t a d b hpt hdkeep
    · rw [ite_eq_right hbkeep]
      by_cases hdkeep : T.head d ≤ T.P 0 a T.Z
      · rw [ite_eq_left hdkeep]
        have hhead : T.head b ≤ T.head d := T.head_mono hbd
        have hcontra : T.head b ≤ T.P 0 a T.Z :=
          partial_order.trans (T.head b) (T.head d) (T.P 0 a T.Z) hhead hdkeep
        exact False.elim (hbkeep hcontra)
      · rw [ite_eq_right hdkeep]
        exact hbd

#print axioms ec_same_fst_mono

theorem ec_good0_mono (s t : T)
    (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hgs : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (_hgt : ∀ x : T, x ∈ T.G1 0 t → x < t)
    (hst : s < t) :
    T.early_collapse s < T.early_collapse t := by
  cases hps : T.part s with
  | mk a b =>
    cases hpt : T.part t with
    | mk c d =>
      have hparts := part_lt_cases s t hst
      rw [hps, hpt] at hparts
      cases hparts with
      | inl hac =>
          have hleft : T.early_collapse s < T.P 0 c T.Z :=
            ec_left_below_next_fst s a b c hs hgs hps
              (by
                have hh := ec_part_fst_fixed t
                rw [hpt] at hh
                exact hh) hac
          have hcne : c ≠ T.Z := by
            intro hc
            rw [hc] at hac
            exact False.elim (lt_Z_inv hac)
          have hright : T.P 0 c T.Z ≤ T.early_collapse t :=
            ec_wrap_fst_le t c d ht hpt hcne
          exact lt_of_lt_of_le_thm T
            (T.early_collapse s) (T.P 0 c T.Z) (T.early_collapse t)
            hleft hright
      | inr heq =>
          have hac : a = c := heq.1
          have hbd : b < d := heq.2
          rw [← hac] at hpt
          exact ec_same_fst_mono s t a b d hs ht hps hpt hbd

#print axioms ec_good0_mono

theorem ec_good0_reflect (s t : T)
    (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hgs : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (hgt : ∀ x : T, x ∈ T.G1 0 t → x < t)
    (h : T.early_collapse s < T.early_collapse t) :
    s < t := by
  cases lt_total_thm s t with
  | inl hst => exact hst
  | inr hor =>
      cases hor with
      | inl hts =>
          have hrev := ec_good0_mono t s ht hs hgt hgs hts
          exact False.elim (lt_asymm_thm h hrev)
      | inr heq =>
          rw [heq] at h
          exact False.elim (lt_irrefl_thm (T.early_collapse t) h)

#print axioms ec_good0_reflect

theorem ec_one_del_NF_index_good1 (s : T)
    (hs : T.isNF1 s)
    (hi : T.index_Prop1 0 s)
    (_hg : ∀ x : T, x ∈ T.G1 1 s → x < s) :
    T.isNF1 (T.one_del s) ∧
      T.index_Prop1 0 (T.one_del s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.one_del s) → x < T.one_del s) := by
  cases s with
  | Z =>
      change T.isNF1 T.Z ∧ T.index_Prop1 0 T.Z ∧
        (∀ x : T, x ∈ T.G1 1 T.Z → x < T.Z)
      constructor
      · exact T.isNF1.z
      · constructor
        · exact T.index_Prop1.z
        · intro x hx
          rw [T.G1.eq_1] at hx
          cases hx
  | P p a b =>
      cases hi with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        cases a with
        | Z =>
            change T.isNF1 b ∧ T.index_Prop1 0 b ∧
              (∀ x : T, x ∈ T.G1 1 b → x < b)
            have hbNF := (T.isNF1_P_inv 0 T.Z b hs).2.1
            constructor
            · exact hbNF
            · constructor
              · exact hib
              · intro x hx
                have hempty := index_Prop1_G1_empty 0 b hib 1
                  (Nat.zero_lt_succ 0)
                rw [hempty] at hx
                cases hx
        | P q c d =>
            change T.isNF1 (T.P 0 (T.P q c d) b) ∧
              T.index_Prop1 0 (T.P 0 (T.P q c d) b) ∧
              (∀ x : T, x ∈ T.G1 1 (T.P 0 (T.P q c d) b) →
                x < T.P 0 (T.P q c d) b)
            exact ⟨hs, T.index_Prop1.p 0 (T.P q c d) b
              (Nat.le_refl 0) hib, _hg⟩

theorem ec_one_del_mono_nonzero (s t : T)
    (hs : T.isNF1 s) (_ht : T.isNF1 t)
    (his : T.index_Prop1 0 s) (hit : T.index_Prop1 0 t)
    (hsz : s ≠ T.Z) (htz : t ≠ T.Z)
    (hst : s < t) :
    T.one_del s < T.one_del t := by
  cases s with
  | Z => exact False.elim (hsz rfl)
  | P p a b =>
    cases his with
    | p _ _ _ hp hib =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      cases t with
      | Z => exact False.elim (htz rfl)
      | P q c d =>
        cases hit with
        | p _ _ _ hq hid =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          subst q
          cases a with
          | Z =>
            cases c with
            | Z =>
                change b < d
                cases lt_inv 0 T.Z b 0 T.Z d hst with
                | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
                | inr hor =>
                    cases hor with
                    | inl hm => exact False.elim (lt_Z_inv hm.2)
                    | inr htcase => exact htcase.2.2
            | P r u v =>
                change b < T.P 0 (T.P r u v) d
                have hheadb : T.head b ≤ T.P 0 T.Z T.Z :=
                  (T.isNF1_P_inv 0 T.Z b hs).2.2.2
                cases b with
                | Z => exact T.Lt.Z_lt_P 0 (T.P r u v) d
                | P k e f =>
                    have hk0 : k = 0 := by
                      exact Nat.eq_zero_of_le_zero
                        (head_le_index k 0 e T.Z hheadb)
                    subst k
                    have hez : e = T.Z := by
                      cases hheadb with
                      | inl hlt =>
                          cases lt_inv 0 e T.Z 0 T.Z T.Z hlt with
                          | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
                          | inr hor =>
                              cases hor with
                              | inl hm => exact False.elim (lt_Z_inv hm.2)
                              | inr htcase => exact False.elim (lt_Z_Z_inv htcase.2.2)
                      | inr heq =>
                          injection heq
                    rw [hez]
                    exact T.Lt.p_mid 0 T.Z (T.P r u v) f d
                      (T.Lt.Z_lt_P r u v)
          | P r u v =>
            cases c with
            | Z =>
                have hinv := lt_inv 0 (T.P r u v) b 0 T.Z d hst
                cases hinv with
                | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
                | inr hor =>
                    cases hor with
                    | inl hm => exact False.elim (lt_P_Z_inv r u v hm.2)
                    | inr htcase =>
                        have heq : T.P r u v = T.Z := htcase.2.1
                        cases heq
            | P k e f =>
                change T.P 0 (T.P r u v) b < T.P 0 (T.P k e f) d
                exact hst

#print axioms ec_one_del_mono_nonzero

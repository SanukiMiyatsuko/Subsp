import Subsp.new.stop_progress

open T



-- extracted from Subsp/new/stop_progress_ec.lean
theorem bridge_early_collapse_closed (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    T.isNF1 (T.early_collapse s) ∧
      T.index_Prop1 0 (T.early_collapse s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.early_collapse s) → x < T.early_collapse s) := by
  cases s with
  | Z =>
    have hec : T.early_collapse T.Z = T.Z := by rfl
    rw [hec]
    constructor
    · exact T.isNF1.z
    · constructor
      · exact T.index_Prop1.z
      · intro x hx
        rw [T.G1.eq_1] at hx
        cases hx
  | P s0 s1 s2 =>
    apply Decidable.byCases (p := s0 = 0)
    · intro hs0
      have hec : T.early_collapse (T.P s0 s1 s2) = T.P s0 s1 s2 := by
        rw [T.early_collapse, T.part, ite_eq_left hs0]
        rfl
      rw [hec]
      subst s0
      have hindex : T.index_Prop1 0 (T.P 0 s1 s2) :=
        isNF1_index 0 0 s1 s2 hs (Nat.le_refl 0)
      constructor
      · exact hs
      · constructor
        · exact hindex
        · intro x hx
          have hempty := index_Prop1_G1_empty 0 (T.P 0 s1 s2) hindex 1 (Nat.zero_lt_succ 0)
          rw [hempty] at hx
          cases hx
    · intro hs0
      cases hp : T.part s2 with
      | mk a b =>
        have hpne : T.P s0 s1 a ≠ T.Z := by
          intro h
          cases h
        have hec : T.early_collapse (T.P s0 s1 s2) =
            T.stand (T.P 0 (T.P s0 s1 a) b) := by
          rw [T.early_collapse, T.part, ite_eq_right hs0, hp]
          change (if T.P s0 s1 a = T.Z then T.P s0 s1 s2
            else T.stand (T.P 0 (T.P s0 s1 a) b)) =
            T.stand (T.P 0 (T.P s0 s1 a) b)
          rw [ite_eq_right hpne]
        rw [hec]
        let p : T := T.P s0 s1 a
        have hsumTail : T.add a b = s2 := by
          have hh := bridge_part_add s2
          rw [hp] at hh
          exact hh
        have hwhole : T.add p b = T.P s0 s1 s2 := by
          unfold p
          rw [T.P_add_eq, hsumTail]
        have hnfFull : T.isNF1 (T.add p b) := by
          rw [hwhole]
          exact hs
        have hgFull : ∀ x : T, x ∈ T.G1 0 (T.add p b) → x < T.add p b := by
          intro x hx
          rw [hwhole] at hx ⊢
          exact hg x hx
        have hpStrong := bridge_strong_add_prefix p b (by
          unfold p
          intro h
          cases h) hnfFull hgFull
        have hbNF : T.isNF1 b := bridge_isNF1_add_inv_right p b hnfFull
        have hbIndex : T.index_Prop1 0 b :=
          bridge_part_second_index0 s2 a b
            (T.isNF1_P_inv s0 s1 s2 hs).2.1 hp
        change
          T.isNF1 (T.stand (T.P 0 p b)) ∧
          T.index_Prop1 0 (T.stand (T.P 0 p b)) ∧
          (∀ x : T, x ∈ T.G1 1 (T.stand (T.P 0 p b)) →
            x < T.stand (T.P 0 p b))
        rw [T.stand, bridge_stand_eq_self_of_NF1 b hbNF]
        apply Decidable.byCases (p := T.head b ≤ T.P 0 p T.Z)
        · intro hhead
          rw [ite_eq_left hhead]
          have hkeep : T.isNF1 (T.P 0 p b) :=
            T.isNF1.p 0 p b hpStrong.1 hbNF hpStrong.2 hhead
          have hindex : T.index_Prop1 0 (T.P 0 p b) :=
            isNF1_index 0 0 p b hkeep (Nat.le_refl 0)
          constructor
          · exact hkeep
          · constructor
            · exact hindex
            · intro x hx
              have hempty := index_Prop1_G1_empty 0 (T.P 0 p b) hindex 1 (Nat.zero_lt_succ 0)
              rw [hempty] at hx
              cases hx
        · intro hhead
          rw [ite_eq_right hhead]
          constructor
          · exact hbNF
          · constructor
            · exact hbIndex
            · intro x hx
              have hempty := index_Prop1_G1_empty 0 b hbIndex 1 (Nat.zero_lt_succ 0)
              rw [hempty] at hx
              cases hx

#print axioms bridge_early_collapse_closed

theorem bridge_add_left_lt (p a b : T) (h : a < b) :
    T.add p a < T.add p b := by
  induction p with
  | Z =>
    rw [T.add, T.add]
    exact h
  | P p0 p1 p2 ih1 ih2 =>
    rw [T.P_add_eq, T.P_add_eq]
    exact T.Lt.p_tail p0 p1 (T.add p2 a) (T.add p2 b) ih2

#print axioms bridge_add_left_lt



-- extracted from Subsp/new/stop_progress_mid.lean
theorem bridge_nat1_NF (k : Nat) :
    T.isNF1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) := by
  have h := mul_isNF1_and_head 1 T.Z T.isNF1.z
    (fun x hx => by
      rw [T.G1.eq_1] at hx
      cases hx) k
  exact h.1

theorem bridge_nat1_index (k : Nat) :
    T.index_Prop1 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) := by
  induction k with
  | zero =>
    rw [T.ofNat, T.mul]
    exact T.index_Prop1.z
  | succ k ih =>
    rw [mul_succ_shape 1 T.Z k]
    exact T.index_Prop1.p 1 T.Z _ (Nat.le_refl 1) ih

theorem bridge_shift_index (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.index_Prop1 1
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  apply Rank1Termination.index_add 1
  · exact bridge_nat1_index k
  · exact Rank1Termination.index_mono (Nat.zero_le 1) c hc

theorem bridge_shift_head_le (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.head (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) ≤
      T.P 1 T.Z T.Z := by
  cases k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    cases c with
    | Z => exact T.Z_le (T.P 1 T.Z T.Z)
    | P p a b =>
      cases hc with
      | p _ _ _ hp htail =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact Or.inl (T.Lt.p_head 0 1 a T.Z T.Z T.Z (Nat.zero_lt_succ 0))
  | succ k =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact Or.inr rfl

theorem bridge_shift_NF (k : Nat) (c : T)
    (hnf : T.isNF1 c) (hc : T.index_Prop1 0 c) :
    T.isNF1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  induction k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    exact hnf
  | succ k ih =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact T.isNF1.p 1 T.Z
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)
      T.isNF1.z ih
      (fun x hx => by
        rw [T.G1.eq_1] at hx
        cases hx)
      (bridge_shift_head_le k c hc)

#print axioms bridge_shift_NF

theorem bridge_shift_lt_wrap (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 T.Z
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  induction k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    cases c with
    | Z => exact T.Lt.Z_lt_P 1 T.Z T.Z
    | P p a b =>
      cases hc with
      | p _ _ _ hp htail =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact T.Lt.p_head 0 1 a T.Z b (T.P 0 a b) (Nat.zero_lt_succ 0)
  | succ k ih =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact T.Lt.p_tail 1 T.Z
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)
      (T.P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c))
      ih

theorem bridge_shift_strong1 (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    ∀ x : T,
      x ∈ T.G1 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) →
      x < T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c := by
  induction k with
  | zero =>
    intro x hx
    rw [T.ofNat, T.mul, T.add] at hx ⊢
    have hempty := index_Prop1_G1_empty 0 c hc 1 (Nat.zero_lt_succ 0)
    rw [hempty] at hx
    cases hx
  | succ k ih =>
    intro x hx
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq] at hx ⊢
    rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1), List.mem_append, List.mem_append] at hx
    cases hx with
    | inl hleft =>
      cases hleft with
      | inl hz =>
        have heq : x = T.Z := List.mem_singleton.mp hz
        rw [heq]
        exact T.Lt.Z_lt_P 1 T.Z _
      | inr hzG =>
        rw [T.G1.eq_1] at hzG
        cases hzG
    | inr htail =>
      have hxtail := ih x htail
      have htailwrap := bridge_shift_lt_wrap k c hc
      exact lt_trans_thm x _ _ hxtail htailwrap

#print axioms bridge_shift_strong1

theorem bridge_part_fst_head_le (s : T) :
    T.head (T.part s).1 ≤ T.head s := by
  cases s with
  | Z =>
      change T.Z ≤ T.Z
      exact Or.inr rfl
  | P p a b =>
      rw [T.part]
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [ite_eq_left hp]
        exact T.Z_le (T.head (T.P p a b))
      · intro hp
        rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            change T.P p a T.Z ≤ T.P p a T.Z
            exact Or.inr rfl

theorem bridge_part_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part s).1 ∧ T.isNF1 (T.part s).2 := by
  induction hs with
  | z => exact ⟨T.isNF1.z, T.isNF1.z⟩
  | p p a b ha hb hg hh iha ihb =>
      rw [T.part]
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [ite_eq_left hp]
        exact ⟨T.isNF1.z, T.isNF1.p p a b ha hb hg hh⟩
      · intro hp
        rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            have hcnf : T.isNF1 c := by
              have h := ihb.1
              rw [hpart] at h
              exact h
            have hdnf : T.isNF1 d := by
              have h := ihb.2
              rw [hpart] at h
              exact h
            have hcle : T.head c ≤ T.head b := by
              have h := bridge_part_fst_head_le b
              rw [hpart] at h
              exact h
            have hhead : T.head c ≤ T.P p a T.Z :=
              partial_order.trans (T.head c) (T.head b) (T.P p a T.Z) hcle hh
            exact ⟨T.isNF1.p p a c ha hcnf hg hhead, hdnf⟩

#print axioms bridge_part_NF1

theorem part_lt_cases : ∀ s t : T, s < t →
    (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2) := by
  intro s
  induction s with
  | Z =>
    intro t h
    cases t with
    | Z => cases h
    | P q u v =>
      rw [T.part]
      rw [T.part]
      apply Decidable.byCases (p := q = 0)
      · intro hq
        rw [ite_eq_left hq]
        exact Or.inr ⟨rfl, T.Lt.Z_lt_P q u v⟩
      · intro hq
        rw [ite_eq_right hq]
        cases hp : T.part v with
        | mk c d =>
          exact Or.inl (T.Lt.Z_lt_P q u c)
  | P p x y ihx ihy =>
    intro t h
    cases t with
    | Z => cases h
    | P q u v =>
      rw [T.part]
      rw [T.part]
      apply Decidable.byCases (p := p = 0)
      · intro hp0
        rw [ite_eq_left hp0]
        apply Decidable.byCases (p := q = 0)
        · intro hq0
          rw [ite_eq_left hq0]
          exact Or.inr ⟨rfl, h⟩
        · intro hq0
          rw [ite_eq_right hq0]
          cases hvp : T.part v with
          | mk c d =>
            exact Or.inl (T.Lt.Z_lt_P q u c)
      · intro hp0
        rw [ite_eq_right hp0]
        cases hyp : T.part y with
        | mk a b =>
          apply Decidable.byCases (p := q = 0)
          · intro hq0
            rw [ite_eq_left hq0]
            have hinv := lt_inv p x y q u v h
            cases hinv with
            | inl hpq =>
              have hpzero : p < 0 := by rw [hq0] at hpq; exact hpq
              exact False.elim (Nat.not_lt_zero p hpzero)
            | inr hor =>
              cases hor with
              | inl hm =>
                have hpq : p = 0 := by rw [hq0] at hm; exact hm.1
                exact False.elim (hp0 hpq)
              | inr ht =>
                have hpq : p = 0 := by rw [hq0] at ht; exact ht.1
                exact False.elim (hp0 hpq)
          · intro hq0
            rw [ite_eq_right hq0]
            cases hvp : T.part v with
            | mk c d =>
              have hinv := lt_inv p x y q u v h
              cases hinv with
              | inl hpq =>
                exact Or.inl (T.Lt.p_head p q x u a c hpq)
              | inr hor =>
                cases hor with
                | inl hm =>
                  cases hm.1
                  exact Or.inl (T.Lt.p_mid p x u a c hm.2)
                | inr ht =>
                  cases ht.1
                  cases ht.2.1
                  have hrec := ihy v ht.2.2
                  rw [hyp, hvp] at hrec
                  cases hrec with
                  | inl hac =>
                    exact Or.inl (T.Lt.p_tail p x a c hac)
                  | inr heq =>
                    apply Or.inr
                    constructor
                    · have hac : a = c := heq.1
                      rw [hac]
                    · exact heq.2

#print axioms part_lt_cases

theorem bridge_early_collapse_part (s a b : T)
    (hp : T.part s = (a, b)) (hb : T.isNF1 b) :
    T.early_collapse s =
      if a = T.Z then b
      else if T.head b ≤ T.P 0 a T.Z then T.P 0 a b else b := by
  rw [T.early_collapse, hp]
  apply Decidable.byCases (p := a = T.Z)
  · intro ha
    rw [ite_eq_left ha]
    have hadd := bridge_part_add s
    rw [hp, ha, T.add] at hadd
    have hbs : b = s := hadd
    rw [ite_eq_left ha]
    exact hbs.symm
  · intro ha
    rw [ite_eq_right ha]
    rw [T.stand, bridge_stand_eq_self_of_NF1 b hb]
    rw [ite_eq_right ha]

#print axioms bridge_early_collapse_part

theorem bridge_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    apply Decidable.byCases (p := p = 0)
    · intro hp
      rw [ite_eq_left hp]
      rfl
    · intro hp
      rw [ite_eq_right hp]
      cases hpb : T.part b with
      | mk c d =>
        have ih := ihb
        rw [hpb] at ih
        change T.part (T.P p a c) = (T.P p a c, T.Z)
        rw [T.part, ite_eq_right hp, ih]

theorem bridge_part_snd_fixed (s : T) :
    T.part (T.part s).2 = (T.Z, (T.part s).2) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    apply Decidable.byCases (p := p = 0)
    · intro hp
      rw [ite_eq_left hp]
      rw [T.part, ite_eq_left hp]
    · intro hp
      rw [ite_eq_right hp]
      cases hpb : T.part b with
      | mk c d =>
        have ih := ihb
        rw [hpb] at ih
        exact ih

#print axioms bridge_part_fst_fixed
#print axioms bridge_part_snd_fixed

theorem bridge_part_lt_of_cases (s t : T)
    (h : (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2)) :
    s < t := by
  cases lt_total_thm s t with
  | inl hst => exact hst
  | inr hor =>
    cases hor with
    | inl hts =>
      have hr := part_lt_cases t s hts
      cases h with
      | inl hfst =>
        cases hr with
        | inl hrev =>
          exact False.elim (lt_asymm_thm hfst hrev)
        | inr hrev =>
          rw [hrev.1] at hfst
          exact False.elim (lt_irrefl_thm _ hfst)
      | inr heq =>
        cases hr with
        | inl hrev =>
          rw [heq.1] at hrev
          exact False.elim (lt_irrefl_thm (T.part t).1 hrev)
        | inr hrev =>
          exact False.elim (lt_asymm_thm heq.2 hrev.2)
    | inr heqst =>
      have hp : T.part s = T.part t := congrArg T.part heqst
      cases h with
      | inl hfst =>
        rw [hp] at hfst
        exact False.elim (lt_irrefl_thm (T.part t).1 hfst)
      | inr hsnd =>
        rw [hp] at hsnd
        exact False.elim (lt_irrefl_thm (T.part t).2 hsnd.2)

#print axioms bridge_part_lt_of_cases

theorem bridge_lt_of_not_le (a b : T) (h : ¬ a ≤ b) : b < a := by
  cases lt_total_thm a b with
  | inl hab => exact False.elim (h (Or.inl hab))
  | inr hor =>
    cases hor with
    | inl hba => exact hba
    | inr heq => exact False.elim (h (Or.inr heq))

theorem bridge_part_prefix_upper (s t : T)
    (h : (T.part s).1 < (T.part t).1) :
    s < (T.part t).1 := by
  apply bridge_part_lt_of_cases s (T.part t).1
  have hfix := bridge_part_fst_fixed t
  rw [hfix]
  exact Or.inl h

theorem bridge_insert_lt (a b d : T)
    (hb : T.isNF1 b) (hd : T.isNF1 d)
    (hpb : T.part b = (T.Z, b))
    (hpd : T.part d = (T.Z, d))
    (hbd : b < d) :
    T.stand (T.P 0 a b) < T.stand (T.P 0 a d) := by
  rw [T.stand, bridge_stand_eq_self_of_NF1 b hb]
  rw [T.stand, bridge_stand_eq_self_of_NF1 d hd]
  have hbshape := bridge_part_second_shape b T.Z b hpb
  have hdshape := bridge_part_second_shape d T.Z d hpd
  cases hbshape with
  | inl hbz =>
    subst b
    cases hdshape with
    | inl hdz =>
      subst d
      exact False.elim (lt_irrefl_thm T.Z hbd)
    | inr hdp =>
      exact match hdp with
      | ⟨f, g, hdeq⟩ => by
        rw [hdeq] at hbd ⊢
        have hleft : T.head T.Z ≤ T.P 0 a T.Z := T.Z_le _
        rw [ite_eq_left hleft]
        change
          T.P 0 a T.Z <
            (if T.P 0 f T.Z ≤ T.P 0 a T.Z then
              T.P 0 a (T.P 0 f g) else T.P 0 f g)
        apply Decidable.byCases (p := T.P 0 f T.Z ≤ T.P 0 a T.Z)
        · intro hfa
          rw [ite_eq_left hfa]
          exact T.Lt.p_tail 0 a T.Z (T.P 0 f g)
            (T.Lt.Z_lt_P 0 f g)
        · intro hfa
          rw [ite_eq_right hfa]
          have haf : T.P 0 a T.Z < T.P 0 f T.Z :=
            bridge_lt_of_not_le (T.P 0 f T.Z) (T.P 0 a T.Z) hfa
          cases lt_inv 0 a T.Z 0 f T.Z haf with
          | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
          | inr hor =>
            cases hor with
            | inl hm => exact T.Lt.p_mid 0 a f T.Z g hm.2
            | inr ht => exact False.elim (lt_Z_inv ht.2.2)
  | inr hbp =>
    exact match hbp with
    | ⟨c, e, hbeq⟩ => by
      subst b
      cases hdshape with
      | inl hdz =>
        subst d
        exact False.elim (lt_Z_inv hbd)
      | inr hdp =>
        exact match hdp with
        | ⟨f, g, hdeq⟩ => by
          subst d
          change
            (if T.P 0 c T.Z ≤ T.P 0 a T.Z then
              T.P 0 a (T.P 0 c e) else T.P 0 c e) <
            (if T.P 0 f T.Z ≤ T.P 0 a T.Z then
              T.P 0 a (T.P 0 f g) else T.P 0 f g)
          apply Decidable.byCases (p := T.P 0 c T.Z ≤ T.P 0 a T.Z)
          · intro hca
            rw [ite_eq_left hca]
            apply Decidable.byCases (p := T.P 0 f T.Z ≤ T.P 0 a T.Z)
            · intro hfa
              rw [ite_eq_left hfa]
              exact T.Lt.p_tail 0 a (T.P 0 c e) (T.P 0 f g) hbd
            · intro hfa
              rw [ite_eq_right hfa]
              have haf : T.P 0 a T.Z < T.P 0 f T.Z :=
                bridge_lt_of_not_le (T.P 0 f T.Z) (T.P 0 a T.Z) hfa
              cases lt_inv 0 a T.Z 0 f T.Z haf with
              | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
              | inr hor =>
                cases hor with
                | inl hm => exact T.Lt.p_mid 0 a f (T.P 0 c e) g hm.2
                | inr ht => exact False.elim (lt_Z_inv ht.2.2)
          · intro hca
            rw [ite_eq_right hca]
            apply Decidable.byCases (p := T.P 0 f T.Z ≤ T.P 0 a T.Z)
            · intro hfa
              rw [ite_eq_left hfa]
              have hcf : c < f ∨ (c = f ∧ e < g) := by
                cases lt_inv 0 c e 0 f g hbd with
                | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
                | inr hor =>
                  cases hor with
                  | inl hm => exact Or.inl hm.2
                  | inr ht => exact Or.inr ⟨ht.2.1, ht.2.2⟩
              cases hcf with
              | inl hcf =>
                have hclef : c ≤ f := Or.inl hcf
                have hflea : f ≤ a := by
                  cases hfa with
                  | inl hlt =>
                    cases lt_inv 0 f T.Z 0 a T.Z hlt with
                    | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                    | inr hor =>
                      cases hor with
                      | inl hm => exact Or.inl hm.2
                      | inr ht => exact Or.inr ht.2.1
                  | inr heq =>
                    cases heq
                    exact Or.inr rfl
                have hcla : c ≤ a := partial_order.trans c f a hclef hflea
                have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
                  cases hcla with
                  | inl hlt => exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
                  | inr heq => rw [heq]; exact Or.inr rfl
                exact False.elim (hca hheadca)
              | inr heq =>
                have hcfEq : c = f := heq.1
                subst f
                have hclea : c ≤ a := by
                  cases hfa with
                  | inl hlt =>
                    cases lt_inv 0 c T.Z 0 a T.Z hlt with
                    | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                    | inr hor =>
                      cases hor with
                      | inl hm => exact Or.inl hm.2
                      | inr ht => exact Or.inr ht.2.1
                  | inr heqca =>
                    cases heqca
                    exact Or.inr rfl
                have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
                  cases hclea with
                  | inl hlt => exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
                  | inr heqca => rw [heqca]; exact Or.inr rfl
                exact False.elim (hca hheadca)
            · intro hfa
              rw [ite_eq_right hfa]
              exact hbd

#print axioms bridge_insert_lt



-- extracted from Subsp/new/stop_progress_order.lean
theorem bridge_G1_add_eq (u : Nat) (a b : T) :
    T.G1 u (T.add a b) = T.G1 u a ++ T.G1 u b := by
  induction a with
  | Z =>
    rw [T.add]
    rw [T.G1.eq_1]
    rw [List.nil_append]
  | P p x y ihx ihy =>
    cases b with
    | Z =>
      rw [T.add_Z]
      rw [T.G1.eq_1]
      rw [List.append_nil]
    | P q c d =>
      rw [T.P_add_eq]
      rw [T.G1.eq_2, T.G1.eq_2]
      apply Decidable.byCases (p := u ≤ p)
      · intro hup
        rw [ite_eq_left hup, ite_eq_left hup]
        rw [ihy]
        rw [← List.append_assoc]
      · intro hup
        rw [ite_eq_right hup, ite_eq_right hup]
        exact ihy

theorem bridge_head_le_self (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P p a b =>
    cases b with
    | Z => exact Or.inr rfl
    | P q c d =>
      exact Or.inl (T.Lt.p_tail p a T.Z (T.P q c d)
        (T.Lt.Z_lt_P q c d))

theorem bridge_part_fst_le_self (s : T) : (T.part s).1 ≤ s := by
  apply Decidable.byCases (p := (T.part s).2 = T.Z)
  · intro hb
    have hadd := bridge_part_add s
    rw [hb, T.add_Z] at hadd
    exact Or.inr hadd
  · intro hb
    apply Or.inl
    apply bridge_part_lt_of_cases (T.part s).1 s
    have hfix := bridge_part_fst_fixed s
    rw [hfix]
    have hzb : T.Z < (T.part s).2 := by
      cases T.Z_le (T.part s).2 with
      | inl hlt => exact hlt
      | inr heq => exact False.elim (hb heq.symm)
    exact Or.inr ⟨rfl, hzb⟩

#print axioms bridge_part_fst_le_self

theorem bridge_mid_mem_G1_zero (a b : T) :
    a ∈ T.G1 0 (T.P 0 a b) := by
  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
  exact List.mem_append_left _
    (List.mem_append_left _ (List.mem_singleton_self a))

theorem bridge_remainder_member_lt (s a c d : T)
    (hp : T.part s = (a, T.P 0 c d))
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    c < s := by
  have hadd := bridge_part_add s
  rw [hp] at hadd
  have hmemTail : c ∈ T.G1 0 (T.P 0 c d) :=
    bridge_mid_mem_G1_zero c d
  have hmemAdd : c ∈ T.G1 0 (T.add a (T.P 0 c d)) := by
    rw [bridge_G1_add_eq]
    exact List.mem_append_right _ hmemTail
  rw [hadd] at hmemAdd
  exact hg c hmemAdd

theorem bridge_early_collapse_upper (s c : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (hsc : s < c) :
    T.early_collapse s < T.P 0 c T.Z := by
  cases hp : T.part s with
  | mk a b =>
    have hadd := bridge_part_add s
    rw [hp] at hadd
    have hnfAdd : T.isNF1 (T.add a b) := by
      rw [hadd]
      exact hs
    have hbNF : T.isNF1 b := bridge_isNF1_add_inv_right a b hnfAdd
    have hec := bridge_early_collapse_part s a b hp hbNF
    apply Decidable.byCases (p := a = T.Z)
    · intro ha
      rw [hec, ite_eq_left ha]
      have hbEq : b = s := by
        rw [ha, T.add] at hadd
        exact hadd
      have hbshape := bridge_part_second_shape s a b hp
      cases hbshape with
      | inl hbz =>
        rw [hbz]
        exact T.Lt.Z_lt_P 0 c T.Z
      | inr hbp =>
        exact match hbp with
        | ⟨e, f, hbeq⟩ => by
          rw [hbeq]
          have hes : e < s := bridge_remainder_member_lt s a e f (by
            rw [hbeq] at hp
            exact hp) hg
          have hecLt : e < c := lt_trans_thm e s c hes hsc
          exact T.Lt.p_mid 0 e c f T.Z hecLt
    · intro ha
      rw [hec, ite_eq_right ha]
      apply Decidable.byCases (p := T.head b ≤ T.P 0 a T.Z)
      · intro hhead
        rw [ite_eq_left hhead]
        have has0 := bridge_part_fst_le_self s
        have has : a ≤ s := by
          rw [hp] at has0
          exact has0
        have hac : a < c := lt_of_le_of_lt_thm T a s c has hsc
        exact T.Lt.p_mid 0 a c b T.Z hac
      · intro hhead
        rw [ite_eq_right hhead]
        have hbshape := bridge_part_second_shape s a b hp
        cases hbshape with
        | inl hbz =>
          rw [hbz]
          exact T.Lt.Z_lt_P 0 c T.Z
        | inr hbp =>
          exact match hbp with
          | ⟨e, f, hbeq⟩ => by
            rw [hbeq]
            have hes : e < s := bridge_remainder_member_lt s a e f (by
              rw [hbeq] at hp
              exact hp) hg
            have hecLt : e < c := lt_trans_thm e s c hes hsc
            exact T.Lt.p_mid 0 e c f T.Z hecLt

#print axioms bridge_early_collapse_upper

theorem bridge_part_base_le_early_collapse (t : T)
    (ht : T.isNF1 t) (hc : (T.part t).1 ≠ T.Z) :
    T.P 0 (T.part t).1 T.Z ≤ T.early_collapse t := by
  cases hp : T.part t with
  | mk c d =>
    have hadd := bridge_part_add t
    rw [hp] at hadd
    have hnfAdd : T.isNF1 (T.add c d) := by
      rw [hadd]
      exact ht
    have hdNF : T.isNF1 d := bridge_isNF1_add_inv_right c d hnfAdd
    have hc' : c ≠ T.Z := by
      intro hcz
      apply hc
      rw [hp]
      exact hcz
    have hec := bridge_early_collapse_part t c d hp hdNF
    change T.P 0 c T.Z ≤ T.early_collapse t
    rw [hec, ite_eq_right hc']
    apply Decidable.byCases (p := T.head d ≤ T.P 0 c T.Z)
    · intro hhead
      rw [ite_eq_left hhead]
      cases T.Z_le d with
      | inl hzd =>
        exact Or.inl (T.Lt.p_tail 0 c T.Z d hzd)
      | inr hzd =>
        have hdZ : d = T.Z := hzd.symm
        rw [hdZ]
        exact Or.inr rfl
    · intro hhead
      rw [ite_eq_right hhead]
      have hbaseHead : T.P 0 c T.Z < T.head d :=
        bridge_lt_of_not_le (T.head d) (T.P 0 c T.Z) hhead
      have hheadD : T.head d ≤ d := bridge_head_le_self d
      exact Or.inl (lt_of_lt_of_le_thm T (T.P 0 c T.Z) (T.head d) d
        hbaseHead hheadD)

#print axioms bridge_part_base_le_early_collapse

theorem bridge_early_collapse_lt (s t : T)
    (hs : T.isNF1 s)
    (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
    (hst : s < t) :
    T.early_collapse s < T.early_collapse t := by
  cases hps : T.part s with
  | mk a b =>
    cases hpt : T.part t with
    | mk c d =>
      have hsadd := bridge_part_add s
      rw [hps] at hsadd
      have htadd := bridge_part_add t
      rw [hpt] at htadd
      have hsnfadd : T.isNF1 (T.add a b) := by
        rw [hsadd]
        exact hs
      have htnfadd : T.isNF1 (T.add c d) := by
        rw [htadd]
        exact ht
      have hbNF : T.isNF1 b := bridge_isNF1_add_inv_right a b hsnfadd
      have hdNF : T.isNF1 d := bridge_isNF1_add_inv_right c d htnfadd
      have hbfix0 := bridge_part_snd_fixed s
      have hdfix0 := bridge_part_snd_fixed t
      rw [hps] at hbfix0
      rw [hpt] at hdfix0
      have hbfix : T.part b = (T.Z, b) := hbfix0
      have hdfix : T.part d = (T.Z, d) := hdfix0
      have hparts := part_lt_cases s t hst
      rw [hps, hpt] at hparts
      cases hparts with
      | inl hac =>
        have hsc0 := bridge_part_prefix_upper s t
          (by
            rw [hps, hpt]
            exact hac)
        have hsc : s < c := by
          rw [hpt] at hsc0
          exact hsc0
        have hupper := bridge_early_collapse_upper s c hs hsg hsc
        have hcne : c ≠ T.Z := by
          intro hcz
          rw [hcz] at hac
          exact lt_Z_inv hac
        have hlower0 := bridge_part_base_le_early_collapse t ht (by
          rw [hpt]
          exact hcne)
        have hlower : T.P 0 c T.Z ≤ T.early_collapse t := by
          rw [hpt] at hlower0
          exact hlower0
        exact lt_of_lt_of_le_thm T (T.early_collapse s)
          (T.P 0 c T.Z) (T.early_collapse t) hupper hlower
      | inr heq =>
        have hacEq : a = c := heq.1
        have hbd : b < d := heq.2
        subst c
        apply Decidable.byCases (p := a = T.Z)
        · intro ha
          have hecs := bridge_early_collapse_part s a b hps hbNF
          have hect := bridge_early_collapse_part t a d hpt hdNF
          rw [hecs, hect, ite_eq_left ha, ite_eq_left ha]
          exact hbd
        · intro ha
          rw [T.early_collapse, hps, ite_eq_right ha]
          rw [T.early_collapse, hpt, ite_eq_right ha]
          exact bridge_insert_lt a b d hbNF hdNF hbfix hdfix hbd

#print axioms bridge_early_collapse_lt

theorem bridge_card_times_lt_same (n : Nat) :
    ∀ c d : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d → T.card_times n c < T.card_times n d := by
  intro c
  induction c with
  | Z =>
    intro d hcNF hcIdx hdNF hdIdx hcd
    have hdne : d ≠ T.Z := by
      intro heq
      rw [heq] at hcd
      exact lt_Z_inv hcd
    have hctne : T.card_times n d ≠ T.Z := bridge_card_times_ne_Z n d hdne
    cases T.Z_le (T.card_times n d) with
    | inl hlt =>
      rw [T.card_times]
      exact hlt
    | inr heq =>
      exact False.elim (hctne heq.symm)
  | P p a b iha ihb =>
    intro d hcNF hcIdx hdNF hdIdx hcd
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      cases d with
      | Z => exact False.elim (lt_Z_inv hcd)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          subst q
          exact match T.isNF1_P_inv 0 a b hcNF with
          | ⟨haNF, hbNF, haG, hheadb⟩ => by
            exact match T.isNF1_P_inv 0 e f hdNF with
            | ⟨heNF, hfNF, heG, hheadf⟩ => by
              cases n with
              | zero =>
                rw [T.card_times, T.card_times]
                exact hcd
              | succ k =>
                rw [T.card_times, T.card_times]
                rw [ite_eq_left rfl, ite_eq_left rfl]
                rw [← add_eq_hAdd
                  (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                  (T.card_times (k + 1) b),
                  T.P_add_eq]
                rw [← add_eq_hAdd
                  (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse e) T.Z)
                  (T.card_times (k + 1) f),
                  T.P_add_eq]
                change
                  T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a))
                    (T.card_times (k + 1) b) <
                  T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse e))
                    (T.card_times (k + 1) f)
                cases lt_inv 0 a b 0 e f hcd with
                | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                | inr hor =>
                  cases hor with
                  | inl hmid =>
                    have hae : a < e := hmid.2
                    have hec : T.early_collapse a < T.early_collapse e :=
                      bridge_early_collapse_lt a e haNF haG heNF hae
                    have hshift := bridge_add_left_lt
                      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a) (T.early_collapse e) hec
                    exact T.Lt.p_mid 1 _ _ _ _ hshift
                  | inr htail =>
                    have hae : a = e := htail.2.1
                    subst e
                    have hbf : b < f := htail.2.2
                    have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
                    exact T.Lt.p_tail 1
                      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                        (T.early_collapse a))
                      (T.card_times (k + 1) b)
                      (T.card_times (k + 1) f) hrec

#print axioms bridge_card_times_lt_same

theorem bridge_shift_level_lt : ∀ k l : Nat, k < l →
    ∀ x y : T, T.index_Prop1 0 x → T.index_Prop1 0 y →
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) x <
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) y := by
  intro k
  induction k with
  | zero =>
    intro l hkl x y hx hy
    cases l with
    | zero => exact False.elim (Nat.lt_irrefl 0 hkl)
    | succ l =>
      rw [T.ofNat, T.mul, T.add]
      rw [mul_succ_shape 1 T.Z l, T.P_add_eq]
      cases x with
      | Z => exact T.Lt.Z_lt_P 1 T.Z _
      | P p a b =>
        cases hx with
        | p _ _ _ hp htail =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          exact T.Lt.p_head 0 1 a T.Z b _ (Nat.zero_lt_succ 0)
  | succ k ih =>
    intro l hkl x y hx hy
    cases l with
    | zero => exact False.elim (Nat.not_lt_zero (k + 1) hkl)
    | succ l =>
      have hkl' : k < l := Nat.lt_of_succ_lt_succ hkl
      rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
      rw [mul_succ_shape 1 T.Z l, T.P_add_eq]
      exact T.Lt.p_tail 1 T.Z _ _ (ih l hkl' x y hx hy)

#print axioms bridge_shift_level_lt

theorem bridge_card_times_level_lt (m n : Nat) (c d : T)
    (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ T.Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ T.Z) :
    T.card_times m c < T.card_times n d := by
  cases c with
  | Z => exact False.elim (hcne rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      cases d with
      | Z => exact False.elim (hdne rfl)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          subst q
          exact match T.isNF1_P_inv 0 a b hcNF with
          | ⟨haNF, hbNF, haG, hheadb⟩ => by
            exact match T.isNF1_P_inv 0 e f hdNF with
            | ⟨heNF, hfNF, heG, hheadf⟩ => by
              have haEC := bridge_early_collapse_closed a haNF haG
              have heEC := bridge_early_collapse_closed e heNF heG
              cases m with
              | zero =>
                cases n with
                | zero => exact False.elim (Nat.lt_irrefl 0 hmn)
                | succ l =>
                  rw [T.card_times]
                  rw [T.card_times, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                    (T.card_times (l + 1) f), T.P_add_eq]
                  exact T.Lt.p_head 0 1 a
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) (T.early_collapse e))
                    b (T.card_times (l + 1) f) (Nat.zero_lt_succ 0)
              | succ k =>
                cases n with
                | zero => exact False.elim (Nat.not_lt_zero (k + 1) hmn)
                | succ l =>
                  have hkl : k < l := Nat.lt_of_succ_lt_succ hmn
                  rw [T.card_times, T.card_times]
                  rw [ite_eq_left rfl, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                    (T.card_times (k + 1) b), T.P_add_eq]
                  rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                    (T.card_times (l + 1) f), T.P_add_eq]
                  have hshift := bridge_shift_level_lt k l hkl
                    (T.early_collapse a) (T.early_collapse e) haEC.2.1 heEC.2.1
                  exact T.Lt.p_mid 1 _ _ _ _ hshift

#print axioms bridge_card_times_level_lt


theorem bridge_add_left_le (p a b : T) (h : a ≤ b) :
    T.add p a ≤ T.add p b := by
  cases h with
  | inl hlt => exact Or.inl (bridge_add_left_lt p a b hlt)
  | inr heq => rw [heq]; exact Or.inr rfl

theorem bridge_shift_lt_outer (k : Nat) (c tail : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail := by
  cases k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    cases c with
    | Z => exact T.Lt.Z_lt_P 1 T.Z tail
    | P p a b =>
      cases hc with
      | p _ _ _ hp hidx =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact T.Lt.p_head 0 1 a (T.P 0 a b) b tail (Nat.zero_lt_succ 0)
  | succ k =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact T.Lt.p_mid 1 T.Z
      (T.P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c))
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail
      (T.Lt.Z_lt_P 1 T.Z _)

#print axioms bridge_shift_lt_outer

theorem bridge_early_collapse_le (s t : T)
    (hs : T.isNF1 s) (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
    (hst : s ≤ t) : T.early_collapse s ≤ T.early_collapse t := by
  cases hst with
  | inl hlt => exact Or.inl (bridge_early_collapse_lt s t hs hsg ht hlt)
  | inr heq => rw [heq]; exact Or.inr rfl

theorem bridge_P0_head_mid_le (a e f : T)
    (h : T.head (T.P 0 e f) ≤ T.P 0 a T.Z) : e ≤ a := by
  change T.P 0 e T.Z ≤ T.P 0 a T.Z at h
  cases h with
  | inl hlt =>
    cases lt_inv 0 e T.Z 0 a T.Z hlt with
    | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
    | inr hor =>
      cases hor with
      | inl hm => exact Or.inl hm.2
      | inr ht => exact Or.inr ht.2.1
  | inr heq =>
    cases heq
    exact Or.inr rfl

theorem bridge_lift_P1_le (a b : T) (h : a ≤ b) :
    T.P 1 a T.Z ≤ T.P 1 b T.Z := by
  cases h with
  | inl hlt => exact Or.inl (T.Lt.p_mid 1 a b T.Z T.Z hlt)
  | inr heq => rw [heq]; exact Or.inr rfl

theorem bridge_card_times_closed (n : Nat) :
    ∀ c : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 (T.card_times n c) ∧
        T.index_Prop1 1 (T.card_times n c) ∧
        (∀ x : T, x ∈ T.G1 1 (T.card_times n c) →
          x < T.card_times n c) := by
  intro c
  induction c with
  | Z =>
    intro hcNF hcIdx
    rw [T.card_times]
    constructor
    · exact T.isNF1.z
    · constructor
      · exact T.index_Prop1.z
      · intro x hx
        rw [T.G1.eq_1] at hx
        cases hx
  | P p a b iha ihb =>
    intro hcNF hcIdx
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      exact match T.isNF1_P_inv 0 a b hcNF with
      | ⟨haNF, hbNF, haG, hheadb⟩ => by
        cases n with
        | zero =>
          rw [T.card_times]
          have hidx0 : T.index_Prop1 0 (T.P 0 a b) :=
            T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx
          have hidx1 : T.index_Prop1 1 (T.P 0 a b) :=
            Rank1Termination.index_mono (Nat.zero_le 1) (T.P 0 a b) hidx0
          have hempty := index_Prop1_G1_empty 0 (T.P 0 a b) hidx0 1
            (Nat.zero_lt_succ 0)
          constructor
          · exact hcNF
          · constructor
            · exact hidx1
            · intro x hx
              rw [hempty] at hx
              cases hx
        | succ k =>
          rw [T.card_times, ite_eq_left rfl]
          rw [← add_eq_hAdd
                (T.P 1
                  ((T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) +
                    (T.early_collapse a)) T.Z)
                (T.card_times (k + 1) b),
              T.P_add_eq, T.add.eq_1]
          let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
            (T.early_collapse a)
          let R := T.card_times (k + 1) b
          change
            T.isNF1 (T.P 1 M R) ∧
              T.index_Prop1 1 (T.P 1 M R) ∧
                (∀ x : T, x ∈ T.G1 1 (T.P 1 M R) → x < T.P 1 M R)
          have hec := bridge_early_collapse_closed a haNF haG
          have hMNF : T.isNF1 M := by
            unfold M
            exact bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
          have hMG : ∀ x : T, x ∈ T.G1 1 M → x < M := by
            unfold M
            exact bridge_shift_strong1 k (T.early_collapse a) hec.2.1
          have htail := ihb hbNF hbIdx
          have hRhead : T.head R ≤ T.P 1 M T.Z := by
            cases b with
            | Z =>
              unfold R
              rw [T.card_times, T.head]
              exact T.Z_le (T.P 1 M T.Z)
            | P q e f =>
              cases hbIdx with
              | p _ _ _ hq0 hfIdx =>
                have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
                subst q
                exact match T.isNF1_P_inv 0 e f hbNF with
                | ⟨heNF, hfNF, heG, hheadf⟩ => by
                  have hea : e ≤ a := bridge_P0_head_mid_le a e f hheadb
                  have hecE := bridge_early_collapse_closed e heNF heG
                  have hecLe : T.early_collapse e ≤ T.early_collapse a :=
                    bridge_early_collapse_le e a heNF heG haNF hea
                  have hshiftLe :
                      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                        (T.early_collapse e) ≤ M := by
                    unfold M
                    exact bridge_add_left_le
                      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse e) (T.early_collapse a) hecLe
                  unfold R
                  rw [T.card_times, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                    (T.P 1
                      ((T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) +
                        (T.early_collapse e)) T.Z)
                    (T.card_times (k + 1) f), T.P_add_eq, T.add.eq_1]
                  rw [T.head]
                  exact bridge_lift_P1_le _ _ hshiftLe
          have hcurNF : T.isNF1 (T.P 1 M R) :=
            T.isNF1.p 1 M R hMNF htail.1 hMG hRhead
          have hcurIdx : T.index_Prop1 1 (T.P 1 M R) :=
            T.index_Prop1.p 1 M R (Nat.le_refl 1) htail.2.1
          constructor
          · exact hcurNF
          · constructor
            · exact hcurIdx
            · intro x hx
              rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
                List.mem_append, List.mem_append] at hx
              cases hx with
              | inl hleft =>
                cases hleft with
                | inl hxm =>
                  have hxEq : x = M := List.mem_singleton.mp hxm
                  rw [hxEq]
                  unfold M
                  exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
                | inr hxG =>
                  have hxM : x < M := hMG x hxG
                  have hMwhole : M < T.P 1 M R := by
                    unfold M
                    exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
                  exact lt_trans_thm x M (T.P 1 M R) hxM hMwhole
              | inr hxR =>
                have hxRt : x < R := htail.2.2 x hxR
                have hRle : R ≤ T.P 1 M R :=
                  T.isNF1_tail_le (T.P 1 M R) hcurNF 1 M R rfl
                exact lt_of_lt_of_le_thm T x R (T.P 1 M R) hxRt hRle

#print axioms bridge_card_times_closed

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
  intro c
  induction c with
  | Z =>
    intro y hcNF hcIdx hyNF hyIdx hyG hbound
    rw [T.card_times.eq_1, T.add.eq_1]
    exact ⟨hyNF, hyIdx, hyG⟩
  | P p a b iha ihb =>
    intro y hcNF hcIdx hyNF hyIdx hyG hbound
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      exact match T.isNF1_P_inv 0 a b hcNF with
      | ⟨haNF, hbNF, haG, hheadb⟩ => by
        have hec := bridge_early_collapse_closed a haNF haG
        let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
          (T.early_collapse a)
        have hMNF : T.isNF1 M := by
          unfold M
          exact bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
        have hMG : ∀ x : T, x ∈ T.G1 1 M → x < M := by
          unfold M
          exact bridge_shift_strong1 k (T.early_collapse a) hec.2.1
        have htail := ihb y hbNF hbIdx hyNF hyIdx hyG hbound
        let R := T.add (T.card_times (k + 1) b) y
        have hRNF : T.isNF1 R := by
          unfold R
          exact htail.1
        have hRIdx : T.index_Prop1 1 R := by
          unfold R
          exact htail.2.1
        have hRG : ∀ x : T, x ∈ T.G1 1 R → x < R := by
          unfold R
          exact htail.2.2
        have hRhead : T.head R ≤ T.P 1 M T.Z := by
          cases b with
          | Z =>
            unfold R
            rw [T.card_times.eq_1, T.add.eq_1]
            have hzNF : T.isNF1 (T.P 0 a T.Z) :=
              T.isNF1.p 0 a T.Z haNF T.isNF1.z haG (T.Z_le _)
            have hzIdx : T.index_Prop1 0 (T.P 0 a T.Z) :=
              T.index_Prop1.p 0 a T.Z (Nat.le_refl 0) T.index_Prop1.z
            have hylt := hbound (T.P 0 a T.Z) hzNF hzIdx (by
              intro heq
              cases heq)
            rw [T.card_times.eq_3, ite_eq_left rfl] at hylt
            rw [← add_eq_hAdd
                  (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                  (T.card_times (k + 1) T.Z),
                T.card_times.eq_1, T.add_Z] at hylt
            have hheadle := T.head_mono hylt
            unfold M
            exact hheadle
          | P q e f =>
            have hbne : T.P q e f ≠ T.Z := by intro heq; cases heq
            unfold R
            rw [bridge_head_add_ne_Z (T.card_times (k + 1) (T.P q e f)) y
              (bridge_card_times_ne_Z (k + 1) (T.P q e f) hbne)]
            have hclosed := bridge_card_times_closed (k + 1) (T.P 0 a (T.P q e f)) hcNF
              (T.index_Prop1.p 0 a (T.P q e f) (Nat.le_refl 0) hbIdx)
            have hinv := T.isNF1_P_inv 1 M (T.card_times (k + 1) (T.P q e f)) (by
              -- identify the closed term with its unfolded card-times shape
              rw [T.card_times.eq_3, ite_eq_left rfl] at hclosed
              rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                    (T.card_times (k + 1) (T.P q e f)),
                  T.P_add_eq, T.add.eq_1] at hclosed
              have hclosedNF := hclosed.1
              change T.isNF1 (T.P 1 M (T.card_times (k + 1) (T.P q e f))) at hclosedNF
              exact hclosedNF)
            exact hinv.2.2.2
        have hwholeNF : T.isNF1 (T.P 1 M R) :=
          T.isNF1.p 1 M R hMNF hRNF hMG hRhead
        have hwholeIdx : T.index_Prop1 1 (T.P 1 M R) :=
          T.index_Prop1.p 1 M R (Nat.le_refl 1) hRIdx
        have hwholeG : ∀ x : T, x ∈ T.G1 1 (T.P 1 M R) → x < T.P 1 M R := by
          intro x hx
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
            List.mem_append, List.mem_append] at hx
          cases hx with
          | inl hleft =>
            cases hleft with
            | inl hxm =>
              have hxEq : x = M := List.mem_singleton.mp hxm
              rw [hxEq]
              unfold M
              exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
            | inr hxG =>
              have hxM : x < M := hMG x hxG
              have hMwhole : M < T.P 1 M R := by
                unfold M
                exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
              exact lt_trans_thm x M (T.P 1 M R) hxM hMwhole
          | inr hxR =>
            have hxRt : x < R := hRG x hxR
            have hRle : R ≤ T.P 1 M R :=
              T.isNF1_tail_le (T.P 1 M R) hwholeNF 1 M R rfl
            exact lt_of_lt_of_le_thm T x R (T.P 1 M R) hxRt hRle
        rw [T.card_times.eq_3, ite_eq_left rfl]
        rw [← add_eq_hAdd
              (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
              (T.card_times (k + 1) b), T.P_add_eq, T.add.eq_1]
        rw [T.P_add_eq]
        change
          T.isNF1 (T.P 1 M R) ∧
            T.index_Prop1 1 (T.P 1 M R) ∧
              (∀ x : T, x ∈ T.G1 1 (T.P 1 M R) → x < T.P 1 M R)
        exact ⟨hwholeNF, hwholeIdx, hwholeG⟩

#print axioms bridge_card_times_succ_append

theorem bridge_card_times_add_level_lt (m n : Nat) (c d y : T)
    (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ T.Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ T.Z) :
    T.add (T.card_times m c) y < T.card_times n d := by
  cases c with
  | Z => exact False.elim (hcne rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      cases d with
      | Z => exact False.elim (hdne rfl)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          subst q
          exact match T.isNF1_P_inv 0 a b hcNF with
          | ⟨haNF, hbNF, haG, hheadb⟩ => by
            exact match T.isNF1_P_inv 0 e f hdNF with
            | ⟨heNF, hfNF, heG, hheadf⟩ => by
              have haEC := bridge_early_collapse_closed a haNF haG
              have heEC := bridge_early_collapse_closed e heNF heG
              cases m with
              | zero =>
                cases n with
                | zero => exact False.elim (Nat.lt_irrefl 0 hmn)
                | succ l =>
                  rw [T.card_times.eq_2, T.P_add_eq]
                  rw [T.card_times.eq_3, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                        (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                        (T.card_times (l + 1) f),
                      T.P_add_eq, T.add.eq_1]
                  exact T.Lt.p_head 0 1 a
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) (T.early_collapse e))
                    (T.add b y) (T.card_times (l + 1) f) (Nat.zero_lt_succ 0)
              | succ k =>
                cases n with
                | zero => exact False.elim (Nat.not_lt_zero (k + 1) hmn)
                | succ l =>
                  have hkl : k < l := Nat.lt_of_succ_lt_succ hmn
                  rw [T.card_times.eq_3, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                        (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                        (T.card_times (k + 1) b),
                      T.P_add_eq, T.add.eq_1]
                  rw [T.P_add_eq]
                  rw [T.card_times.eq_3, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                        (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                        (T.card_times (l + 1) f),
                      T.P_add_eq, T.add.eq_1]
                  have hshift := bridge_shift_level_lt k l hkl
                    (T.early_collapse a) (T.early_collapse e) haEC.2.1 heEC.2.1
                  exact T.Lt.p_mid 1 _ _ _ _ hshift

#print axioms bridge_card_times_add_level_lt

theorem bridge_lt_P0ZZ_eq_Z (x : T) (h : x < T.P 0 T.Z T.Z) : x = T.Z := by
  cases x with
  | Z => rfl
  | P p a b =>
    cases lt_inv p a b 0 T.Z T.Z h with
    | inl hp => exact False.elim (Nat.not_lt_zero p hp)
    | inr hor =>
      cases hor with
      | inl hm => exact False.elim (lt_Z_inv hm.2)
      | inr ht => exact False.elim (lt_Z_inv ht.2.2)

#print axioms bridge_lt_P0ZZ_eq_Z



-- extracted from Subsp/new/stop_order_aux_base.lean
-- From AuxBridge.lean

theorem aux_card_times_zero (s : T) : T.card_times 0 s = s := by
  cases s with
  | Z => rfl
  | P p a b => rfl

theorem aux_index0_lt_card_times_one (c z : T)
    (hc : T.index_Prop1 0 c)
    (hz : T.index_Prop1 0 z) (hzne : z ≠ T.Z) :
    c < T.card_times 1 z := by
  cases c with
  | Z =>
    have hne : T.card_times 1 z ≠ T.Z :=
      bridge_card_times_ne_Z 1 z hzne
    cases T.Z_le (T.card_times 1 z) with
    | inl hlt => exact hlt
    | inr heq => exact False.elim (hne heq.symm)
  | P p a b =>
    cases hc with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      cases z with
      | Z => exact False.elim (hzne rfl)
      | P q e f =>
        cases hz with
        | p _ _ _ hq hf =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          subst q
          rw [T.card_times.eq_3, ite_eq_left rfl]
          rw [← add_eq_hAdd
                (T.P 1
                  ((T.P 1 T.Z T.Z).mul (T.ofNat 0) + T.early_collapse e)
                  T.Z)
                (T.card_times 1 f),
              T.P_add_eq, T.add.eq_1]
          exact T.Lt.p_head 0 1 a
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0))
              (T.early_collapse e))
            b (T.card_times 1 f) (Nat.zero_lt_succ 0)

#print axioms aux_index0_lt_card_times_one

theorem aux_sum_inv {lam : Nat} :
    ∀ (k : Nat) (v : new.Vec (new.T lam) (k + 1)),
      (∀ a ∈ new.Vec.toList v,
        T.isNF1 (trans a) ∧
          ∀ x : T, x ∈ T.G1 0 (trans a) → x < trans a) →
      let r := transAux v
      T.isNF1 r.2.1 ∧
        T.index_Prop1 1 r.2.1 ∧
        (∀ x : T, x ∈ T.G1 1 r.2.1 → x < r.2.1) ∧
        (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
          r.2.1 < T.card_times k z) := by
  intro k
  induction k with
  | zero =>
    intro v hcoord
    cases v with
    | snoc n xs a =>
      cases xs with
      | nil =>
        rw [transAux.eq_2]
        change
          T.isNF1 T.Z ∧ T.index_Prop1 1 T.Z ∧
            (∀ x : T, x ∈ T.G1 1 T.Z → x < T.Z) ∧
            (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
              T.Z < T.card_times 0 z)
        constructor
        · exact T.isNF1.z
        · constructor
          · exact T.index_Prop1.z
          · constructor
            · intro x hx
              rw [T.G1.eq_1] at hx
              cases hx
            · intro z hzNF hzIdx hzne
              cases z with
              | Z => exact False.elim (hzne rfl)
              | P p c d =>
                rw [T.card_times.eq_2]
                exact T.Lt.Z_lt_P p c d
  | succ m ih =>
    intro v hcoord
    cases v with
    | snoc n xs a =>
        have hxsCoord :
            ∀ b ∈ new.Vec.toList xs,
              T.isNF1 (trans b) ∧
                ∀ x : T, x ∈ T.G1 0 (trans b) → x < trans b := by
          intro b hb
          apply hcoord b
          change b ∈ new.Vec.toList xs ++ [a]
          exact List.mem_append_left [a] hb
        have haCoord :
            T.isNF1 (trans a) ∧
              ∀ x : T, x ∈ T.G1 0 (trans a) → x < trans a := by
          apply hcoord a
          change a ∈ new.Vec.toList xs ++ [a]
          exact List.mem_append_right _ (List.mem_singleton_self a)
        have hrest := ih xs hxsCoord
        rw [transAux.eq_3]
        cases haux : transAux xs with
        | mk found rest =>
          cases rest with
          | mk sum a0 =>
            rw [haux] at hrest
            change
              T.isNF1
                  (T.add (T.card_times m (T.early_collapse (trans a))) sum) ∧
                T.index_Prop1 1
                  (T.add (T.card_times m (T.early_collapse (trans a))) sum) ∧
                (∀ x : T,
                  x ∈ T.G1 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum) →
                  x < T.add (T.card_times m (T.early_collapse (trans a))) sum) ∧
                (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
                  T.add (T.card_times m (T.early_collapse (trans a))) sum <
                    T.card_times (m + 1) z)
            have hec := bridge_early_collapse_closed
              (trans a) haCoord.1 haCoord.2
            apply Decidable.byCases (p := T.early_collapse (trans a) = T.Z)
            · intro hecz
              rw [hecz, T.card_times.eq_1, T.add.eq_1]
              constructor
              · exact hrest.1
              · constructor
                · exact hrest.2.1
                · constructor
                  · exact hrest.2.2.1
                  · intro z hzNF hzIdx hzne
                    have hlow := hrest.2.2.2 z hzNF hzIdx hzne
                    have hlevel := bridge_card_times_level_lt m (m + 1) z z
                      (Nat.lt_succ_self m) hzNF hzIdx hzne hzNF hzIdx hzne
                    exact lt_trans_thm sum (T.card_times m z)
                      (T.card_times (m + 1) z) hlow hlevel
            · intro hecz
              cases m with
              | zero =>
                rw [aux_card_times_zero]
                have hsumZ : sum = T.Z := by
                  have hbound := hrest.2.2.2 (T.P 0 T.Z T.Z)
                    (T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                      (fun x hx => by rw [T.G1.eq_1] at hx; cases hx)
                      (T.Z_le _))
                    (T.index_Prop1.p 0 T.Z T.Z (Nat.le_refl 0)
                      T.index_Prop1.z)
                    (by intro h; cases h)
                  rw [T.card_times.eq_2] at hbound
                  exact bridge_lt_P0ZZ_eq_Z sum hbound
                rw [hsumZ, T.add_Z]
                have hidx1 := Rank1Termination.index_mono (Nat.zero_le 1)
                  (T.early_collapse (trans a)) hec.2.1
                constructor
                · exact hec.1
                · constructor
                  · exact hidx1
                  · constructor
                    · exact hec.2.2
                    · intro z hzNF hzIdx hzne
                      exact aux_index0_lt_card_times_one
                        (T.early_collapse (trans a)) z hec.2.1 hzIdx hzne
              | succ q =>
                have happ := bridge_card_times_succ_append q
                  (T.early_collapse (trans a)) sum
                  hec.1 hec.2.1 hrest.1 hrest.2.1 hrest.2.2.1
                  (fun z hzNF hzIdx hzne =>
                    hrest.2.2.2 z hzNF hzIdx hzne)
                constructor
                · exact happ.1
                · constructor
                  · exact happ.2.1
                  · constructor
                    · exact happ.2.2
                    · intro z hzNF hzIdx hzne
                      exact bridge_card_times_add_level_lt (q + 1) (q + 2)
                        (T.early_collapse (trans a)) z sum
                        (Nat.lt_succ_self (q + 1))
                        hec.1 hec.2.1 hecz hzNF hzIdx hzne

#print axioms aux_sum_inv


-- From TransCore.lean

theorem tc_trans_P_add {lam : Nat} (ls : new.Vec (new.T lam) lam) (a : new.T lam) :
    trans (new.T.P ls a) = T.add (trans (new.T.P ls new.T.Z)) (trans a) := by
  rw [_root_.trans.eq_2 ls a, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1]
  cases haux : transAux ls with
  | mk found rest =>
    cases rest with
    | mk sum a0 =>
      change
        (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
         else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a)) =
        T.add
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
           else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z)
          (trans a)
      apply Decidable.byCases (p := found = true)
      · intro hf
        rw [ite_eq_left hf, ite_eq_left hf, T.P_add_eq, T.add]
      · intro hf
        rw [ite_eq_right hf, ite_eq_right hf]
        apply Decidable.byCases (p := a0 = T.Z)
        · intro ha0
          rw [ite_eq_left ha0, ite_eq_left ha0, T.P_add_eq, T.add]
        · intro ha0
          rw [ite_eq_right ha0, ite_eq_right ha0, T.P_add_eq, T.add]

theorem tc_trans_head {lam : Nat} (s : new.T lam) :
    trans (new.T.head s) = T.head (trans s) := by
  cases s with
  | Z => rfl
  | P ls a =>
    rw [new.T.head, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1,
      _root_.trans.eq_2 ls a]
    cases haux : transAux ls with
    | mk found rest =>
      cases rest with
      | mk sum a0 =>
        change
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
           else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z) =
          T.head
            (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
             else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a))
        apply Decidable.byCases (p := found = true)
        · intro hf
          rw [ite_eq_left hf, ite_eq_left hf]
          rfl
        · intro hf
          rw [ite_eq_right hf, ite_eq_right hf]
          apply Decidable.byCases (p := a0 = T.Z)
          · intro ha0
            rw [ite_eq_left ha0, ite_eq_left ha0]
            rfl
          · intro ha0
            rw [ite_eq_right ha0, ite_eq_right ha0]
            rfl

#print axioms tc_trans_P_add
#print axioms tc_trans_head


-- From AuxCore.lean

theorem tc_trans_ne_Z_of_ne_Z {lam : Nat} (s : new.T lam)
    (hs : s ≠ new.T.Z) : trans s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P ls add =>
    rw [_root_.trans.eq_2]
    cases haux : transAux ls with
    | mk found rest =>
      cases rest with
      | mk sum a0 =>
        change
          (if found = true then
            T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans add)
          else if a0 = T.Z then T.P 0 T.Z (trans add)
          else T.P 0 a0 (trans add)) ≠ T.Z
        apply Decidable.byCases (p := found = true)
        · intro hf
          rw [ite_eq_left hf]
          intro h
          cases h
        · intro hf
          rw [ite_eq_right hf]
          apply Decidable.byCases (p := a0 = T.Z)
          · intro ha0
            rw [ite_eq_left ha0]
            intro h
            cases h
          · intro ha0
            rw [ite_eq_right ha0]
            intro h
            cases h

#print axioms tc_trans_ne_Z_of_ne_Z

theorem tc_Z_lt_of_ne (x : T) (hx : x ≠ T.Z) : T.Z < x := by
  cases T.Z_le x with
  | inl h => exact h
  | inr h => exact False.elim (hx h.symm)

#print axioms tc_Z_lt_of_ne

theorem tc_add_ne_Z_left (a b : T) (ha : a ≠ T.Z) : a + b ≠ T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d =>
    cases b with
    | Z =>
      intro h
      cases h
    | P q e f =>
      intro h
      cases h


theorem tc_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c with
  | Z => rfl
  | P p a b => rfl

#print axioms tc_card_times_zero

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
      | snoc n xs a =>
        cases xs with
        | nil =>
          rw [transAux.eq_2] at haux
          cases haux
          have ha := hcomp a (List.mem_singleton.mpr rfl)
          refine ⟨ha.1, ha.2, T.isNF1.z, T.index_Prop1.z, ?_, ?_, ?_, ?_⟩
          · intro y hy
            rw [T.G1.eq_1] at hy
            cases hy
          · intro c hcNF hcIdx hcne
            rw [tc_card_times_zero]
            exact tc_Z_lt_of_ne c hcne
          · intro h
            cases h
          · intro _
            rfl
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc n xs a =>
        have hrest :
            ∀ x : new.T lam, x ∈ new.Vec.toList xs →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
          intro x hx
          exact hcomp x (List.mem_append_left [a] hx)
        have ha :
            T.isNF1 (trans a) ∧
              (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
          apply hcomp a
          exact List.mem_append_right (new.Vec.toList xs)
            (List.mem_singleton.mpr rfl)
        cases hrestaux : transAux xs with
        | mk foundRest restpair =>
          cases restpair with
          | mk sumRest a0Rest =>
            have ihr := ih xs hrest foundRest sumRest a0Rest hrestaux
            rw [transAux.eq_3, hrestaux] at haux
            cases a with
            | Z =>
              change
                (foundRest, T.card_times m (T.early_collapse (trans new.T.Z)) + sumRest, a0Rest) =
                  (found, sum, a0) at haux
              rw [_root_.trans.eq_1] at haux
              change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
              cases haux
              refine ⟨ihr.1, ihr.2.1, ihr.2.2.1, ihr.2.2.2.1,
                ihr.2.2.2.2.1, ?_, ihr.2.2.2.2.2.2.1, ihr.2.2.2.2.2.2.2⟩
              intro c hcNF hcIdx hcne
              have hold := ihr.2.2.2.2.2.1 c hcNF hcIdx hcne
              have hnext := bridge_card_times_level_lt m (m + 1) c c
                (Nat.lt_succ_self m) hcNF hcIdx hcne hcNF hcIdx hcne
              exact lt_trans_thm _ _ _ hold hnext
            | P als aadd =>
              have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                intro h
                cases h
              have hatne : trans (new.T.P als aadd) ≠ T.Z :=
                tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
              have hec := bridge_early_collapse_closed
                (trans (new.T.P als aadd)) ha.1 ha.2
              have hecne : T.early_collapse (trans (new.T.P als aadd)) ≠ T.Z :=
                bridge_early_collapse_ne_Z (trans (new.T.P als aadd)) hatne
              change
                (true,
                  T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                  a0Rest) = (found, sum, a0) at haux
              cases haux
              have hboundnext :
                  ∀ c : T,
                    T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                    T.add
                        (T.card_times m
                          (T.early_collapse (trans (new.T.P als aadd))))
                        sumRest <
                      T.card_times (m + 1) c := by
                intro c hcNF hcIdx hcne
                exact bridge_card_times_add_level_lt m (m + 1)
                  (T.early_collapse (trans (new.T.P als aadd))) c sumRest
                  (Nat.lt_succ_self m) hec.1 hec.2.1 hecne
                  hcNF hcIdx hcne
              cases m with
              | zero =>
                have hsumZ : sumRest = T.Z := by
                  have hlt := ihr.2.2.2.2.2.1 (T.P 0 T.Z T.Z)
                    (T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                      (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
                      (T.Z_le (T.P 0 T.Z T.Z)))
                    (T.index_Prop1.p 0 T.Z T.Z (Nat.le_refl 0) T.index_Prop1.z)
                    (by intro h; cases h)
                  rw [T.card_times.eq_2] at hlt
                  exact bridge_lt_P0ZZ_eq_Z sumRest hlt
                rw [hsumZ]
                have haddz :
                    T.card_times 0
                        (T.early_collapse (trans (new.T.P als aadd))) + T.Z =
                      T.early_collapse (trans (new.T.P als aadd)) := by
                  rw [tc_card_times_zero]
                  let A := T.early_collapse (trans (new.T.P als aadd))
                  change A + T.Z = A
                  exact (add_eq_hAdd A T.Z).symm.trans (T.add_Z A)
                rw [haddz]
                have hidx1 :
                    T.index_Prop1 1
                      (T.early_collapse (trans (new.T.P als aadd))) :=
                  Rank1Termination.index_mono (Nat.zero_le 1)
                    (T.early_collapse (trans (new.T.P als aadd))) hec.2.1
                refine ⟨ihr.1, ihr.2.1, hec.1, hidx1, hec.2.2,
                  ?_, ?_, ?_⟩
                · intro c hcNF hcIdx hcne
                  have hb := hboundnext c hcNF hcIdx hcne
                  rw [hsumZ] at hb
                  have hleft :
                      T.add
                          (T.card_times 0
                            (T.early_collapse (trans (new.T.P als aadd)))) T.Z =
                        T.early_collapse (trans (new.T.P als aadd)) := by
                    rw [T.add_Z, tc_card_times_zero]
                  rw [hleft] at hb
                  exact hb
                · intro _
                  exact hecne
                · intro h
                  cases h
              | succ j =>
                have happ := bridge_card_times_succ_append j
                  (T.early_collapse (trans (new.T.P als aadd))) sumRest
                  hec.1 hec.2.1 ihr.2.2.1 ihr.2.2.2.1
                  ihr.2.2.2.2.1
                  ihr.2.2.2.2.2.1
                refine ⟨ihr.1, ihr.2.1, happ.1, happ.2.1, happ.2.2,
                  ?_, ?_, ?_⟩
                · intro c hcNF hcIdx hcne
                  exact hboundnext c hcNF hcIdx hcne
                · intro _
                  have hheadne := bridge_card_times_ne_Z (j + 1)
                    (T.early_collapse (trans (new.T.P als aadd))) hecne
                  intro hz
                  exact (tc_add_ne_Z_left
                    (T.card_times (j + 1)
                      (T.early_collapse (trans (new.T.P als aadd))))
                    sumRest hheadne) hz
                · intro h
                  cases h

#print axioms tc_transAux_inv


-- From CardAlg.lean



-- extracted from Subsp/new/stop_order_aux_card.lean
theorem ca_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c with
  | Z => rfl
  | P p a b => rfl

theorem ca_card_times_add (n : Nat) (a b : T) :
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  induction a with
  | Z =>
    rw [T.add, T.card_times.eq_1, T.add]
  | P p x y ihx ihy =>
    cases b with
    | Z =>
      rw [T.add_Z, T.card_times.eq_1, T.add_Z]
    | P q c d =>
      rw [T.P_add_eq]
      cases n with
      | zero =>
        rw [ca_card_times_zero, ca_card_times_zero, ca_card_times_zero]
        rw [T.P_add_eq]
      | succ k =>
        rw [T.card_times.eq_3, T.card_times.eq_3, T.card_times.eq_3]
        rw [ihy]
        apply Decidable.byCases (p := p = 0)
        · intro hp
          rw [← add_eq_hAdd]
          exact (Rank1Termination.add_assoc _ _ _).symm
        · intro hp
          rw [← add_eq_hAdd]
          exact (Rank1Termination.add_assoc _ _ _).symm

#print axioms ca_card_times_add

theorem ca_mul_P1_ofNat_succ (k : Nat) :
    T.add (T.P 1 T.Z T.Z)
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) =
    T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
  rw [T.ofNat.eq_2, T.mul.eq_2]
  rw [← add_eq_hAdd]
  rw [T.P_add_eq, T.add]
  exact (mul_add_shape 1 T.Z k).symm

#print axioms ca_mul_P1_ofNat_succ


theorem ca_PZ_add (p : Nat) (a b : T) :
    T.P p a T.Z + b = T.P p a b := by
  change T.add (T.P p a T.Z) b = T.P p a b
  rw [T.P_add_eq, T.add]

theorem ca_mul_P1_one :
    T.mul (T.P 1 T.Z T.Z) (T.ofNat 1) = T.P 1 T.Z T.Z := by
  rfl

theorem ca_card_times_one_comp (m : Nat) (c : T) :
    T.card_times 1 (T.card_times m c) = T.card_times (m + 1) c := by
  induction c with
  | Z =>
    rw [T.card_times.eq_1, T.card_times.eq_1, T.card_times.eq_1]
  | P p a b iha ihb =>
    cases m with
    | zero =>
      rw [ca_card_times_zero]
    | succ k =>
      rw [T.card_times.eq_3]
      let H :=
        if p = 0 then
          T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k) + T.early_collapse a) T.Z
        else
          T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) + a) T.Z
      change T.card_times 1 (T.add H (T.card_times (k + 1) b)) =
        T.card_times (k + 1 + 1) (T.P p a b)
      rw [ca_card_times_add, ihb]
      unfold H
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [ite_eq_left hp]
        rw [T.card_times.eq_3, ite_eq_right Nat.one_ne_zero]
        rw [T.card_times.eq_1, ca_PZ_add]
        rw [T.card_times.eq_3, ite_eq_left hp]
        rw [T.P_add_eq, T.add, ca_PZ_add]
        congr 1
        change
          T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) =
            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)))
              (T.early_collapse a)
        rw [ca_mul_P1_one]
        rw [← Rank1Termination.add_assoc]
        rw [ca_mul_P1_ofNat_succ]
      · intro hp
        rw [ite_eq_right hp]
        rw [T.card_times.eq_3, ite_eq_right Nat.one_ne_zero]
        rw [T.card_times.eq_1, ca_PZ_add]
        rw [T.card_times.eq_3, ite_eq_right hp]
        rw [T.P_add_eq, T.add, ca_PZ_add]
        congr 1
        change
          T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) =
            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1 + 1))) a
        rw [ca_mul_P1_one]
        rw [← Rank1Termination.add_assoc]
        rw [ca_mul_P1_ofNat_succ]

#print axioms ca_card_times_one_comp


-- From Weighted.lean

theorem wt_add_self_le (a z : T) : a ≤ T.add a z := by
  induction a with
  | Z =>
    rw [T.add]
    exact T.Z_le z
  | P p x y ihx ihy =>
    cases z with
    | Z =>
      rw [T.add_Z]
      exact Or.inr rfl
    | P q c d =>
      rw [T.P_add_eq]
      cases ihy with
      | inl hlt => exact Or.inl (T.Lt.p_tail p x y (T.add y (T.P q c d)) hlt)
      | inr heq =>
        exact Or.inr (congrArg (fun t => T.P p x t) heq)

#print axioms wt_add_self_le


theorem wt_expand_card_succ_add (k : Nat) (a b y : T) :
    T.add (T.card_times (k + 1) (T.P 0 a b)) y =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a))
        (T.add (T.card_times (k + 1) b) y) := by
  rw [T.card_times.eq_3, ite_eq_left rfl]
  rw [← add_eq_hAdd]
  rw [Rank1Termination.add_assoc]
  rw [T.P_add_eq, T.add]
  rfl

#print axioms wt_expand_card_succ_add

theorem wt_card_append_lt (n : Nat) :
    ∀ c d y z : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d →
      (∀ q : T, T.isNF1 q → T.index_Prop1 0 q → q ≠ T.Z →
        y < T.card_times n q) →
      T.add (T.card_times n c) y < T.add (T.card_times n d) z := by
  intro c
  induction c with
  | Z =>
    intro d y z hcNF hcIdx hdNF hdIdx hcd hy
    have hdNe : d ≠ T.Z := by
      intro heq
      rw [heq] at hcd
      exact lt_Z_inv hcd
    have hyD : y < T.card_times n d := hy d hdNF hdIdx hdNe
    have hle : T.card_times n d ≤ T.add (T.card_times n d) z :=
      wt_add_self_le (T.card_times n d) z
    rw [T.card_times.eq_1, T.add]
    exact lt_of_lt_of_le_thm T y (T.card_times n d)
      (T.add (T.card_times n d) z) hyD hle
  | P p a b iha ihb =>
    intro d y z hcNF hcIdx hdNF hdIdx hcd hy
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      cases d with
      | Z => exact False.elim (lt_Z_inv hcd)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq hfIdx =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          subst q
          exact match T.isNF1_P_inv 0 a b hcNF with
          | ⟨haNF, hbNF, haG, hheadb⟩ => by
            exact match T.isNF1_P_inv 0 e f hdNF with
            | ⟨heNF, hfNF, heG, hheadf⟩ => by
              cases lt_inv 0 a b 0 e f hcd with
              | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
              | inr hor =>
                cases n with
                | zero =>
                  rw [tc_card_times_zero, tc_card_times_zero]
                  rw [T.P_add_eq, T.P_add_eq]
                  cases hor with
                  | inl hm =>
                    exact T.Lt.p_mid 0 a e (T.add b y) (T.add f z) hm.2
                  | inr ht =>
                    have hae : a = e := ht.2.1
                    subst e
                    have hbf : b < f := ht.2.2
                    have hrec := ihb f y z hbNF hbIdx hfNF hfIdx hbf hy
                    rw [tc_card_times_zero, tc_card_times_zero] at hrec
                    exact T.Lt.p_tail 0 a (T.add b y) (T.add f z) hrec
                | succ k =>
                  rw [wt_expand_card_succ_add k a b y]
                  rw [wt_expand_card_succ_add k e f z]
                  cases hor with
                  | inl hm =>
                    have hec : T.early_collapse a < T.early_collapse e :=
                      bridge_early_collapse_lt a e haNF haG heNF hm.2
                    have hmid := bridge_add_left_lt
                      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a) (T.early_collapse e) hec
                    exact T.Lt.p_mid 1 _ _ _ _ hmid
                  | inr ht =>
                    have hae : a = e := ht.2.1
                    subst e
                    have hbf : b < f := ht.2.2
                    have hrec := ihb f y z hbNF hbIdx hfNF hfIdx hbf hy
                    exact T.Lt.p_tail 1
                      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                        (T.early_collapse a)) _ _ hrec

#print axioms wt_card_append_lt


-- From AuxOrder.lean



-- extracted from Subsp/new/stop_order_aux.lean
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
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases xv with
        | nil =>
          cases w with
          | @snoc nw xw b =>
            cases xw with
            | nil =>
              rw [new.compareVec.eq_2] at hcmp
              cases hca : new.compareT a b with
              | lt =>
                rw [transAux.eq_2] at hav
                rw [transAux.eq_2] at haw
                cases hav
                cases haw
                apply Or.inr
                constructor
                · rfl
                · apply hmono a b
                  · exact List.mem_singleton.mpr rfl
                  · exact List.mem_singleton.mpr rfl
                  · exact hca
              | eq =>
                rw [hca, new.compareVec.eq_1] at hcmp
                cases hcmp
              | gt =>
                rw [hca] at hcmp
                cases hcmp
  | succ m ih =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases w with
        | @snoc nw xw b =>
          change
            (match new.compareT a b with
            | Ordering.eq => new.compareVec xv xw
            | ord => ord) = Ordering.lt at hcmp
          have hvrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xv →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hv x (List.mem_append_left [a] hx)
          have hwrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xw →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hw x (List.mem_append_left [b] hx)
          have ha := hv a
            (List.mem_append_right (new.Vec.toList xv) (List.mem_singleton.mpr rfl))
          have hb := hw b
            (List.mem_append_right (new.Vec.toList xw) (List.mem_singleton.mpr rfl))
          have hmonoRest :
              ∀ x y : new.T lam,
                x ∈ new.Vec.toList xv → y ∈ new.Vec.toList xw →
                x < y → trans x < trans y := by
            intro x y hx hy hxy
            exact hmono x y
              (List.mem_append_left [a] hx)
              (List.mem_append_left [b] hy) hxy
          cases havrest : transAux xv with
          | mk fvr pr =>
            cases pr with
            | mk svr avr =>
              cases hawrest : transAux xw with
              | mk fwr qr =>
                cases qr with
                | mk swr awr =>
                  rw [transAux.eq_3, havrest] at hav
                  rw [transAux.eq_3, hawrest] at haw
                  cases hca : new.compareT a b with
                  | lt =>
                    rw [hca] at hcmp
                    have hab : a < b := hca
                    have htab : trans a < trans b := by
                      exact hmono a b
                        (List.mem_append_right (new.Vec.toList xv)
                          (List.mem_singleton.mpr rfl))
                        (List.mem_append_right (new.Vec.toList xw)
                          (List.mem_singleton.mpr rfl)) hab
                    have hec : T.early_collapse (trans a) < T.early_collapse (trans b) :=
                      bridge_early_collapse_lt (trans a) (trans b)
                        ha.1 ha.2 hb.1 htab
                    have heca := bridge_early_collapse_closed (trans a) ha.1 ha.2
                    have hecb := bridge_early_collapse_closed (trans b) hb.1 hb.2
                    have invr := tc_transAux_inv xv hvrest fvr svr avr havrest
                    have hsum :
                        T.add (T.card_times m (T.early_collapse (trans a))) svr <
                          T.add (T.card_times m (T.early_collapse (trans b))) swr := by
                      apply wt_card_append_lt m
                        (T.early_collapse (trans a)) (T.early_collapse (trans b))
                        svr swr heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                      exact invr.2.2.2.2.2.1
                    cases hav
                    cases haw
                    exact Or.inl hsum
                  | gt =>
                    rw [hca] at hcmp
                    cases hcmp
                  | eq =>
                    rw [hca] at hcmp
                    have habEq : a = b := new.T_eq_sound a b hca
                    subst b
                    have hrec := ih xv xw hvrest hwrest hmonoRest hcmp
                      fvr fwr svr avr swr awr havrest hawrest
                    cases hrec with
                    | inl hsumRest =>
                      cases hav
                      cases haw
                      apply Or.inl
                      exact bridge_add_left_lt
                        (T.card_times m (T.early_collapse (trans a)))
                        svr swr hsumRest
                    | inr heqrest =>
                      cases hav
                      cases haw
                      apply Or.inr
                      constructor
                      · rw [heqrest.1]
                      · exact heqrest.2

#print axioms ao_transAux_lex


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
      intro v hcomp found sum a0 haux
      cases v with
      | @snoc n xs a =>
        cases xs with
        | nil =>
          rw [transAux.eq_2] at haux
          cases haux
          change
            T.isNF1 T.Z ∧ T.index_Prop1 1 T.Z ∧
              (∀ y : T, y ∈ T.G1 1 T.Z → y < T.Z) ∧
              (∀ c : T,
                T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                  T.Z < T.card_times 1 c)
          refine ⟨T.isNF1.z, T.index_Prop1.z, ?_, ?_⟩
          · intro y hy
            rw [T.G1.eq_1] at hy
            cases hy
          · intro c hcNF hcIdx hcNe
            exact tc_Z_lt_of_ne (T.card_times 1 c)
              (bridge_card_times_ne_Z 1 c hcNe)
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | @snoc n xs a =>
        have hrest :
            ∀ x : new.T lam, x ∈ new.Vec.toList xs →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
          intro x hx
          exact hcomp x (List.mem_append_left [a] hx)
        have ha :
            T.isNF1 (trans a) ∧
              (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
          apply hcomp a
          exact List.mem_append_right (new.Vec.toList xs)
            (List.mem_singleton.mpr rfl)
        cases hrestaux : transAux xs with
        | mk foundRest restpair =>
          cases restpair with
          | mk sumRest a0Rest =>
            have ihr := ih xs hrest foundRest sumRest a0Rest hrestaux
            rw [transAux.eq_3, hrestaux] at haux
            cases a with
            | Z =>
              rw [_root_.trans.eq_1] at haux
              change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
              cases haux
              refine ⟨ihr.1, ihr.2.1, ihr.2.2.1, ?_⟩
              intro c hcNF hcIdx hcNe
              have hold := ihr.2.2.2 c hcNF hcIdx hcNe
              have hnext := bridge_card_times_level_lt (m + 1) (m + 2) c c
                (Nat.lt_succ_self (m + 1)) hcNF hcIdx hcNe hcNF hcIdx hcNe
              exact lt_trans_thm _ _ _ hold hnext
            | P als aadd =>
              have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                intro h
                cases h
              have hatNe := tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
              have hec := bridge_early_collapse_closed
                (trans (new.T.P als aadd)) ha.1 ha.2
              have hecNe := bridge_early_collapse_ne_Z
                (trans (new.T.P als aadd)) hatNe
              change
                (true,
                  T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                  a0Rest) = (found, sum, a0) at haux
              cases haux
              rw [← add_eq_hAdd]
              rw [ca_card_times_add, ca_card_times_one_comp]
              have happ := bridge_card_times_succ_append m
                (T.early_collapse (trans (new.T.P als aadd)))
                (T.card_times 1 sumRest)
                hec.1 hec.2.1 ihr.1 ihr.2.1 ihr.2.2.1 ihr.2.2.2
              refine ⟨happ.1, happ.2.1, happ.2.2, ?_⟩
              intro c hcNF hcIdx hcNe
              exact bridge_card_times_add_level_lt (m + 1) (m + 2)
                (T.early_collapse (trans (new.T.P als aadd))) c
                (T.card_times 1 sumRest)
                (Nat.lt_succ_self (m + 1)) hec.1 hec.2.1 hecNe
                hcNF hcIdx hcNe

#print axioms sc_transAux_card1_inv


-- From CardOrder_fixed.lean

theorem co_len1_sum_zero {lam : Nat}
    (v : new.Vec (new.T lam) 1) (f : Bool) (s a0 : T)
    (h : transAux v = (f, s, a0)) : s = T.Z := by
  cases v with
  | @snoc n xs a =>
    cases xs with
    | nil =>
      rw [transAux.eq_2] at h
      cases h
      rfl

#print axioms co_len1_sum_zero

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
  intro k
  induction k with
  | zero =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      have hlex := ao_transAux_lex v w hv hw hmono hcmp
        fv fw sv av sw aw hav haw
      have hsv : sv = T.Z := co_len1_sum_zero v fv sv av hav
      have hsw : sw = T.Z := co_len1_sum_zero w fw sw aw haw
      cases hlex with
      | inl hslt =>
        rw [hsv, hsw] at hslt
        exact False.elim (lt_irrefl_thm T.Z hslt)
      | inr heq =>
        apply Or.inr
        constructor
        · rw [hsv, hsw]
        · exact heq.2
  | succ m ih =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases w with
        | @snoc nw xw b =>
          change
            (match new.compareT a b with
            | Ordering.eq => new.compareVec xv xw
            | ord => ord) = Ordering.lt at hcmp
          have hvrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xv →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hv x (List.mem_append_left [a] hx)
          have hwrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xw →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hw x (List.mem_append_left [b] hx)
          have ha := hv a
            (List.mem_append_right (new.Vec.toList xv) (List.mem_singleton.mpr rfl))
          have hb := hw b
            (List.mem_append_right (new.Vec.toList xw) (List.mem_singleton.mpr rfl))
          have hmonoRest :
              ∀ x y : new.T lam,
                x ∈ new.Vec.toList xv → y ∈ new.Vec.toList xw →
                x < y → trans x < trans y := by
            intro x y hx hy hxy
            exact hmono x y
              (List.mem_append_left [a] hx)
              (List.mem_append_left [b] hy) hxy
          cases havrest : transAux xv with
          | mk fvr pr =>
            cases pr with
            | mk svr avr =>
              cases hawrest : transAux xw with
              | mk fwr qr =>
                cases qr with
                | mk swr awr =>
                  rw [transAux.eq_3, havrest] at hav
                  rw [transAux.eq_3, hawrest] at haw
                  cases hca : new.compareT a b with
                  | lt =>
                    rw [hca] at hcmp
                    have htab : trans a < trans b := by
                      exact hmono a b
                        (List.mem_append_right (new.Vec.toList xv)
                          (List.mem_singleton.mpr rfl))
                        (List.mem_append_right (new.Vec.toList xw)
                          (List.mem_singleton.mpr rfl)) hca
                    have hec : T.early_collapse (trans a) < T.early_collapse (trans b) :=
                      bridge_early_collapse_lt (trans a) (trans b)
                        ha.1 ha.2 hb.1 htab
                    have heca := bridge_early_collapse_closed (trans a) ha.1 ha.2
                    have hecb := bridge_early_collapse_closed (trans b) hb.1 hb.2
                    have invr := sc_transAux_card1_inv xv hvrest fvr svr avr havrest
                    cases hav
                    cases haw
                    cases m with
                    | zero =>
                      have hsv : svr = T.Z := co_len1_sum_zero xv fvr svr av havrest
                      have hsw : swr = T.Z := co_len1_sum_zero xw fwr swr aw hawrest
                      rw [hsv, hsw]
                      rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                      rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                      apply Or.inl
                      exact bridge_card_times_lt_same 1
                        (T.early_collapse (trans a)) (T.early_collapse (trans b))
                        heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                    | succ j =>
                      rw [← add_eq_hAdd]
                      rw [← add_eq_hAdd]
                      rw [ca_card_times_add, ca_card_times_one_comp]
                      rw [ca_card_times_add, ca_card_times_one_comp]
                      apply Or.inl
                      apply wt_card_append_lt (j + 2)
                        (T.early_collapse (trans a)) (T.early_collapse (trans b))
                        (T.card_times 1 svr) (T.card_times 1 swr)
                        heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                      exact invr.2.2.2
                  | gt =>
                    rw [hca] at hcmp
                    cases hcmp
                  | eq =>
                    rw [hca] at hcmp
                    have habEq : a = b := new.T_eq_sound a b hca
                    subst b
                    have hrec := ih xv xw hvrest hwrest hmonoRest hcmp
                      fvr fwr svr avr swr awr havrest hawrest
                    cases hav
                    cases haw
                    cases a with
                    | Z =>
                      change
                        T.card_times 1 svr < T.card_times 1 swr ∨
                          (T.card_times 1 svr = T.card_times 1 swr ∧ av < aw)
                      exact hrec
                    | P als aadd =>
                      cases m with
                      | zero =>
                        have hsv : svr = T.Z := co_len1_sum_zero xv fvr svr av havrest
                        have hsw : swr = T.Z := co_len1_sum_zero xw fwr swr aw hawrest
                        cases hrec with
                        | inl hbad =>
                          rw [hsv, hsw] at hbad
                          exact False.elim (lt_irrefl_thm T.Z hbad)
                        | inr hr =>
                          apply Or.inr
                          constructor
                          · rw [hsv, hsw]
                          · exact hr.2
                      | succ j =>
                        rw [← add_eq_hAdd]
                        rw [← add_eq_hAdd]
                        rw [ca_card_times_add, ca_card_times_one_comp]
                        rw [ca_card_times_add, ca_card_times_one_comp]
                        cases hrec with
                        | inl hr =>
                          apply Or.inl
                          exact bridge_add_left_lt
                            (T.card_times (j + 2)
                              (T.early_collapse (trans (new.T.P als aadd))))
                            (T.card_times 1 svr) (T.card_times 1 swr) hr
                        | inr hr =>
                          apply Or.inr
                          constructor
                          · rw [hr.1]
                          · exact hr.2

#print axioms co_transAux_card1_lex



-- extracted from Subsp/new/stop_ec.lean
theorem ec_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    apply Decidable.byCases (p := p = 0)
    · intro hp
      rw [ite_eq_left hp]
      rfl
    · intro hp
      rw [ite_eq_right hp]
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
        cases ha
        rfl
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
          cases hc
          rfl
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
  apply Decidable.byCases (p := a = T.Z)
  · intro ha
    rw [ite_eq_left ha, ite_eq_left ha]
  · intro ha
    rw [ite_eq_right ha, ite_eq_right ha]
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
  apply Decidable.byCases (p := a = T.Z)
  · intro ha0
    rw [ite_eq_left ha0]
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
  · intro ha0
    rw [ite_eq_right ha0]
    apply Decidable.byCases (p := T.head b ≤ T.P 0 a T.Z)
    · intro hkeep
      rw [ite_eq_left hkeep]
      exact T.Lt.p_mid 0 a c b T.Z hac
    · intro hkeep
      rw [ite_eq_right hkeep]
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
  apply Decidable.byCases (p := T.head d ≤ T.P 0 c T.Z)
  · intro hkeep
    rw [ite_eq_left hkeep]
    cases d with
    | Z => exact Or.inr rfl
    | P p e f =>
        exact Or.inl (T.Lt.p_tail 0 c T.Z (T.P p e f) (T.Lt.Z_lt_P p e f))
  · intro hkeep
    rw [ite_eq_right hkeep]
    have hdshape := bridge_part_second_shape t c d hp
    cases hdshape with
    | inl hd0 =>
        rw [hd0] at hkeep
        exact False.elim (hkeep (T.Z_le (T.P 0 c T.Z)))
    | inr hP =>
        exact match hP with
        | ⟨e, f, heq⟩ => by
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
      exact match hP with
      | ⟨e, f, heq⟩ => by
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
  apply Decidable.byCases (p := a = T.Z)
  · intro ha
    rw [ite_eq_left ha, ite_eq_left ha]
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
  · intro ha
    rw [ite_eq_right ha, ite_eq_right ha]
    apply Decidable.byCases (p := T.head b ≤ T.P 0 a T.Z)
    · intro hbkeep
      rw [ite_eq_left hbkeep]
      apply Decidable.byCases (p := T.head d ≤ T.P 0 a T.Z)
      · intro hdkeep
        rw [ite_eq_left hdkeep]
        exact T.Lt.p_tail 0 a b d hbd
      · intro hdkeep
        rw [ite_eq_right hdkeep]
        exact ec_P0_lt_snd_of_not_head_le t a d b hpt hdkeep
    · intro hbkeep
      rw [ite_eq_right hbkeep]
      apply Decidable.byCases (p := T.head d ≤ T.P 0 a T.Z)
      · intro hdkeep
        rw [ite_eq_left hdkeep]
        have hhead : T.head b ≤ T.head d := T.head_mono hbd
        have hcontra : T.head b ≤ T.P 0 a T.Z :=
          partial_order.trans (T.head b) (T.head d) (T.P 0 a T.Z) hhead hdkeep
        exact False.elim (hbkeep hcontra)
      · intro hdkeep
        rw [ite_eq_right hdkeep]
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
                          cases heq
                          rfl
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

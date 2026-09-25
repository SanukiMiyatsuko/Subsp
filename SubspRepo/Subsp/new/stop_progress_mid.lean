import Subsp.new.stop_progress_ec

open T

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
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact T.Z_le (T.head (T.P p a b))
      · rw [ite_eq_right hp]
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
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact ⟨T.isNF1.z, T.isNF1.p p a b ha hb hg hh⟩
      · rw [ite_eq_right hp]
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
      by_cases hq : q = 0
      · rw [ite_eq_left hq]
        exact Or.inr ⟨rfl, T.Lt.Z_lt_P q u v⟩
      · rw [ite_eq_right hq]
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
      by_cases hp0 : p = 0
      · rw [ite_eq_left hp0]
        by_cases hq0 : q = 0
        · rw [ite_eq_left hq0]
          exact Or.inr ⟨rfl, h⟩
        · rw [ite_eq_right hq0]
          cases hvp : T.part v with
          | mk c d =>
            exact Or.inl (T.Lt.Z_lt_P q u c)
      · rw [ite_eq_right hp0]
        cases hyp : T.part y with
        | mk a b =>
          by_cases hq0 : q = 0
          · rw [ite_eq_left hq0]
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
          · rw [ite_eq_right hq0]
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
  by_cases ha : a = T.Z
  · rw [ite_eq_left ha]
    have hadd := bridge_part_add s
    rw [hp, ha, T.add] at hadd
    have hbs : b = s := hadd
    rw [ite_eq_left ha]
    exact hbs.symm
  · rw [ite_eq_right ha]
    rw [T.stand, bridge_stand_eq_self_of_NF1 b hb]
    rw [ite_eq_right ha]

#print axioms bridge_early_collapse_part

theorem bridge_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    by_cases hp : p = 0
    · rw [ite_eq_left hp]
      rfl
    · rw [ite_eq_right hp]
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
    by_cases hp : p = 0
    · rw [ite_eq_left hp]
      rw [T.part, ite_eq_left hp]
    · rw [ite_eq_right hp]
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
      obtain ⟨f, g, hdeq⟩ := hdp
      rw [hdeq] at hbd ⊢
      have hleft : T.head T.Z ≤ T.P 0 a T.Z := T.Z_le _
      rw [ite_eq_left hleft]
      change
        T.P 0 a T.Z <
          (if T.P 0 f T.Z ≤ T.P 0 a T.Z then
            T.P 0 a (T.P 0 f g) else T.P 0 f g)
      by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
      · rw [ite_eq_left hfa]
        exact T.Lt.p_tail 0 a T.Z (T.P 0 f g)
          (T.Lt.Z_lt_P 0 f g)
      · rw [ite_eq_right hfa]
        have haf : T.P 0 a T.Z < T.P 0 f T.Z :=
          bridge_lt_of_not_le (T.P 0 f T.Z) (T.P 0 a T.Z) hfa
        cases lt_inv 0 a T.Z 0 f T.Z haf with
        | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
        | inr hor =>
          cases hor with
          | inl hm => exact T.Lt.p_mid 0 a f T.Z g hm.2
          | inr ht => exact False.elim (lt_Z_inv ht.2.2)
  | inr hbp =>
    obtain ⟨c, e, hbeq⟩ := hbp
    subst b
    cases hdshape with
    | inl hdz =>
      subst d
      exact False.elim (lt_Z_inv hbd)
    | inr hdp =>
      obtain ⟨f, g, hdeq⟩ := hdp
      subst d
      change
        (if T.P 0 c T.Z ≤ T.P 0 a T.Z then
          T.P 0 a (T.P 0 c e) else T.P 0 c e) <
        (if T.P 0 f T.Z ≤ T.P 0 a T.Z then
          T.P 0 a (T.P 0 f g) else T.P 0 f g)
      by_cases hca : T.P 0 c T.Z ≤ T.P 0 a T.Z
      · rw [ite_eq_left hca]
        by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
        · rw [ite_eq_left hfa]
          exact T.Lt.p_tail 0 a (T.P 0 c e) (T.P 0 f g) hbd
        · rw [ite_eq_right hfa]
          have haf : T.P 0 a T.Z < T.P 0 f T.Z :=
            bridge_lt_of_not_le (T.P 0 f T.Z) (T.P 0 a T.Z) hfa
          cases lt_inv 0 a T.Z 0 f T.Z haf with
          | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
          | inr hor =>
            cases hor with
            | inl hm => exact T.Lt.p_mid 0 a f (T.P 0 c e) g hm.2
            | inr ht => exact False.elim (lt_Z_inv ht.2.2)
      · rw [ite_eq_right hca]
        by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
        · rw [ite_eq_left hfa]
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
                injection heq with _ hmid
                exact Or.inr hmid
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
                injection heqca with _ hmid
                exact Or.inr hmid
            have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
              cases hclea with
              | inl hlt => exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
              | inr heqca => rw [heqca]; exact Or.inr rfl
            exact False.elim (hca hheadca)
        · rw [ite_eq_right hfa]
          exact hbd

#print axioms bridge_insert_lt


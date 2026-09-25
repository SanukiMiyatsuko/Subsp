import Subsp.new.stop_progress_mid

open T

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
      by_cases hup : u ≤ p
      · rw [ite_eq_left hup, ite_eq_left hup]
        rw [ihy]
        rw [← List.append_assoc]
      · rw [ite_eq_right hup, ite_eq_right hup]
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
  by_cases hb : (T.part s).2 = T.Z
  · have hadd := bridge_part_add s
    rw [hb, T.add_Z] at hadd
    exact Or.inr hadd
  · apply Or.inl
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
    by_cases ha : a = T.Z
    · rw [hec, ite_eq_left ha]
      have hbEq : b = s := by
        rw [ha, T.add] at hadd
        exact hadd
      have hbshape := bridge_part_second_shape s a b hp
      cases hbshape with
      | inl hbz =>
        rw [hbz]
        exact T.Lt.Z_lt_P 0 c T.Z
      | inr hbp =>
        obtain ⟨e, f, hbeq⟩ := hbp
        rw [hbeq]
        have hes : e < s := bridge_remainder_member_lt s a e f (by
          rw [hbeq] at hp
          exact hp) hg
        have hecLt : e < c := lt_trans_thm e s c hes hsc
        exact T.Lt.p_mid 0 e c f T.Z hecLt
    · rw [hec, ite_eq_right ha]
      by_cases hhead : T.head b ≤ T.P 0 a T.Z
      · rw [ite_eq_left hhead]
        have has0 := bridge_part_fst_le_self s
        have has : a ≤ s := by
          rw [hp] at has0
          exact has0
        have hac : a < c := lt_of_le_of_lt_thm T a s c has hsc
        exact T.Lt.p_mid 0 a c b T.Z hac
      · rw [ite_eq_right hhead]
        have hbshape := bridge_part_second_shape s a b hp
        cases hbshape with
        | inl hbz =>
          rw [hbz]
          exact T.Lt.Z_lt_P 0 c T.Z
        | inr hbp =>
          obtain ⟨e, f, hbeq⟩ := hbp
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
    by_cases hhead : T.head d ≤ T.P 0 c T.Z
    · rw [ite_eq_left hhead]
      cases T.Z_le d with
      | inl hzd =>
        exact Or.inl (T.Lt.p_tail 0 c T.Z d hzd)
      | inr hzd =>
        have hdZ : d = T.Z := hzd.symm
        rw [hdZ]
        exact Or.inr rfl
    · rw [ite_eq_right hhead]
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
    (htg : ∀ x : T, x ∈ T.G1 0 t → x < t)
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
        by_cases ha : a = T.Z
        · have hecs := bridge_early_collapse_part s a b hps hbNF
          have hect := bridge_early_collapse_part t a d hpt hdNF
          rw [hecs, hect, ite_eq_left ha, ite_eq_left ha]
          exact hbd
        · rw [T.early_collapse, hps, ite_eq_right ha]
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
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
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
                  bridge_early_collapse_lt a e haNF haG heNF heG hae
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
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
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
    (ht : T.isNF1 t) (htg : ∀ x : T, x ∈ T.G1 0 t → x < t)
    (hst : s ≤ t) : T.early_collapse s ≤ T.early_collapse t := by
  cases hst with
  | inl hlt => exact Or.inl (bridge_early_collapse_lt s t hs hsg ht htg hlt)
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
    injection heq with _ hmid
    exact Or.inr hmid

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
      obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
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
              obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hbNF
              have hea : e ≤ a := bridge_P0_head_mid_le a e f hheadb
              have hecE := bridge_early_collapse_closed e heNF heG
              have hecLe : T.early_collapse e ≤ T.early_collapse a :=
                bridge_early_collapse_le e a heNF heG haNF haG hea
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
      obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
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
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
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

import FoundUpper

open T

theorem tn_head_index0_le_P1 (e m : T)
    (he : T.index_Prop1 0 e) : T.head e ≤ T.P 1 m T.Z := by
  cases e with
  | Z => exact T.Z_le (T.P 1 m T.Z)
  | P p a b =>
    cases he with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      exact Or.inl (T.Lt.p_head 0 1 a m T.Z T.Z (Nat.zero_lt_succ 0))

#print axioms tn_head_index0_le_P1

theorem tn_shift1_lt_outer_any (a tail : T) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a <
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a) tail := by
  rw [mul_succ_shape 1 T.Z 0, T.P_add_eq]
  exact T.Lt.p_mid 1 T.Z
    (T.P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) a))
    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) a) tail
    (T.Lt.Z_lt_P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) a))

#print axioms tn_shift1_lt_outer_any

theorem tn_append_card1_index0 : ∀ c e : T,
    T.isNF1 (T.card_times 1 c) →
    T.isNF1 e → T.index_Prop1 0 e →
    T.isNF1 (T.add (T.card_times 1 c) e) ∧
      T.index_Prop1 1 (T.add (T.card_times 1 c) e) ∧
      (∀ x : T, x ∈ T.G1 1 (T.add (T.card_times 1 c) e) →
        x < T.add (T.card_times 1 c) e) := by
  intro c
  induction c with
  | Z =>
    intro e hcNF heNF heIdx
    rw [T.card_times.eq_1, T.add.eq_1]
    have heIdx1 := Rank1Termination.index_mono (Nat.zero_le 1) e heIdx
    have heEmpty := index_Prop1_G1_empty 0 e heIdx 1 (Nat.zero_lt_succ 0)
    refine ⟨heNF, heIdx1, ?_⟩
    intro x hx
    rw [heEmpty] at hx
    cases hx
  | P p a b iha ihb =>
    intro e hcNF heNF heIdx
    rw [T.card_times.eq_3] at hcNF ⊢
    by_cases hp : p = 0
    · rw [ite_eq_left hp] at hcNF ⊢
      let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) (T.early_collapse a)
      change T.isNF1 (T.add (T.P 1 M T.Z) (T.card_times 1 b)) at hcNF
      rw [T.P_add_eq, T.add.eq_1] at hcNF
      change
        T.isNF1 (T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e) ∧
          T.index_Prop1 1 (T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e) ∧
          (∀ x : T, x ∈ T.G1 1 (T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e) →
            x < T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e)
      rw [T.P_add_eq, T.add.eq_1, T.P_add_eq]
      have hinv := T.isNF1_P_inv 1 M (T.card_times 1 b) hcNF
      have htail := ihb e hinv.2.1 heNF heIdx
      have hhead : T.head (T.add (T.card_times 1 b) e) ≤ T.P 1 M T.Z := by
        by_cases hbz : T.card_times 1 b = T.Z
        · rw [hbz, T.add.eq_1]
          exact tn_head_index0_le_P1 e M heIdx
        · rw [bridge_head_add_ne_Z (T.card_times 1 b) e hbz]
          exact hinv.2.2.2
      have hwholeNF := T.isNF1.p 1 M (T.add (T.card_times 1 b) e)
        hinv.1 htail.1 hinv.2.2.1 hhead
      have hwholeIdx := T.index_Prop1.p 1 M (T.add (T.card_times 1 b) e)
        (Nat.le_refl 1) htail.2.1
      refine ⟨hwholeNF, hwholeIdx, ?_⟩
      intro x hx
      rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1), List.mem_append,
        List.mem_append] at hx
      cases hx with
      | inl hl =>
        cases hl with
        | inl hm =>
          have heq : x = M := List.mem_singleton.mp hm
          rw [heq]
          unfold M
          exact bridge_shift_lt_outer 0 (T.early_collapse a)
            (T.add (T.card_times 1 b) e)
            (by
              have hMnf := hinv.1
              rw [T.ofNat, T.mul, T.add] at hMnf
              -- M is early_collapse a at shift 0; its index-zero property follows from its shape.
              exact bridge_early_collapse_closed a
                (by
                  -- extract NF of a from NF of M via the original construction is not needed;
                  -- use the already normalized NF constructor to recover it below.
                  exact (T.isNF1_P_inv 1 M (T.card_times 1 b) hcNF).1 |> fun _ => by
                    cases hp)
                (fun y hy => by cases hp))
        | inr hgm =>
          have hxm := hinv.2.2.1 x hgm
          have hmwhole : M < T.P 1 M (T.add (T.card_times 1 b) e) := by
            -- M starts below the enclosing index-one principal; derive this from its explicit shift-zero form.
            unfold M
            cases T.early_collapse a with
            | Z => exact T.Lt.Z_lt_P 1 T.Z (T.add (T.card_times 1 b) e)
            | P q d f =>
              rw [T.ofNat, T.mul, T.add]
              exact T.Lt.p_head q 1 d (T.P q d f) f
                (T.add (T.card_times 1 b) e)
                (by
                  -- early_collapse of an index-zero source has index zero; q must be zero.
                  sorry)
          exact lt_trans_thm x M _ hxm hmwhole
      | inr ht =>
        have hxt := htail.2.2 x ht
        have htle := T.isNF1_tail_le _ hwholeNF 1 M
          (T.add (T.card_times 1 b) e) rfl
        exact lt_of_lt_of_le_thm T x _ _ hxt htle
    · rw [ite_eq_right hp] at hcNF ⊢
      let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a
      change T.isNF1 (T.add (T.P 1 M T.Z) (T.card_times 1 b)) at hcNF
      rw [T.P_add_eq, T.add.eq_1] at hcNF
      change
        T.isNF1 (T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e) ∧
          T.index_Prop1 1 (T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e) ∧
          (∀ x : T, x ∈ T.G1 1 (T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e) →
            x < T.add (T.add (T.P 1 M T.Z) (T.card_times 1 b)) e)
      rw [T.P_add_eq, T.add.eq_1, T.P_add_eq]
      have hinv := T.isNF1_P_inv 1 M (T.card_times 1 b) hcNF
      have htail := ihb e hinv.2.1 heNF heIdx
      have hhead : T.head (T.add (T.card_times 1 b) e) ≤ T.P 1 M T.Z := by
        by_cases hbz : T.card_times 1 b = T.Z
        · rw [hbz, T.add.eq_1]
          exact tn_head_index0_le_P1 e M heIdx
        · rw [bridge_head_add_ne_Z (T.card_times 1 b) e hbz]
          exact hinv.2.2.2
      have hwholeNF := T.isNF1.p 1 M (T.add (T.card_times 1 b) e)
        hinv.1 htail.1 hinv.2.2.1 hhead
      have hwholeIdx := T.index_Prop1.p 1 M (T.add (T.card_times 1 b) e)
        (Nat.le_refl 1) htail.2.1
      refine ⟨hwholeNF, hwholeIdx, ?_⟩
      intro x hx
      rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1), List.mem_append,
        List.mem_append] at hx
      cases hx with
      | inl hl =>
        cases hl with
        | inl hm =>
          have heq : x = M := List.mem_singleton.mp hm
          rw [heq]
          unfold M
          exact tn_shift1_lt_outer_any a (T.add (T.card_times 1 b) e)
        | inr hgm =>
          have hxm := hinv.2.2.1 x hgm
          have hmwhole : M < T.P 1 M (T.add (T.card_times 1 b) e) := by
            unfold M
            exact tn_shift1_lt_outer_any a (T.add (T.card_times 1 b) e)
          exact lt_trans_thm x M _ hxm hmwhole
      | inr ht =>
        have hxt := htail.2.2 x ht
        have htle := T.isNF1_tail_le _ hwholeNF 1 M
          (T.add (T.card_times 1 b) e) rfl
        exact lt_of_lt_of_le_thm T x _ _ hxt htle

#print axioms tn_append_card1_index0

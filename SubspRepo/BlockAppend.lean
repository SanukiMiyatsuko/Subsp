import AppendBridge
import CardAux

open T

theorem ba_index0_lt_card_succ (n : Nat) (d z : T)
    (hdIdx : T.index_Prop1 0 d)
    (hzIdx : T.index_Prop1 0 z) (hzNe : z ≠ T.Z) :
    d < T.card_times (n + 1) z := by
  cases z with
  | Z => exact False.elim (hzNe rfl)
  | P p a b =>
    cases hzIdx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      rw [T.card_times.eq_3, ite_eq_left rfl]
      rw [← add_eq_hAdd
            (T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                (T.early_collapse a)) T.Z)
            (T.card_times (n + 1) b),
          T.P_add_eq, T.add.eq_1]
      cases d with
      | Z => exact T.Lt.Z_lt_P 1 _ _
      | P q c e =>
        cases hdIdx with
        | p _ _ _ hq he =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          subst q
          exact T.Lt.p_head 0 1 c _ e _ (Nat.zero_lt_succ 0)

#print axioms ba_index0_lt_card_succ

theorem ba_append_index0_below_card : ∀ n : Nat, ∀ z p d : T,
    T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
    T.index_Prop1 1 p → T.index_Prop1 0 d →
    p < T.card_times (n + 1) z →
    T.add p d < T.card_times (n + 1) z := by
  intro n z
  induction z with
  | Z =>
    intro p d hzNF hzIdx hzNe hpIdx hdIdx hlt
    exact False.elim (hzNe rfl)
  | P q a b iha ihb =>
    intro p d hzNF hzIdx hzNe hpIdx hdIdx hlt
    cases hzIdx with
    | p _ _ _ hq hbIdx =>
      have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
      subst q
      obtain ⟨haNF, hbNF, haG, hhead⟩ := T.isNF1_P_inv 0 a b hzNF
      rw [T.card_times.eq_3, ite_eq_left rfl] at hlt ⊢
      rw [← add_eq_hAdd
            (T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                (T.early_collapse a)) T.Z)
            (T.card_times (n + 1) b),
          T.P_add_eq, T.add.eq_1] at hlt ⊢
      let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
        (T.early_collapse a)
      cases p with
      | Z =>
        rw [T.add.eq_1]
        exact ba_index0_lt_card_succ n d (T.P 0 a b)
          hdIdx (T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx)
          (by intro h; cases h)
      | P r c e =>
        cases hpIdx with
        | p _ _ _ hr heIdx =>
          have hrCases : r = 0 ∨ r = 1 := by
            cases r with
            | zero => exact Or.inl rfl
            | succ r' =>
              have hs : r' + 1 ≤ 1 := hr
              have hr0 : r' = 0 :=
                Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hs)
              subst r'
              exact Or.inr rfl
          cases hrCases with
          | inl hr0 =>
            subst r
            rw [T.P_add_eq]
            exact T.Lt.p_head 0 1 c M (T.add e d)
              (T.card_times (n + 1) b) (Nat.zero_lt_succ 0)
          | inr hr1 =>
            subst r
            rw [T.P_add_eq]
            cases lt_inv 1 c e 1 M (T.card_times (n + 1) b) hlt with
            | inl hh => exact False.elim (Nat.lt_irrefl 1 hh)
            | inr hor =>
              cases hor with
              | inl hm =>
                exact T.Lt.p_mid 1 c M (T.add e d)
                  (T.card_times (n + 1) b) hm.2
              | inr ht =>
                cases ht.1
                cases ht.2.1
                have heb : e < T.card_times (n + 1) b := ht.2.2
                by_cases hbZ : b = T.Z
                · rw [hbZ, T.card_times.eq_1] at heb
                  exact False.elim (lt_Z_inv heb)
                · have hrec := ihb e d hbNF hbIdx hbZ heIdx hdIdx heb
                  exact T.Lt.p_tail 1 M (T.add e d)
                    (T.card_times (n + 1) b) hrec

#print axioms ba_append_index0_below_card

theorem ba_card_same_append_lt (n : Nat) : ∀ c d y : T,
    T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
    T.isNF1 d → T.index_Prop1 0 d → d ≠ T.Z →
    c < d →
    (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
      y < T.card_times (n + 1) z) →
    T.add (T.card_times (n + 1) c) y < T.card_times (n + 1) d := by
  intro c
  induction c with
  | Z =>
    intro d y hcNF hcIdx hcNe hdNF hdIdx hdNe hcd hy
    exact False.elim (hcNe rfl)
  | P p a b iha ihb =>
    intro d y hcNF hcIdx hcNe hdNF hdIdx hdNe hcd hy
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      cases d with
      | Z => exact False.elim (hdNe rfl)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq hfIdx =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ :=
            T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ :=
            T.isNF1_P_inv 0 e f hdNF
          rw [T.card_times.eq_3, ite_eq_left rfl]
          rw [T.card_times.eq_3, ite_eq_left rfl]
          rw [← add_eq_hAdd
                (T.P 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                    (T.early_collapse a)) T.Z)
                (T.card_times (n + 1) b),
              T.P_add_eq, T.add.eq_1]
          rw [← add_eq_hAdd
                (T.P 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                    (T.early_collapse e)) T.Z)
                (T.card_times (n + 1) f),
              T.P_add_eq, T.add.eq_1]
          rw [T.P_add_eq]
          cases lt_inv 0 a b 0 e f hcd with
          | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
          | inr hor =>
            cases hor with
            | inl hm =>
              have hec : T.early_collapse a < T.early_collapse e :=
                bridge_early_collapse_lt a e haNF haG heNF heG hm.2
              have hmid := bridge_add_left_lt
                (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                (T.early_collapse a) (T.early_collapse e) hec
              exact T.Lt.p_mid 1 _ _ _ _ hmid
            | inr ht =>
              cases ht.1
              cases ht.2.1
              have hbf : b < f := ht.2.2
              by_cases hbZ : b = T.Z
              · subst b
                rw [T.card_times.eq_1, T.add.eq_1]
                have hfNe : f ≠ T.Z := by
                  intro heq
                  rw [heq] at hbf
                  exact lt_Z_inv hbf
                exact T.Lt.p_tail 1 _ y (T.card_times (n + 1) f)
                  (hy f hfNF hfIdx hfNe)
              · have hfNe : f ≠ T.Z := by
                  intro heq
                  rw [heq] at hbf
                  exact lt_Z_inv hbf
                have htail := ihb f y hbNF hbIdx hbZ
                  hfNF hfIdx hfNe hbf hy
                exact T.Lt.p_tail 1 _
                  (T.add (T.card_times (n + 1) b) y)
                  (T.card_times (n + 1) f) htail

#print axioms ba_card_same_append_lt

import CardAlgebra


theorem ac_card1_sum_inv {lam : Nat} :
    ∀ (k : Nat) (v : new.Vec (new.T lam) (k + 1)),
      (∀ a ∈ new.Vec.toList v,
        T.isNF1 (trans a) ∧
          ∀ x : T, x ∈ T.G1 0 (trans a) → x < trans a) →
      let sum := (transAux v).2.1
      T.isNF1 (T.card_times 1 sum) ∧
        T.index_Prop1 1 (T.card_times 1 sum) ∧
        (∀ x : T, x ∈ T.G1 1 (T.card_times 1 sum) →
          x < T.card_times 1 sum) ∧
        (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
          T.card_times 1 sum < T.card_times (k + 1) z) := by
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
          T.isNF1 (T.card_times 1 T.Z) ∧
            T.index_Prop1 1 (T.card_times 1 T.Z) ∧
            (∀ x : T, x ∈ T.G1 1 (T.card_times 1 T.Z) → x < T.card_times 1 T.Z) ∧
            (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
              T.card_times 1 T.Z < T.card_times 1 z)
        rw [T.card_times.eq_1]
        constructor
        · exact T.isNF1.z
        · constructor
          · exact T.index_Prop1.z
          · constructor
            · intro x hx
              rw [T.G1.eq_1] at hx
              cases hx
            · intro z hzNF hzIdx hzne
              have hne := bridge_card_times_ne_Z 1 z hzne
              cases T.Z_le (T.card_times 1 z) with
              | inl hlt => exact hlt
              | inr heq => exact False.elim (hne heq.symm)
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
                (T.card_times 1
                  (T.add (T.card_times m (T.early_collapse (trans a))) sum)) ∧
              T.index_Prop1 1
                (T.card_times 1
                  (T.add (T.card_times m (T.early_collapse (trans a))) sum)) ∧
              (∀ x : T,
                x ∈ T.G1 1
                  (T.card_times 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum)) →
                x < T.card_times 1
                  (T.add (T.card_times m (T.early_collapse (trans a))) sum)) ∧
              (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
                T.card_times 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum) <
                  T.card_times (m + 2) z)
          have hec := bridge_early_collapse_closed
            (trans a) haCoord.1 haCoord.2
          rw [ca_card_times_add]
          rw [ca_card_times_one_comp hec.2.1 m]
          by_cases hecz : T.early_collapse (trans a) = T.Z
          · rw [hecz, T.card_times.eq_1, T.add.eq_1]
            constructor
            · exact hrest.1
            · constructor
              · exact hrest.2.1
              · constructor
                · exact hrest.2.2.1
                · intro z hzNF hzIdx hzne
                  have hlow := hrest.2.2.2 z hzNF hzIdx hzne
                  have hlevel := bridge_card_times_level_lt (m + 1) (m + 2)
                    z z (Nat.lt_succ_self (m + 1))
                    hzNF hzIdx hzne hzNF hzIdx hzne
                  exact lt_trans_thm (T.card_times 1 sum)
                    (T.card_times (m + 1) z) (T.card_times (m + 2) z)
                    hlow hlevel
          · have happ := bridge_card_times_succ_append m
              (T.early_collapse (trans a)) (T.card_times 1 sum)
              hec.1 hec.2.1 hrest.1 hrest.2.1 hrest.2.2.1
              (fun z hzNF hzIdx hzne => hrest.2.2.2 z hzNF hzIdx hzne)
            constructor
            · exact happ.1
            · constructor
              · exact happ.2.1
              · constructor
                · exact happ.2.2
                · intro z hzNF hzIdx hzne
                  exact bridge_card_times_add_level_lt (m + 1) (m + 2)
                    (T.early_collapse (trans a)) z (T.card_times 1 sum)
                    (Nat.lt_succ_self (m + 1))
                    hec.1 hec.2.1 hecz hzNF hzIdx hzne

#print axioms ac_card1_sum_inv


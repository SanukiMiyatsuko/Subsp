import Bridge

open T

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
                    have hlevel := bridge_card_times_level_lt m (m + 1) z z
                      (Nat.lt_succ_self m) hzNF hzIdx hzne hzNF hzIdx hzne
                    exact lt_trans_thm sum (T.card_times m z)
                      (T.card_times (m + 1) z) hlow hlevel
            · cases m with
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

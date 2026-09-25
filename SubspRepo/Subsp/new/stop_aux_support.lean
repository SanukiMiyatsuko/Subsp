import Subsp.new.stop_card_support

open T

theorem as_card1_support_pair {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ z : new.T lam, z ∈ new.Vec.toList v →
        T.isNF1 (trans z) ∧
          (∀ y : T, y ∈ T.G1 0 (trans z) → y < trans z)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        (∀ x : T, x ∈ T.G1 0 (T.card_times 1 sum) →
          x < T.P 1 (T.card_times 1 sum) T.Z ∨
            ∃ z : new.T lam, z ∈ new.Vec.toList v ∧ x ≤ trans z) ∧
        (∀ x : T, x ∈ T.G1 0 (T.card_times 1 (T.one_del sum)) →
          x < T.P 1 (T.card_times 1 (T.one_del sum)) T.Z ∨
            ∃ z : new.T lam, z ∈ new.Vec.toList v ∧ x ≤ trans z) := by
  intro k
  induction k with
  | zero =>
      intro v hcoord found sum a0 haux
      cases v with
      | @snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              cases haux
              constructor
              · intro x hx
                rw [T.card_times.eq_1, T.G1.eq_1] at hx
                cases hx
              · intro x hx
                change x ∈ T.G1 0 (T.card_times 1 T.Z) at hx
                rw [T.card_times.eq_1, T.G1.eq_1] at hx
                cases hx
  | succ m ih =>
      intro v hcoord found sum a0 haux
      cases v with
      | @snoc n xs a =>
          have hxs :
              ∀ z : new.T lam, z ∈ new.Vec.toList xs →
                T.isNF1 (trans z) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans z) → y < trans z) := by
            intro z hz
            exact hcoord z (List.mem_append_left [a] hz)
          have ha :
              T.isNF1 (trans a) ∧
                (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
            apply hcoord a
            exact List.mem_append_right (new.Vec.toList xs)
              (List.mem_singleton_self a)
          cases hrest : transAux xs with
          | mk foundRest rest =>
              cases rest with
              | mk sumRest a0Rest =>
                  have hpair := ih xs hxs foundRest sumRest a0Rest hrest
                  have hrestCard := sc_transAux_card1_inv xs hxs
                    foundRest sumRest a0Rest hrest
                  rw [transAux.eq_3, hrest] at haux
                  cases a with
                  | Z =>
                      rw [_root_.trans.eq_1] at haux
                      change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
                      cases haux
                      constructor
                      · intro x hx
                        cases hpair.1 x hx with
                        | inl hlt => exact Or.inl hlt
                        | inr hw =>
                            obtain ⟨z, hz, hxz⟩ := hw
                            exact Or.inr ⟨z,
                              List.mem_append_left [new.T.Z] hz, hxz⟩
                      · intro x hx
                        cases hpair.2 x hx with
                        | inl hlt => exact Or.inl hlt
                        | inr hw =>
                            obtain ⟨z, hz, hxz⟩ := hw
                            exact Or.inr ⟨z,
                              List.mem_append_left [new.T.Z] hz, hxz⟩
                  | P als aadd =>
                      have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                        intro h
                        cases h
                      have hatNe : trans (new.T.P als aadd) ≠ T.Z :=
                        tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
                      have hec := bridge_early_collapse_closed
                        (trans (new.T.P als aadd)) ha.1 ha.2
                      have hecNe := bridge_early_collapse_ne_Z
                        (trans (new.T.P als aadd)) hatNe
                      change
                        (true,
                          T.card_times m
                              (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                          a0Rest) = (found, sum, a0) at haux
                      cases haux
                      let ec := T.early_collapse (trans (new.T.P als aadd))
                      let B := T.card_times (m + 1) ec
                      let R := T.card_times 1 sumRest
                      let A := T.add B R
                      have hBA : B ≤ A := by
                        unfold A
                        exact wt_add_self_le B R
                      have hRB : R < B := by
                        unfold R B ec
                        exact hrestCard.2.2.2
                          (T.early_collapse (trans (new.T.P als aadd)))
                          hec.1 hec.2.1 hecNe
                      have hU :
                          ∀ x : T, x ∈ T.G1 0 A →
                            x < T.P 1 A T.Z ∨
                              ∃ z : new.T lam,
                                z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                                x ≤ trans z := by
                        intro x hx
                        unfold A at hx ⊢
                        rw [bridge_G1_add_eq] at hx
                        cases List.mem_append.mp hx with
                        | inl hBmem =>
                            have hcur := cs_card_support m ec
                              (trans (new.T.P als aadd)) hec.1 hec.2.1
                              (sg_early_G0_le (trans (new.T.P als aadd)) ha.1 ha.2)
                              x hBmem
                            cases hcur with
                            | inl hlt =>
                                have hLift := bridge_lift_P1_le B (T.add B R)
                                  (wt_add_self_le B R)
                                exact Or.inl (lt_of_lt_of_le_thm T x
                                  (T.P 1 B T.Z) (T.P 1 (T.add B R) T.Z)
                                  hlt hLift)
                            | inr hxcoord =>
                                exact Or.inr ⟨new.T.P als aadd,
                                  List.mem_append_right (new.Vec.toList xs)
                                    (List.mem_singleton_self (new.T.P als aadd)),
                                  hxcoord⟩
                        | inr hRmem =>
                            have hrestDec := hpair.1 x hRmem
                            cases hrestDec with
                            | inr hw =>
                                obtain ⟨z, hz, hxz⟩ := hw
                                exact Or.inr ⟨z,
                                  List.mem_append_left [new.T.P als aadd] hz,
                                  hxz⟩
                            | inl hlt =>
                                have hRA : R < T.add B R :=
                                  lt_of_lt_of_le_thm T R B (T.add B R) hRB
                                    (wt_add_self_le B R)
                                have hLift : T.P 1 R T.Z < T.P 1 (T.add B R) T.Z :=
                                  T.Lt.p_mid 1 R (T.add B R) T.Z T.Z hRA
                                exact Or.inl (lt_trans_thm x (T.P 1 R T.Z)
                                  (T.P 1 (T.add B R) T.Z) hlt hLift)
                      have hsumCard : T.card_times 1
                            (T.add (T.card_times m ec) sumRest) = A := by
                        unfold A B R
                        rw [ca_card_times_add, ca_card_times_one_comp]
                      constructor
                      · intro x hx
                        change x ∈ T.G1 0
                          (T.card_times 1
                            (T.add (T.card_times m ec) sumRest)) at hx
                        change x < T.P 1
                            (T.card_times 1
                              (T.add (T.card_times m ec) sumRest)) T.Z ∨
                          ∃ z : new.T lam,
                            z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                            x ≤ trans z
                        rw [hsumCard] at hx ⊢
                        exact hU x hx
                      · cases m with
                        | zero =>
                            cases xs with
                            | @snoc q ys b =>
                                cases ys with
                                | nil =>
                                    rw [transAux.eq_2] at hrest
                                    cases hrest
                                    change
                                      ∀ x : T,
                                        x ∈ T.G1 0
                                          (T.card_times 1
                                            (T.one_del
                                              (T.add (T.card_times 0 ec) T.Z))) →
                                        x < T.P 1
                                          (T.card_times 1
                                            (T.one_del
                                              (T.add (T.card_times 0 ec) T.Z))) T.Z ∨
                                          ∃ z : new.T lam,
                                            z ∈ new.Vec.toList
                                              (new.Vec.snoc 1
                                                (new.Vec.snoc 0 new.Vec.nil b)
                                                (new.T.P als aadd)) ∧
                                            x ≤ trans z
                                    rw [tc_card_times_zero, T.add_Z]
                                    have hdel := oc_one_del_NF_index0 ec hec.1 hec.2.1
                                    intro x hx
                                    have hbase := cs_card_support 0 (T.one_del ec)
                                      (trans (new.T.P als aadd)) hdel.1 hdel.2
                                      (by
                                        intro y hy
                                        exact sg_early_G0_le
                                          (trans (new.T.P als aadd)) ha.1 ha.2 y
                                          (cs_one_del_G0 ec y hy))
                                      x hx
                                    cases hbase with
                                    | inl hlt => exact Or.inl hlt
                                    | inr hle =>
                                        exact Or.inr ⟨new.T.P als aadd,
                                          List.mem_append_right
                                            (new.Vec.toList
                                              (new.Vec.snoc 0 new.Vec.nil b))
                                            (List.mem_singleton_self
                                              (new.T.P als aadd)), hle⟩
                        | succ j =>
                            have hdel :
                                T.one_del
                                    (T.add (T.card_times (j + 1) ec) sumRest) =
                                  T.add (T.card_times (j + 1) ec) sumRest :=
                              cs_one_del_card_succ_add j ec sumRest hec.2.1 hecNe
                            intro x hx
                            change x ∈ T.G1 0
                              (T.card_times 1
                                (T.one_del
                                  (T.add (T.card_times (j + 1) ec) sumRest))) at hx
                            change x < T.P 1
                                (T.card_times 1
                                  (T.one_del
                                    (T.add (T.card_times (j + 1) ec) sumRest))) T.Z ∨
                              ∃ z : new.T lam,
                                z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                                x ≤ trans z
                            rw [hdel] at hx ⊢
                            have hcardEq : T.card_times 1
                                (T.add (T.card_times (j + 1) ec) sumRest) =
                              T.add (T.card_times (j + 2) ec)
                                (T.card_times 1 sumRest) := by
                              rw [ca_card_times_add, ca_card_times_one_comp]
                            rw [hcardEq] at hx ⊢
                            change x ∈ T.G1 0 (T.add
                              (T.card_times (j + 2) ec) R) at hx
                            change x < T.P 1
                              (T.add (T.card_times (j + 2) ec) R) T.Z ∨
                              ∃ z : new.T lam,
                                z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                                x ≤ trans z
                            exact hU x hx

#print axioms as_card1_support_pair

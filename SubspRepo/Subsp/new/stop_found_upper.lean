import Subsp.new.stop_card_sum
import Subsp.new.stop_order_aux
import Subsp.new.stop_nf_aux

open T

theorem fu_card_times_pos_shape (q : Nat) (c : T)
    (hc : T.index_Prop1 0 c) (hne : c ≠ T.Z) :
    ∃ m tail : T, T.card_times (q + 1) c = T.P 1 m tail := by
  cases c with
  | Z => exact False.elim (hne rfl)
  | P p a b =>
    cases hc with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      rw [T.card_times.eq_3, ite_eq_left rfl]
      refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat q)) (T.early_collapse a),
        T.card_times (q + 1) b, ?_⟩
      change
        T.add
          (T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat q))
            (T.early_collapse a)) T.Z)
          (T.card_times (q + 1) b) =
        T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat q))
          (T.early_collapse a)) (T.card_times (q + 1) b)
      rw [T.P_add_eq, T.add.eq_1]

#print axioms fu_card_times_pos_shape

theorem fu_found_upper_closed {lam : Nat} :
    ∀ (k : Nat) (v : new.Vec (new.T lam) (k + 1)),
      (∀ a ∈ new.Vec.toList v,
        T.isNF1 (trans a) ∧
          ∀ x : T, x ∈ T.G1 0 (trans a) → x < trans a) →
      let r := transAux v
      r.1 = true →
        T.isNF1 (T.card_times 1 (T.one_del r.2.1)) ∧
          T.index_Prop1 1 (T.card_times 1 (T.one_del r.2.1)) ∧
          (∀ x : T,
            x ∈ T.G1 1 (T.card_times 1 (T.one_del r.2.1)) →
              x < T.card_times 1 (T.one_del r.2.1)) := by
  intro k
  induction k with
  | zero =>
    intro v hcoord
    cases v with
    | snoc n xs a =>
      cases xs with
      | nil =>
        change false = true → _
        intro h
        cases h
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
      cases haux : transAux xs with
      | mk found rest =>
        cases rest with
        | mk sum a0 =>
          rw [transAux.eq_3, haux]
          cases a with
          | Z =>
            change found = true →
              T.isNF1 (T.card_times 1 (T.one_del sum)) ∧
                T.index_Prop1 1 (T.card_times 1 (T.one_del sum)) ∧
                (∀ x : T, x ∈ T.G1 1 (T.card_times 1 (T.one_del sum)) →
                  x < T.card_times 1 (T.one_del sum))
            intro hfound
            have hrec := ih xs hxsCoord
            rw [haux] at hrec
            exact hrec hfound
          | P ls add =>
            change true = true → _
            intro _
            have htransNe : trans (new.T.P ls add) ≠ T.Z :=
              tc_trans_ne_Z_of_ne_Z (new.T.P ls add) (by intro h; cases h)
            have hec := bridge_early_collapse_closed
              (trans (new.T.P ls add)) haCoord.1 haCoord.2
            have hecNe := bridge_early_collapse_ne_Z
              (trans (new.T.P ls add)) htransNe
            cases m with
            | zero =>
              cases xs with
              | snoc n ys b =>
                cases ys with
                | nil =>
                  rw [transAux.eq_2] at haux
                  cases haux
                  change
                    T.isNF1
                        (T.card_times 1
                          (T.one_del
                            (T.add (T.card_times 0
                              (T.early_collapse (trans (new.T.P ls add)))) T.Z))) ∧
                      T.index_Prop1 1
                        (T.card_times 1
                          (T.one_del
                            (T.add (T.card_times 0
                              (T.early_collapse (trans (new.T.P ls add)))) T.Z))) ∧
                      (∀ x : T,
                        x ∈ T.G1 1
                          (T.card_times 1
                            (T.one_del
                              (T.add (T.card_times 0
                                (T.early_collapse (trans (new.T.P ls add)))) T.Z))) →
                        x < T.card_times 1
                          (T.one_del
                            (T.add (T.card_times 0
                              (T.early_collapse (trans (new.T.P ls add)))) T.Z)))
                  rw [tc_card_times_zero, T.add_Z]
                  have hdel := ca_one_del_index0
                    (T.early_collapse (trans (new.T.P ls add))) hec.1 hec.2.1
                  exact bridge_card_times_closed 1
                    (T.one_del (T.early_collapse (trans (new.T.P ls add))))
                    hdel.1 hdel.2
            | succ q =>
              have hwhole := ac_card1_sum_inv (q + 2)
                (new.Vec.snoc (q + 2) xs (new.T.P ls add)) hcoord
              rw [transAux.eq_3, haux] at hwhole
              change
                T.isNF1
                    (T.card_times 1
                      (T.add
                        (T.card_times (q + 1)
                          (T.early_collapse (trans (new.T.P ls add)))) sum)) ∧
                  T.index_Prop1 1
                    (T.card_times 1
                      (T.add
                        (T.card_times (q + 1)
                          (T.early_collapse (trans (new.T.P ls add)))) sum)) ∧
                  (∀ x : T,
                    x ∈ T.G1 1
                      (T.card_times 1
                        (T.add
                          (T.card_times (q + 1)
                            (T.early_collapse (trans (new.T.P ls add)))) sum)) →
                    x < T.card_times 1
                      (T.add
                        (T.card_times (q + 1)
                          (T.early_collapse (trans (new.T.P ls add)))) sum)) ∧ _ at hwhole
              obtain ⟨mid, tail, hshape⟩ := fu_card_times_pos_shape q
                (T.early_collapse (trans (new.T.P ls add))) hec.2.1 hecNe
              have hone :
                  T.one_del
                    (T.add
                      (T.card_times (q + 1)
                        (T.early_collapse (trans (new.T.P ls add)))) sum) =
                  T.add
                    (T.card_times (q + 1)
                      (T.early_collapse (trans (new.T.P ls add)))) sum := by
                rw [hshape, T.P_add_eq]
                rfl
              change
                T.isNF1
                    (T.card_times 1
                      (T.one_del
                        (T.add
                          (T.card_times (q + 1)
                            (T.early_collapse (trans (new.T.P ls add)))) sum))) ∧
                  T.index_Prop1 1
                    (T.card_times 1
                      (T.one_del
                        (T.add
                          (T.card_times (q + 1)
                            (T.early_collapse (trans (new.T.P ls add)))) sum))) ∧
                  (∀ x : T,
                    x ∈ T.G1 1
                      (T.card_times 1
                        (T.one_del
                          (T.add
                            (T.card_times (q + 1)
                              (T.early_collapse (trans (new.T.P ls add)))) sum))) →
                    x < T.card_times 1
                      (T.one_del
                        (T.add
                          (T.card_times (q + 1)
                            (T.early_collapse (trans (new.T.P ls add)))) sum)))
              rw [hone]
              exact ⟨hwhole.1, hwhole.2.1, hwhole.2.2.1⟩

#print axioms fu_found_upper_closed

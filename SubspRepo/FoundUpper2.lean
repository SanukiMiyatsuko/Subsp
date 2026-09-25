import CardSum

open T

theorem fu2_trans_ne_Z {lam : Nat} (a : new.T lam) (ha : a ≠ new.T.Z) :
    trans a ≠ T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P ls add =>
    rw [_root_.trans.eq_2]
    cases haux : transAux ls with
    | mk found rest =>
      cases rest with
      | mk sum a0 =>
        change
          (if found = true then
            T.P 1
              (T.add (T.card_times 1 (T.one_del sum))
                (T.early_collapse a0)) (trans add)
          else if a0 = T.Z then
            T.P 0 T.Z (trans add)
          else T.P 0 a0 (trans add)) ≠ T.Z
        by_cases hf : found = true
        · rw [ite_eq_left hf]
          intro h
          cases h
        · rw [ite_eq_right hf]
          by_cases ha0 : a0 = T.Z
          · rw [ite_eq_left ha0]
            intro h
            cases h
          · rw [ite_eq_right ha0]
            intro h
            cases h

#print axioms fu2_trans_ne_Z

theorem fu2_found_upper_closed {lam : Nat} :
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
        rw [transAux.eq_2]
        change false = true → _
        intro h
        cases h
  | succ m ih =>
    intro v hcoord
    cases v with
    | snoc n xs a =>
      cases a with
      | Z =>
        have hxsCoord :
            ∀ b ∈ new.Vec.toList xs,
              T.isNF1 (trans b) ∧
                ∀ x : T, x ∈ T.G1 0 (trans b) → x < trans b := by
          intro b hb
          apply hcoord b
          change b ∈ new.Vec.toList xs ++ [new.T.Z]
          exact List.mem_append_left [new.T.Z] hb
        rw [transAux.eq_3]
        cases haux : transAux xs with
        | mk found rest =>
          cases rest with
          | mk sum a0 =>
            change found = true → _
            intro hfound
            have hrec := ih xs hxsCoord
            rw [haux] at hrec
            exact hrec hfound
      | P ls add =>
        have hxsCoord :
            ∀ b ∈ new.Vec.toList xs,
              T.isNF1 (trans b) ∧
                ∀ x : T, x ∈ T.G1 0 (trans b) → x < trans b := by
          intro b hb
          apply hcoord b
          change b ∈ new.Vec.toList xs ++ [new.T.P ls add]
          exact List.mem_append_left [new.T.P ls add] hb
        have haCoord :
            T.isNF1 (trans (new.T.P ls add)) ∧
              ∀ x : T, x ∈ T.G1 0 (trans (new.T.P ls add)) →
                x < trans (new.T.P ls add) := by
          apply hcoord (new.T.P ls add)
          change new.T.P ls add ∈ new.Vec.toList xs ++ [new.T.P ls add]
          exact List.mem_append_right _
            (List.mem_singleton_self (new.T.P ls add))
        have hsum := aux_sum_inv m xs hxsCoord
        rw [transAux.eq_3]
        cases haux : transAux xs with
        | mk found rest =>
          cases rest with
          | mk sum a0 =>
            rw [haux] at hsum
            change true = true → _
            intro htrue
            have htransNe : trans (new.T.P ls add) ≠ T.Z :=
              fu2_trans_ne_Z (new.T.P ls add) (by intro h; cases h)
            have hec := bridge_early_collapse_closed
              (trans (new.T.P ls add)) haCoord.1 haCoord.2
            have hecNe := bridge_early_collapse_ne_Z
              (trans (new.T.P ls add)) htransNe
            cases m with
            | zero =>
              have hsumZ : sum = T.Z := by
                have hbound := hsum.2.2.2 (T.P 0 T.Z T.Z)
                  (T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                    (fun x hx => by rw [T.G1.eq_1] at hx; cases hx)
                    (T.Z_le _))
                  (T.index_Prop1.p 0 T.Z T.Z (Nat.le_refl 0)
                    T.index_Prop1.z)
                  (by intro h; cases h)
                rw [T.card_times.eq_2] at hbound
                exact bridge_lt_P0ZZ_eq_Z sum hbound
              change
                T.isNF1
                    (T.card_times 1
                      (T.one_del
                        (T.add
                          (T.card_times 0
                            (T.early_collapse (trans (new.T.P ls add)))) sum))) ∧
                  T.index_Prop1 1
                    (T.card_times 1
                      (T.one_del
                        (T.add
                          (T.card_times 0
                            (T.early_collapse (trans (new.T.P ls add)))) sum))) ∧
                  (∀ x : T,
                    x ∈ T.G1 1
                      (T.card_times 1
                        (T.one_del
                          (T.add
                            (T.card_times 0
                              (T.early_collapse (trans (new.T.P ls add)))) sum))) →
                    x < T.card_times 1
                      (T.one_del
                        (T.add
                          (T.card_times 0
                            (T.early_collapse (trans (new.T.P ls add)))) sum)))
              rw [aux_card_times_zero, hsumZ, T.add_Z]
              have hdel := ca_one_del_index0
                (T.early_collapse (trans (new.T.P ls add))) hec.1 hec.2.1
              exact bridge_card_times_closed 1
                (T.one_del (T.early_collapse (trans (new.T.P ls add))))
                hdel.1 hdel.2
            | succ q =>
              obtain ⟨mid, tail, hshape⟩ :=
                ca_card_times_pos_shape q
                  (T.early_collapse (trans (new.T.P ls add)))
                  hec.2.1 hecNe
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
              have hwhole :=
                ac_card1_sum_inv (q + 2)
                  (new.Vec.snoc (q + 2) xs (new.T.P ls add)) hcoord
              rw [transAux.eq_3, haux] at hwhole
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


#print axioms fu2_found_upper_closed

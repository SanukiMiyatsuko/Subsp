import SumAppend
import FoundUpper

open T

theorem fa_found_append_lower {lam : Nat} :
    ∀ (k : Nat) (v : new.Vec (new.T lam) (k + 1)) (L : T),
      (∀ a ∈ new.Vec.toList v,
        T.isNF1 (trans a) ∧
          ∀ x : T, x ∈ T.G1 0 (trans a) → x < trans a) →
      T.isNF1 L → T.index_Prop1 0 L →
      let r := transAux v
      r.1 = true →
        T.isNF1 (T.add (T.card_times 1 (T.one_del r.2.1)) L) ∧
          T.index_Prop1 1 (T.add (T.card_times 1 (T.one_del r.2.1)) L) ∧
          (∀ x : T,
            x ∈ T.G1 1 (T.add (T.card_times 1 (T.one_del r.2.1)) L) →
              x < T.add (T.card_times 1 (T.one_del r.2.1)) L) := by
  intro k
  induction k with
  | zero =>
    intro v L hcoord hL hLidx
    cases v with
    | snoc n xs a =>
      cases xs with
      | nil =>
        change false = true → _
        intro h
        cases h
  | succ m ih =>
    intro v L hcoord hL hLidx
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
              T.isNF1 (T.add (T.card_times 1 (T.one_del sum)) L) ∧
                T.index_Prop1 1 (T.add (T.card_times 1 (T.one_del sum)) L) ∧
                (∀ x : T,
                  x ∈ T.G1 1 (T.add (T.card_times 1 (T.one_del sum)) L) →
                    x < T.add (T.card_times 1 (T.one_del sum)) L)
            intro hfound
            have hrec := ih xs L hxsCoord hL hLidx
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
                        (T.add
                          (T.card_times 1
                            (T.one_del
                              (T.add (T.card_times 0
                                (T.early_collapse (trans (new.T.P ls add)))) T.Z))) L) ∧
                      T.index_Prop1 1
                        (T.add
                          (T.card_times 1
                            (T.one_del
                              (T.add (T.card_times 0
                                (T.early_collapse (trans (new.T.P ls add)))) T.Z))) L) ∧
                      (∀ x : T,
                        x ∈ T.G1 1
                          (T.add
                            (T.card_times 1
                              (T.one_del
                                (T.add (T.card_times 0
                                  (T.early_collapse (trans (new.T.P ls add)))) T.Z))) L) →
                        x < T.add
                          (T.card_times 1
                            (T.one_del
                              (T.add (T.card_times 0
                                (T.early_collapse (trans (new.T.P ls add)))) T.Z))) L)
                  rw [tc_card_times_zero, T.add_Z]
                  let c := T.one_del (T.early_collapse (trans (new.T.P ls add)))
                  have hc := ca_one_del_index0
                    (T.early_collapse (trans (new.T.P ls add))) hec.1 hec.2.1
                  have hLidx1 := Rank1Termination.index_mono (Nat.zero_le 1) L hLidx
                  have hLG : ∀ x : T, x ∈ T.G1 1 L → x < L := by
                    intro x hx
                    have hempty := index_Prop1_G1_empty 0 L hLidx 1
                      (Nat.zero_lt_succ 0)
                    rw [hempty] at hx
                    cases hx
                  have hLbound : L <
                      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z := by
                    rw [T.ofNat, T.mul]
                    exact index_Prop1_lt_succ 0 L hLidx
                  have hcb := cb_card_append_lower 0 c L
                    hc.1 hc.2 hL hLidx1 hLG hLbound
                  exact ⟨hcb.1, hcb.2.1, hcb.2.2.1⟩
            | succ q =>
              have hsumAll := sa_sum_append_lower (q + 2)
                (new.Vec.snoc (q + 2) xs (new.T.P ls add)) L
                hcoord hL hLidx
              rw [transAux.eq_3, haux] at hsumAll
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
                    (T.add
                      (T.card_times 1
                        (T.one_del
                          (T.add
                            (T.card_times (q + 1)
                              (T.early_collapse (trans (new.T.P ls add)))) sum))) L) ∧
                  T.index_Prop1 1
                    (T.add
                      (T.card_times 1
                        (T.one_del
                          (T.add
                            (T.card_times (q + 1)
                              (T.early_collapse (trans (new.T.P ls add)))) sum))) L) ∧
                  (∀ x : T,
                    x ∈ T.G1 1
                      (T.add
                        (T.card_times 1
                          (T.one_del
                            (T.add
                              (T.card_times (q + 1)
                                (T.early_collapse (trans (new.T.P ls add)))) sum))) L) →
                    x < T.add
                      (T.card_times 1
                        (T.one_del
                          (T.add
                            (T.card_times (q + 1)
                              (T.early_collapse (trans (new.T.P ls add)))) sum))) L)
              rw [hone]
              exact ⟨hsumAll.1, hsumAll.2.1, hsumAll.2.2.1⟩

#print axioms fa_found_append_lower

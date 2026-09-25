import CardBridge
import CardAlgebra
import AuxCore

open T

theorem sa_sum_append_lower {lam : Nat} :
    ∀ (k : Nat) (v : new.Vec (new.T lam) (k + 1)) (L : T),
      (∀ a ∈ new.Vec.toList v,
        T.isNF1 (trans a) ∧
          ∀ x : T, x ∈ T.G1 0 (trans a) → x < trans a) →
      T.isNF1 L → T.index_Prop1 0 L →
      let sum := (transAux v).2.1
      let R := T.add (T.card_times 1 sum) L
      T.isNF1 R ∧ T.index_Prop1 1 R ∧
        (∀ x : T, x ∈ T.G1 1 R → x < R) ∧
        R < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z := by
  intro k
  induction k with
  | zero =>
    intro v L hcoord hL hLidx
    cases v with
    | snoc n xs a =>
      cases xs with
      | nil =>
        rw [transAux.eq_2]
        change
          T.isNF1 (T.add (T.card_times 1 T.Z) L) ∧
            T.index_Prop1 1 (T.add (T.card_times 1 T.Z) L) ∧
            (∀ x : T, x ∈ T.G1 1 (T.add (T.card_times 1 T.Z) L) →
              x < T.add (T.card_times 1 T.Z) L) ∧
            T.add (T.card_times 1 T.Z) L <
              T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z
        rw [T.card_times.eq_1, T.add.eq_1, T.ofNat, T.mul]
        have hidx1 := Rank1Termination.index_mono (Nat.zero_le 1) L hLidx
        have hempty := index_Prop1_G1_empty 0 L hLidx 1 (Nat.zero_lt_succ 0)
        refine ⟨hL, hidx1, ?_, index_Prop1_lt_succ 0 L hLidx⟩
        intro x hx
        rw [hempty] at hx
        cases hx
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
      have hrest := ih xs L hxsCoord hL hLidx
      cases haux : transAux xs with
      | mk found rest =>
        cases rest with
        | mk sum a0 =>
          rw [haux] at hrest
          have hec := bridge_early_collapse_closed (trans a) haCoord.1 haCoord.2
          let R0 := T.add (T.card_times 1 sum) L
          have hcb := cb_card_append_lower m
            (T.early_collapse (trans a)) R0
            hec.1 hec.2.1 hrest.1 hrest.2.1 hrest.2.2.1 hrest.2.2.2
          rw [transAux.eq_3, haux]
          change
            T.isNF1
                (T.add
                  (T.card_times 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
              T.index_Prop1 1
                (T.add
                  (T.card_times 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
              (∀ x : T,
                x ∈ T.G1 1
                  (T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) →
                x < T.add
                  (T.card_times 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
              T.add
                  (T.card_times 1
                    (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L <
                T.P 1
                  (T.mul (T.P 1 T.Z T.Z) (T.ofNat (m + 1))) T.Z
          rw [ca_card_times_add, ca_card_times_one_comp hec.2.1 m]
          rw [Rank1Termination.add_assoc]
          change
            T.isNF1
                (T.add (T.card_times (m + 1) (T.early_collapse (trans a))) R0) ∧
              T.index_Prop1 1
                (T.add (T.card_times (m + 1) (T.early_collapse (trans a))) R0) ∧
              (∀ x : T,
                x ∈ T.G1 1
                  (T.add (T.card_times (m + 1) (T.early_collapse (trans a))) R0) →
                x < T.add (T.card_times (m + 1) (T.early_collapse (trans a))) R0) ∧
              T.add (T.card_times (m + 1) (T.early_collapse (trans a))) R0 <
                T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (m + 1))) T.Z
          exact hcb

#print axioms sa_sum_append_lower

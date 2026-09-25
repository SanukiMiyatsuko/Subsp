import CardAlg
import AuxCore

open T

theorem sc_transAux_card1_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 (T.card_times 1 sum) ∧
          T.index_Prop1 1 (T.card_times 1 sum) ∧
          (∀ y : T, y ∈ T.G1 1 (T.card_times 1 sum) →
            y < T.card_times 1 sum) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              T.card_times 1 sum < T.card_times (k + 1) c) := by
  intro k
  induction k with
  | zero =>
      intro v hcomp found sum a0 haux
      cases v with
      | @snoc n xs a =>
        cases xs with
        | nil =>
          rw [transAux.eq_2] at haux
          cases haux
          change
            T.isNF1 T.Z ∧ T.index_Prop1 1 T.Z ∧
              (∀ y : T, y ∈ T.G1 1 T.Z → y < T.Z) ∧
              (∀ c : T,
                T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                  T.Z < T.card_times 1 c)
          refine ⟨T.isNF1.z, T.index_Prop1.z, ?_, ?_⟩
          · intro y hy
            rw [T.G1.eq_1] at hy
            cases hy
          · intro c hcNF hcIdx hcNe
            exact tc_Z_lt_of_ne (T.card_times 1 c)
              (bridge_card_times_ne_Z 1 c hcNe)
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | @snoc n xs a =>
        have hrest :
            ∀ x : new.T lam, x ∈ new.Vec.toList xs →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
          intro x hx
          exact hcomp x (List.mem_append_left [a] hx)
        have ha :
            T.isNF1 (trans a) ∧
              (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
          apply hcomp a
          exact List.mem_append_right (new.Vec.toList xs)
            (List.mem_singleton.mpr rfl)
        cases hrestaux : transAux xs with
        | mk foundRest restpair =>
          cases restpair with
          | mk sumRest a0Rest =>
            have ihr := ih xs hrest foundRest sumRest a0Rest hrestaux
            rw [transAux.eq_3, hrestaux] at haux
            cases a with
            | Z =>
              rw [_root_.trans.eq_1] at haux
              change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
              cases haux
              refine ⟨ihr.1, ihr.2.1, ihr.2.2.1, ?_⟩
              intro c hcNF hcIdx hcNe
              have hold := ihr.2.2.2 c hcNF hcIdx hcNe
              have hnext := bridge_card_times_level_lt (m + 1) (m + 2) c c
                (Nat.lt_succ_self (m + 1)) hcNF hcIdx hcNe hcNF hcIdx hcNe
              exact lt_trans_thm _ _ _ hold hnext
            | P als aadd =>
              have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                intro h
                cases h
              have hatNe := tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
              have hec := bridge_early_collapse_closed
                (trans (new.T.P als aadd)) ha.1 ha.2
              have hecNe := bridge_early_collapse_ne_Z
                (trans (new.T.P als aadd)) hatNe
              change
                (true,
                  T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                  a0Rest) = (found, sum, a0) at haux
              cases haux
              rw [← add_eq_hAdd]
              rw [ca_card_times_add, ca_card_times_one_comp]
              have happ := bridge_card_times_succ_append m
                (T.early_collapse (trans (new.T.P als aadd)))
                (T.card_times 1 sumRest)
                hec.1 hec.2.1 ihr.1 ihr.2.1 ihr.2.2.1 ihr.2.2.2
              refine ⟨happ.1, happ.2.1, happ.2.2, ?_⟩
              intro c hcNF hcIdx hcNe
              exact bridge_card_times_add_level_lt (m + 1) (m + 2)
                (T.early_collapse (trans (new.T.P als aadd))) c
                (T.card_times 1 sumRest)
                (Nat.lt_succ_self (m + 1)) hec.1 hec.2.1 hecNe
                hcNF hcIdx hcNe

#print axioms sc_transAux_card1_inv

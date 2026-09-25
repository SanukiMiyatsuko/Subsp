import CardAux
import ShiftHelpers

open T

theorem sf_transAux_shift_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 (T.card_times 1 (T.one_del sum)) ∧
          T.index_Prop1 1 (T.card_times 1 (T.one_del sum)) ∧
          (∀ y : T,
            y ∈ T.G1 1 (T.card_times 1 (T.one_del sum)) →
              y < T.card_times 1 (T.one_del sum)) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              T.card_times 1 (T.one_del sum) < T.card_times (k + 1) c) := by
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
            have iinv := tc_transAux_inv xs hrest foundRest sumRest a0Rest hrestaux
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
              have hcurAux :
                  transAux (new.Vec.snoc (m + 1) xs (new.T.P als aadd)) =
                    (true,
                      T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                      a0Rest) := by
                rw [transAux.eq_3, hrestaux]
              change
                (true,
                  T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                  a0Rest) = (found, sum, a0) at haux
              cases haux
              cases m with
              | zero =>
                have hsumZ : sumRest = T.Z := by
                  have hlt := iinv.2.2.2.2.2.1 (T.P 0 T.Z T.Z)
                    (T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                      (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
                      (T.Z_le (T.P 0 T.Z T.Z)))
                    (T.index_Prop1.p 0 T.Z T.Z (Nat.le_refl 0) T.index_Prop1.z)
                    (by intro h; cases h)
                  rw [tc_card_times_zero] at hlt
                  exact bridge_lt_P0ZZ_eq_Z sumRest hlt
                rw [hsumZ]
                rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                have hclosed := sa_shift_base_closed
                  (T.early_collapse (trans (new.T.P als aadd))) hec.1 hec.2.1
                refine ⟨hclosed.1, hclosed.2.1, hclosed.2.2, ?_⟩
                intro c hcNF hcIdx hcNe
                exact sa_shift_base_bound
                  (T.early_collapse (trans (new.T.P als aadd))) c
                  hec.1 hec.2.1 hcNF hcIdx hcNe
              | succ j =>
                let ec := T.early_collapse (trans (new.T.P als aadd))
                have hone :
                    T.one_del (T.add (T.card_times (j + 1) ec) sumRest) =
                      T.add (T.card_times (j + 1) ec) sumRest :=
                  sa_one_del_card_succ_add j ec sumRest hec.2.1 hecNe
                have hcur :
                    transAux (new.Vec.snoc (j + 1 + 1) xs (new.T.P als aadd)) =
                      (true, T.card_times (j + 1) ec + sumRest, a0) := by
                  exact hcurAux
                have icur := sc_transAux_card1_inv
                  (new.Vec.snoc (j + 1 + 1) xs (new.T.P als aadd))
                  hcomp true (T.card_times (j + 1) ec + sumRest) a0 hcur
                change
                  T.isNF1
                      (T.card_times 1
                        (T.one_del (T.card_times (j + 1) ec + sumRest))) ∧
                    T.index_Prop1 1
                      (T.card_times 1
                        (T.one_del (T.card_times (j + 1) ec + sumRest))) ∧
                    (∀ y : T,
                      y ∈ T.G1 1
                          (T.card_times 1
                            (T.one_del (T.card_times (j + 1) ec + sumRest))) →
                        y < T.card_times 1
                          (T.one_del (T.card_times (j + 1) ec + sumRest))) ∧
                    (∀ c : T,
                      T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                        T.card_times 1
                            (T.one_del (T.card_times (j + 1) ec + sumRest)) <
                          T.card_times (j + 1 + 1 + 1) c)
                rw [← add_eq_hAdd (T.card_times (j + 1) ec) sumRest]
                rw [hone]
                exact icur

#print axioms sf_transAux_shift_inv

import CardAlg
import AuxCore

open T

theorem sa_one_del_index0 (c : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) :
    T.isNF1 (T.one_del c) ∧ T.index_Prop1 0 (T.one_del c) := by
  cases c with
  | Z =>
    exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      obtain ⟨haNF, hbNF, haG, hhead⟩ := T.isNF1_P_inv 0 a b hcNF
      cases a with
      | Z =>
        change T.isNF1 b ∧ T.index_Prop1 0 b
        exact ⟨hbNF, hbIdx⟩
      | P q d e =>
        change T.isNF1 (T.P 0 (T.P q d e) b) ∧
          T.index_Prop1 0 (T.P 0 (T.P q d e) b)
        exact ⟨hcNF, T.index_Prop1.p 0 (T.P q d e) b (Nat.le_refl 0) hbIdx⟩

#print axioms sa_one_del_index0

theorem sa_shift_base_closed (c : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) :
    T.isNF1 (T.card_times 1 (T.one_del c)) ∧
      T.index_Prop1 1 (T.card_times 1 (T.one_del c)) ∧
      (∀ x : T, x ∈ T.G1 1 (T.card_times 1 (T.one_del c)) →
        x < T.card_times 1 (T.one_del c)) := by
  have hd := sa_one_del_index0 c hcNF hcIdx
  exact bridge_card_times_closed 1 (T.one_del c) hd.1 hd.2

#print axioms sa_shift_base_closed

theorem sa_shift_base_bound (c z : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c)
    (hzNF : T.isNF1 z) (hzIdx : T.index_Prop1 0 z) (hzNe : z ≠ T.Z) :
    T.card_times 1 (T.one_del c) < T.card_times 2 z := by
  have hd := sa_one_del_index0 c hcNF hcIdx
  by_cases hdZ : T.one_del c = T.Z
  · rw [hdZ, T.card_times.eq_1]
    exact tc_Z_lt_of_ne (T.card_times 2 z)
      (bridge_card_times_ne_Z 2 z hzNe)
  · exact bridge_card_times_level_lt 1 2 (T.one_del c) z
      (Nat.lt_succ_self 1) hd.1 hd.2 hdZ hzNF hzIdx hzNe

#print axioms sa_shift_base_bound

theorem sa_one_del_card_succ_add (k : Nat) (c y : T)
    (hcIdx : T.index_Prop1 0 c) (hcNe : c ≠ T.Z) :
    T.one_del (T.add (T.card_times (k + 1) c) y) =
      T.add (T.card_times (k + 1) c) y := by
  cases c with
  | Z => exact False.elim (hcNe rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      rw [T.card_times.eq_3, ite_eq_left rfl]
      rw [← add_eq_hAdd]
      rw [Rank1Termination.add_assoc]
      rw [T.P_add_eq, T.add]
      rfl

#print axioms sa_one_del_card_succ_add

theorem sa_transAux_shift_inv {lam : Nat} :
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
            T.isNF1 T.Z ∧
              T.index_Prop1 1 T.Z ∧
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
                rw [ca_card_times_add, ca_card_times_one_comp]
                have happ := bridge_card_times_succ_append (j + 1) ec
                  (T.card_times 1 (T.one_del sumRest))
                  hec.1 hec.2.1 ihr.1 ihr.2.1 ihr.2.2.1 ihr.2.2.2
                refine ⟨happ.1, happ.2.1, happ.2.2, ?_⟩
                intro c hcNF hcIdx hcNe
                exact bridge_card_times_add_level_lt (j + 2) (j + 3)
                  ec c (T.card_times 1 (T.one_del sumRest))
                  (Nat.lt_succ_self (j + 2)) hec.1 hec.2.1 hecNe
                  hcNF hcIdx hcNe

#print axioms sa_transAux_shift_inv

import Subsp.new.stop_progress_order

open T


-- From AuxBridge.lean

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


-- From TransCore.lean

theorem tc_trans_P_add {lam : Nat} (ls : new.Vec (new.T lam) lam) (a : new.T lam) :
    trans (new.T.P ls a) = T.add (trans (new.T.P ls new.T.Z)) (trans a) := by
  rw [_root_.trans.eq_2 ls a, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1]
  cases haux : transAux ls with
  | mk found rest =>
    cases rest with
    | mk sum a0 =>
      change
        (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
         else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a)) =
        T.add
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
           else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z)
          (trans a)
      by_cases hf : found = true
      · rw [ite_eq_left hf, ite_eq_left hf, T.P_add_eq, T.add]
      · rw [ite_eq_right hf, ite_eq_right hf]
        by_cases ha0 : a0 = T.Z
        · rw [ite_eq_left ha0, ite_eq_left ha0, T.P_add_eq, T.add]
        · rw [ite_eq_right ha0, ite_eq_right ha0, T.P_add_eq, T.add]

theorem tc_trans_head {lam : Nat} (s : new.T lam) :
    trans (new.T.head s) = T.head (trans s) := by
  cases s with
  | Z => rfl
  | P ls a =>
    rw [new.T.head, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1,
      _root_.trans.eq_2 ls a]
    cases haux : transAux ls with
    | mk found rest =>
      cases rest with
      | mk sum a0 =>
        change
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
           else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z) =
          T.head
            (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
             else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a))
        by_cases hf : found = true
        · rw [ite_eq_left hf, ite_eq_left hf]
          rfl
        · rw [ite_eq_right hf, ite_eq_right hf]
          by_cases ha0 : a0 = T.Z
          · rw [ite_eq_left ha0, ite_eq_left ha0]
            rfl
          · rw [ite_eq_right ha0, ite_eq_right ha0]
            rfl

#print axioms tc_trans_P_add
#print axioms tc_trans_head


-- From AuxCore.lean

theorem tc_trans_ne_Z_of_ne_Z {lam : Nat} (s : new.T lam)
    (hs : s ≠ new.T.Z) : trans s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P ls add =>
    rw [_root_.trans.eq_2]
    cases haux : transAux ls with
    | mk found rest =>
      cases rest with
      | mk sum a0 =>
        change
          (if found = true then
            T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans add)
          else if a0 = T.Z then T.P 0 T.Z (trans add)
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

#print axioms tc_trans_ne_Z_of_ne_Z

theorem tc_Z_lt_of_ne (x : T) (hx : x ≠ T.Z) : T.Z < x := by
  cases T.Z_le x with
  | inl h => exact h
  | inr h => exact False.elim (hx h.symm)

#print axioms tc_Z_lt_of_ne

theorem tc_add_ne_Z_left (a b : T) (ha : a ≠ T.Z) : a + b ≠ T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d =>
    cases b with
    | Z =>
      intro h
      cases h
    | P q e f =>
      intro h
      cases h


theorem tc_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c with
  | Z => rfl
  | P p a b => rfl

#print axioms tc_card_times_zero

theorem tc_transAux_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 a0 ∧
          (∀ y : T, y ∈ T.G1 0 a0 → y < a0) ∧
          T.isNF1 sum ∧
          T.index_Prop1 1 sum ∧
          (∀ y : T, y ∈ T.G1 1 sum → y < sum) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              sum < T.card_times k c) ∧
          (found = true → sum ≠ T.Z) ∧
          (found = false → sum = T.Z) := by
  intro k
  induction k with
  | zero =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc n xs a =>
        cases xs with
        | nil =>
          rw [transAux.eq_2] at haux
          cases haux
          have ha := hcomp a (List.mem_singleton.mpr rfl)
          refine ⟨ha.1, ha.2, T.isNF1.z, T.index_Prop1.z, ?_, ?_, ?_, ?_⟩
          · intro y hy
            rw [T.G1.eq_1] at hy
            cases hy
          · intro c hcNF hcIdx hcne
            rw [tc_card_times_zero]
            exact tc_Z_lt_of_ne c hcne
          · intro h
            cases h
          · intro _
            rfl
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc n xs a =>
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
              change
                (foundRest, T.card_times m (T.early_collapse (trans new.T.Z)) + sumRest, a0Rest) =
                  (found, sum, a0) at haux
              rw [_root_.trans.eq_1] at haux
              change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
              cases haux
              refine ⟨ihr.1, ihr.2.1, ihr.2.2.1, ihr.2.2.2.1,
                ihr.2.2.2.2.1, ?_, ihr.2.2.2.2.2.2.1, ihr.2.2.2.2.2.2.2⟩
              intro c hcNF hcIdx hcne
              have hold := ihr.2.2.2.2.2.1 c hcNF hcIdx hcne
              have hnext := bridge_card_times_level_lt m (m + 1) c c
                (Nat.lt_succ_self m) hcNF hcIdx hcne hcNF hcIdx hcne
              exact lt_trans_thm _ _ _ hold hnext
            | P als aadd =>
              have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                intro h
                cases h
              have hatne : trans (new.T.P als aadd) ≠ T.Z :=
                tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
              have hec := bridge_early_collapse_closed
                (trans (new.T.P als aadd)) ha.1 ha.2
              have hecne : T.early_collapse (trans (new.T.P als aadd)) ≠ T.Z :=
                bridge_early_collapse_ne_Z (trans (new.T.P als aadd)) hatne
              change
                (true,
                  T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                  a0Rest) = (found, sum, a0) at haux
              cases haux
              have hboundnext :
                  ∀ c : T,
                    T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                    T.add
                        (T.card_times m
                          (T.early_collapse (trans (new.T.P als aadd))))
                        sumRest <
                      T.card_times (m + 1) c := by
                intro c hcNF hcIdx hcne
                exact bridge_card_times_add_level_lt m (m + 1)
                  (T.early_collapse (trans (new.T.P als aadd))) c sumRest
                  (Nat.lt_succ_self m) hec.1 hec.2.1 hecne
                  hcNF hcIdx hcne
              cases m with
              | zero =>
                have hsumZ : sumRest = T.Z := by
                  have hlt := ihr.2.2.2.2.2.1 (T.P 0 T.Z T.Z)
                    (T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                      (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
                      (T.Z_le (T.P 0 T.Z T.Z)))
                    (T.index_Prop1.p 0 T.Z T.Z (Nat.le_refl 0) T.index_Prop1.z)
                    (by intro h; cases h)
                  rw [T.card_times.eq_2] at hlt
                  exact bridge_lt_P0ZZ_eq_Z sumRest hlt
                rw [hsumZ]
                have haddz :
                    T.card_times 0
                        (T.early_collapse (trans (new.T.P als aadd))) + T.Z =
                      T.early_collapse (trans (new.T.P als aadd)) := by
                  rw [tc_card_times_zero]
                  let A := T.early_collapse (trans (new.T.P als aadd))
                  change A + T.Z = A
                  exact (add_eq_hAdd A T.Z).symm.trans (T.add_Z A)
                rw [haddz]
                have hidx1 :
                    T.index_Prop1 1
                      (T.early_collapse (trans (new.T.P als aadd))) :=
                  Rank1Termination.index_mono (Nat.zero_le 1)
                    (T.early_collapse (trans (new.T.P als aadd))) hec.2.1
                refine ⟨ihr.1, ihr.2.1, hec.1, hidx1, hec.2.2,
                  ?_, ?_, ?_⟩
                · intro c hcNF hcIdx hcne
                  have hb := hboundnext c hcNF hcIdx hcne
                  rw [hsumZ] at hb
                  have hleft :
                      T.add
                          (T.card_times 0
                            (T.early_collapse (trans (new.T.P als aadd)))) T.Z =
                        T.early_collapse (trans (new.T.P als aadd)) := by
                    rw [T.add_Z, tc_card_times_zero]
                  rw [hleft] at hb
                  exact hb
                · intro _
                  exact hecne
                · intro h
                  cases h
              | succ j =>
                have happ := bridge_card_times_succ_append j
                  (T.early_collapse (trans (new.T.P als aadd))) sumRest
                  hec.1 hec.2.1 ihr.2.2.1 ihr.2.2.2.1
                  ihr.2.2.2.2.1
                  ihr.2.2.2.2.2.1
                refine ⟨ihr.1, ihr.2.1, happ.1, happ.2.1, happ.2.2,
                  ?_, ?_, ?_⟩
                · intro c hcNF hcIdx hcne
                  exact hboundnext c hcNF hcIdx hcne
                · intro _
                  have hheadne := bridge_card_times_ne_Z (j + 1)
                    (T.early_collapse (trans (new.T.P als aadd))) hecne
                  intro hz
                  exact (tc_add_ne_Z_left
                    (T.card_times (j + 1)
                      (T.early_collapse (trans (new.T.P als aadd))))
                    sumRest hheadne) hz
                · intro h
                  cases h

#print axioms tc_transAux_inv


-- From CardAlg.lean


import Subsp.new.stop_order_aux

open T

theorem pn_index0_lt_threshold0 (a : T)
    (ha : T.index_Prop1 0 a) :
    a < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z := by
  change a < T.P 1 T.Z T.Z
  cases a with
  | Z => exact T.Lt.Z_lt_P 1 T.Z T.Z
  | P p c d =>
      cases ha with
      | p _ _ _ hp htail =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          exact T.Lt.p_head 0 1 c T.Z d T.Z (Nat.zero_lt_succ 0)

#print axioms pn_index0_lt_threshold0

theorem pn_aux_card1_sum_append {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ L : T,
        T.isNF1 L → T.index_Prop1 0 L →
        (∀ y : T, y ∈ T.G1 1 L → y < L) →
        L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z →
        let sum := (transAux v).2.1
        let R := T.add (T.card_times 1 sum) L
        T.isNF1 R ∧ T.index_Prop1 1 R ∧
          (∀ y : T, y ∈ T.G1 1 R → y < R) ∧
          R < T.P 1
            (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z := by
  intro k
  induction k with
  | zero =>
      intro v hcoord L hL hLi hLg hLb
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2]
              change T.isNF1 (T.add (T.card_times 1 T.Z) L) ∧
                T.index_Prop1 1 (T.add (T.card_times 1 T.Z) L) ∧
                (∀ y : T, y ∈ T.G1 1 (T.add (T.card_times 1 T.Z) L) →
                  y < T.add (T.card_times 1 T.Z) L) ∧
                T.add (T.card_times 1 T.Z) L <
                  T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z
              rw [T.card_times.eq_1, T.add.eq_1]
              exact ⟨hL,
                Rank1Termination.index_mono (Nat.zero_le 1) L hLi,
                hLg, hLb⟩
  | succ m ih =>
      intro v hcoord L hL hLi hLg hLb
      cases v with
      | @snoc n xs a =>
          have hxs :
              ∀ x : new.T lam, x ∈ new.Vec.toList xs →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hcoord x (List.mem_append_left [a] hx)
          have ha :
              T.isNF1 (trans a) ∧
                (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
            apply hcoord a
            exact List.mem_append_right (new.Vec.toList xs)
              (List.mem_singleton_self a)
          have hrec := ih xs hxs L hL hLi hLg hLb
          cases haux : transAux xs with
          | mk found rest =>
            cases rest with
            | mk sum a0 =>
              rw [haux] at hrec
              rw [transAux.eq_3, haux]
              change T.isNF1
                  (T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
                T.index_Prop1 1
                  (T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
                (∀ y : T,
                  y ∈ T.G1 1
                    (T.add
                      (T.card_times 1
                        (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) →
                  y < T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
                T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L <
                  T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (m + 1))) T.Z
              have hec := bridge_early_collapse_closed (trans a) ha.1 ha.2
              have hblockNF : T.isNF1 (T.early_collapse (trans a)) := hec.1
              have hblockIdx : T.index_Prop1 0 (T.early_collapse (trans a)) := hec.2.1
              have hR := cb_card_append_lower m
                (T.early_collapse (trans a))
                (T.add (T.card_times 1 sum) L)
                hblockNF hblockIdx hrec.1 hrec.2.1 hrec.2.2.1 hrec.2.2.2
              rw [ca_card_times_add]
              rw [ca_card_times_one_comp]
              rw [Rank1Termination.add_assoc]
              exact hR

#print axioms pn_aux_card1_sum_append


theorem pn_card_times_pos_shape (q : Nat) (c : T)
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
          refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat q))
              (T.early_collapse a), T.card_times (q + 1) b, ?_⟩
          rw [← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
          rfl

#print axioms pn_card_times_pos_shape

theorem pn_aux_sum_P0_index0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        ∀ c d : T, sum = T.P 0 c d → T.index_Prop1 0 sum := by
  intro k
  induction k with
  | zero =>
      intro v hcoord found sum a0 haux c d hshape
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              cases haux
              cases hshape
  | succ m ih =>
      intro v hcoord found sum a0 haux c d hshape
      cases v with
      | @snoc n xs a =>
          have hxs :
              ∀ x : new.T lam, x ∈ new.Vec.toList xs →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hcoord x (List.mem_append_left [a] hx)
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
              rw [transAux.eq_3, hrest] at haux
              cases a with
              | Z =>
                  change
                    (foundRest,
                      T.add (T.card_times m (T.early_collapse T.Z)) sumRest,
                      a0Rest) = (found, sum, a0) at haux
                  have hecz : T.early_collapse T.Z = T.Z := by
                    rw [T.early_collapse, T.part, ite_eq_left rfl]
                  rw [hecz, T.card_times.eq_1, T.add.eq_1] at haux
                  have hsum : sumRest = sum :=
                    congrArg (fun q : Bool × T × T => q.2.1) haux
                  have hshapeRest : sumRest = T.P 0 c d := hsum.trans hshape
                  rw [← hsum]
                  exact ih xs hxs foundRest sumRest a0Rest hrest c d hshapeRest
              | P als aadd =>
                  have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                    intro h
                    cases h
                  have hatne : trans (new.T.P als aadd) ≠ T.Z :=
                    tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
                  have hec := bridge_early_collapse_closed
                    (trans (new.T.P als aadd)) ha.1 ha.2
                  have hecne :
                      T.early_collapse (trans (new.T.P als aadd)) ≠ T.Z :=
                    bridge_early_collapse_ne_Z (trans (new.T.P als aadd)) hatne
                  change
                    (true,
                      T.add
                        (T.card_times m
                          (T.early_collapse (trans (new.T.P als aadd)))) sumRest,
                      a0Rest) = (found, sum, a0) at haux
                  cases haux
                  cases m with
                  | zero =>
                      cases xs with
                      | @snoc n ys b =>
                          cases ys with
                          | nil =>
                              rw [transAux.eq_2] at hrest
                              cases hrest
                              rw [ca_card_times_zero, T.add_Z]
                              exact hec.2.1
                  | succ j =>
                      obtain ⟨mid, tail, hcard⟩ :=
                        pn_card_times_pos_shape j
                          (T.early_collapse (trans (new.T.P als aadd)))
                          hec.2.1 hecne
                      rw [hcard, T.P_add_eq] at hshape
                      cases hshape

#print axioms pn_aux_sum_P0_index0

theorem pn_aux_found_middle_closed {lam : Nat}
    {k : Nat} (v : new.Vec (new.T lam) (k + 1))
    (hcoord : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (found : Bool) (sum a0 : T)
    (haux : transAux v = (found, sum, a0))
    (hf : found = true) :
    let M := T.add (T.card_times 1 (T.one_del sum))
      (T.early_collapse a0)
    T.isNF1 M ∧ T.index_Prop1 1 M ∧
      (∀ y : T, y ∈ T.G1 1 M → y < M) := by
  have hi := tc_transAux_inv v hcoord found sum a0 haux
  have haec := bridge_early_collapse_closed a0 hi.1 hi.2.1
  have hbaseBound := pn_index0_lt_threshold0 (T.early_collapse a0) haec.2.1
  cases sum with
  | Z =>
      exact False.elim (hi.2.2.2.2.2.2.1 hf rfl)
  | P p c d =>
      have hsumIdx := hi.2.2.2.1
      cases hsumIdx with
      | p _ _ _ hp htail =>
          cases p with
          | zero =>
              have hsumGood1 := hi.2.2.2.2.1
              have hsumIdx0 := pn_aux_sum_P0_index0 v hcoord found
                (T.P 0 c d) a0 haux c d rfl
              have hdel := ec_one_del_NF_index_good1
                (T.P 0 c d) hi.2.2.1 hsumIdx0 hsumGood1
              have hres := cb_card_append_lower 0
                (T.one_del (T.P 0 c d)) (T.early_collapse a0)
                hdel.1 hdel.2.1 haec.1
                (Rank1Termination.index_mono (Nat.zero_le 1)
                  (T.early_collapse a0) haec.2.1)
                haec.2.2 hbaseBound
              exact ⟨hres.1, hres.2.1, hres.2.2.1⟩
          | succ p' =>
              have hp' : p' = 0 := by
                have hle : p' + 1 ≤ 1 := hp
                exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hle)
              subst p'
              have hone : T.one_del (T.P 1 c d) = T.P 1 c d := rfl
              rw [hone]
              have hres := pn_aux_card1_sum_append v hcoord
                (T.early_collapse a0) haec.1 haec.2.1 haec.2.2 hbaseBound
              rw [haux] at hres
              exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

#print axioms pn_aux_found_middle_closed

theorem pn_principal_NF {lam : Nat} (v : new.Vec (new.T lam) lam)
    (hcoord : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    T.isNF1 (trans (new.T.P v new.T.Z)) := by
  rw [_root_.trans.eq_2]
  cases lam with
  | zero =>
      cases v with
      | nil =>
          rw [transAux.eq_1]
          change T.isNF1 (T.P 0 T.Z T.Z)
          exact T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
            (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
            (T.Z_le _)
  | succ k =>
      cases haux : transAux v with
      | mk found rest =>
        cases rest with
        | mk sum a0 =>
          change
            T.isNF1
              (if found = true then
                T.P 1
                  (T.add (T.card_times 1 (T.one_del sum))
                    (T.early_collapse a0)) T.Z
              else if a0 = T.Z then T.P 0 T.Z T.Z
              else T.P 0 a0 T.Z)
          by_cases hf : found = true
          · rw [ite_eq_left hf]
            have hm := pn_aux_found_middle_closed v hcoord found sum a0 haux hf
            exact T.isNF1.p 1
              (T.add (T.card_times 1 (T.one_del sum)) (T.early_collapse a0))
              T.Z hm.1 T.isNF1.z hm.2.2 (T.Z_le _)
          · rw [ite_eq_right hf]
            have hi := tc_transAux_inv v hcoord found sum a0 haux
            by_cases ha0 : a0 = T.Z
            · rw [ite_eq_left ha0]
              exact T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
                (T.Z_le _)
            · rw [ite_eq_right ha0]
              exact T.isNF1.p 0 a0 T.Z hi.1 T.isNF1.z hi.2.1 (T.Z_le _)

#print axioms pn_principal_NF

import AuxSupport

open T

theorem ts_transAux_a0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        a0 = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  intro k
  induction k with
  | zero =>
      intro v found sum a0 haux
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              have ha0 : a0 = trans a :=
                congrArg (fun q : Bool × T × T => q.2.2) haux.symm
              change a0 = trans
                (if h : 0 < 0 then new.Vec.idx new.Vec.nil ⟨0, h⟩ else a)
              rw [dite_eq_right (Nat.lt_irrefl 0)]
              exact ha0
  | succ m ih =>
      intro v found sum a0 haux
      cases v with
      | @snoc n xs a =>
          cases hrest : transAux xs with
          | mk foundRest rest =>
              cases rest with
              | mk sumRest a0Rest =>
                  rw [transAux.eq_3, hrest] at haux
                  have ha0eq : a0 = a0Rest :=
                    congrArg (fun q : Bool × T × T => q.2.2) haux.symm
                  have hrec := ih xs foundRest sumRest a0Rest hrest
                  rw [ha0eq, hrec]
                  change trans (new.Vec.idx xs ⟨0, Nat.zero_lt_succ m⟩) =
                    trans (if h : 0 < m + 1 then
                      new.Vec.idx xs ⟨0, h⟩ else a)
                  rw [dite_eq_left (Nat.zero_lt_succ m)]

#print axioms ts_transAux_a0

theorem ts_coord_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.Vec.toList v) :
    z ∈ new.T.G (new.T.P v a) := by
  obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v z hz
  rw [new.T.G_P_eq]
  apply List.mem_append_left (new.T.G a)
  rw [← hi]
  exact new.Vec.Gres_mem_of_idx v i

#print axioms ts_coord_mem_G

theorem ts_tail_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.G a) :
    z ∈ new.T.G (new.T.P v a) := by
  rw [new.T.G_P_eq]
  exact List.mem_append_right (new.T.G.res v) hz

#print axioms ts_tail_mem_G

theorem ts_P1Z_le_tail (m tail : T) :
    T.P 1 m T.Z ≤ T.P 1 m tail := by
  cases T.Z_le tail with
  | inl hlt => exact Or.inl (T.Lt.p_tail 1 m T.Z tail hlt)
  | inr heq =>
      rw [← heq]
      exact Or.inr rfl

#print axioms ts_P1Z_le_tail

theorem ts_support_decomp_step {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s)
    (ht : T.isNF1 (trans s))
    (hgoodSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size s → new.T.isNFComp x →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hdecompSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size s → new.T.isNF x →
        ∀ y : T, y ∈ T.G1 0 (trans x) →
          y < trans x ∨
            ∃ z : new.T lam, z ∈ new.T.G x ∧ y ≤ trans z) :
    ∀ y : T, y ∈ T.G1 0 (trans s) →
      y < trans s ∨
        ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z := by
  cases s with
  | Z =>
      intro y hy
      rw [_root_.trans.eq_1, T.G1.eq_1] at hy
      cases hy
  | P v a =>
      cases hs with
      | p _ _ hvNF haNF hvG hhead =>
          have hcoord :
              ∀ z : new.T lam, z ∈ new.Vec.toList v →
                T.isNF1 (trans z) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans z) → y < trans z) := by
            intro z hz
            have hsz := oc_mem_size_lt_P v a z hz
            exact hgoodSmall z hsz ⟨hvNF z hz, hvG z hz⟩
          have htailDecomp :
              ∀ y : T, y ∈ T.G1 0 (trans a) →
                y < trans a ∨
                  ∃ z : new.T lam, z ∈ new.T.G a ∧ y ≤ trans z :=
            hdecompSmall a (new.T.add_size_lt_P v a) haNF
          cases lam with
          | zero =>
              cases v with
              | nil =>
                  rw [_root_.trans.eq_2, transAux.eq_1] at ht ⊢
                  change
                    ∀ y : T, y ∈ T.G1 0 (T.P 0 T.Z (trans a)) →
                      y < T.P 0 T.Z (trans a) ∨
                        ∃ z : new.T 0,
                          z ∈ new.T.G (new.T.P new.Vec.nil a) ∧ y ≤ trans z
                  intro y hy
                  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                    List.mem_append, List.mem_append] at hy
                  cases hy with
                  | inl hleft =>
                      cases hleft with
                      | inl hz =>
                          have hyz : y = T.Z := List.mem_singleton.mp hz
                          rw [hyz]
                          exact Or.inl (T.Lt.Z_lt_P 0 T.Z (trans a))
                      | inr hzG =>
                          rw [T.G1.eq_1] at hzG
                          cases hzG
                  | inr htail =>
                      cases htailDecomp y htail with
                      | inl hya =>
                          have htle := T.isNF1_tail_le
                            (T.P 0 T.Z (trans a)) ht 0 T.Z (trans a) rfl
                          exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                            (T.P 0 T.Z (trans a)) hya htle)
                      | inr hw =>
                          obtain ⟨z, hz, hyz⟩ := hw
                          exact Or.inr ⟨z,
                            ts_tail_mem_G new.Vec.nil a z hz, hyz⟩
          | succ k =>
              cases haux : transAux v with
              | mk found rest =>
                  cases rest with
                  | mk sum a0 =>
                      have ha0eq := ts_transAux_a0 v found sum a0 haux
                      have hauxSupp := as_card1_support_pair v hcoord
                        found sum a0 haux
                      have hauxInv := tc_transAux_inv v hcoord
                        found sum a0 haux
                      rw [_root_.trans.eq_2, haux] at ht ⊢
                      change T.isNF1
                        (if found = true then
                          T.P 1
                            (T.add (T.card_times 1 (T.one_del sum))
                              (T.early_collapse a0)) (trans a)
                        else if a0 = T.Z then T.P 0 T.Z (trans a)
                        else T.P 0 a0 (trans a)) at ht
                      change ∀ y : T,
                        y ∈ T.G1 0
                            (if found = true then
                              T.P 1
                                (T.add (T.card_times 1 (T.one_del sum))
                                  (T.early_collapse a0)) (trans a)
                            else if a0 = T.Z then T.P 0 T.Z (trans a)
                            else T.P 0 a0 (trans a)) →
                          (y <
                              (if found = true then
                                T.P 1
                                  (T.add (T.card_times 1 (T.one_del sum))
                                    (T.early_collapse a0)) (trans a)
                              else if a0 = T.Z then T.P 0 T.Z (trans a)
                              else T.P 0 a0 (trans a)) ∨
                            ∃ z : new.T (k + 1),
                              z ∈ new.T.G (new.T.P v a) ∧ y ≤ trans z)
                      by_cases hf : found = true
                      · rw [ite_eq_left hf] at ht ⊢
                        let A := T.card_times 1 (T.one_del sum)
                        let E := T.early_collapse a0
                        let M := T.add A E
                        have hMclosed := pn_aux_found_middle_closed v hcoord
                          found sum a0 haux hf
                        change T.isNF1 (T.P 1 M (trans a)) at ht
                        have hMwrap : M < T.P 1 M T.Z :=
                          cs_self_lt_wrap M hMclosed.1 hMclosed.2.1 hMclosed.2.2
                        have hMfull : M < T.P 1 M (trans a) :=
                          lt_of_lt_of_le_thm T M (T.P 1 M T.Z)
                            (T.P 1 M (trans a)) hMwrap (ts_P1Z_le_tail M (trans a))
                        intro y hy
                        change y ∈ T.G1 0 (T.P 1 M (trans a)) at hy
                        rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
                          List.mem_append, List.mem_append] at hy
                        cases hy with
                        | inl hleft =>
                            cases hleft with
                            | inl hmid =>
                                have hym : y = M := List.mem_singleton.mp hmid
                                rw [hym]
                                exact Or.inl hMfull
                            | inr hGM =>
                                unfold M at hGM
                                rw [bridge_G1_add_eq] at hGM
                                cases List.mem_append.mp hGM with
                                | inl hA =>
                                    have hdec := hauxSupp.2 y hA
                                    cases hdec with
                                    | inl hlt =>
                                        have hAle : A ≤ T.add A E := wt_add_self_le A E
                                        have hLift := bridge_lift_P1_le A (T.add A E) hAle
                                        have hyMZ : y < T.P 1 M T.Z := by
                                          unfold M
                                          exact lt_of_lt_of_le_thm T y (T.P 1 A T.Z)
                                            (T.P 1 (T.add A E) T.Z) hlt hLift
                                        exact Or.inl (lt_of_lt_of_le_thm T y
                                          (T.P 1 M T.Z) (T.P 1 M (trans a))
                                          hyMZ (ts_P1Z_le_tail M (trans a)))
                                    | inr hw =>
                                        obtain ⟨z, hz, hyz⟩ := hw
                                        exact Or.inr ⟨z, ts_coord_mem_G v a z hz, hyz⟩
                                | inr hE =>
                                    have ha0good := hauxInv.1
                                    have ha0G := hauxInv.2.1
                                    have hy0 : y ≤ a0 :=
                                      sg_early_G0_le a0 ha0good ha0G y hE
                                    let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                                    have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                                      new.Vec.idx_mem_toList v i0
                                    have htrans0 : trans (v.idx i0) = a0 := by
                                      exact ha0eq.symm
                                    exact Or.inr ⟨v.idx i0,
                                      ts_coord_mem_G v a (v.idx i0) hiMem,
                                      by rw [htrans0]; exact hy0⟩
                        | inr htail =>
                            cases htailDecomp y htail with
                            | inl hya =>
                                have htle := T.isNF1_tail_le
                                  (T.P 1 M (trans a)) ht 1 M (trans a) rfl
                                exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                                  (T.P 1 M (trans a)) hya htle)
                            | inr hw =>
                                obtain ⟨z, hz, hyz⟩ := hw
                                exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩
                      · rw [ite_eq_right hf] at ht ⊢
                        by_cases ha0z : a0 = T.Z
                        · rw [ite_eq_left ha0z] at ht ⊢
                          intro y hy
                          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                            List.mem_append, List.mem_append] at hy
                          cases hy with
                          | inl hleft =>
                              cases hleft with
                              | inl hz =>
                                  have hyz : y = T.Z := List.mem_singleton.mp hz
                                  rw [hyz]
                                  exact Or.inl (T.Lt.Z_lt_P 0 T.Z (trans a))
                              | inr hzG =>
                                  rw [T.G1.eq_1] at hzG
                                  cases hzG
                          | inr htail =>
                              cases htailDecomp y htail with
                              | inl hya =>
                                  have htle := T.isNF1_tail_le
                                    (T.P 0 T.Z (trans a)) ht 0 T.Z (trans a) rfl
                                  exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                                    (T.P 0 T.Z (trans a)) hya htle)
                              | inr hw =>
                                  obtain ⟨z, hz, hyz⟩ := hw
                                  exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩
                        · rw [ite_eq_right ha0z] at ht ⊢
                          intro y hy
                          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                            List.mem_append, List.mem_append] at hy
                          cases hy with
                          | inl hleft =>
                              cases hleft with
                              | inl ha0mem =>
                                  have hya0 : y = a0 := List.mem_singleton.mp ha0mem
                                  let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                                  have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                                    new.Vec.idx_mem_toList v i0
                                  exact Or.inr ⟨v.idx i0,
                                    ts_coord_mem_G v a (v.idx i0) hiMem,
                                    by
                                      rw [hya0, ← ha0eq]
                                      exact Or.inr rfl⟩
                              | inr hGa0 =>
                                  let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                                  have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                                    new.Vec.idx_mem_toList v i0
                                  have hgood0 := hcoord (v.idx i0) hiMem
                                  have htrans0 : trans (v.idx i0) = a0 := ha0eq.symm
                                  have hlt0 : y < a0 := hauxInv.2.1 y hGa0
                                  exact Or.inr ⟨v.idx i0,
                                    ts_coord_mem_G v a (v.idx i0) hiMem,
                                    Or.inl (by rw [htrans0]; exact hlt0)⟩
                          | inr htail =>
                              cases htailDecomp y htail with
                              | inl hya =>
                                  have htle := T.isNF1_tail_le
                                    (T.P 0 a0 (trans a)) ht 0 a0 (trans a) rfl
                                  exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                                    (T.P 0 a0 (trans a)) hya htle)
                              | inr hw =>
                                  obtain ⟨z, hz, hyz⟩ := hw
                                  exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩

#print axioms ts_support_decomp_step

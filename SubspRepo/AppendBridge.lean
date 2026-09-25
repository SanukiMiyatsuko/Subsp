import FoundUpper2

open T

theorem ab_le_add (a b : T) : a ≤ T.add a b := by
  induction a with
  | Z =>
    rw [T.add.eq_1]
    exact T.Z_le b
  | P p c d ihc ihd =>
    rw [T.P_add_eq]
    cases ihd with
    | inl hlt =>
      exact Or.inl (T.Lt.p_tail p c d (T.add d b) hlt)
    | inr heq =>
      exact Or.inr (congrArg (fun z => T.P p c z) heq)

#print axioms ab_le_add

theorem ab_index0_head_le_P1 (d M : T)
    (hd : T.index_Prop1 0 d) :
    T.head d ≤ T.P 1 M T.Z := by
  cases d with
  | Z => exact T.Z_le (T.P 1 M T.Z)
  | P p a b =>
    cases hd with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      exact Or.inl (T.Lt.p_head 0 1 a M T.Z T.Z
        (Nat.zero_lt_succ 0))

#print axioms ab_index0_head_le_P1

theorem ab_card1_P_shape (p : Nat) (a b : T) :
    ∃ M : T, T.card_times 1 (T.P p a b) =
      T.P 1 M (T.card_times 1 b) := by
  rw [T.card_times.eq_3]
  by_cases hp : p = 0
  · rw [ite_eq_left hp]
    refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0))
      (T.early_collapse a), ?_⟩
    change
      T.add
        (T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0))
            (T.early_collapse a)) T.Z)
        (T.card_times 1 b) =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0))
          (T.early_collapse a))
        (T.card_times 1 b)
    rw [T.P_add_eq, T.add.eq_1]
  · rw [ite_eq_right hp]
    refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a, ?_⟩
    change
      T.add
        (T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a) T.Z)
        (T.card_times 1 b) =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a)
        (T.card_times 1 b)
    rw [T.P_add_eq, T.add.eq_1]

#print axioms ab_card1_P_shape

theorem ab_card1_append_NF : ∀ c d : T,
    T.isNF1 (T.card_times 1 c) →
    T.isNF1 d → T.index_Prop1 0 d →
    T.isNF1 (T.add (T.card_times 1 c) d) := by
  intro c
  induction c with
  | Z =>
    intro d hc hdNF hdIdx
    rw [T.card_times.eq_1, T.add.eq_1]
    exact hdNF
  | P p a b iha ihb =>
    intro d hc hdNF hdIdx
    obtain ⟨M, hshape⟩ := ab_card1_P_shape p a b
    rw [hshape] at hc ⊢
    obtain ⟨hMNF, htailNF, hMG, hhead⟩ :=
      T.isNF1_P_inv 1 M (T.card_times 1 b) hc
    rw [T.P_add_eq]
    apply T.isNF1.p 1 M (T.add (T.card_times 1 b) d)
    · exact hMNF
    · exact ihb d htailNF hdNF hdIdx
    · exact hMG
    · by_cases htailZ : T.card_times 1 b = T.Z
      · rw [htailZ, T.add.eq_1]
        exact ab_index0_head_le_P1 d M hdIdx
      · rw [bridge_head_add_ne_Z (T.card_times 1 b) d htailZ]
        exact hhead

#print axioms ab_card1_append_NF

theorem ab_card1_append_good (c d : T)
    (hcNF : T.isNF1 (T.card_times 1 c))
    (hcIdx : T.index_Prop1 1 (T.card_times 1 c))
    (hcG : ∀ x : T, x ∈ T.G1 1 (T.card_times 1 c) →
      x < T.card_times 1 c)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) :
    T.isNF1 (T.add (T.card_times 1 c) d) ∧
      T.index_Prop1 1 (T.add (T.card_times 1 c) d) ∧
      (∀ x : T,
        x ∈ T.G1 1 (T.add (T.card_times 1 c) d) →
          x < T.add (T.card_times 1 c) d) := by
  have hnf := ab_card1_append_NF c d hcNF hdNF hdIdx
  have hdIdx1 := Rank1Termination.index_mono (Nat.zero_le 1) d hdIdx
  have hidx := Rank1Termination.index_add 1
    (T.card_times 1 c) d hcIdx hdIdx1
  constructor
  · exact hnf
  · constructor
    · exact hidx
    · intro x hx
      rw [bridge_G1_add_eq] at hx
      cases List.mem_append.mp hx with
      | inl hleft =>
        have hlt := hcG x hleft
        exact lt_of_lt_of_le_thm T x (T.card_times 1 c)
          (T.add (T.card_times 1 c) d) hlt
          (ab_le_add (T.card_times 1 c) d)
      | inr hright =>
        have hempty := index_Prop1_G1_empty 0 d hdIdx 1
          (Nat.zero_lt_succ 0)
        rw [hempty] at hright
        cases hright

#print axioms ab_card1_append_good

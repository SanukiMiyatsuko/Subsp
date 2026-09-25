import Bridge

open T

theorem tb_head_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.head s) := by
  cases s with
  | Z => exact T.isNF1.z
  | P p a b =>
    obtain ⟨ha, hb, hg, hh⟩ := T.isNF1_P_inv p a b hs
    exact T.isNF1.p p a T.Z ha T.isNF1.z hg (T.Z_le _)

theorem tb_head_index0 (s : T) (hs : T.index_Prop1 0 s) :
    T.index_Prop1 0 (T.head s) := by
  cases s with
  | Z => exact T.index_Prop1.z
  | P p a b =>
    cases hs with
    | p _ _ _ hp hb =>
      exact T.index_Prop1.p p a T.Z hp T.index_Prop1.z

theorem tb_card_times_head (n : Nat) (s : T) :
    T.head (T.card_times n s) = T.card_times n (T.head s) := by
  cases s with
  | Z => rfl
  | P p a b =>
    cases n with
    | zero => rfl
    | succ k =>
      change
        T.head
          (T.add
            (if p = 0 then
              T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) T.Z
            else
              T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) T.Z)
            (T.card_times (k + 1) b)) =
        T.add
          (if p = 0 then
            T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) T.Z
          else
            T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) T.Z)
          (T.card_times (k + 1) T.Z)
      by_cases hp : p = 0
      · rw [ite_eq_left hp, T.card_times.eq_1, T.add_Z, T.P_add_eq]
        rfl
      · rw [ite_eq_right hp, T.card_times.eq_1, T.add_Z, T.P_add_eq]
        rfl

#print axioms tb_card_times_head

theorem tb_card_times_le_same (n : Nat) (c d : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d)
    (hcd : c ≤ d) :
    T.card_times n c ≤ T.card_times n d := by
  cases hcd with
  | inl hlt =>
    exact Or.inl (bridge_card_times_lt_same n c d hcNF hcIdx hdNF hdIdx hlt)
  | inr heq =>
    have hEq : c = d := heq
    rw [hEq]
    exact Or.inr rfl


theorem tb_card_times_P0_succ (k : Nat) (a b : T) :
    T.card_times (k + 1) (T.P 0 a b) =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
          (T.early_collapse a))
        (T.card_times (k + 1) b) := by
  rw [T.card_times.eq_def]
  change
    T.add
      (if 0 = 0 then
        T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
            (T.early_collapse a)) T.Z
      else
        T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) T.Z)
      (T.card_times (k + 1) b) = _
  rw [ite_eq_left rfl, T.P_add_eq, T.add]

theorem tb_card_times_closed (n : Nat) :
    ∀ c : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 (T.card_times n c) ∧
        T.index_Prop1 1 (T.card_times n c) ∧
        (∀ x : T, x ∈ T.G1 1 (T.card_times n c) →
          x < T.card_times n c) := by
  intro c
  induction c with
  | Z =>
    intro hcNF hcIdx
    rw [T.card_times]
    exact ⟨T.isNF1.z, T.index_Prop1.z, fun x hx => by
      rw [T.G1.eq_1] at hx
      cases hx⟩
  | P p a b iha ihb =>
    intro hcNF hcIdx
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
      cases n with
      | zero =>
        rw [T.card_times]
        have hidx0 : T.index_Prop1 0 (T.P 0 a b) :=
          T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx
        have hidx1 : T.index_Prop1 1 (T.P 0 a b) :=
          Rank1Termination.index_mono (Nat.zero_le 1) (T.P 0 a b) hidx0
        have hempty := index_Prop1_G1_empty 0 (T.P 0 a b)
          hidx0 1 (Nat.zero_lt_succ 0)
        constructor
        · exact hcNF
        · constructor
          · exact hidx1
          · intro x hx
            rw [hempty] at hx
            cases hx
      | succ k =>
        rw [tb_card_times_P0_succ]
        have hec := bridge_early_collapse_closed a haNF haG
        have hshiftNF := bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
        have htail := ihb hbNF hbIdx
        have hbaseNF : T.isNF1 (T.P 0 a T.Z) :=
          T.isNF1.p 0 a T.Z haNF T.isNF1.z haG (T.Z_le _)
        have hbaseIdx : T.index_Prop1 0 (T.P 0 a T.Z) :=
          T.index_Prop1.p 0 a T.Z (Nat.le_refl 0) T.index_Prop1.z
        have hheadNF : T.isNF1 (T.head b) := tb_head_NF1 b hbNF
        have hheadIdx : T.index_Prop1 0 (T.head b) := tb_head_index0 b hbIdx
        have htailHead :
            T.head (T.card_times (k + 1) b) ≤
              T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a)) T.Z := by
          rw [tb_card_times_head]
          have hmono := tb_card_times_le_same (k + 1)
            (T.head b) (T.P 0 a T.Z)
            hheadNF hheadIdx hbaseNF hbaseIdx hheadb
          change T.card_times (k + 1) (T.head b) ≤
            T.card_times (k + 1) (T.P 0 a T.Z)
          exact hmono
        have hcurNF :
            T.isNF1
              (T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b)) :=
          T.isNF1.p 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)
            hshiftNF htail.1
            (bridge_shift_strong1 k (T.early_collapse a) hec.2.1)
            htailHead
        have hcurIdx :
            T.index_Prop1 1
              (T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b)) :=
          T.index_Prop1.p 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)
            (Nat.le_refl 1) htail.2.1
        constructor
        · exact hcurNF
        · constructor
          · exact hcurIdx
          · intro x hx
            rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
              List.mem_append, List.mem_append] at hx
            have hmidOuter := bridge_shift_lt_outer k (T.early_collapse a)
              (T.card_times (k + 1) b) hec.2.1
            cases hx with
            | inl hleft =>
              cases hleft with
              | inl hmid =>
                have hEq : x =
                    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a) := List.mem_singleton.mp hmid
                rw [hEq]
                exact hmidOuter
              | inr hG =>
                have hxmid := bridge_shift_strong1 k (T.early_collapse a)
                  hec.2.1 x hG
                exact lt_trans_thm x _ _ hxmid hmidOuter
            | inr htailG =>
              have hxtail := htail.2.2 x htailG
              have htailLe := T.isNF1_tail_le _ hcurNF 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b) rfl
              exact lt_of_lt_of_le_thm T x (T.card_times (k + 1) b) _
                hxtail htailLe

#print axioms tb_card_times_closed

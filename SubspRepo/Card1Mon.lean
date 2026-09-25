import OrderCases

open T

theorem c1_p0 (a b : T) :
    T.card_times 1 (T.P 0 a b) =
      T.P 1 (T.early_collapse a) (T.card_times 1 b) := by
  rw [T.card_times.eq_3, ite_eq_left rfl]
  rw [T.ofNat.eq_1, T.mul.eq_1]
  change T.add (T.P 1 (T.add T.Z (T.early_collapse a)) T.Z)
    (T.card_times 1 b) = T.P 1 (T.early_collapse a) (T.card_times 1 b)
  rw [T.add.eq_1, T.P_add_eq, T.add.eq_1]

theorem c1_p1 (a b : T) :
    T.card_times 1 (T.P 1 a b) =
      T.P 1 (T.P 1 T.Z a) (T.card_times 1 b) := by
  rw [T.card_times.eq_3, ite_eq_right (Nat.one_ne_zero)]
  rw [mul_succ_shape 1 T.Z 0]
  rw [T.ofNat.eq_1, T.mul.eq_1]
  change T.add (T.P 1 (T.add (T.P 1 T.Z T.Z) a) T.Z)
    (T.card_times 1 b) = T.P 1 (T.P 1 T.Z a) (T.card_times 1 b)
  rw [T.P_add_eq, T.add.eq_1]
  rw [T.P_add_eq, T.add.eq_1]

theorem c1_idx0_lt_P1 (x y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 T.Z y := by
  cases x with
  | Z => exact T.Lt.Z_lt_P 1 T.Z y
  | P p a b =>
    cases hx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      exact T.Lt.p_head 0 1 a T.Z b y (Nat.zero_lt_succ 0)

#print axioms c1_idx0_lt_P1

theorem c1_card_times_mono_index1 :
    ∀ s t : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.card_times 1 s < T.card_times 1 t := by
  intro s
  induction s with
  | Z =>
    intro t hsNF hsIdx htNF htIdx hst
    have htne : t ≠ T.Z := by
      intro heq
      rw [heq] at hst
      exact lt_Z_inv hst
    have hctne : T.card_times 1 t ≠ T.Z :=
      bridge_card_times_ne_Z 1 t htne
    rw [T.card_times.eq_1]
    cases T.Z_le (T.card_times 1 t) with
    | inl hlt => exact hlt
    | inr heq => exact False.elim (hctne heq.symm)
  | P p a b iha ihb =>
    intro t hsNF hsIdx htNF htIdx hst
    cases t with
    | Z => exact False.elim (lt_Z_inv hst)
    | P q e f =>
      have hpLe : p ≤ 1 := by
        cases hsIdx with
        | p _ _ _ hp _ => exact hp
      have hqLe : q ≤ 1 := by
        cases htIdx with
        | p _ _ _ hq _ => exact hq
      cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hpLe) with
      | inl hp0 =>
        subst p
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
        | inl hq0 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p0, c1_p0]
          cases lt_inv 0 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 0 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hec : T.early_collapse a < T.early_collapse e :=
                bridge_early_collapse_lt a e haNF haG heNF heG hae
              exact T.Lt.p_mid 1 (T.early_collapse a) (T.early_collapse e)
                (T.card_times 1 b) (T.card_times 1 f) hec
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
              exact T.Lt.p_tail 1 (T.early_collapse a)
                (T.card_times 1 b) (T.card_times 1 f) hrec
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          have hec := bridge_early_collapse_closed a haNF haG
          rw [c1_p0, c1_p1]
          have hmid : T.early_collapse a < T.P 1 T.Z e :=
            c1_idx0_lt_P1 (T.early_collapse a) e hec.2.1
          exact T.Lt.p_mid 1 (T.early_collapse a) (T.P 1 T.Z e)
            (T.card_times 1 b) (T.card_times 1 f) hmid
      | inr hp1 =>
        subst p
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
        | inl hq0 =>
          subst q
          cases lt_inv 1 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.not_lt_zero 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid => cases hmid.1
            | inr htail => cases htail.1
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 1 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 1 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p1, c1_p1]
          cases lt_inv 1 a b 1 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hinner : T.P 1 T.Z a < T.P 1 T.Z e :=
                T.Lt.p_tail 1 T.Z a e hae
              exact T.Lt.p_mid 1 (T.P 1 T.Z a) (T.P 1 T.Z e)
                (T.card_times 1 b) (T.card_times 1 f) hinner
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
              exact T.Lt.p_tail 1 (T.P 1 T.Z a)
                (T.card_times 1 b) (T.card_times 1 f) hrec

#print axioms c1_card_times_mono_index1

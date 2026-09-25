import Subsp.new.stop_order_aux

open T

theorem oc_true_false_absurd {lam k : Nat}
    (v w : new.Vec (new.T lam) (k + 1))
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt)
    (sv av sw aw : T)
    (hav : transAux v = (true, sv, av))
    (haw : transAux w = (false, sw, aw)) : False := by
  have hlex := co_transAux_card1_lex v w hv hw hmono hcmp
    true false sv av sw aw hav haw
  have hiv := tc_transAux_inv v hv true sv av hav
  have hiw := tc_transAux_inv w hw false sw aw haw
  have hsvne : sv ≠ T.Z := hiv.2.2.2.2.2.2.1 rfl
  have hswz : sw = T.Z := hiw.2.2.2.2.2.2.2 rfl
  cases hlex with
  | inl hlt =>
      rw [hswz, T.card_times.eq_1] at hlt
      exact lt_Z_inv hlt
  | inr heq =>
      have hcz : T.card_times 1 sv = T.Z := by
        rw [hswz, T.card_times.eq_1] at heq
        exact heq.1
      exact (bridge_card_times_ne_Z 1 sv hsvne) hcz

#print axioms oc_true_false_absurd

theorem oc_false_false_a0_lt {lam k : Nat}
    (v w : new.Vec (new.T lam) (k + 1))
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt)
    (sv av sw aw : T)
    (hav : transAux v = (false, sv, av))
    (haw : transAux w = (false, sw, aw)) : av < aw := by
  have hlex := co_transAux_card1_lex v w hv hw hmono hcmp
    false false sv av sw aw hav haw
  have hiv := tc_transAux_inv v hv false sv av hav
  have hiw := tc_transAux_inv w hw false sw aw haw
  have hsvz : sv = T.Z := hiv.2.2.2.2.2.2.2 rfl
  have hswz : sw = T.Z := hiw.2.2.2.2.2.2.2 rfl
  cases hlex with
  | inl hlt =>
      rw [hsvz, hswz] at hlt
      exact False.elim (lt_irrefl_thm T.Z hlt)
  | inr heq =>
      exact heq.2

#print axioms oc_false_false_a0_lt

theorem oc_principal_lt_false_false {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (hv : ∀ x : new.T (k + 1), x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T (k + 1), x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T (k + 1),
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt)
    (sv av sw aw : T)
    (hav : transAux v = (false, sv, av))
    (haw : transAux w = (false, sw, aw)) :
    _root_.trans (new.T.P v new.T.Z) < _root_.trans (new.T.P w new.T.Z) := by
  have ha0lt := oc_false_false_a0_lt v w hv hw hmono hcmp sv av sw aw hav haw
  rw [_root_.trans.eq_2, hav, _root_.trans.eq_1]
  rw [_root_.trans.eq_2, haw, _root_.trans.eq_1]
  change
    (if av = T.Z then T.P 0 T.Z T.Z else T.P 0 av T.Z) <
      (if aw = T.Z then T.P 0 T.Z T.Z else T.P 0 aw T.Z)
  by_cases havz : av = T.Z
  · subst av
    rw [ite_eq_left rfl]
    by_cases hawz : aw = T.Z
    · subst aw
      exact False.elim (lt_irrefl_thm T.Z ha0lt)
    · rw [ite_eq_right hawz]
      exact T.Lt.p_mid 0 T.Z aw T.Z T.Z ha0lt
  · rw [ite_eq_right havz]
    have hawz : aw ≠ T.Z := by
      intro heq
      rw [heq] at ha0lt
      exact lt_Z_inv ha0lt
    rw [ite_eq_right hawz]
    exact T.Lt.p_mid 0 av aw T.Z T.Z ha0lt

#print axioms oc_principal_lt_false_false

theorem oc_principal_lt_false_true {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (sv av sw aw : T)
    (hav : transAux v = (false, sv, av))
    (haw : transAux w = (true, sw, aw)) :
    _root_.trans (new.T.P v new.T.Z) < _root_.trans (new.T.P w new.T.Z) := by
  rw [_root_.trans.eq_2, hav, _root_.trans.eq_1]
  rw [_root_.trans.eq_2, haw, _root_.trans.eq_1]
  change
    (if av = T.Z then T.P 0 T.Z T.Z else T.P 0 av T.Z) <
      T.P 1 (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw)) T.Z
  by_cases havz : av = T.Z
  · rw [ite_eq_left havz]
    exact T.Lt.p_head 0 1 T.Z
      (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw))
      T.Z T.Z (Nat.zero_lt_succ 0)
  · rw [ite_eq_right havz]
    exact T.Lt.p_head 0 1 av
      (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw))
      T.Z T.Z (Nat.zero_lt_succ 0)

#print axioms oc_principal_lt_false_true


theorem oc_one_del_P0 (a b : T) :
    T.one_del (T.P 0 a b) = if a = T.Z then b else T.P 0 a b := by
  by_cases ha : a = T.Z
  · subst a
    rw [ite_eq_left rfl]
    exact T.one_del.eq_1 b
  · rw [ite_eq_right ha]
    exact T.one_del.eq_2 (T.P 0 a b) (by
      intro s2 h
      injection h with hidx hmid htail
      exact ha hmid)

#print axioms oc_one_del_P0

theorem oc_one_del_NF_index0 (s : T)
    (hs : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    T.isNF1 (T.one_del s) ∧ T.index_Prop1 0 (T.one_del s) := by
  cases s with
  | Z =>
      have hz : T.one_del T.Z = T.Z := T.one_del.eq_2 T.Z (by
        intro s2 h
        cases h)
      rw [hz]
      exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P p a b =>
      cases hi with
      | p _ _ _ hp hbidx =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        rw [oc_one_del_P0]
        by_cases ha : a = T.Z
        · rw [ite_eq_left ha]
          have hbNF := (T.isNF1_P_inv 0 a b hs).2.1
          exact ⟨hbNF, hbidx⟩
        · rw [ite_eq_right ha]
          exact ⟨hs, T.index_Prop1.p 0 a b (Nat.le_refl 0) hbidx⟩

#print axioms oc_one_del_NF_index0

theorem oc_P0Z_tail_shape (b : T)
    (hbNF : T.isNF1 b) (hhead : T.head b ≤ T.P 0 T.Z T.Z) :
    b = T.Z ∨ ∃ d : T, b = T.P 0 T.Z d := by
  cases b with
  | Z => exact Or.inl rfl
  | P q c d =>
      have hq0 : q = 0 := Nat.eq_zero_of_le_zero
        (head_le_index q 0 c T.Z hhead)
      subst q
      have hc0 : c = T.Z := by
        cases hhead with
        | inl hlt =>
          cases lt_inv 0 c T.Z 0 T.Z T.Z hlt with
          | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
          | inr hor =>
            cases hor with
            | inl hm => exact False.elim (lt_Z_inv hm.2)
            | inr ht => exact ht.2.1
        | inr heq =>
          injection heq
      subst c
      exact Or.inr ⟨d, rfl⟩

#print axioms oc_P0Z_tail_shape

theorem oc_one_del_lt_index0 (a b : T)
    (haNF : T.isNF1 a) (haIdx : T.index_Prop1 0 a) (haNe : a ≠ T.Z)
    (hbNF : T.isNF1 b) (hbIdx : T.index_Prop1 0 b) (hbNe : b ≠ T.Z)
    (hab : a < b) :
    T.one_del a < T.one_del b := by
  cases a with
  | Z => exact False.elim (haNe rfl)
  | P pa aa ab =>
    cases haIdx with
    | p _ _ _ hpa habIdx =>
      have hpa0 : pa = 0 := Nat.eq_zero_of_le_zero hpa
      subst pa
      cases b with
      | Z => exact False.elim (hbNe rfl)
      | P pb ba bb =>
        cases hbIdx with
        | p _ _ _ hpb hbbIdx =>
          have hpb0 : pb = 0 := Nat.eq_zero_of_le_zero hpb
          subst pb
          rw [oc_one_del_P0, oc_one_del_P0]
          by_cases haaZ : aa = T.Z
          · rw [ite_eq_left haaZ]
            by_cases hbaZ : ba = T.Z
            · rw [ite_eq_left hbaZ]
              subst aa
              subst ba
              cases lt_inv 0 T.Z ab 0 T.Z bb hab with
              | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
              | inr hor =>
                cases hor with
                | inl hm => exact False.elim (lt_Z_inv hm.2)
                | inr ht => exact ht.2.2
            · rw [ite_eq_right hbaZ]
              subst aa
              have habNF := (T.isNF1_P_inv 0 T.Z ab haNF).2.1
              have hheadab := (T.isNF1_P_inv 0 T.Z ab haNF).2.2.2
              cases oc_P0Z_tail_shape ab habNF hheadab with
              | inl hz =>
                rw [hz]
                exact T.Lt.Z_lt_P 0 ba bb
              | inr hp =>
                obtain ⟨d, hd⟩ := hp
                rw [hd]
                exact T.Lt.p_mid 0 T.Z ba d bb (tc_Z_lt_of_ne ba hbaZ)
          · rw [ite_eq_right haaZ]
            by_cases hbaZ : ba = T.Z
            · rw [ite_eq_left hbaZ]
              subst ba
              cases lt_inv 0 aa ab 0 T.Z bb hab with
              | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
              | inr hor =>
                cases hor with
                | inl hm => exact False.elim (lt_Z_inv hm.2)
                | inr ht =>
                  have heq : aa = T.Z := ht.2.1
                  exact False.elim (haaZ heq)
            · rw [ite_eq_right hbaZ]
              exact hab

#print axioms oc_one_del_lt_index0

theorem oc_P1ZZ_le (c d : T) : T.P 1 T.Z T.Z ≤ T.P 1 c d := by
  cases c with
  | Z =>
      cases d with
      | Z => exact Or.inr rfl
      | P q a b =>
          exact Or.inl (T.Lt.p_tail 1 T.Z T.Z (T.P q a b)
            (T.Lt.Z_lt_P q a b))
  | P q a b =>
      exact Or.inl (T.Lt.p_mid 1 T.Z (T.P q a b) T.Z d
        (T.Lt.Z_lt_P q a b))

#print axioms oc_P1ZZ_le

theorem oc_one_del_lt_index1 (s t : T)
    (hsNF : T.isNF1 s) (hsIdx : T.index_Prop1 1 s) (hsNe : s ≠ T.Z)
    (htNF : T.isNF1 t) (htIdx : T.index_Prop1 1 t) (htNe : t ≠ T.Z)
    (hst : s < t) :
    T.one_del s < T.one_del t := by
  cases s with
  | Z => exact False.elim (hsNe rfl)
  | P p a b =>
    cases t with
    | Z => exact False.elim (htNe rfl)
    | P q c d =>
      cases hsIdx with
      | p _ _ _ hp hbIdx =>
        cases htIdx with
        | p _ _ _ hq hdIdx =>
          cases lt_inv p a b q c d hst with
          | inl hpq =>
            have hp0 : p = 0 := by
              cases p with
              | zero => rfl
              | succ p' =>
                have hp'0 : p' = 0 :=
                  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hp)
                subst p'
                have hqgt : 1 < q := hpq
                exact False.elim ((Nat.not_lt_of_ge hq) hqgt)
            have hq1 : q = 1 := by
              subst p
              cases q with
              | zero => exact False.elim (Nat.not_lt_zero 0 hpq)
              | succ q' =>
                have hq'0 : q' = 0 :=
                  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hq)
                subst q'
                rfl
            subst p
            subst q
            have hsIdx0 : T.index_Prop1 0 (T.P 0 a b) :=
              isNF1_index 0 0 a b hsNF (Nat.le_refl 0)
            have hdel := oc_one_del_NF_index0 (T.P 0 a b) hsNF hsIdx0
            have hright : T.one_del (T.P 1 c d) = T.P 1 c d :=
              T.one_del.eq_2 (T.P 1 c d) (by
                intro s2 h
                cases h)
            rw [hright]
            have hlow := index_Prop1_lt_succ 0
              (T.one_del (T.P 0 a b)) hdel.2
            exact lt_of_lt_of_le_thm T
              (T.one_del (T.P 0 a b)) (T.P 1 T.Z T.Z) (T.P 1 c d)
              hlow (oc_P1ZZ_le c d)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hpq : p = q := hmid.1
              subst q
              cases p with
              | zero =>
                have hsIdx0 : T.index_Prop1 0 (T.P 0 a b) :=
                  isNF1_index 0 0 a b hsNF (Nat.le_refl 0)
                have htIdx0 : T.index_Prop1 0 (T.P 0 c d) :=
                  isNF1_index 0 0 c d htNF (Nat.le_refl 0)
                exact oc_one_del_lt_index0 (T.P 0 a b) (T.P 0 c d)
                  hsNF hsIdx0 (by intro h; cases h)
                  htNF htIdx0 (by intro h; cases h) hst
              | succ p' =>
                have hp'0 : p' = 0 :=
                  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hp)
                subst p'
                have hsdel : T.one_del (T.P 1 a b) = T.P 1 a b :=
                  T.one_del.eq_2 (T.P 1 a b) (by intro s2 h; cases h)
                have htdel : T.one_del (T.P 1 c d) = T.P 1 c d :=
                  T.one_del.eq_2 (T.P 1 c d) (by intro s2 h; cases h)
                rw [hsdel, htdel]
                exact hst
            | inr htail =>
              have hpq : p = q := htail.1
              subst q
              cases p with
              | zero =>
                have hsIdx0 : T.index_Prop1 0 (T.P 0 a b) :=
                  isNF1_index 0 0 a b hsNF (Nat.le_refl 0)
                have htIdx0 : T.index_Prop1 0 (T.P 0 c d) :=
                  isNF1_index 0 0 c d htNF (Nat.le_refl 0)
                exact oc_one_del_lt_index0 (T.P 0 a b) (T.P 0 c d)
                  hsNF hsIdx0 (by intro h; cases h)
                  htNF htIdx0 (by intro h; cases h) hst
              | succ p' =>
                have hp'0 : p' = 0 :=
                  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hp)
                subst p'
                have hsdel : T.one_del (T.P 1 a b) = T.P 1 a b :=
                  T.one_del.eq_2 (T.P 1 a b) (by intro s2 h; cases h)
                have htdel : T.one_del (T.P 1 c d) = T.P 1 c d :=
                  T.one_del.eq_2 (T.P 1 c d) (by intro s2 h; cases h)
                rw [hsdel, htdel]
                exact hst

#print axioms oc_one_del_lt_index1

theorem oc_one_del_NF_index1 (s : T)
    (hs : T.isNF1 s) (hi : T.index_Prop1 1 s) :
    T.isNF1 (T.one_del s) ∧ T.index_Prop1 1 (T.one_del s) := by
  cases s with
  | Z =>
    have hne : ∀ s2 : T, T.Z = T.P 0 T.Z s2 → False := by
      intro s2 h
      cases h
    rw [T.one_del.eq_2 T.Z hne]
    exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P p a b =>
    have hp : p ≤ 1 := by
      cases hi with
      | p _ _ _ hp _ => exact hp
    cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hp) with
    | inl hp0 =>
      subst p
      have hi0 : T.index_Prop1 0 (T.P 0 a b) :=
        isNF1_index 0 0 a b hs (Nat.le_refl 0)
      have h0 := oc_one_del_NF_index0 (T.P 0 a b) hs hi0
      exact ⟨h0.1,
        Rank1Termination.index_mono (Nat.zero_le 1) (T.one_del (T.P 0 a b)) h0.2⟩
    | inr hp1 =>
      subst p
      have hne : ∀ s2 : T, T.P 1 a b = T.P 0 T.Z s2 → False := by
        intro s2 h
        cases h
      rw [T.one_del.eq_2 (T.P 1 a b) hne]
      exact ⟨hs, hi⟩

#print axioms oc_one_del_NF_index1
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


theorem c1_idx0_lt_outer1 (x m y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 m y := by
  cases x with
  | Z => exact T.Lt.Z_lt_P 1 m y
  | P p a b =>
    cases hx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      exact T.Lt.p_head 0 1 a m b y (Nat.zero_lt_succ 0)

#print axioms c1_idx0_lt_outer1
theorem c1_card_append_lt_index1 :
    ∀ s t x y : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.index_Prop1 0 x →
      T.add (T.card_times 1 s) x < T.add (T.card_times 1 t) y := by
  intro s
  induction s with
  | Z =>
    intro t x y hsNF hsIdx htNF htIdx hst hxIdx
    cases t with
    | Z => exact False.elim (lt_Z_inv hst)
    | P q e f =>
      have hqLe : q ≤ 1 := by
        cases htIdx with
        | p _ _ _ hq _ => exact hq
      rw [T.card_times.eq_1, T.add.eq_1]
      cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
      | inl hq0 =>
        subst q
        rw [c1_p0, T.P_add_eq]
        exact c1_idx0_lt_outer1 x (T.early_collapse e)
          (T.add (T.card_times 1 f) y) hxIdx
      | inr hq1 =>
        subst q
        rw [c1_p1, T.P_add_eq]
        exact c1_idx0_lt_outer1 x (T.P 1 T.Z e)
          (T.add (T.card_times 1 f) y) hxIdx
  | P p a b iha ihb =>
    intro t x y hsNF hsIdx htNF htIdx hst hxIdx
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
          rw [c1_p0, c1_p0, T.P_add_eq, T.P_add_eq]
          cases lt_inv 0 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 0 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hec : T.early_collapse a < T.early_collapse e :=
                bridge_early_collapse_lt a e haNF haG heNF heG hae
              exact T.Lt.p_mid 1 (T.early_collapse a) (T.early_collapse e)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hec
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f x y hbNF hbIdx hfNF hfIdx hbf hxIdx
              exact T.Lt.p_tail 1 (T.early_collapse a)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hrec
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          have hec := bridge_early_collapse_closed a haNF haG
          rw [c1_p0, c1_p1, T.P_add_eq, T.P_add_eq]
          have hmid : T.early_collapse a < T.P 1 T.Z e :=
            c1_idx0_lt_P1 (T.early_collapse a) e hec.2.1
          exact T.Lt.p_mid 1 (T.early_collapse a) (T.P 1 T.Z e)
            (T.add (T.card_times 1 b) x)
            (T.add (T.card_times 1 f) y) hmid
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
          rw [c1_p1, c1_p1, T.P_add_eq, T.P_add_eq]
          cases lt_inv 1 a b 1 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hinner : T.P 1 T.Z a < T.P 1 T.Z e :=
                T.Lt.p_tail 1 T.Z a e hae
              exact T.Lt.p_mid 1 (T.P 1 T.Z a) (T.P 1 T.Z e)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hinner
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f x y hbNF hbIdx hfNF hfIdx hbf hxIdx
              exact T.Lt.p_tail 1 (T.P 1 T.Z a)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hrec

#print axioms c1_card_append_lt_index1

theorem oc_principal_lt_true_true {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (hv : ∀ x : new.T (k + 1), x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T (k + 1), x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T (k + 1),
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt)
    (sv av sw aw : T)
    (hav : transAux v = (true, sv, av))
    (haw : transAux w = (true, sw, aw)) :
    _root_.trans (new.T.P v new.T.Z) < _root_.trans (new.T.P w new.T.Z) := by
  have hlex := ao_transAux_lex v w hv hw hmono hcmp
    true true sv av sw aw hav haw
  have hiv := tc_transAux_inv v hv true sv av hav
  have hiw := tc_transAux_inv w hw true sw aw haw
  have hsvne : sv ≠ T.Z := hiv.2.2.2.2.2.2.1 rfl
  have hswne : sw ≠ T.Z := hiw.2.2.2.2.2.2.1 rfl
  have havEC := bridge_early_collapse_closed av hiv.1 hiv.2.1
  have hawEC := bridge_early_collapse_closed aw hiw.1 hiw.2.1
  rw [_root_.trans.eq_2, hav, _root_.trans.eq_1]
  rw [_root_.trans.eq_2, haw, _root_.trans.eq_1]
  change T.P 1
      (T.add (T.card_times 1 (T.one_del sv)) (T.early_collapse av)) T.Z <
    T.P 1
      (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw)) T.Z
  cases hlex with
  | inl hsum =>
      have hsvDel := oc_one_del_NF_index1 sv hiv.2.2.1 hiv.2.2.2.1
      have hswDel := oc_one_del_NF_index1 sw hiw.2.2.1 hiw.2.2.2.1
      have hdel : T.one_del sv < T.one_del sw :=
        oc_one_del_lt_index1 sv sw
          hiv.2.2.1 hiv.2.2.2.1 hsvne
          hiw.2.2.1 hiw.2.2.2.1 hswne hsum
      have hmid :
          T.add (T.card_times 1 (T.one_del sv)) (T.early_collapse av) <
          T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw) :=
        c1_card_append_lt_index1 (T.one_del sv) (T.one_del sw)
          (T.early_collapse av) (T.early_collapse aw)
          hsvDel.1 hsvDel.2 hswDel.1 hswDel.2 hdel havEC.2.1
      exact T.Lt.p_mid 1 _ _ T.Z T.Z hmid
  | inr heq =>
      have hsumEq : sv = sw := heq.1
      have ha0lt : av < aw := heq.2
      subst sw
      have hec : T.early_collapse av < T.early_collapse aw :=
        bridge_early_collapse_lt av aw hiv.1 hiv.2.1 hiw.1 hiw.2.1 ha0lt
      have hmid := bridge_add_left_lt (T.card_times 1 (T.one_del sv))
        (T.early_collapse av) (T.early_collapse aw) hec
      exact T.Lt.p_mid 1 _ _ T.Z T.Z hmid

#print axioms oc_principal_lt_true_true

theorem oc_full_lt_false_false {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (a b : new.T (k + 1))
    (hv : ∀ x : new.T (k + 1), x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T (k + 1), x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T (k + 1),
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt)
    (sv av sw aw : T)
    (hav : transAux v = (false, sv, av))
    (haw : transAux w = (false, sw, aw)) :
    _root_.trans (new.T.P v a) < _root_.trans (new.T.P w b) := by
  have ha0lt := oc_false_false_a0_lt v w hv hw hmono hcmp sv av sw aw hav haw
  rw [_root_.trans.eq_2, hav]
  rw [_root_.trans.eq_2, haw]
  change
    (if av = T.Z then T.P 0 T.Z (trans a) else T.P 0 av (trans a)) <
      (if aw = T.Z then T.P 0 T.Z (trans b) else T.P 0 aw (trans b))
  by_cases havz : av = T.Z
  · subst av
    rw [ite_eq_left rfl]
    by_cases hawz : aw = T.Z
    · subst aw
      exact False.elim (lt_irrefl_thm T.Z ha0lt)
    · rw [ite_eq_right hawz]
      exact T.Lt.p_mid 0 T.Z aw (trans a) (trans b) ha0lt
  · rw [ite_eq_right havz]
    have hawz : aw ≠ T.Z := by
      intro heq
      rw [heq] at ha0lt
      exact lt_Z_inv ha0lt
    rw [ite_eq_right hawz]
    exact T.Lt.p_mid 0 av aw (trans a) (trans b) ha0lt

#print axioms oc_full_lt_false_false

theorem oc_full_lt_false_true {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (a b : new.T (k + 1))
    (sv av sw aw : T)
    (hav : transAux v = (false, sv, av))
    (haw : transAux w = (true, sw, aw)) :
    _root_.trans (new.T.P v a) < _root_.trans (new.T.P w b) := by
  rw [_root_.trans.eq_2, hav]
  rw [_root_.trans.eq_2, haw]
  change
    (if av = T.Z then T.P 0 T.Z (trans a) else T.P 0 av (trans a)) <
      T.P 1 (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw)) (trans b)
  by_cases havz : av = T.Z
  · rw [ite_eq_left havz]
    exact T.Lt.p_head 0 1 T.Z
      (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw))
      (trans a) (trans b) (Nat.zero_lt_succ 0)
  · rw [ite_eq_right havz]
    exact T.Lt.p_head 0 1 av
      (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw))
      (trans a) (trans b) (Nat.zero_lt_succ 0)

#print axioms oc_full_lt_false_true

theorem oc_full_lt_true_true {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (a b : new.T (k + 1))
    (hv : ∀ x : new.T (k + 1), x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T (k + 1), x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T (k + 1),
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt)
    (sv av sw aw : T)
    (hav : transAux v = (true, sv, av))
    (haw : transAux w = (true, sw, aw)) :
    _root_.trans (new.T.P v a) < _root_.trans (new.T.P w b) := by
  have hlex := ao_transAux_lex v w hv hw hmono hcmp
    true true sv av sw aw hav haw
  have hiv := tc_transAux_inv v hv true sv av hav
  have hiw := tc_transAux_inv w hw true sw aw haw
  have hsvne : sv ≠ T.Z := hiv.2.2.2.2.2.2.1 rfl
  have hswne : sw ≠ T.Z := hiw.2.2.2.2.2.2.1 rfl
  have havEC := bridge_early_collapse_closed av hiv.1 hiv.2.1
  rw [_root_.trans.eq_2, hav]
  rw [_root_.trans.eq_2, haw]
  change T.P 1
      (T.add (T.card_times 1 (T.one_del sv)) (T.early_collapse av)) (trans a) <
    T.P 1
      (T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw)) (trans b)
  cases hlex with
  | inl hsum =>
      have hsvDel := oc_one_del_NF_index1 sv hiv.2.2.1 hiv.2.2.2.1
      have hswDel := oc_one_del_NF_index1 sw hiw.2.2.1 hiw.2.2.2.1
      have hdel : T.one_del sv < T.one_del sw :=
        oc_one_del_lt_index1 sv sw
          hiv.2.2.1 hiv.2.2.2.1 hsvne
          hiw.2.2.1 hiw.2.2.2.1 hswne hsum
      have hmid :
          T.add (T.card_times 1 (T.one_del sv)) (T.early_collapse av) <
          T.add (T.card_times 1 (T.one_del sw)) (T.early_collapse aw) :=
        c1_card_append_lt_index1 (T.one_del sv) (T.one_del sw)
          (T.early_collapse av) (T.early_collapse aw)
          hsvDel.1 hsvDel.2 hswDel.1 hswDel.2 hdel havEC.2.1
      exact T.Lt.p_mid 1 _ _ (trans a) (trans b) hmid
  | inr heq =>
      have hsumEq : sv = sw := heq.1
      have ha0lt : av < aw := heq.2
      subst sw
      have hec : T.early_collapse av < T.early_collapse aw :=
        bridge_early_collapse_lt av aw hiv.1 hiv.2.1 hiw.1 hiw.2.1 ha0lt
      have hmid := bridge_add_left_lt (T.card_times 1 (T.one_del sv))
        (T.early_collapse av) (T.early_collapse aw) hec
      exact T.Lt.p_mid 1 _ _ (trans a) (trans b) hmid

#print axioms oc_full_lt_true_true

theorem oc_full_lt_of_compareVec {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (a b : new.T (k + 1))
    (hv : ∀ x : new.T (k + 1), x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T (k + 1), x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T (k + 1),
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt) :
    trans (new.T.P v a) < trans (new.T.P w b) := by
  cases hav : transAux v with
  | mk fv rav =>
    cases rav with
    | mk sv av =>
      cases haw : transAux w with
      | mk fw raw =>
        cases raw with
        | mk sw aw =>
          cases fv with
          | false =>
            cases fw with
            | false =>
              exact oc_full_lt_false_false v w a b hv hw hmono hcmp
                sv av sw aw hav haw
            | true =>
              exact oc_full_lt_false_true v w a b sv av sw aw hav haw
          | true =>
            cases fw with
            | false =>
              exact False.elim
                (oc_true_false_absurd v w hv hw hmono hcmp
                  sv av sw aw hav haw)
            | true =>
              exact oc_full_lt_true_true v w a b hv hw hmono hcmp
                sv av sw aw hav haw

#print axioms oc_full_lt_of_compareVec

theorem oc_full_lt_of_compareVec_general {lam : Nat}
    (v w : new.Vec (new.T lam) lam)
    (a b : new.T lam)
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧ (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
      x < y → trans x < trans y)
    (hcmp : new.compareVec v w = Ordering.lt) :
    trans (new.T.P v a) < trans (new.T.P w b) := by
  cases lam with
  | zero =>
    cases v with
    | nil =>
      cases w with
      | nil =>
        change Ordering.eq = Ordering.lt at hcmp
        cases hcmp
  | succ k =>
    exact oc_full_lt_of_compareVec v w a b hv hw hmono hcmp

#print axioms oc_full_lt_of_compareVec_general

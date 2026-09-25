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


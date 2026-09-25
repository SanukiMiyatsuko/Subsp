import Subsp.new.stop_order_cases_card

open T

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

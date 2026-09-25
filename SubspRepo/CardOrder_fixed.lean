import AuxOrder
import CardAux
import ShiftFinal

open T

theorem co_len1_sum_zero {lam : Nat}
    (v : new.Vec (new.T lam) 1) (f : Bool) (s a0 : T)
    (h : transAux v = (f, s, a0)) : s = T.Z := by
  cases v with
  | @snoc n xs a =>
    cases xs with
    | nil =>
      rw [transAux.eq_2] at h
      cases h
      rfl

#print axioms co_len1_sum_zero

theorem co_transAux_card1_lex {lam : Nat} :
    ∀ {k : Nat} (v w : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x : new.T lam, x ∈ new.Vec.toList w →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x y : new.T lam,
        x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
        x < y → trans x < trans y) →
      new.compareVec v w = Ordering.lt →
      ∀ fv fw : Bool, ∀ sv av sw aw : T,
        transAux v = (fv, sv, av) →
        transAux w = (fw, sw, aw) →
        T.card_times 1 sv < T.card_times 1 sw ∨
          (T.card_times 1 sv = T.card_times 1 sw ∧ av < aw) := by
  intro k
  induction k with
  | zero =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      have hlex := ao_transAux_lex v w hv hw hmono hcmp
        fv fw sv av sw aw hav haw
      have hsv : sv = T.Z := co_len1_sum_zero v fv sv av hav
      have hsw : sw = T.Z := co_len1_sum_zero w fw sw aw haw
      cases hlex with
      | inl hslt =>
        rw [hsv, hsw] at hslt
        exact False.elim (lt_irrefl_thm T.Z hslt)
      | inr heq =>
        apply Or.inr
        constructor
        · rw [hsv, hsw]
        · exact heq.2
  | succ m ih =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases w with
        | @snoc nw xw b =>
          change
            (match new.compareT a b with
            | Ordering.eq => new.compareVec xv xw
            | ord => ord) = Ordering.lt at hcmp
          have hvrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xv →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hv x (List.mem_append_left [a] hx)
          have hwrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xw →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hw x (List.mem_append_left [b] hx)
          have ha := hv a
            (List.mem_append_right (new.Vec.toList xv) (List.mem_singleton.mpr rfl))
          have hb := hw b
            (List.mem_append_right (new.Vec.toList xw) (List.mem_singleton.mpr rfl))
          have hmonoRest :
              ∀ x y : new.T lam,
                x ∈ new.Vec.toList xv → y ∈ new.Vec.toList xw →
                x < y → trans x < trans y := by
            intro x y hx hy hxy
            exact hmono x y
              (List.mem_append_left [a] hx)
              (List.mem_append_left [b] hy) hxy
          cases havrest : transAux xv with
          | mk fvr pr =>
            cases pr with
            | mk svr avr =>
              cases hawrest : transAux xw with
              | mk fwr qr =>
                cases qr with
                | mk swr awr =>
                  rw [transAux.eq_3, havrest] at hav
                  rw [transAux.eq_3, hawrest] at haw
                  cases hca : new.compareT a b with
                  | lt =>
                    rw [hca] at hcmp
                    have htab : trans a < trans b := by
                      exact hmono a b
                        (List.mem_append_right (new.Vec.toList xv)
                          (List.mem_singleton.mpr rfl))
                        (List.mem_append_right (new.Vec.toList xw)
                          (List.mem_singleton.mpr rfl)) hca
                    have hec : T.early_collapse (trans a) < T.early_collapse (trans b) :=
                      bridge_early_collapse_lt (trans a) (trans b)
                        ha.1 ha.2 hb.1 hb.2 htab
                    have heca := bridge_early_collapse_closed (trans a) ha.1 ha.2
                    have hecb := bridge_early_collapse_closed (trans b) hb.1 hb.2
                    have invr := sc_transAux_card1_inv xv hvrest fvr svr avr havrest
                    cases hav
                    cases haw
                    cases m with
                    | zero =>
                      have hsv : svr = T.Z := co_len1_sum_zero xv fvr svr av havrest
                      have hsw : swr = T.Z := co_len1_sum_zero xw fwr swr aw hawrest
                      rw [hsv, hsw]
                      rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                      rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                      apply Or.inl
                      exact bridge_card_times_lt_same 1
                        (T.early_collapse (trans a)) (T.early_collapse (trans b))
                        heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                    | succ j =>
                      rw [← add_eq_hAdd]
                      rw [← add_eq_hAdd]
                      rw [ca_card_times_add, ca_card_times_one_comp]
                      rw [ca_card_times_add, ca_card_times_one_comp]
                      apply Or.inl
                      apply wt_card_append_lt (j + 2)
                        (T.early_collapse (trans a)) (T.early_collapse (trans b))
                        (T.card_times 1 svr) (T.card_times 1 swr)
                        heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                      exact invr.2.2.2
                  | gt =>
                    rw [hca] at hcmp
                    cases hcmp
                  | eq =>
                    rw [hca] at hcmp
                    have habEq : a = b := new.T_eq_sound a b hca
                    subst b
                    have hrec := ih xv xw hvrest hwrest hmonoRest hcmp
                      fvr fwr svr avr swr awr havrest hawrest
                    cases hav
                    cases haw
                    cases a with
                    | Z =>
                      change
                        T.card_times 1 svr < T.card_times 1 swr ∨
                          (T.card_times 1 svr = T.card_times 1 swr ∧ av < aw)
                      exact hrec
                    | P als aadd =>
                      cases m with
                      | zero =>
                        have hsv : svr = T.Z := co_len1_sum_zero xv fvr svr av havrest
                        have hsw : swr = T.Z := co_len1_sum_zero xw fwr swr aw hawrest
                        cases hrec with
                        | inl hbad =>
                          rw [hsv, hsw] at hbad
                          exact False.elim (lt_irrefl_thm T.Z hbad)
                        | inr hr =>
                          apply Or.inr
                          constructor
                          · rw [hsv, hsw]
                          · exact hr.2
                      | succ j =>
                        rw [← add_eq_hAdd]
                        rw [← add_eq_hAdd]
                        rw [ca_card_times_add, ca_card_times_one_comp]
                        rw [ca_card_times_add, ca_card_times_one_comp]
                        cases hrec with
                        | inl hr =>
                          apply Or.inl
                          exact bridge_add_left_lt
                            (T.card_times (j + 2)
                              (T.early_collapse (trans (new.T.P als aadd))))
                            (T.card_times 1 svr) (T.card_times 1 swr) hr
                        | inr hr =>
                          apply Or.inr
                          constructor
                          · rw [hr.1]
                          · exact hr.2

#print axioms co_transAux_card1_lex

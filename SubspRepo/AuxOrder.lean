import Weighted
import AuxCore

open T

theorem ao_transAux_lex {lam : Nat} :
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
        sv < sw ∨ (sv = sw ∧ av < aw) := by
  intro k
  induction k with
  | zero =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases xv with
        | nil =>
          cases w with
          | @snoc nw xw b =>
            cases xw with
            | nil =>
              rw [new.compareVec.eq_2] at hcmp
              cases hca : new.compareT a b with
              | lt =>
                rw [transAux.eq_2] at hav
                rw [transAux.eq_2] at haw
                cases hav
                cases haw
                apply Or.inr
                constructor
                · rfl
                · apply hmono a b
                  · exact List.mem_singleton.mpr rfl
                  · exact List.mem_singleton.mpr rfl
                  · exact hca
              | eq =>
                rw [hca, new.compareVec.eq_1] at hcmp
                cases hcmp
              | gt =>
                rw [hca] at hcmp
                cases hcmp
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
                    have hab : a < b := hca
                    have htab : trans a < trans b := by
                      exact hmono a b
                        (List.mem_append_right (new.Vec.toList xv)
                          (List.mem_singleton.mpr rfl))
                        (List.mem_append_right (new.Vec.toList xw)
                          (List.mem_singleton.mpr rfl)) hab
                    have hec : T.early_collapse (trans a) < T.early_collapse (trans b) :=
                      bridge_early_collapse_lt (trans a) (trans b)
                        ha.1 ha.2 hb.1 hb.2 htab
                    have heca := bridge_early_collapse_closed (trans a) ha.1 ha.2
                    have hecb := bridge_early_collapse_closed (trans b) hb.1 hb.2
                    have invr := tc_transAux_inv xv hvrest fvr svr avr havrest
                    have hsum :
                        T.add (T.card_times m (T.early_collapse (trans a))) svr <
                          T.add (T.card_times m (T.early_collapse (trans b))) swr := by
                      apply wt_card_append_lt m
                        (T.early_collapse (trans a)) (T.early_collapse (trans b))
                        svr swr heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                      exact invr.2.2.2.2.2.1
                    cases hav
                    cases haw
                    exact Or.inl hsum
                  | gt =>
                    rw [hca] at hcmp
                    cases hcmp
                  | eq =>
                    rw [hca] at hcmp
                    have habEq : a = b := new.T_eq_sound a b hca
                    subst b
                    have hrec := ih xv xw hvrest hwrest hmonoRest hcmp
                      fvr fwr svr avr swr awr havrest hawrest
                    cases hrec with
                    | inl hsumRest =>
                      cases hav
                      cases haw
                      apply Or.inl
                      exact bridge_add_left_lt
                        (T.card_times m (T.early_collapse (trans a)))
                        svr swr hsumRest
                    | inr heqrest =>
                      cases hav
                      cases haw
                      apply Or.inr
                      constructor
                      · rw [heqrest.1]
                      · exact heqrest.2

#print axioms ao_transAux_lex

import Subsp.new.stop_nf_core

open T

theorem spg_tail_lt_of_NF1 (p : Nat) (a b : T)
    (h : T.isNF1 (T.P p a b)) : b < T.P p a b := by
  have hle := T.isNF1_tail_le (T.P p a b) h p a b rfl
  cases hle with
  | inl hlt => exact hlt
  | inr heq =>
      have hsz : b.size < (T.P p a b).size := T.size_lt_size_P_right p a b
      have hszeq : b.size = (T.P p a b).size := congrArg T.size heq
      exact False.elim ((Nat.ne_of_lt hsz) hszeq)

#print axioms spg_tail_lt_of_NF1

theorem spg_card1_support_wrap : ∀ c : T,
    T.isNF1 c → T.index_Prop1 0 c →
    ∀ x : T, x ∈ T.G1 0 (T.card_times 1 c) →
      x < T.P 1 (T.card_times 1 c) T.Z := by
  intro c
  induction c with
  | Z =>
      intro hc hi x hx
      rw [T.card_times.eq_1, T.G1.eq_1] at hx
      cases hx
  | P p a b iha ihb =>
      intro hc hi x hx
      cases hi with
      | p _ _ _ hp hib =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hc
          have hec := bridge_early_collapse_closed a haNF haG
          have htail := bridge_card_times_closed 1 b hbNF hib
          rw [T.card_times.eq_3, ite_eq_left rfl] at hx ⊢
          rw [T.ofNat.eq_1, T.mul.eq_1] at hx ⊢
          have hzero : T.Z + T.early_collapse a = T.early_collapse a := rfl
          rw [hzero] at hx ⊢
          have houter :
              T.P 1 (T.early_collapse a) T.Z + T.card_times 1 b =
                T.P 1 (T.early_collapse a) (T.card_times 1 b) := by
            rw [T.P_add_eq]
            rfl
          rw [houter] at hx ⊢
          change x ∈ T.G1 0 (T.P 1 (T.early_collapse a) (T.card_times 1 b)) at hx
          change x < T.P 1 (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1), List.mem_append, List.mem_append] at hx
          cases hx with
          | inl hleft =>
              cases hleft with
              | inl hsingle =>
                  have heq : x = T.early_collapse a := List.mem_singleton.mp hsingle
                  rw [heq]
                  exact c1_idx0_lt_outer1 (T.early_collapse a)
                    (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z hec.2.1
              | inr hgec =>
                  have hxe : x < T.early_collapse a := hec.2.2 x hgec
                  have hew : T.early_collapse a <
                      T.P 1 (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z :=
                    c1_idx0_lt_outer1 (T.early_collapse a)
                      (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z hec.2.1
                  exact lt_trans_thm x (T.early_collapse a) _ hxe hew
          | inr hxr =>
              have hxwrap : x < T.P 1 (T.card_times 1 b) T.Z :=
                ihb hbNF hib x hxr
              have hRlt : T.card_times 1 b <
                  T.P 1 (T.early_collapse a) (T.card_times 1 b) :=
                spg_tail_lt_of_NF1 1 (T.early_collapse a) (T.card_times 1 b)
                  (T.isNF1.p 1 (T.early_collapse a) (T.card_times 1 b)
                    hec.1 htail.1 hec.2.2
                    (by
                      cases b with
                      | Z =>
                          rw [T.card_times.eq_1, T.head]
                          exact T.Z_le _
                      | P q d e =>
                          cases hib with
                          | p _ _ _ hq hie =>
                              have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
                              subst q
                              obtain ⟨hdNF, heNF, hdG, hhe⟩ := T.isNF1_P_inv 0 d e hbNF
                              have hda : d ≤ a := bridge_P0_head_mid_le a d e hheadb
                              have hdc := bridge_early_collapse_closed d hdNF hdG
                              have hle := bridge_early_collapse_le d a hdNF hdG haNF haG hda
                              rw [T.card_times.eq_3, ite_eq_left rfl,
                                T.ofNat.eq_1, T.mul.eq_1, T.add.eq_1, T.head]
                              exact bridge_lift_P1_le _ _ hle))
              have hLift : T.P 1 (T.card_times 1 b) T.Z <
                  T.P 1 (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z :=
                T.Lt.p_mid 1 (T.card_times 1 b)
                  (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z T.Z hRlt
              exact lt_trans_thm x _ _ hxwrap hLift

#print axioms spg_card1_support_wrap

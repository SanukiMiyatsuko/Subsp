import Subsp.new.stop_solve_good

open T

theorem gc_tail_lt_of_NF1 (p : Nat) (a b : T)
    (h : T.isNF1 (T.P p a b)) : b < T.P p a b := by
  have hle := T.isNF1_tail_le (T.P p a b) h p a b rfl
  cases hle with
  | inl hlt => exact hlt
  | inr heq =>
      have hsz : b.size < (T.P p a b).size := T.size_lt_size_P_right p a b
      have hszeq : b.size = (T.P p a b).size := congrArg T.size heq
      exact False.elim ((Nat.ne_of_lt hsz) hszeq)

#print axioms gc_tail_lt_of_NF1

theorem gc_card1_support_map : ∀ c : T,
    T.isNF1 c → T.index_Prop1 0 c →
    ∀ x : T, x ∈ T.G1 0 (T.card_times 1 c) →
      x < T.P 1 (T.card_times 1 c) T.Z ∨
        ∃ z : T, z ∈ T.G1 0 c ∧ x ≤ z := by
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
          rw [c1_p0] at hx ⊢
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
            List.mem_append, List.mem_append] at hx
          cases hx with
          | inl hleft =>
              cases hleft with
              | inl hsingle =>
                  have heq : x = T.early_collapse a := List.mem_singleton.mp hsingle
                  rw [heq]
                  exact Or.inl (c1_idx0_lt_outer1 (T.early_collapse a)
                    (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z hec.2.1)
              | inr hgec =>
                  have hxa : x ≤ a := sg_early_G0_le a haNF haG x hgec
                  apply Or.inr
                  refine ⟨a, ?_, hxa⟩
                  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                  exact List.mem_append_left (T.G1 0 b)
                    (List.mem_append_left (T.G1 0 a)
                      (List.mem_singleton_self a))
          | inr htail =>
              have hrec := ihb hbNF hib x htail
              cases hrec with
              | inl hwrap =>
                  have hcardNF := bridge_card_times_closed 1 (T.P 0 a b) hc
                    (T.index_Prop1.p 0 a b (Nat.le_refl 0) hib)
                  rw [c1_p0] at hcardNF
                  have htailLt : T.card_times 1 b <
                      T.P 1 (T.early_collapse a) (T.card_times 1 b) :=
                    gc_tail_lt_of_NF1 1 (T.early_collapse a)
                      (T.card_times 1 b) hcardNF.1
                  have hlift : T.P 1 (T.card_times 1 b) T.Z <
                      T.P 1 (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z :=
                    T.Lt.p_mid 1 (T.card_times 1 b)
                      (T.P 1 (T.early_collapse a) (T.card_times 1 b)) T.Z T.Z htailLt
                  exact Or.inl (lt_trans_thm x _ _ hwrap hlift)
              | inr hwit =>
                  obtain ⟨z, hz, hxz⟩ := hwit
                  apply Or.inr
                  refine ⟨z, ?_, hxz⟩
                  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                  exact List.mem_append_right ([a] ++ T.G1 0 a) hz

#print axioms gc_card1_support_map

import GoodCore1
import SupportWork

open T

theorem cs_self_lt_wrap (c : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 1 c)
    (hcG : ∀ x : T, x ∈ T.G1 1 c → x < c) :
    c < T.P 1 c T.Z := by
  cases c with
  | Z =>
      exact T.Lt.Z_lt_P 1 T.Z T.Z
  | P p a b =>
      cases hcIdx with
      | p _ _ _ hp hib =>
          cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hp) with
          | inl hp0 =>
              subst p
              exact T.Lt.p_head 0 1 a (T.P 0 a b) b T.Z
                (Nat.zero_lt_succ 0)
          | inr hp1 =>
              subst p
              have haMem : a ∈ T.G1 1 (T.P 1 a b) := by
                rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1)]
                exact List.mem_append_left (T.G1 1 b)
                  (List.mem_append_left (T.G1 1 a)
                    (List.mem_singleton_self a))
              have haLt : a < T.P 1 a b := hcG a haMem
              exact T.Lt.p_mid 1 a (T.P 1 a b) b T.Z haLt

#print axioms cs_self_lt_wrap

theorem cs_card_support (n : Nat) : ∀ c s : T,
    T.isNF1 c → T.index_Prop1 0 c →
    (∀ x : T, x ∈ T.G1 0 c → x ≤ s) →
    ∀ x : T, x ∈ T.G1 0 (T.card_times (n + 1) c) →
      x < T.P 1 (T.card_times (n + 1) c) T.Z ∨ x ≤ s := by
  intro c
  induction c with
  | Z =>
      intro s hcNF hcIdx hsupp x hx
      rw [T.card_times.eq_1, T.G1.eq_1] at hx
      cases hx
  | P p a b iha ihb =>
      intro s hcNF hcIdx hsupp x hx
      cases hcIdx with
      | p _ _ _ hp hib =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          have hec := bridge_early_collapse_closed a haNF haG
          have hcard := bridge_card_times_closed (n + 1) (T.P 0 a b)
            hcNF (T.index_Prop1.p 0 a b (Nat.le_refl 0) hib)
          rw [T.card_times.eq_3, ite_eq_left rfl] at hx hcard ⊢
          let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
            (T.early_collapse a)
          change x ∈ T.G1 0
            (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) at hx
          change
            x < T.P 1
              (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) T.Z ∨
              x ≤ s
          rw [T.P_add_eq, T.add.eq_1] at hx ⊢
          rw [← add_eq_hAdd, T.P_add_eq, T.add.eq_1] at hcard
          let C := T.P 1 M (T.card_times (n + 1) b)
          change T.isNF1 C ∧ T.index_Prop1 1 C ∧
            (∀ y : T, y ∈ T.G1 1 C → y < C) at hcard
          have hCwrap : C < T.P 1 C T.Z := by
            exact cs_self_lt_wrap C hcard.1 hcard.2.1 hcard.2.2
          change x ∈ T.G1 0 C at hx
          change x < T.P 1 C T.Z ∨ x ≤ s
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
            List.mem_append, List.mem_append] at hx
          cases hx with
          | inl hleft =>
              cases hleft with
              | inl hM =>
                  have hxM : x = M := List.mem_singleton.mp hM
                  rw [hxM]
                  have hMC : M < C := by
                    unfold C M
                    exact bridge_shift_lt_outer n (T.early_collapse a)
                      (T.card_times (n + 1) b) hec.2.1
                  exact Or.inl (lt_trans_thm M C (T.P 1 C T.Z) hMC hCwrap)
              | inr hGM =>
                  have hshift := sw_shift_support n (T.early_collapse a) a
                    (T.card_times (n + 1) b) hec.2.1
                    (sg_early_G0_le a haNF haG) x hGM
                  cases hshift with
                  | inl hxC =>
                      exact Or.inl (lt_trans_thm x C (T.P 1 C T.Z) hxC hCwrap)
                  | inr hxa =>
                      have haMem : a ∈ T.G1 0 (T.P 0 a b) := by
                        rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                        exact List.mem_append_left (T.G1 0 b)
                          (List.mem_append_left (T.G1 0 a)
                            (List.mem_singleton_self a))
                      exact Or.inr (partial_order.trans x a s hxa (hsupp a haMem))
          | inr htail =>
              have hsuppB : ∀ y : T, y ∈ T.G1 0 b → y ≤ s := by
                intro y hy
                apply hsupp y
                rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                exact List.mem_append_right ([a] ++ T.G1 0 a) hy
              have hrec := ihb s hbNF hib hsuppB x htail
              cases hrec with
              | inr hxs => exact Or.inr hxs
              | inl hxwrap =>
                  have htailNF := (bridge_card_times_closed (n + 1) b hbNF hib).1
                  have htailLt : T.card_times (n + 1) b < C := by
                    unfold C
                    exact gc_tail_lt_of_NF1 1 M (T.card_times (n + 1) b) hcard.1
                  have hlift :
                      T.P 1 (T.card_times (n + 1) b) T.Z < T.P 1 C T.Z :=
                    T.Lt.p_mid 1 (T.card_times (n + 1) b) C T.Z T.Z htailLt
                  exact Or.inl (lt_trans_thm x
                    (T.P 1 (T.card_times (n + 1) b) T.Z)
                    (T.P 1 C T.Z) hxwrap hlift)

#print axioms cs_card_support

theorem cs_one_del_G0 (s x : T)
    (hx : x ∈ T.G1 0 (T.one_del s)) :
    x ∈ T.G1 0 s := by
  cases s with
  | Z =>
      rw [T.one_del.eq_2 T.Z (by intro y h; cases h)] at hx
      exact hx
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z =>
              change x ∈ T.G1 0 b at hx
              rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
              exact List.mem_append_right ([T.Z] ++ T.G1 0 T.Z) hx
          | P q c d =>
              change x ∈ T.G1 0 (T.P 0 (T.P q c d) b) at hx
              exact hx
      | succ p =>
          change x ∈ T.G1 0 (T.P (p + 1) a b) at hx
          exact hx

#print axioms cs_one_del_G0

theorem cs_one_del_card_succ_add (k : Nat) (c y : T)
    (hcIdx : T.index_Prop1 0 c) (hcNe : c ≠ T.Z) :
    T.one_del (T.add (T.card_times (k + 1) c) y) =
      T.add (T.card_times (k + 1) c) y := by
  cases c with
  | Z => exact False.elim (hcNe rfl)
  | P p a b =>
      cases hcIdx with
      | p _ _ _ hp hbIdx =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          rw [T.card_times.eq_3, ite_eq_left rfl]
          rw [← add_eq_hAdd]
          rw [Rank1Termination.add_assoc]
          rw [T.P_add_eq, T.add]
          rfl

#print axioms cs_one_del_card_succ_add

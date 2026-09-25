import Subsp.new.stop_nf_core

open T

theorem sw_shift_support (k : Nat) (c s tail : T)
    (hc : T.index_Prop1 0 c)
    (hsupp : ∀ x : T, x ∈ T.G1 0 c → x ≤ s) :
    ∀ x : T,
      x ∈ T.G1 0 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) →
        x < T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail ∨
          x ≤ s := by
  induction k with
  | zero =>
      intro x hx
      rw [T.ofNat, T.mul, T.add] at hx ⊢
      exact Or.inr (hsupp x hx)
  | succ k ih =>
      intro x hx
      rw [mul_succ_shape 1 T.Z k, T.P_add_eq] at hx ⊢
      rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
        List.mem_append, List.mem_append] at hx
      cases hx with
      | inl hleft =>
          cases hleft with
          | inl hz =>
              have hxz : x = T.Z := List.mem_singleton.mp hz
              rw [hxz]
              exact Or.inl (T.Lt.Z_lt_P 1 (T.P 1 T.Z
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)) tail)
          | inr hzG =>
              rw [T.G1.eq_1] at hzG
              cases hzG
      | inr htail =>
          have hrec := ih x htail
          cases hrec with
          | inl hlt =>
              have hmid :
                  T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
                    T.P 1 T.Z
                      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) :=
                bridge_shift_lt_wrap k c hc
              have hlift :
                  T.P 1
                      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail <
                    T.P 1
                      (T.P 1 T.Z
                        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)) tail :=
                T.Lt.p_mid 1 _ _ tail tail hmid
              exact Or.inl (lt_trans_thm x _ _ hlt hlift)
          | inr hs => exact Or.inr hs

#print axioms sw_shift_support

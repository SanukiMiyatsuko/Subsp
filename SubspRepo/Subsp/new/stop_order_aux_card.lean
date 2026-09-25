import Subsp.new.stop_order_aux_base

open T

theorem ca_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c with
  | Z => rfl
  | P p a b => rfl

theorem ca_card_times_add (n : Nat) (a b : T) :
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  induction a with
  | Z =>
    rw [T.add, T.card_times.eq_1, T.add]
  | P p x y ihx ihy =>
    cases b with
    | Z =>
      rw [T.add_Z, T.card_times.eq_1, T.add_Z]
    | P q c d =>
      rw [T.P_add_eq]
      cases n with
      | zero =>
        rw [ca_card_times_zero, ca_card_times_zero, ca_card_times_zero]
        rw [T.P_add_eq]
      | succ k =>
        rw [T.card_times.eq_3, T.card_times.eq_3, T.card_times.eq_3]
        rw [ihy]
        by_cases hp : p = 0
        · rw [← add_eq_hAdd]
          exact (Rank1Termination.add_assoc _ _ _).symm
        · rw [← add_eq_hAdd]
          exact (Rank1Termination.add_assoc _ _ _).symm

#print axioms ca_card_times_add

theorem ca_mul_P1_ofNat_succ (k : Nat) :
    T.add (T.P 1 T.Z T.Z)
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) =
    T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
  rw [T.ofNat.eq_2, T.mul.eq_2]
  rw [← add_eq_hAdd]
  rw [T.P_add_eq, T.add]
  exact (mul_add_shape 1 T.Z k).symm

#print axioms ca_mul_P1_ofNat_succ


theorem ca_PZ_add (p : Nat) (a b : T) :
    T.P p a T.Z + b = T.P p a b := by
  change T.add (T.P p a T.Z) b = T.P p a b
  rw [T.P_add_eq, T.add]

theorem ca_mul_P1_one :
    T.mul (T.P 1 T.Z T.Z) (T.ofNat 1) = T.P 1 T.Z T.Z := by
  rfl

theorem ca_card_times_one_comp (m : Nat) (c : T) :
    T.card_times 1 (T.card_times m c) = T.card_times (m + 1) c := by
  induction c with
  | Z =>
    rw [T.card_times.eq_1, T.card_times.eq_1, T.card_times.eq_1]
  | P p a b iha ihb =>
    cases m with
    | zero =>
      rw [ca_card_times_zero]
    | succ k =>
      rw [T.card_times.eq_3]
      let H :=
        if p = 0 then
          T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k) + T.early_collapse a) T.Z
        else
          T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) + a) T.Z
      change T.card_times 1 (T.add H (T.card_times (k + 1) b)) =
        T.card_times (k + 1 + 1) (T.P p a b)
      rw [ca_card_times_add, ihb]
      unfold H
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        rw [T.card_times.eq_3, ite_eq_right Nat.one_ne_zero]
        rw [T.card_times.eq_1, ca_PZ_add]
        rw [T.card_times.eq_3, ite_eq_left hp]
        rw [T.P_add_eq, T.add, ca_PZ_add]
        congr 1
        change
          T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) =
            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)))
              (T.early_collapse a)
        rw [ca_mul_P1_one]
        rw [← Rank1Termination.add_assoc]
        rw [ca_mul_P1_ofNat_succ]
      · rw [ite_eq_right hp]
        rw [T.card_times.eq_3, ite_eq_right Nat.one_ne_zero]
        rw [T.card_times.eq_1, ca_PZ_add]
        rw [T.card_times.eq_3, ite_eq_right hp]
        rw [T.P_add_eq, T.add, ca_PZ_add]
        congr 1
        change
          T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) =
            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1 + 1))) a
        rw [ca_mul_P1_one]
        rw [← Rank1Termination.add_assoc]
        rw [ca_mul_P1_ofNat_succ]

#print axioms ca_card_times_one_comp


-- From Weighted.lean

theorem wt_add_self_le (a z : T) : a ≤ T.add a z := by
  induction a with
  | Z =>
    rw [T.add]
    exact T.Z_le z
  | P p x y ihx ihy =>
    cases z with
    | Z =>
      rw [T.add_Z]
      exact Or.inr rfl
    | P q c d =>
      rw [T.P_add_eq]
      cases ihy with
      | inl hlt => exact Or.inl (T.Lt.p_tail p x y (T.add y (T.P q c d)) hlt)
      | inr heq =>
        exact Or.inr (congrArg (fun t => T.P p x t) heq)

#print axioms wt_add_self_le


theorem wt_expand_card_succ_add (k : Nat) (a b y : T) :
    T.add (T.card_times (k + 1) (T.P 0 a b)) y =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a))
        (T.add (T.card_times (k + 1) b) y) := by
  rw [T.card_times.eq_3, ite_eq_left rfl]
  rw [← add_eq_hAdd]
  rw [Rank1Termination.add_assoc]
  rw [T.P_add_eq, T.add]
  rfl

#print axioms wt_expand_card_succ_add

theorem wt_card_append_lt (n : Nat) :
    ∀ c d y z : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d →
      (∀ q : T, T.isNF1 q → T.index_Prop1 0 q → q ≠ T.Z →
        y < T.card_times n q) →
      T.add (T.card_times n c) y < T.add (T.card_times n d) z := by
  intro c
  induction c with
  | Z =>
    intro d y z hcNF hcIdx hdNF hdIdx hcd hy
    have hdNe : d ≠ T.Z := by
      intro heq
      rw [heq] at hcd
      exact lt_Z_inv hcd
    have hyD : y < T.card_times n d := hy d hdNF hdIdx hdNe
    have hle : T.card_times n d ≤ T.add (T.card_times n d) z :=
      wt_add_self_le (T.card_times n d) z
    rw [T.card_times.eq_1, T.add] 
    exact lt_of_lt_of_le_thm T y (T.card_times n d)
      (T.add (T.card_times n d) z) hyD hle
  | P p a b iha ihb =>
    intro d y z hcNF hcIdx hdNF hdIdx hcd hy
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      cases d with
      | Z => exact False.elim (lt_Z_inv hcd)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq hfIdx =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
          cases lt_inv 0 a b 0 e f hcd with
          | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
          | inr hor =>
            cases n with
            | zero =>
              rw [tc_card_times_zero, tc_card_times_zero]
              rw [T.P_add_eq, T.P_add_eq]
              cases hor with
              | inl hm =>
                exact T.Lt.p_mid 0 a e (T.add b y) (T.add f z) hm.2
              | inr ht =>
                have hae : a = e := ht.2.1
                subst e
                have hbf : b < f := ht.2.2
                have hrec := ihb f y z hbNF hbIdx hfNF hfIdx hbf hy
                rw [tc_card_times_zero, tc_card_times_zero] at hrec
                exact T.Lt.p_tail 0 a (T.add b y) (T.add f z) hrec
            | succ k =>
              rw [wt_expand_card_succ_add k a b y]
              rw [wt_expand_card_succ_add k e f z]
              cases hor with
              | inl hm =>
                have hec : T.early_collapse a < T.early_collapse e :=
                  bridge_early_collapse_lt a e haNF haG heNF heG hm.2
                have hmid := bridge_add_left_lt
                  (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a) (T.early_collapse e) hec
                exact T.Lt.p_mid 1 _ _ _ _ hmid
              | inr ht =>
                have hae : a = e := ht.2.1
                subst e
                have hbf : b < f := ht.2.2
                have hrec := ihb f y z hbNF hbIdx hfNF hfIdx hbf hy
                exact T.Lt.p_tail 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse a)) _ _ hrec

#print axioms wt_card_append_lt


-- From AuxOrder.lean


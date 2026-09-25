import EcMono
open T

theorem cb_middle_good0 (a b : T)
    (h : T.isNF1 (T.P 0 a b)) :
    T.isNF1 a ∧ (∀ x : T, x ∈ T.G1 0 a → x < a) := by
  have hi := T.isNF1_P_inv 0 a b h
  exact ⟨hi.1, hi.2.2.1⟩

theorem cb_index0_head {s : T} (hi : T.index_Prop1 0 s) :
    T.index_Prop1 0 (T.head s) := by
  cases s with
  | Z => exact T.index_Prop1.z
  | P p a b =>
      cases hi with
      | p _ _ _ hp _ =>
        exact T.index_Prop1.p p a T.Z hp T.index_Prop1.z

theorem cb_card_times_mono (n : Nat) : ∀ s t : T,
    T.isNF1 s → T.isNF1 t →
    T.index_Prop1 0 s → T.index_Prop1 0 t →
    s < t → T.card_times n s < T.card_times n t := by
  intro s
  induction s with
  | Z =>
      intro t hs ht his hit hst
      rw [T.card_times]
      have htne : t ≠ T.Z := by
        intro h
        rw [h] at hst
        exact lt_Z_inv hst
      have hctne : T.card_times n t ≠ T.Z :=
        bridge_card_times_ne_Z n t htne
      cases hct : T.card_times n t with
      | Z => exact False.elim (hctne hct)
      | P p a b => exact T.Lt.Z_lt_P p a b
  | P p a b iha ihb =>
      intro t hs ht his hit hst
      cases his with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        cases t with
        | Z => cases hst
        | P q c d =>
          cases hit with
          | p _ _ _ hq hid =>
            have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
            subst q
            cases n with
            | zero =>
                rw [T.card_times, T.card_times]
                exact hst
            | succ k =>
                rw [T.card_times, T.card_times,
                  ite_eq_left rfl, ite_eq_left rfl]
                change T.add
                    (T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a)) T.Z)
                    (T.card_times (k + 1) b) <
                  T.add
                    (T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse c)) T.Z)
                    (T.card_times (k + 1) d)
                rw [T.P_add_eq, T.P_add_eq, T.add]
                have hsa := cb_middle_good0 a b hs
                have htc := cb_middle_good0 c d ht
                cases lt_inv 0 a b 0 c d hst with
                | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
                | inr hor =>
                    cases hor with
                    | inl hm =>
                        have hec : T.early_collapse a < T.early_collapse c :=
                          ec_good0_mono a c hsa.1 htc.1 hsa.2 htc.2 hm.2
                        have hshift :
                            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                                (T.early_collapse a) <
                              T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                                (T.early_collapse c) :=
                          bridge_add_left_lt
                            (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                            (T.early_collapse a) (T.early_collapse c) hec
                        exact T.Lt.p_mid 1
                          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                            (T.early_collapse a))
                          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                            (T.early_collapse c))
                          (T.card_times (k + 1) b)
                          (T.card_times (k + 1) d) hshift
                    | inr htail =>
                        cases htail.1
                        cases htail.2.1
                        have hbNF := (T.isNF1_P_inv 0 a b hs).2.1
                        have hdNF := (T.isNF1_P_inv 0 a d ht).2.1
                        have hctail := ihb d hbNF hdNF hib hid htail.2.2
                        exact T.Lt.p_tail 1
                          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                            (T.early_collapse a))
                          (T.card_times (k + 1) b)
                          (T.card_times (k + 1) d) hctail

#print axioms cb_card_times_mono

theorem cb_shift_lt_P1_self (k : Nat) (c tail : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail := by
  cases k with
  | zero =>
      rw [T.ofNat, T.mul, T.add]
      cases c with
      | Z => exact T.Lt.Z_lt_P 1 T.Z tail
      | P p a b =>
          cases hc with
          | p _ _ _ hp _ =>
              have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
              subst p
              exact T.Lt.p_head 0 1 a (T.P 0 a b) b tail
                (Nat.zero_lt_succ 0)
  | succ k =>
      rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
      exact T.Lt.p_mid 1 T.Z
        (T.P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c))
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail
        (T.Lt.Z_lt_P 1 T.Z
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c))

#print axioms cb_shift_lt_P1_self

theorem cb_P0_mid_le (a c : T)
    (h : T.P 0 c T.Z ≤ T.P 0 a T.Z) : c ≤ a := by
  cases h with
  | inl hlt =>
      cases lt_inv 0 c T.Z 0 a T.Z hlt with
      | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
      | inr hor =>
          cases hor with
          | inl hm => exact Or.inl hm.2
          | inr ht => exact False.elim (lt_Z_Z_inv ht.2.2)
  | inr heq =>
      have hca : c = a := by injection heq
      exact Or.inr hca

theorem cb_shift_le_of_le (k : Nat) (a c : T)
    (ha : T.isNF1 a) (hc : T.isNF1 c)
    (hga : ∀ x : T, x ∈ T.G1 0 a → x < a)
    (hgc : ∀ x : T, x ∈ T.G1 0 c → x < c)
    (hca : c ≤ a) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse c) ≤
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a) := by
  cases hca with
  | inl hlt =>
      exact Or.inl (bridge_add_left_lt
        (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
        (T.early_collapse c) (T.early_collapse a)
        (ec_good0_mono c a hc ha hgc hga hlt))
  | inr heq =>
      rw [heq]
      exact Or.inr rfl

theorem cb_card_times_closed (n : Nat) : ∀ s : T,
    T.isNF1 s → T.index_Prop1 0 s →
    (∀ x : T, x ∈ T.G1 1 s → x < s) →
    T.isNF1 (T.card_times n s) ∧
      T.index_Prop1 (match n with | 0 => 0 | _ + 1 => 1) (T.card_times n s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.card_times n s) → x < T.card_times n s) := by
  intro s
  induction s with
  | Z =>
      intro hs hi hg
      cases n with
      | zero =>
          change T.isNF1 T.Z ∧ T.index_Prop1 0 T.Z ∧
            (∀ x : T, x ∈ T.G1 1 T.Z → x < T.Z)
          exact ⟨T.isNF1.z, T.index_Prop1.z, fun x hx => by
            rw [T.G1.eq_1] at hx
            cases hx⟩
      | succ k =>
          change T.isNF1 T.Z ∧ T.index_Prop1 1 T.Z ∧
            (∀ x : T, x ∈ T.G1 1 T.Z → x < T.Z)
          exact ⟨T.isNF1.z, T.index_Prop1.z, fun x hx => by
            rw [T.G1.eq_1] at hx
            cases hx⟩
  | P p a b iha ihb =>
      intro hs hi hg
      cases hi with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        cases n with
        | zero =>
            change T.isNF1 (T.P 0 a b) ∧
              T.index_Prop1 0 (T.P 0 a b) ∧
              (∀ x : T, x ∈ T.G1 1 (T.P 0 a b) → x < T.P 0 a b)
            exact ⟨hs, T.index_Prop1.p 0 a b (Nat.le_refl 0) hib, hg⟩
        | succ k =>
            have hinv := T.isNF1_P_inv 0 a b hs
            have haNF : T.isNF1 a := hinv.1
            have hbNF : T.isNF1 b := hinv.2.1
            have haG0 : ∀ x : T, x ∈ T.G1 0 a → x < a := hinv.2.2.1
            have hec := bridge_early_collapse_closed a haNF haG0
            let m : T := T.add
              (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a)
            have hmNF : T.isNF1 m := by
              unfold m
              exact bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
            have hmG : ∀ x : T, x ∈ T.G1 1 m → x < m := by
              unfold m
              exact bridge_shift_strong1 k (T.early_collapse a) hec.2.1
            have hbG1 : ∀ x : T, x ∈ T.G1 1 b → x < b := by
              intro x hx
              have hwhole : x ∈ T.G1 1 (T.P 0 a b) := by
                rw [T.G1.eq_2, ite_eq_right (by
                  intro h
                  exact Nat.not_succ_le_zero 0 h)]
                exact hx
              -- Since the whole term has index 0, this set is exactly the tail set.
              -- The given inequality is already the needed one only after restricting to the tail;
              -- use the fact that index-0 tails have empty G1 at level 1.
              have hempty := index_Prop1_G1_empty 0 b hib 1
                (Nat.zero_lt_succ 0)
              rw [hempty] at hx
              cases hx
            have hrec := ihb hbNF hib hbG1
            have htailNF : T.isNF1 (T.card_times (k + 1) b) := hrec.1
            have htailIndex : T.index_Prop1 1 (T.card_times (k + 1) b) := hrec.2.1
            have htailG : ∀ x : T, x ∈ T.G1 1 (T.card_times (k + 1) b) →
                x < T.card_times (k + 1) b := hrec.2.2
            have hhead : T.head (T.card_times (k + 1) b) ≤ T.P 1 m T.Z := by
              cases b with
              | Z =>
                  change T.Z ≤ T.P 1 m T.Z
                  exact T.Z_le (T.P 1 m T.Z)
              | P q c d =>
                  cases hib with
                  | p _ _ _ hq hid =>
                    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
                    subst q
                    have hbc := T.isNF1_P_inv 0 c d hbNF
                    have hcNF := hbc.1
                    have hcG0 := hbc.2.2.1
                    have hca : c ≤ a := cb_P0_mid_le a c hinv.2.2.2
                    have hshift := cb_shift_le_of_le k a c haNF hcNF haG0 hcG0 hca
                    rw [T.card_times, ite_eq_left rfl]
                    change T.head
                        (T.add
                          (T.P 1
                            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                              (T.early_collapse c)) T.Z)
                          (T.card_times (k + 1) d)) ≤
                      T.P 1 m T.Z
                    rw [T.P_add_eq]
                    change T.P 1
                        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                          (T.early_collapse c)) T.Z ≤
                      T.P 1 m T.Z
                    cases hshift with
                    | inl hlt => exact Or.inl (T.Lt.p_mid 1 _ _ T.Z T.Z hlt)
                    | inr heq =>
                        rw [heq]
                        exact Or.inr rfl
            have hwholeNF : T.isNF1 (T.P 1 m (T.card_times (k + 1) b)) :=
              T.isNF1.p 1 m (T.card_times (k + 1) b)
                hmNF htailNF hmG hhead
            have hwholeG : ∀ x : T,
                x ∈ T.G1 1 (T.P 1 m (T.card_times (k + 1) b)) →
                x < T.P 1 m (T.card_times (k + 1) b) := by
              intro x hx
              rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
                List.mem_append, List.mem_append] at hx
              cases hx with
              | inl hleft =>
                  cases hleft with
                  | inl hmemb =>
                      have heq : x = m := List.mem_singleton.mp hmemb
                      rw [heq]
                      exact cb_shift_lt_P1_self k (T.early_collapse a)
                        (T.card_times (k + 1) b) hec.2.1
                  | inr hmg =>
                      have hxm : x < m := hmG x hmg
                      have hmwhole := cb_shift_lt_P1_self k (T.early_collapse a)
                        (T.card_times (k + 1) b) hec.2.1
                      exact lt_trans_thm x m _ hxm hmwhole
              | inr htg =>
                  have hxtail := htailG x htg
                  have htaille := T.isNF1_tail_le
                    (T.P 1 m (T.card_times (k + 1) b)) hwholeNF
                    1 m (T.card_times (k + 1) b) rfl
                  exact lt_of_lt_of_le_thm T x (T.card_times (k + 1) b)
                    (T.P 1 m (T.card_times (k + 1) b)) hxtail htaille
            rw [T.card_times, ite_eq_left rfl]
            change T.isNF1
                (T.add (T.P 1 m T.Z) (T.card_times (k + 1) b)) ∧
              T.index_Prop1 1
                (T.add (T.P 1 m T.Z) (T.card_times (k + 1) b)) ∧
              (∀ x : T,
                x ∈ T.G1 1 (T.add (T.P 1 m T.Z) (T.card_times (k + 1) b)) →
                x < T.add (T.P 1 m T.Z) (T.card_times (k + 1) b))
            rw [T.P_add_eq, T.add]
            exact ⟨hwholeNF,
              T.index_Prop1.p 1 m (T.card_times (k + 1) b)
                (Nat.le_refl 1) htailIndex,
              hwholeG⟩

#print axioms cb_card_times_closed

theorem cb_card_times_add (n : Nat) : ∀ a b : T,
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  intro a
  induction a with
  | Z =>
      intro b
      change T.card_times n b = T.add T.Z (T.card_times n b)
      rfl
  | P p x y ihx ihy =>
      intro b
      cases b with
      | Z =>
          rw [T.add_Z, T.card_times]
          rw [T.add_Z]
      | P q u v =>
          rw [T.P_add_eq]
          cases n with
          | zero =>
              rw [T.card_times, T.card_times]
              exact (T.P_add_eq p x y (T.P q u v)).symm
          | succ k =>
              rw [T.card_times, T.card_times, ihy]
              exact (Rank1Termination.add_assoc
                (if p = 0 then
                  T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse x)) T.Z
                else
                  T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) x) T.Z)
                (T.card_times (k + 1) y)
                (T.card_times (k + 1) (T.P q u v))).symm

#print axioms cb_card_times_add

theorem cb_mul_one_add_mul (k : Nat) :
    T.add
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) =
    T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
  rw [mul_succ_shape 1 T.Z 0, T.ofNat, T.mul]
  rw [mul_succ_shape 1 T.Z k]
  rw [T.P_add_eq, T.add]

theorem cb_shift_one_shift (k : Nat) (c : T) :
    T.add
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) =
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) c := by
  rw [← Rank1Termination.add_assoc]
  rw [cb_mul_one_add_mul]

theorem cb_card_one_comp (m : Nat) : ∀ s : T,
    T.index_Prop1 0 s →
    T.card_times 1 (T.card_times m s) = T.card_times (m + 1) s := by
  intro s
  induction s with
  | Z =>
      intro hi
      rfl
  | P p a b iha ihb =>
      intro hi
      cases hi with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        cases m with
        | zero =>
            rfl
        | succ k =>
            rw [T.card_times, ite_eq_left rfl]
            change T.card_times 1
                (T.add
                  (T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a)) T.Z)
                  (T.card_times (k + 1) b)) =
              T.card_times (k + 2) (T.P 0 a b)
            rw [cb_card_times_add]
            rw [T.card_times]
            change T.add
                (T.P 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a))) T.Z)
                (T.card_times 1 (T.card_times (k + 1) b)) =
              T.add
                (T.P 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)))
                    (T.early_collapse a)) T.Z)
                (T.card_times (k + 2) b)
            rw [cb_shift_one_shift k (T.early_collapse a)]
            have htail := ihb hib
            change T.card_times 1 (T.card_times (k + 1) b) =
              T.card_times (k + 2) b at htail
            rw [htail]

#print axioms cb_card_one_comp

theorem cb_shift_succ (k : Nat) (c : T) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) c =
      T.P 1 T.Z
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  rw [mul_succ_shape 1 T.Z k, T.P_add_eq]

theorem cb_shift_rank_lt : ∀ k l : Nat, k < l → ∀ c d : T,
    T.index_Prop1 0 c → T.index_Prop1 0 d →
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) d := by
  intro k
  induction k with
  | zero =>
      intro l hkl c d hc hd
      cases l with
      | zero => exact False.elim (Nat.lt_irrefl 0 hkl)
      | succ l =>
          rw [T.ofNat, T.mul, T.add]
          rw [cb_shift_succ l d]
          cases c with
          | Z => exact T.Lt.Z_lt_P 1 T.Z _
          | P p a b =>
              cases hc with
              | p _ _ _ hp _ =>
                  have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
                  subst p
                  exact T.Lt.p_head 0 1 a T.Z b _ (Nat.zero_lt_succ 0)
  | succ k ih =>
      intro l hkl c d hc hd
      cases l with
      | zero => exact False.elim (Nat.not_lt_zero (k + 1) hkl)
      | succ l =>
          have hkl' : k < l := Nat.succ_lt_succ_iff.mp hkl
          rw [cb_shift_succ k c, cb_shift_succ l d]
          exact T.Lt.p_tail 1 T.Z _ _ (ih l hkl' c d hc hd)

#print axioms cb_shift_rank_lt

theorem cb_le_add_right (a b : T) : a ≤ T.add a b := by
  induction a generalizing b with
  | Z => exact T.Z_le b
  | P p x y ihx ihy =>
      cases b with
      | Z =>
          rw [T.add_Z]
          exact Or.inr rfl
      | P q u v =>
          rw [T.P_add_eq]
          have hy := ihy (T.P q u v)
          cases hy with
          | inl hlt => exact Or.inl (T.Lt.p_tail p x y _ hlt)
          | inr heq =>
              have hterm : T.P p x y = T.P p x (T.add y (T.P q u v)) :=
                congrArg (fun z => T.P p x z) heq
              exact Or.inr hterm

theorem cb_threshold_step (n : Nat) :
    T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z <
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z := by
  have hm : T.mul (T.P 1 T.Z T.Z) (T.ofNat n) <
      T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1)) := by
    rw [mul_succ_shape 1 T.Z n]
    exact tail_lt_wrap 1 T.Z n
  exact T.Lt.p_mid 1 _ _ T.Z T.Z hm

theorem cb_lower_head_le_shift (n : Nat) (L c : T)
    (hL : L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z) :
    T.head L ≤
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) c) T.Z := by
  have hh : T.head L ≤
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z :=
    T.head_mono hL
  have hpref : T.mul (T.P 1 T.Z T.Z) (T.ofNat n) ≤
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) c :=
    cb_le_add_right _ c
  have hwrap :
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z ≤
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) c) T.Z := by
    cases hpref with
    | inl hlt => exact Or.inl (T.Lt.p_mid 1 _ _ T.Z T.Z hlt)
    | inr heq =>
        have hterm :
            T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z =
              T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) c) T.Z :=
          congrArg (fun z => T.P 1 z T.Z) heq
        exact Or.inr hterm
  exact partial_order.trans _ _ _ hh hwrap

theorem cb_card_append_lower (n : Nat) : ∀ E L : T,
    T.isNF1 E → T.index_Prop1 0 E →
    T.isNF1 L → T.index_Prop1 1 L →
    (∀ x : T, x ∈ T.G1 1 L → x < L) →
    L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z →
    let R := T.add (T.card_times (n + 1) E) L
    T.isNF1 R ∧ T.index_Prop1 1 R ∧
      (∀ x : T, x ∈ T.G1 1 R → x < R) ∧
      R < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z := by
  intro E
  induction E with
  | Z =>
      intro L hE hiE hL hiL hgL hbound
      change T.isNF1 L ∧ T.index_Prop1 1 L ∧
        (∀ x : T, x ∈ T.G1 1 L → x < L) ∧
        L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z
      exact ⟨hL, hiL, hgL,
        lt_trans_thm L
          (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z)
          (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z)
          hbound (cb_threshold_step n)⟩
  | P p a b iha ihb =>
      intro L hE hiE hL hiL hgL hbound
      cases hiE with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        have hinv := T.isNF1_P_inv 0 a b hE
        have haNF := hinv.1
        have hbNF := hinv.2.1
        have haG0 := hinv.2.2.1
        have hec := bridge_early_collapse_closed a haNF haG0
        have hrec := ihb L hbNF hib hL hiL hgL hbound
        let M : T := T.add
          (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
          (T.early_collapse a)
        let Rtail : T := T.add (T.card_times (n + 1) b) L
        have hmNF : T.isNF1 M := by
          unfold M
          exact bridge_shift_NF n (T.early_collapse a) hec.1 hec.2.1
        have hmG : ∀ x : T, x ∈ T.G1 1 M → x < M := by
          unfold M
          exact bridge_shift_strong1 n (T.early_collapse a) hec.2.1
        have htailNF : T.isNF1 Rtail := by
          unfold Rtail
          exact hrec.1
        have htailIndex : T.index_Prop1 1 Rtail := by
          unfold Rtail
          exact hrec.2.1
        have htailG : ∀ x : T, x ∈ T.G1 1 Rtail → x < Rtail := by
          unfold Rtail
          exact hrec.2.2.1
        have hhead : T.head Rtail ≤ T.P 1 M T.Z := by
          cases b with
          | Z =>
              change T.head L ≤ T.P 1 M T.Z
              unfold M
              exact cb_lower_head_le_shift n L (T.early_collapse a) hbound
          | P q c d =>
              cases hib with
              | p _ _ _ hq hid =>
                have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
                subst q
                have hbc := T.isNF1_P_inv 0 c d hbNF
                have hcNF := hbc.1
                have hcG0 := hbc.2.2.1
                have hca := cb_P0_mid_le a c hinv.2.2.2
                have hshift := cb_shift_le_of_le n a c haNF hcNF haG0 hcG0 hca
                unfold Rtail
                rw [T.card_times, ite_eq_left rfl]
                change T.head
                    (T.add
                      (T.add
                        (T.P 1
                          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                            (T.early_collapse c)) T.Z)
                        (T.card_times n.succ d)) L) ≤ T.P 1 M T.Z
                have hassoc :
                    T.add
                      (T.add
                        (T.P 1
                          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                            (T.early_collapse c)) T.Z)
                        (T.card_times n.succ d)) L =
                      T.add
                        (T.P 1
                          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                            (T.early_collapse c)) T.Z)
                        (T.add (T.card_times n.succ d) L) :=
                  Rank1Termination.add_assoc _ _ _
                rw [hassoc]
                rw [T.P_add_eq]
                change T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
                      (T.early_collapse c)) T.Z ≤ T.P 1 M T.Z
                cases hshift with
                | inl hlt => exact Or.inl (T.Lt.p_mid 1 _ _ T.Z T.Z hlt)
                | inr heq => rw [heq]; exact Or.inr rfl
        have hwholeNF : T.isNF1 (T.P 1 M Rtail) :=
          T.isNF1.p 1 M Rtail hmNF htailNF hmG hhead
        have hwholeG : ∀ x : T, x ∈ T.G1 1 (T.P 1 M Rtail) →
            x < T.P 1 M Rtail := by
          intro x hx
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
            List.mem_append, List.mem_append] at hx
          cases hx with
          | inl hl =>
              cases hl with
              | inl hmemb =>
                  have heq : x = M := List.mem_singleton.mp hmemb
                  rw [heq]
                  unfold M
                  exact cb_shift_lt_P1_self n (T.early_collapse a) Rtail hec.2.1
              | inr hxM =>
                  have hxm := hmG x hxM
                  have hmwhole : M < T.P 1 M Rtail := by
                    unfold M
                    exact cb_shift_lt_P1_self n (T.early_collapse a) Rtail hec.2.1
                  exact lt_trans_thm x M _ hxm hmwhole
          | inr hxt =>
              have hxt' := htailG x hxt
              have htle := T.isNF1_tail_le (T.P 1 M Rtail) hwholeNF
                1 M Rtail rfl
              exact lt_of_lt_of_le_thm T x Rtail (T.P 1 M Rtail) hxt' htle
        have hupper : T.P 1 M Rtail <
            T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z := by
          unfold M
          have hrank :=
            cb_shift_rank_lt n (n + 1) (Nat.lt_succ_self n)
              (T.early_collapse a) T.Z hec.2.1 T.index_Prop1.z
          rw [T.add_Z] at hrank
          exact T.Lt.p_mid 1 _ _ Rtail T.Z hrank
        change T.isNF1
            (T.add (T.card_times (n + 1) (T.P 0 a b)) L) ∧
          T.index_Prop1 1
            (T.add (T.card_times (n + 1) (T.P 0 a b)) L) ∧
          (∀ x : T,
            x ∈ T.G1 1 (T.add (T.card_times (n + 1) (T.P 0 a b)) L) →
              x < T.add (T.card_times (n + 1) (T.P 0 a b)) L) ∧
          T.add (T.card_times (n + 1) (T.P 0 a b)) L <
            T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z
        rw [T.card_times, ite_eq_left rfl]
        change T.isNF1
            (T.add (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) L) ∧
          T.index_Prop1 1
            (T.add (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) L) ∧
          (∀ x : T,
            x ∈ T.G1 1
              (T.add (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) L) →
              x < T.add (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) L) ∧
          T.add (T.add (T.P 1 M T.Z) (T.card_times (n + 1) b)) L <
            T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z
        rw [Rank1Termination.add_assoc]
        rw [T.P_add_eq, T.add]
        change T.isNF1 (T.P 1 M Rtail) ∧ T.index_Prop1 1 (T.P 1 M Rtail) ∧
          (∀ x : T, x ∈ T.G1 1 (T.P 1 M Rtail) → x < T.P 1 M Rtail) ∧
          T.P 1 M Rtail <
            T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z
        exact ⟨hwholeNF,
          T.index_Prop1.p 1 M Rtail (Nat.le_refl 1) htailIndex,
          hwholeG, hupper⟩

#print axioms cb_card_append_lower

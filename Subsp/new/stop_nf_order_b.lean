import Subsp.new.stop_nf_order_a

open T



-- extracted from Subsp/new/stop_card_bridge.lean
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



-- extracted from Subsp/new/stop_principal.lean
theorem pn_index0_lt_threshold0 (a : T)
    (ha : T.index_Prop1 0 a) :
    a < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z := by
  change a < T.P 1 T.Z T.Z
  cases a with
  | Z => exact T.Lt.Z_lt_P 1 T.Z T.Z
  | P p c d =>
      cases ha with
      | p _ _ _ hp htail =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          exact T.Lt.p_head 0 1 c T.Z d T.Z (Nat.zero_lt_succ 0)

#print axioms pn_index0_lt_threshold0

theorem pn_aux_card1_sum_append {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ L : T,
        T.isNF1 L → T.index_Prop1 0 L →
        (∀ y : T, y ∈ T.G1 1 L → y < L) →
        L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z →
        let sum := (transAux v).2.1
        let R := T.add (T.card_times 1 sum) L
        T.isNF1 R ∧ T.index_Prop1 1 R ∧
          (∀ y : T, y ∈ T.G1 1 R → y < R) ∧
          R < T.P 1
            (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z := by
  intro k
  induction k with
  | zero =>
      intro v hcoord L hL hLi hLg hLb
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2]
              change T.isNF1 (T.add (T.card_times 1 T.Z) L) ∧
                T.index_Prop1 1 (T.add (T.card_times 1 T.Z) L) ∧
                (∀ y : T, y ∈ T.G1 1 (T.add (T.card_times 1 T.Z) L) →
                  y < T.add (T.card_times 1 T.Z) L) ∧
                T.add (T.card_times 1 T.Z) L <
                  T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z
              rw [T.card_times.eq_1, T.add.eq_1]
              exact ⟨hL,
                Rank1Termination.index_mono (Nat.zero_le 1) L hLi,
                hLg, hLb⟩
  | succ m ih =>
      intro v hcoord L hL hLi hLg hLb
      cases v with
      | @snoc n xs a =>
          have hxs :
              ∀ x : new.T lam, x ∈ new.Vec.toList xs →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hcoord x (List.mem_append_left [a] hx)
          have ha :
              T.isNF1 (trans a) ∧
                (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
            apply hcoord a
            exact List.mem_append_right (new.Vec.toList xs)
              (List.mem_singleton_self a)
          have hrec := ih xs hxs L hL hLi hLg hLb
          cases haux : transAux xs with
          | mk found rest =>
            cases rest with
            | mk sum a0 =>
              rw [haux] at hrec
              rw [transAux.eq_3, haux]
              change T.isNF1
                  (T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
                T.index_Prop1 1
                  (T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
                (∀ y : T,
                  y ∈ T.G1 1
                    (T.add
                      (T.card_times 1
                        (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) →
                  y < T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L) ∧
                T.add
                    (T.card_times 1
                      (T.add (T.card_times m (T.early_collapse (trans a))) sum)) L <
                  T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (m + 1))) T.Z
              have hec := bridge_early_collapse_closed (trans a) ha.1 ha.2
              have hblockNF : T.isNF1 (T.early_collapse (trans a)) := hec.1
              have hblockIdx : T.index_Prop1 0 (T.early_collapse (trans a)) := hec.2.1
              have hR := cb_card_append_lower m
                (T.early_collapse (trans a))
                (T.add (T.card_times 1 sum) L)
                hblockNF hblockIdx hrec.1 hrec.2.1 hrec.2.2.1 hrec.2.2.2
              rw [ca_card_times_add]
              rw [ca_card_times_one_comp]
              rw [Rank1Termination.add_assoc]
              exact hR

#print axioms pn_aux_card1_sum_append


theorem pn_card_times_pos_shape (q : Nat) (c : T)
    (hc : T.index_Prop1 0 c) (hne : c ≠ T.Z) :
    ∃ m tail : T, T.card_times (q + 1) c = T.P 1 m tail := by
  cases c with
  | Z => exact False.elim (hne rfl)
  | P p a b =>
      cases hc with
      | p _ _ _ hp hb =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          rw [T.card_times.eq_3, ite_eq_left rfl]
          refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat q))
              (T.early_collapse a), T.card_times (q + 1) b, ?_⟩
          rw [← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
          rfl

#print axioms pn_card_times_pos_shape

theorem pn_aux_sum_P0_index0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        ∀ c d : T, sum = T.P 0 c d → T.index_Prop1 0 sum := by
  intro k
  induction k with
  | zero =>
      intro v hcoord found sum a0 haux c d hshape
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              cases haux
              cases hshape
  | succ m ih =>
      intro v hcoord found sum a0 haux c d hshape
      cases v with
      | @snoc n xs a =>
          have hxs :
              ∀ x : new.T lam, x ∈ new.Vec.toList xs →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hcoord x (List.mem_append_left [a] hx)
          have ha :
              T.isNF1 (trans a) ∧
                (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
            apply hcoord a
            exact List.mem_append_right (new.Vec.toList xs)
              (List.mem_singleton_self a)
          cases hrest : transAux xs with
          | mk foundRest rest =>
            cases rest with
            | mk sumRest a0Rest =>
              rw [transAux.eq_3, hrest] at haux
              cases a with
              | Z =>
                  change
                    (foundRest,
                      T.add (T.card_times m (T.early_collapse T.Z)) sumRest,
                      a0Rest) = (found, sum, a0) at haux
                  have hecz : T.early_collapse T.Z = T.Z := by
                    rw [T.early_collapse, T.part, ite_eq_left rfl]
                  rw [hecz, T.card_times.eq_1, T.add.eq_1] at haux
                  have hsum : sumRest = sum :=
                    congrArg (fun q : Bool × T × T => q.2.1) haux
                  have hshapeRest : sumRest = T.P 0 c d := hsum.trans hshape
                  rw [← hsum]
                  exact ih xs hxs foundRest sumRest a0Rest hrest c d hshapeRest
              | P als aadd =>
                  have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                    intro h
                    cases h
                  have hatne : trans (new.T.P als aadd) ≠ T.Z :=
                    tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
                  have hec := bridge_early_collapse_closed
                    (trans (new.T.P als aadd)) ha.1 ha.2
                  have hecne :
                      T.early_collapse (trans (new.T.P als aadd)) ≠ T.Z :=
                    bridge_early_collapse_ne_Z (trans (new.T.P als aadd)) hatne
                  change
                    (true,
                      T.add
                        (T.card_times m
                          (T.early_collapse (trans (new.T.P als aadd)))) sumRest,
                      a0Rest) = (found, sum, a0) at haux
                  cases haux
                  cases m with
                  | zero =>
                      cases xs with
                      | @snoc n ys b =>
                          cases ys with
                          | nil =>
                              rw [transAux.eq_2] at hrest
                              cases hrest
                              rw [ca_card_times_zero, T.add_Z]
                              exact hec.2.1
                  | succ j =>
                      obtain ⟨mid, tail, hcard⟩ :=
                        pn_card_times_pos_shape j
                          (T.early_collapse (trans (new.T.P als aadd)))
                          hec.2.1 hecne
                      rw [hcard, T.P_add_eq] at hshape
                      cases hshape

#print axioms pn_aux_sum_P0_index0

theorem pn_aux_found_middle_closed {lam : Nat}
    {k : Nat} (v : new.Vec (new.T lam) (k + 1))
    (hcoord : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (found : Bool) (sum a0 : T)
    (haux : transAux v = (found, sum, a0))
    (hf : found = true) :
    let M := T.add (T.card_times 1 (T.one_del sum))
      (T.early_collapse a0)
    T.isNF1 M ∧ T.index_Prop1 1 M ∧
      (∀ y : T, y ∈ T.G1 1 M → y < M) := by
  have hi := tc_transAux_inv v hcoord found sum a0 haux
  have haec := bridge_early_collapse_closed a0 hi.1 hi.2.1
  have hbaseBound := pn_index0_lt_threshold0 (T.early_collapse a0) haec.2.1
  cases sum with
  | Z =>
      exact False.elim (hi.2.2.2.2.2.2.1 hf rfl)
  | P p c d =>
      have hsumIdx := hi.2.2.2.1
      cases hsumIdx with
      | p _ _ _ hp htail =>
          cases p with
          | zero =>
              have hsumGood1 := hi.2.2.2.2.1
              have hsumIdx0 := pn_aux_sum_P0_index0 v hcoord found
                (T.P 0 c d) a0 haux c d rfl
              have hdel := ec_one_del_NF_index_good1
                (T.P 0 c d) hi.2.2.1 hsumIdx0 hsumGood1
              have hres := cb_card_append_lower 0
                (T.one_del (T.P 0 c d)) (T.early_collapse a0)
                hdel.1 hdel.2.1 haec.1
                (Rank1Termination.index_mono (Nat.zero_le 1)
                  (T.early_collapse a0) haec.2.1)
                haec.2.2 hbaseBound
              exact ⟨hres.1, hres.2.1, hres.2.2.1⟩
          | succ p' =>
              have hp' : p' = 0 := by
                have hle : p' + 1 ≤ 1 := hp
                exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hle)
              subst p'
              have hone : T.one_del (T.P 1 c d) = T.P 1 c d := rfl
              rw [hone]
              have hres := pn_aux_card1_sum_append v hcoord
                (T.early_collapse a0) haec.1 haec.2.1 haec.2.2 hbaseBound
              rw [haux] at hres
              exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

#print axioms pn_aux_found_middle_closed

theorem pn_principal_NF {lam : Nat} (v : new.Vec (new.T lam) lam)
    (hcoord : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    T.isNF1 (trans (new.T.P v new.T.Z)) := by
  rw [_root_.trans.eq_2]
  cases lam with
  | zero =>
      cases v with
      | nil =>
          rw [transAux.eq_1]
          change T.isNF1 (T.P 0 T.Z T.Z)
          exact T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
            (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
            (T.Z_le _)
  | succ k =>
      cases haux : transAux v with
      | mk found rest =>
        cases rest with
        | mk sum a0 =>
          change
            T.isNF1
              (if found = true then
                T.P 1
                  (T.add (T.card_times 1 (T.one_del sum))
                    (T.early_collapse a0)) T.Z
              else if a0 = T.Z then T.P 0 T.Z T.Z
              else T.P 0 a0 T.Z)
          by_cases hf : found = true
          · rw [ite_eq_left hf]
            have hm := pn_aux_found_middle_closed v hcoord found sum a0 haux hf
            exact T.isNF1.p 1
              (T.add (T.card_times 1 (T.one_del sum)) (T.early_collapse a0))
              T.Z hm.1 T.isNF1.z hm.2.2 (T.Z_le _)
          · rw [ite_eq_right hf]
            have hi := tc_transAux_inv v hcoord found sum a0 haux
            by_cases ha0 : a0 = T.Z
            · rw [ite_eq_left ha0]
              exact T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
                (T.Z_le _)
            · rw [ite_eq_right ha0]
              exact T.isNF1.p 0 a0 T.Z hi.1 T.isNF1.z hi.2.1 (T.Z_le _)

#print axioms pn_principal_NF



-- extracted from Subsp/new/stop_nf_aux.lean
theorem nfaux_part_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part s).1 ∧ T.isNF1 (T.part s).2 := by
  exact bridge_part_NF1 s hs

#print axioms nfaux_part_NF1



-- extracted from Subsp/new/stop_order_cases_base.lean
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



-- extracted from Subsp/new/stop_order_cases_card.lean
theorem c1_p0 (a b : T) :
    T.card_times 1 (T.P 0 a b) =
      T.P 1 (T.early_collapse a) (T.card_times 1 b) := by
  rw [T.card_times.eq_3, ite_eq_left rfl]
  rw [T.ofNat.eq_1, T.mul.eq_1]
  change T.add (T.P 1 (T.add T.Z (T.early_collapse a)) T.Z)
    (T.card_times 1 b) = T.P 1 (T.early_collapse a) (T.card_times 1 b)
  rw [T.add.eq_1, T.P_add_eq, T.add.eq_1]

theorem c1_p1 (a b : T) :
    T.card_times 1 (T.P 1 a b) =
      T.P 1 (T.P 1 T.Z a) (T.card_times 1 b) := by
  rw [T.card_times.eq_3, ite_eq_right (Nat.one_ne_zero)]
  rw [mul_succ_shape 1 T.Z 0]
  rw [T.ofNat.eq_1, T.mul.eq_1]
  change T.add (T.P 1 (T.add (T.P 1 T.Z T.Z) a) T.Z)
    (T.card_times 1 b) = T.P 1 (T.P 1 T.Z a) (T.card_times 1 b)
  rw [T.P_add_eq, T.add.eq_1]
  rw [T.P_add_eq, T.add.eq_1]

theorem c1_idx0_lt_P1 (x y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 T.Z y := by
  cases x with
  | Z => exact T.Lt.Z_lt_P 1 T.Z y
  | P p a b =>
    cases hx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      exact T.Lt.p_head 0 1 a T.Z b y (Nat.zero_lt_succ 0)

#print axioms c1_idx0_lt_P1

theorem c1_card_times_mono_index1 :
    ∀ s t : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.card_times 1 s < T.card_times 1 t := by
  intro s
  induction s with
  | Z =>
    intro t hsNF hsIdx htNF htIdx hst
    have htne : t ≠ T.Z := by
      intro heq
      rw [heq] at hst
      exact lt_Z_inv hst
    have hctne : T.card_times 1 t ≠ T.Z :=
      bridge_card_times_ne_Z 1 t htne
    rw [T.card_times.eq_1]
    cases T.Z_le (T.card_times 1 t) with
    | inl hlt => exact hlt
    | inr heq => exact False.elim (hctne heq.symm)
  | P p a b iha ihb =>
    intro t hsNF hsIdx htNF htIdx hst
    cases t with
    | Z => exact False.elim (lt_Z_inv hst)
    | P q e f =>
      have hpLe : p ≤ 1 := by
        cases hsIdx with
        | p _ _ _ hp _ => exact hp
      have hqLe : q ≤ 1 := by
        cases htIdx with
        | p _ _ _ hq _ => exact hq
      cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hpLe) with
      | inl hp0 =>
        subst p
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
        | inl hq0 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p0, c1_p0]
          cases lt_inv 0 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 0 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hec : T.early_collapse a < T.early_collapse e :=
                bridge_early_collapse_lt a e haNF haG heNF hae
              exact T.Lt.p_mid 1 (T.early_collapse a) (T.early_collapse e)
                (T.card_times 1 b) (T.card_times 1 f) hec
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
              exact T.Lt.p_tail 1 (T.early_collapse a)
                (T.card_times 1 b) (T.card_times 1 f) hrec
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          have hec := bridge_early_collapse_closed a haNF haG
          rw [c1_p0, c1_p1]
          have hmid : T.early_collapse a < T.P 1 T.Z e :=
            c1_idx0_lt_P1 (T.early_collapse a) e hec.2.1
          exact T.Lt.p_mid 1 (T.early_collapse a) (T.P 1 T.Z e)
            (T.card_times 1 b) (T.card_times 1 f) hmid
      | inr hp1 =>
        subst p
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
        | inl hq0 =>
          subst q
          cases lt_inv 1 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.not_lt_zero 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid => cases hmid.1
            | inr htail => cases htail.1
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 1 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 1 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p1, c1_p1]
          cases lt_inv 1 a b 1 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hinner : T.P 1 T.Z a < T.P 1 T.Z e :=
                T.Lt.p_tail 1 T.Z a e hae
              exact T.Lt.p_mid 1 (T.P 1 T.Z a) (T.P 1 T.Z e)
                (T.card_times 1 b) (T.card_times 1 f) hinner
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
              exact T.Lt.p_tail 1 (T.P 1 T.Z a)
                (T.card_times 1 b) (T.card_times 1 f) hrec

#print axioms c1_card_times_mono_index1


theorem c1_idx0_lt_outer1 (x m y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 m y := by
  cases x with
  | Z => exact T.Lt.Z_lt_P 1 m y
  | P p a b =>
    cases hx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      exact T.Lt.p_head 0 1 a m b y (Nat.zero_lt_succ 0)

#print axioms c1_idx0_lt_outer1
theorem c1_card_append_lt_index1 :
    ∀ s t x y : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.index_Prop1 0 x →
      T.add (T.card_times 1 s) x < T.add (T.card_times 1 t) y := by
  intro s
  induction s with
  | Z =>
    intro t x y hsNF hsIdx htNF htIdx hst hxIdx
    cases t with
    | Z => exact False.elim (lt_Z_inv hst)
    | P q e f =>
      have hqLe : q ≤ 1 := by
        cases htIdx with
        | p _ _ _ hq _ => exact hq
      rw [T.card_times.eq_1, T.add.eq_1]
      cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
      | inl hq0 =>
        subst q
        rw [c1_p0, T.P_add_eq]
        exact c1_idx0_lt_outer1 x (T.early_collapse e)
          (T.add (T.card_times 1 f) y) hxIdx
      | inr hq1 =>
        subst q
        rw [c1_p1, T.P_add_eq]
        exact c1_idx0_lt_outer1 x (T.P 1 T.Z e)
          (T.add (T.card_times 1 f) y) hxIdx
  | P p a b iha ihb =>
    intro t x y hsNF hsIdx htNF htIdx hst hxIdx
    cases t with
    | Z => exact False.elim (lt_Z_inv hst)
    | P q e f =>
      have hpLe : p ≤ 1 := by
        cases hsIdx with
        | p _ _ _ hp _ => exact hp
      have hqLe : q ≤ 1 := by
        cases htIdx with
        | p _ _ _ hq _ => exact hq
      cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hpLe) with
      | inl hp0 =>
        subst p
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
        | inl hq0 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p0, c1_p0, T.P_add_eq, T.P_add_eq]
          cases lt_inv 0 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 0 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hec : T.early_collapse a < T.early_collapse e :=
                bridge_early_collapse_lt a e haNF haG heNF hae
              exact T.Lt.p_mid 1 (T.early_collapse a) (T.early_collapse e)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hec
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f x y hbNF hbIdx hfNF hfIdx hbf hxIdx
              exact T.Lt.p_tail 1 (T.early_collapse a)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hrec
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hsNF
          have hec := bridge_early_collapse_closed a haNF haG
          rw [c1_p0, c1_p1, T.P_add_eq, T.P_add_eq]
          have hmid : T.early_collapse a < T.P 1 T.Z e :=
            c1_idx0_lt_P1 (T.early_collapse a) e hec.2.1
          exact T.Lt.p_mid 1 (T.early_collapse a) (T.P 1 T.Z e)
            (T.add (T.card_times 1 b) x)
            (T.add (T.card_times 1 f) y) hmid
      | inr hp1 =>
        subst p
        cases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with
        | inl hq0 =>
          subst q
          cases lt_inv 1 a b 0 e f hst with
          | inl hhead => exact False.elim (Nat.not_lt_zero 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid => cases hmid.1
            | inr htail => cases htail.1
        | inr hq1 =>
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 1 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 1 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p1, c1_p1, T.P_add_eq, T.P_add_eq]
          cases lt_inv 1 a b 1 e f hst with
          | inl hhead => exact False.elim (Nat.lt_irrefl 1 hhead)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have hae : a < e := hmid.2
              have hinner : T.P 1 T.Z a < T.P 1 T.Z e :=
                T.Lt.p_tail 1 T.Z a e hae
              exact T.Lt.p_mid 1 (T.P 1 T.Z a) (T.P 1 T.Z e)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hinner
            | inr htail =>
              have hae : a = e := htail.2.1
              subst e
              have hbf : b < f := htail.2.2
              have hrec := ihb f x y hbNF hbIdx hfNF hfIdx hbf hxIdx
              exact T.Lt.p_tail 1 (T.P 1 T.Z a)
                (T.add (T.card_times 1 b) x)
                (T.add (T.card_times 1 f) y) hrec

#print axioms c1_card_append_lt_index1



-- extracted from Subsp/new/stop_order_cases.lean
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
        bridge_early_collapse_lt av aw hiv.1 hiv.2.1 hiw.1 ha0lt
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
        bridge_early_collapse_lt av aw hiv.1 hiv.2.1 hiw.1 ha0lt
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



-- extracted from Subsp/new/stop_order_core.lean
theorem oc_mem_size_lt_P {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a x : new.T lam)
    (hx : x ∈ new.Vec.toList v) :
    new.T.size x < new.T.size (new.T.P v a) := by
  obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v x hx
  rw [← hi]
  exact new.T.idx_size_lt_P v a i

#print axioms oc_mem_size_lt_P

theorem oc_order_preserve_core {lam : Nat}
    (hgood : ∀ x : new.T lam, new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s t hsize hs ht hst
      cases s with
      | Z =>
        cases t with
        | Z => exact False.elim (strict_partial_order.irrefl new.T.Z hst)
        | P w b =>
          rw [_root_.trans.eq_1]
          have hne : trans (new.T.P w b) ≠ T.Z :=
            tc_trans_ne_Z_of_ne_Z (new.T.P w b) (by intro h; cases h)
          exact tc_Z_lt_of_ne (trans (new.T.P w b)) hne
      | P v a =>
        cases t with
        | Z => exact False.elim (by
            change new.compareT (new.T.P v a) new.T.Z = Ordering.lt at hst
            cases hst)
        | P w b =>
          cases hs with
          | p _ _ hvNF haNF hvG hheadA =>
            cases ht with
            | p _ _ hwNF hbNF hwG hheadB =>
              change
                (match new.compareVec v w with
                | Ordering.eq => new.compareT a b
                | ord => ord) = Ordering.lt at hst
              cases hcmp : new.compareVec v w with
              | lt =>
                have hvGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList v →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  exact hgood x ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  exact hgood x ⟨hwNF x hx, hwG x hx⟩
                have hmono :
                    ∀ x y : new.T lam,
                      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
                      x < y → trans x < trans y := by
                  intro x y hx hy hxy
                  have hsx : new.T.size x < new.T.size (new.T.P v a) :=
                    oc_mem_size_lt_P v a x hx
                  have hty : new.T.size y < new.T.size (new.T.P w b) :=
                    oc_mem_size_lt_P w b y hy
                  have hsum :
                      new.T.size x + new.T.size y <
                        new.T.size (new.T.P v a) + new.T.size (new.T.P w b) :=
                    Nat.add_lt_add hsx hty
                  have hsum' : new.T.size x + new.T.size y < n := by
                    rw [hsize] at hsum
                    exact hsum
                  exact ih (new.T.size x + new.T.size y) hsum'
                    x y rfl (hvNF x hx) (hwNF y hy) hxy
                exact oc_full_lt_of_compareVec_general v w a b hvGood hwGood hmono hcmp
              | eq =>
                rw [hcmp] at hst
                have hvw : v = w := new.Vec_eq_sound v w hcmp
                subst w
                have hsa : new.T.size a < new.T.size (new.T.P v a) :=
                  new.T.add_size_lt_P v a
                have htb : new.T.size b < new.T.size (new.T.P v b) :=
                  new.T.add_size_lt_P v b
                have hsum :
                    new.T.size a + new.T.size b <
                      new.T.size (new.T.P v a) + new.T.size (new.T.P v b) :=
                  Nat.add_lt_add hsa htb
                have hsum' : new.T.size a + new.T.size b < n := by
                  rw [hsize] at hsum
                  exact hsum
                have htail := ih (new.T.size a + new.T.size b) hsum'
                  a b rfl haNF hbNF hst
                calc
                  trans (new.T.P v a) =
                      T.add (trans (new.T.P v new.T.Z)) (trans a) :=
                    tc_trans_P_add v a
                  _ < T.add (trans (new.T.P v new.T.Z)) (trans b) :=
                    bridge_add_left_lt (trans (new.T.P v new.T.Z))
                      (trans a) (trans b) htail
                  _ = trans (new.T.P v b) := (tc_trans_P_add v b).symm
              | gt =>
                rw [hcmp] at hst
                cases hst)
  intro s t hs ht hst
  exact main (new.T.size s + new.T.size t) s t rfl hs ht hst

#print axioms oc_order_preserve_core

theorem oc_order_embedding_core {lam : Nat}
    (hgood : ∀ x : new.T lam, new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  constructor
  · exact oc_order_preserve_core hgood s t hs ht
  · intro htrans
    cases strict_linear_order.total s t with
    | inl hst => exact hst
    | inr hor =>
      cases hor with
      | inl hts =>
        have hrev := oc_order_preserve_core hgood t s ht hs hts
        have hloop : trans s < trans s :=
          strict_partial_order.trans (trans s) (trans t) (trans s) htrans hrev
        exact False.elim (strict_partial_order.irrefl (trans s) hloop)
      | inr heq =>
        rw [heq] at htrans
        exact False.elim (strict_partial_order.irrefl (trans t) htrans)

#print axioms oc_order_embedding_core


theorem oc_order_preserve_with_smaller_good {lam : Nat}
    (hgood : ∀ x u : new.T lam, new.T.size x < new.T.size u →
      new.T.isNFComp x →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s t hsize hs ht hst
      cases s with
      | Z =>
        cases t with
        | Z => exact False.elim (strict_partial_order.irrefl new.T.Z hst)
        | P w b =>
          rw [_root_.trans.eq_1]
          have hne : trans (new.T.P w b) ≠ T.Z :=
            tc_trans_ne_Z_of_ne_Z (new.T.P w b) (by intro h; cases h)
          exact tc_Z_lt_of_ne (trans (new.T.P w b)) hne
      | P v a =>
        cases t with
        | Z => exact False.elim (by
            change new.compareT (new.T.P v a) new.T.Z = Ordering.lt at hst
            cases hst)
        | P w b =>
          cases hs with
          | p _ _ hvNF haNF hvG hheadA =>
            cases ht with
            | p _ _ hwNF hbNF hwG hheadB =>
              change
                (match new.compareVec v w with
                | Ordering.eq => new.compareT a b
                | ord => ord) = Ordering.lt at hst
              cases hcmp : new.compareVec v w with
              | lt =>
                have hvGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList v →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have hsx := oc_mem_size_lt_P v a x hx
                  exact hgood x (new.T.P v a) hsx ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have htx := oc_mem_size_lt_P w b x hx
                  exact hgood x (new.T.P w b) htx ⟨hwNF x hx, hwG x hx⟩
                have hmono :
                    ∀ x y : new.T lam,
                      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
                      x < y → trans x < trans y := by
                  intro x y hx hy hxy
                  have hsx : new.T.size x < new.T.size (new.T.P v a) :=
                    oc_mem_size_lt_P v a x hx
                  have hty : new.T.size y < new.T.size (new.T.P w b) :=
                    oc_mem_size_lt_P w b y hy
                  have hsum :
                      new.T.size x + new.T.size y <
                        new.T.size (new.T.P v a) + new.T.size (new.T.P w b) :=
                    Nat.add_lt_add hsx hty
                  have hsum' : new.T.size x + new.T.size y < n := by
                    rw [hsize] at hsum
                    exact hsum
                  exact ih (new.T.size x + new.T.size y) hsum'
                    x y rfl (hvNF x hx) (hwNF y hy) hxy
                exact oc_full_lt_of_compareVec_general v w a b hvGood hwGood hmono hcmp
              | eq =>
                rw [hcmp] at hst
                have hvw : v = w := new.Vec_eq_sound v w hcmp
                subst w
                have hsa : new.T.size a < new.T.size (new.T.P v a) :=
                  new.T.add_size_lt_P v a
                have htb : new.T.size b < new.T.size (new.T.P v b) :=
                  new.T.add_size_lt_P v b
                have hsum :
                    new.T.size a + new.T.size b <
                      new.T.size (new.T.P v a) + new.T.size (new.T.P v b) :=
                  Nat.add_lt_add hsa htb
                have hsum' : new.T.size a + new.T.size b < n := by
                  rw [hsize] at hsum
                  exact hsum
                have htail := ih (new.T.size a + new.T.size b) hsum'
                  a b rfl haNF hbNF hst
                calc
                  trans (new.T.P v a) =
                      T.add (trans (new.T.P v new.T.Z)) (trans a) :=
                    tc_trans_P_add v a
                  _ < T.add (trans (new.T.P v new.T.Z)) (trans b) :=
                    bridge_add_left_lt (trans (new.T.P v new.T.Z))
                      (trans a) (trans b) htail
                  _ = trans (new.T.P v b) := (tc_trans_P_add v b).symm
              | gt =>
                rw [hcmp] at hst
                cases hst)
  intro s t hs ht hst
  exact main (new.T.size s + new.T.size t) s t rfl hs ht hst

#print axioms oc_order_preserve_with_smaller_good



-- extracted from Subsp/new/stop_nf_core.lean
theorem nfcore_head_NF {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s) :
    new.T.isNF (new.T.head s) := by
  cases s with
  | Z =>
      exact new.T.isNF.z
  | P ls add =>
      cases hs with
      | p _ _ h0 h1 h2 h3 =>
          rw [new.T.head]
          exact new.T.isNF.p ls new.T.Z h0 new.T.isNF.z h2 (Or.inl rfl)

#print axioms nfcore_head_NF

theorem nfcore_trans_PZ_shape {lam : Nat}
    (v : new.Vec (new.T lam) lam) :
    ∃ i : Nat, ∃ m : T,
      trans (new.T.P v new.T.Z) = T.P i m T.Z := by
  rw [_root_.trans.eq_2]
  cases haux : transAux v with
  | mk found rest =>
      cases rest with
      | mk sum a0 =>
          change
            ∃ i : Nat, ∃ m : T,
              (if found = true then
                T.P 1
                  (T.add (T.card_times 1 (T.one_del sum))
                    (T.early_collapse a0)) T.Z
              else if a0 = T.Z then T.P 0 T.Z T.Z
              else T.P 0 a0 T.Z) = T.P i m T.Z
          by_cases hf : found = true
          · rw [ite_eq_left hf]
            exact ⟨1,
              T.add (T.card_times 1 (T.one_del sum))
                (T.early_collapse a0), rfl⟩
          · rw [ite_eq_right hf]
            by_cases ha0 : a0 = T.Z
            · rw [ite_eq_left ha0]
              exact ⟨0, T.Z, rfl⟩
            · rw [ite_eq_right ha0]
              exact ⟨0, a0, rfl⟩

#print axioms nfcore_trans_PZ_shape

theorem nfcore_add_principal (i : Nat) (m b : T)
    (hp : T.isNF1 (T.P i m T.Z))
    (hb : T.isNF1 b)
    (hhead : T.head b ≤ T.P i m T.Z) :
    T.isNF1 (T.add (T.P i m T.Z) b) := by
  obtain ⟨hm, hz, hg, hh⟩ := T.isNF1_P_inv i m T.Z hp
  rw [T.P_add_eq, T.add.eq_1]
  exact T.isNF1.p i m b hm hb hg hhead

#print axioms nfcore_add_principal

theorem nfcore_trans_P_of_components {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (ha : T.isNF1 (trans a))
    (hhead : T.head (trans a) ≤ trans (new.T.P v new.T.Z)) :
    T.isNF1 (trans (new.T.P v a)) := by
  have hp : T.isNF1 (trans (new.T.P v new.T.Z)) :=
    pn_principal_NF v hv
  obtain ⟨i, m, hshape⟩ := nfcore_trans_PZ_shape v
  rw [tc_trans_P_add v a, hshape]
  rw [hshape] at hp hhead
  exact nfcore_add_principal i m (trans a) hp ha hhead

#print axioms nfcore_trans_P_of_components

theorem nfcore_principal_le {lam : Nat}
    (w v : new.Vec (new.T lam) lam)
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList w → y ∈ new.Vec.toList v →
      x < y → trans x < trans y)
    (hle : new.T.P w new.T.Z ≤ new.T.P v new.T.Z) :
    trans (new.T.P w new.T.Z) ≤ trans (new.T.P v new.T.Z) := by
  cases hle with
  | inl hlt =>
      change
        (match new.compareVec w v with
        | Ordering.eq => new.compareT new.T.Z new.T.Z
        | ord => ord) = Ordering.lt at hlt
      cases hcmp : new.compareVec w v with
      | lt =>
          exact Or.inl
            (oc_full_lt_of_compareVec_general w v new.T.Z new.T.Z
              hw hv hmono hcmp)
      | eq =>
          rw [hcmp] at hlt
          change Ordering.eq = Ordering.lt at hlt
          cases hlt
      | gt =>
          rw [hcmp] at hlt
          cases hlt
  | inr heq =>
      have hterm : new.T.P w new.T.Z = new.T.P v new.T.Z :=
        new.T_eq_sound (new.T.P w new.T.Z) (new.T.P v new.T.Z) heq
      rw [hterm]
      exact Or.inr rfl

#print axioms nfcore_principal_le

theorem nfcore_trans_head_le_P {lam : Nat}
    (w v : new.Vec (new.T lam) lam) (b : new.T lam)
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList w → y ∈ new.Vec.toList v →
      x < y → trans x < trans y)
    (hle : new.T.head (new.T.P w b) ≤ new.T.P v new.T.Z) :
    T.head (trans (new.T.P w b)) ≤ trans (new.T.P v new.T.Z) := by
  rw [← tc_trans_head (new.T.P w b)]
  change trans (new.T.P w new.T.Z) ≤ trans (new.T.P v new.T.Z)
  exact nfcore_principal_le w v hw hv hmono hle

#print axioms nfcore_trans_head_le_P

theorem nfcore_NF_step {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hs : new.T.isNF (new.T.P v a))
    (hnfSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size (new.T.P v a) →
      new.T.isNF x → T.isNF1 (trans x))
    (hgoodSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size (new.T.P v a) →
      new.T.isNFComp x →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hpresSmall : ∀ x y : new.T lam,
      new.T.size x < new.T.size (new.T.P v a) →
      new.T.size y < new.T.size (new.T.P v a) →
      new.T.isNF x → new.T.isNF y →
      x < y → trans x < trans y) :
    T.isNF1 (trans (new.T.P v a)) := by
  cases hs with
  | p _ _ h0 h1 h2 h3 =>
      have hvGood :
          ∀ x : new.T lam, x ∈ new.Vec.toList v →
            T.isNF1 (trans x) ∧
              (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
        intro x hx
        have hsx : new.T.size x < new.T.size (new.T.P v a) :=
          oc_mem_size_lt_P v a x hx
        exact hgoodSmall x hsx ⟨h0 x hx, h2 x hx⟩
      have haNF : T.isNF1 (trans a) :=
        hnfSmall a (new.T.add_size_lt_P v a) h1
      have hhead : T.head (trans a) ≤ trans (new.T.P v new.T.Z) := by
        cases a with
        | Z =>
            rw [_root_.trans.eq_1, T.head]
            exact T.Z_le _
        | P w b =>
            have hwGood :
                ∀ x : new.T lam, x ∈ new.Vec.toList w →
                  T.isNF1 (trans x) ∧
                    (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
              intro x hx
              have hxa : new.T.size x < new.T.size (new.T.P w b) :=
                oc_mem_size_lt_P w b x hx
              have hap : new.T.size (new.T.P w b) <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                new.T.add_size_lt_P v (new.T.P w b)
              have hxp : new.T.size x <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                Nat.lt_trans hxa hap
              have hcomp : new.T.isNFComp x := by
                cases h1 with
                | p _ _ hw0 hb0 hw2 hbhead =>
                    exact ⟨hw0 x hx, hw2 x hx⟩
              exact hgoodSmall x hxp hcomp
            have hmono :
                ∀ x y : new.T lam,
                  x ∈ new.Vec.toList w → y ∈ new.Vec.toList v →
                  x < y → trans x < trans y := by
              intro x y hx hy hxy
              have hxa : new.T.size x < new.T.size (new.T.P w b) :=
                oc_mem_size_lt_P w b x hx
              have hap : new.T.size (new.T.P w b) <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                new.T.add_size_lt_P v (new.T.P w b)
              have hxp : new.T.size x <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                Nat.lt_trans hxa hap
              have hyp : new.T.size y <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                oc_mem_size_lt_P v (new.T.P w b) y hy
              have hxNF : new.T.isNF x := by
                cases h1 with
                | p _ _ hw0 hb0 hw2 hbhead => exact hw0 x hx
              have hyNF : new.T.isNF y := h0 y hy
              exact hpresSmall x y hxp hyp hxNF hyNF hxy
            exact nfcore_trans_head_le_P w v b hwGood hvGood hmono h3
      exact nfcore_trans_P_of_components v a hvGood haNF hhead

#print axioms nfcore_NF_step

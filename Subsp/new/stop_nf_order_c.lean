import Subsp.new.stop_nf_order_b

open T



-- extracted from Subsp/new/stop_solve_good.lean
theorem sg_add_interval_size_le (a b x : T)
    (hax : a ≤ x) (hxu : x < T.add a b) :
    a.size ≤ x.size := by
  induction a generalizing x with
  | Z => exact Nat.zero_le x.size
  | P p c d ihc ihd =>
      cases hax with
      | inr heq =>
          rw [heq]
          exact Nat.le_refl x.size
      | inl hlt =>
          have hu : T.add (T.P p c d) b = T.P p c (T.add d b) :=
            T.P_add_eq p c d b
          rw [hu] at hxu
          obtain ⟨e, hex, hde, heu⟩ :=
            sandwich_tail p c d x (T.add d b) hlt hxu
          rw [hex]
          have hsz : d.size ≤ e.size :=
            ihd e (Or.inl hde) heu
          change c.size + d.size + 1 ≤ c.size + e.size + 1
          exact Nat.add_le_add_right (Nat.add_le_add_left hsz c.size) 1

#print axioms sg_add_interval_size_le

theorem sg_good0_part_fst (s : T)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.part s).1 → x < (T.part s).1 := by
  intro x hx
  let a := (T.part s).1
  let b := (T.part s).2
  have hadd : T.add a b = s := by
    unfold a b
    exact bridge_part_add s
  have hxadd : x ∈ T.G1 0 (T.add a b) := by
    rw [bridge_G1_add_eq]
    exact List.mem_append_left (T.G1 0 b) hx
  have hxsin : x ∈ T.G1 0 s := by
    rw [← hadd]
    exact hxadd
  have hxs : x < s := hg x hxsin
  have hxsz : x.size < a.size := G1_size_lt 0 a x hx
  cases lt_total_thm x a with
  | inl hxa => exact hxa
  | inr hor =>
      cases hor with
      | inl hax =>
          have hsz : a.size ≤ x.size := by
            apply sg_add_interval_size_le a b x (Or.inl hax)
            rw [hadd]
            exact hxs
          exact False.elim ((Nat.not_lt_of_ge hsz) hxsz)
      | inr heq =>
          rw [heq] at hxsz
          exact False.elim (Nat.lt_irrefl a.size hxsz)

#print axioms sg_good0_part_fst

theorem sg_early_G0_le (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.early_collapse s) → x ≤ s := by
  intro x hx
  cases hp : T.part s with
  | mk a b =>
      have hadd := bridge_part_add s
      rw [hp] at hadd
      have hparts := nfaux_part_NF1 s hs
      rw [hp] at hparts
      have hbNF : T.isNF1 b := hparts.2
      have hec := bridge_early_collapse_part s a b hp hbNF
      have haLe : a ≤ s := by
        have h := bridge_part_fst_le_self s
        rw [hp] at h
        exact h
      have hmemB : ∀ y : T, y ∈ T.G1 0 b → y < s := by
        intro y hy
        apply hg y
        rw [← hadd, bridge_G1_add_eq]
        exact List.mem_append_right _ hy
      by_cases_dec ha : a = T.Z
      · rw [hec, ite_eq_left ha] at hx
        exact Or.inl (hmemB x hx)
      · rw [hec, ite_eq_right ha] at hx
        by_cases_dec hkeep : T.head b ≤ T.P 0 a T.Z
        · rw [ite_eq_left hkeep] at hx
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)] at hx
          cases List.mem_append.mp hx with
          | inl hleft =>
              cases List.mem_append.mp hleft with
              | inl hsingle =>
                  have hxa : x = a := List.mem_singleton.mp hsingle
                  rw [hxa]
                  exact haLe
              | inr hGa =>
                  have hgoodA := sg_good0_part_fst s hg
                  rw [hp] at hgoodA
                  exact Or.inl (lt_of_lt_of_le_thm T x a s
                    (hgoodA x hGa) haLe)
          | inr hGb =>
              exact Or.inl (hmemB x hGb)
        · rw [ite_eq_right hkeep] at hx
          exact Or.inl (hmemB x hx)

#print axioms sg_early_G0_le

theorem sg_tail_le_principal_add (i : Nat) (m b : T)
    (hb : T.isNF1 b)
    (hh : T.head b ≤ T.P i m T.Z) :
    b ≤ T.P i m b := by
  cases b with
  | Z => exact T.Z_le (T.P i m T.Z)
  | P q e f =>
      rw [T.head] at hh
      cases hh with
      | inl hlt =>
          cases lt_inv q e T.Z i m T.Z hlt with
          | inl hqi =>
              exact Or.inl (T.Lt.p_head q i e m f (T.P q e f) hqi)
          | inr hor =>
              cases hor with
              | inl hmid =>
                  have hqi : q = i := hmid.1
                  subst i
                  exact Or.inl (T.Lt.p_mid q e m f (T.P q e f) hmid.2)
              | inr htail =>
                  exact False.elim (lt_Z_inv htail.2.2)
      | inr heq =>
          injection heq with hqi hem
          subst i
          subst m
          have hfle : f ≤ T.P q e f :=
            T.isNF1_tail_le (T.P q e f) hb q e f rfl
          cases hfle with
          | inl hflt =>
              exact Or.inl (T.Lt.p_tail q e f (T.P q e f) hflt)
          | inr hfeq =>
              exact Or.inr (congrArg (fun z => T.P q e z) hfeq)

#print axioms sg_tail_le_principal_add

theorem sg_lt_principal_add (i : Nat) (m b x : T)
    (hb : T.isNF1 b)
    (hh : T.head b ≤ T.P i m T.Z)
    (hxb : x < b) :
    x < T.P i m b := by
  have hble := sg_tail_le_principal_add i m b hb hh
  exact lt_of_lt_of_le_thm T x b (T.P i m b) hxb hble

#print axioms sg_lt_principal_add



-- extracted from Subsp/new/stop_good_core1.lean
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



-- extracted from Subsp/new/stop_support_work.lean
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



-- extracted from Subsp/new/stop_card_support.lean
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



-- extracted from Subsp/new/stop_aux_support.lean
theorem as_card1_support_pair {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ z : new.T lam, z ∈ new.Vec.toList v →
        T.isNF1 (trans z) ∧
          (∀ y : T, y ∈ T.G1 0 (trans z) → y < trans z)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        (∀ x : T, x ∈ T.G1 0 (T.card_times 1 sum) →
          x < T.P 1 (T.card_times 1 sum) T.Z ∨
            ∃ z : new.T lam, z ∈ new.Vec.toList v ∧ x ≤ trans z) ∧
        (∀ x : T, x ∈ T.G1 0 (T.card_times 1 (T.one_del sum)) →
          x < T.P 1 (T.card_times 1 (T.one_del sum)) T.Z ∨
            ∃ z : new.T lam, z ∈ new.Vec.toList v ∧ x ≤ trans z) := by
  intro k
  induction k with
  | zero =>
      intro v hcoord found sum a0 haux
      cases v with
      | @snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              cases haux
              constructor
              · intro x hx
                rw [T.card_times.eq_1, T.G1.eq_1] at hx
                cases hx
              · intro x hx
                change x ∈ T.G1 0 (T.card_times 1 T.Z) at hx
                rw [T.card_times.eq_1, T.G1.eq_1] at hx
                cases hx
  | succ m ih =>
      intro v hcoord found sum a0 haux
      cases v with
      | @snoc n xs a =>
          have hxs :
              ∀ z : new.T lam, z ∈ new.Vec.toList xs →
                T.isNF1 (trans z) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans z) → y < trans z) := by
            intro z hz
            exact hcoord z (List.mem_append_left [a] hz)
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
                  have hpair := ih xs hxs foundRest sumRest a0Rest hrest
                  have hrestCard := sc_transAux_card1_inv xs hxs
                    foundRest sumRest a0Rest hrest
                  rw [transAux.eq_3, hrest] at haux
                  cases a with
                  | Z =>
                      rw [_root_.trans.eq_1] at haux
                      change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
                      cases haux
                      constructor
                      · intro x hx
                        cases hpair.1 x hx with
                        | inl hlt => exact Or.inl hlt
                        | inr hw =>
                            obtain ⟨z, hz, hxz⟩ := hw
                            exact Or.inr ⟨z,
                              List.mem_append_left [new.T.Z] hz, hxz⟩
                      · intro x hx
                        cases hpair.2 x hx with
                        | inl hlt => exact Or.inl hlt
                        | inr hw =>
                            obtain ⟨z, hz, hxz⟩ := hw
                            exact Or.inr ⟨z,
                              List.mem_append_left [new.T.Z] hz, hxz⟩
                  | P als aadd =>
                      have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
                        intro h
                        cases h
                      have hatNe : trans (new.T.P als aadd) ≠ T.Z :=
                        tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
                      have hec := bridge_early_collapse_closed
                        (trans (new.T.P als aadd)) ha.1 ha.2
                      have hecNe := bridge_early_collapse_ne_Z
                        (trans (new.T.P als aadd)) hatNe
                      change
                        (true,
                          T.card_times m
                              (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                          a0Rest) = (found, sum, a0) at haux
                      cases haux
                      let ec := T.early_collapse (trans (new.T.P als aadd))
                      let B := T.card_times (m + 1) ec
                      let R := T.card_times 1 sumRest
                      let A := T.add B R
                      have hBA : B ≤ A := by
                        unfold A
                        exact wt_add_self_le B R
                      have hRB : R < B := by
                        unfold R B ec
                        exact hrestCard.2.2.2
                          (T.early_collapse (trans (new.T.P als aadd)))
                          hec.1 hec.2.1 hecNe
                      have hU :
                          ∀ x : T, x ∈ T.G1 0 A →
                            x < T.P 1 A T.Z ∨
                              ∃ z : new.T lam,
                                z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                                x ≤ trans z := by
                        intro x hx
                        unfold A at hx ⊢
                        rw [bridge_G1_add_eq] at hx
                        cases List.mem_append.mp hx with
                        | inl hBmem =>
                            have hcur := cs_card_support m ec
                              (trans (new.T.P als aadd)) hec.1 hec.2.1
                              (sg_early_G0_le (trans (new.T.P als aadd)) ha.1 ha.2)
                              x hBmem
                            cases hcur with
                            | inl hlt =>
                                have hLift := bridge_lift_P1_le B (T.add B R)
                                  (wt_add_self_le B R)
                                exact Or.inl (lt_of_lt_of_le_thm T x
                                  (T.P 1 B T.Z) (T.P 1 (T.add B R) T.Z)
                                  hlt hLift)
                            | inr hxcoord =>
                                exact Or.inr ⟨new.T.P als aadd,
                                  List.mem_append_right (new.Vec.toList xs)
                                    (List.mem_singleton_self (new.T.P als aadd)),
                                  hxcoord⟩
                        | inr hRmem =>
                            have hrestDec := hpair.1 x hRmem
                            cases hrestDec with
                            | inr hw =>
                                obtain ⟨z, hz, hxz⟩ := hw
                                exact Or.inr ⟨z,
                                  List.mem_append_left [new.T.P als aadd] hz,
                                  hxz⟩
                            | inl hlt =>
                                have hRA : R < T.add B R :=
                                  lt_of_lt_of_le_thm T R B (T.add B R) hRB
                                    (wt_add_self_le B R)
                                have hLift : T.P 1 R T.Z < T.P 1 (T.add B R) T.Z :=
                                  T.Lt.p_mid 1 R (T.add B R) T.Z T.Z hRA
                                exact Or.inl (lt_trans_thm x (T.P 1 R T.Z)
                                  (T.P 1 (T.add B R) T.Z) hlt hLift)
                      have hsumCard : T.card_times 1
                            (T.add (T.card_times m ec) sumRest) = A := by
                        unfold A B R
                        rw [ca_card_times_add, ca_card_times_one_comp]
                      constructor
                      · intro x hx
                        change x ∈ T.G1 0
                          (T.card_times 1
                            (T.add (T.card_times m ec) sumRest)) at hx
                        change x < T.P 1
                            (T.card_times 1
                              (T.add (T.card_times m ec) sumRest)) T.Z ∨
                          ∃ z : new.T lam,
                            z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                            x ≤ trans z
                        rw [hsumCard] at hx ⊢
                        exact hU x hx
                      · cases m with
                        | zero =>
                            cases xs with
                            | @snoc q ys b =>
                                cases ys with
                                | nil =>
                                    rw [transAux.eq_2] at hrest
                                    cases hrest
                                    change
                                      ∀ x : T,
                                        x ∈ T.G1 0
                                          (T.card_times 1
                                            (T.one_del
                                              (T.add (T.card_times 0 ec) T.Z))) →
                                        x < T.P 1
                                          (T.card_times 1
                                            (T.one_del
                                              (T.add (T.card_times 0 ec) T.Z))) T.Z ∨
                                          ∃ z : new.T lam,
                                            z ∈ new.Vec.toList
                                              (new.Vec.snoc 1
                                                (new.Vec.snoc 0 new.Vec.nil b)
                                                (new.T.P als aadd)) ∧
                                            x ≤ trans z
                                    rw [tc_card_times_zero, T.add_Z]
                                    have hdel := oc_one_del_NF_index0 ec hec.1 hec.2.1
                                    intro x hx
                                    have hbase := cs_card_support 0 (T.one_del ec)
                                      (trans (new.T.P als aadd)) hdel.1 hdel.2
                                      (by
                                        intro y hy
                                        exact sg_early_G0_le
                                          (trans (new.T.P als aadd)) ha.1 ha.2 y
                                          (cs_one_del_G0 ec y hy))
                                      x hx
                                    cases hbase with
                                    | inl hlt => exact Or.inl hlt
                                    | inr hle =>
                                        exact Or.inr ⟨new.T.P als aadd,
                                          List.mem_append_right
                                            (new.Vec.toList
                                              (new.Vec.snoc 0 new.Vec.nil b))
                                            (List.mem_singleton_self
                                              (new.T.P als aadd)), hle⟩
                        | succ j =>
                            have hdel :
                                T.one_del
                                    (T.add (T.card_times (j + 1) ec) sumRest) =
                                  T.add (T.card_times (j + 1) ec) sumRest :=
                              cs_one_del_card_succ_add j ec sumRest hec.2.1 hecNe
                            intro x hx
                            change x ∈ T.G1 0
                              (T.card_times 1
                                (T.one_del
                                  (T.add (T.card_times (j + 1) ec) sumRest))) at hx
                            change x < T.P 1
                                (T.card_times 1
                                  (T.one_del
                                    (T.add (T.card_times (j + 1) ec) sumRest))) T.Z ∨
                              ∃ z : new.T lam,
                                z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                                x ≤ trans z
                            rw [hdel] at hx ⊢
                            have hcardEq : T.card_times 1
                                (T.add (T.card_times (j + 1) ec) sumRest) =
                              T.add (T.card_times (j + 2) ec)
                                (T.card_times 1 sumRest) := by
                              rw [ca_card_times_add, ca_card_times_one_comp]
                            rw [hcardEq] at hx ⊢
                            change x ∈ T.G1 0 (T.add
                              (T.card_times (j + 2) ec) R) at hx
                            change x < T.P 1
                              (T.add (T.card_times (j + 2) ec) R) T.Z ∨
                              ∃ z : new.T lam,
                                z ∈ new.Vec.toList xs ++ [new.T.P als aadd] ∧
                                x ≤ trans z
                            exact hU x hx

#print axioms as_card1_support_pair



-- extracted from Subsp/new/stop_trans_support.lean
theorem ts_transAux_a0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        a0 = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  intro k
  induction k with
  | zero =>
      intro v found sum a0 haux
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              have ha0 : a0 = trans a :=
                congrArg (fun q : Bool × T × T => q.2.2) haux.symm
              change a0 = trans
                (if h : 0 < 0 then new.Vec.idx new.Vec.nil ⟨0, h⟩ else a)
              rw [dite_eq_right (Nat.lt_irrefl 0)]
              exact ha0
  | succ m ih =>
      intro v found sum a0 haux
      cases v with
      | @snoc n xs a =>
          cases hrest : transAux xs with
          | mk foundRest rest =>
              cases rest with
              | mk sumRest a0Rest =>
                  rw [transAux.eq_3, hrest] at haux
                  have ha0eq : a0 = a0Rest :=
                    congrArg (fun q : Bool × T × T => q.2.2) haux.symm
                  have hrec := ih xs foundRest sumRest a0Rest hrest
                  rw [ha0eq, hrec]
                  change trans (new.Vec.idx xs ⟨0, Nat.zero_lt_succ m⟩) =
                    trans (if h : 0 < m + 1 then
                      new.Vec.idx xs ⟨0, h⟩ else a)
                  rw [dite_eq_left (Nat.zero_lt_succ m)]

#print axioms ts_transAux_a0

theorem ts_coord_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.Vec.toList v) :
    z ∈ new.T.G (new.T.P v a) := by
  obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v z hz
  rw [new.T.G_P_eq]
  apply List.mem_append_left (new.T.G a)
  rw [← hi]
  exact new.Vec.Gres_mem_of_idx v i

#print axioms ts_coord_mem_G

theorem ts_tail_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.G a) :
    z ∈ new.T.G (new.T.P v a) := by
  rw [new.T.G_P_eq]
  exact List.mem_append_right (new.T.G.res v) hz

#print axioms ts_tail_mem_G

theorem ts_P1Z_le_tail (m tail : T) :
    T.P 1 m T.Z ≤ T.P 1 m tail := by
  cases T.Z_le tail with
  | inl hlt => exact Or.inl (T.Lt.p_tail 1 m T.Z tail hlt)
  | inr heq =>
      rw [← heq]
      exact Or.inr rfl

#print axioms ts_P1Z_le_tail

theorem ts_support_decomp_step {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s)
    (ht : T.isNF1 (trans s))
    (hgoodSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size s → new.T.isNFComp x →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hdecompSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size s → new.T.isNF x →
        ∀ y : T, y ∈ T.G1 0 (trans x) →
          y < trans x ∨
            ∃ z : new.T lam, z ∈ new.T.G x ∧ y ≤ trans z) :
    ∀ y : T, y ∈ T.G1 0 (trans s) →
      y < trans s ∨
        ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z := by
  cases s with
  | Z =>
      intro y hy
      rw [_root_.trans.eq_1, T.G1.eq_1] at hy
      cases hy
  | P v a =>
      cases hs with
      | p _ _ hvNF haNF hvG hhead =>
          have hcoord :
              ∀ z : new.T lam, z ∈ new.Vec.toList v →
                T.isNF1 (trans z) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans z) → y < trans z) := by
            intro z hz
            have hsz := oc_mem_size_lt_P v a z hz
            exact hgoodSmall z hsz ⟨hvNF z hz, hvG z hz⟩
          have htailDecomp :
              ∀ y : T, y ∈ T.G1 0 (trans a) →
                y < trans a ∨
                  ∃ z : new.T lam, z ∈ new.T.G a ∧ y ≤ trans z :=
            hdecompSmall a (new.T.add_size_lt_P v a) haNF
          cases lam with
          | zero =>
              cases v with
              | nil =>
                  rw [_root_.trans.eq_2, transAux.eq_1] at ht ⊢
                  change
                    ∀ y : T, y ∈ T.G1 0 (T.P 0 T.Z (trans a)) →
                      y < T.P 0 T.Z (trans a) ∨
                        ∃ z : new.T 0,
                          z ∈ new.T.G (new.T.P new.Vec.nil a) ∧ y ≤ trans z
                  intro y hy
                  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                    List.mem_append, List.mem_append] at hy
                  cases hy with
                  | inl hleft =>
                      cases hleft with
                      | inl hz =>
                          have hyz : y = T.Z := List.mem_singleton.mp hz
                          rw [hyz]
                          exact Or.inl (T.Lt.Z_lt_P 0 T.Z (trans a))
                      | inr hzG =>
                          rw [T.G1.eq_1] at hzG
                          cases hzG
                  | inr htail =>
                      cases htailDecomp y htail with
                      | inl hya =>
                          have htle := T.isNF1_tail_le
                            (T.P 0 T.Z (trans a)) ht 0 T.Z (trans a) rfl
                          exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                            (T.P 0 T.Z (trans a)) hya htle)
                      | inr hw =>
                          obtain ⟨z, hz, hyz⟩ := hw
                          exact Or.inr ⟨z,
                            ts_tail_mem_G new.Vec.nil a z hz, hyz⟩
          | succ k =>
              cases haux : transAux v with
              | mk found rest =>
                  cases rest with
                  | mk sum a0 =>
                      have ha0eq := ts_transAux_a0 v found sum a0 haux
                      have hauxSupp := as_card1_support_pair v hcoord
                        found sum a0 haux
                      have hauxInv := tc_transAux_inv v hcoord
                        found sum a0 haux
                      rw [_root_.trans.eq_2, haux] at ht ⊢
                      change T.isNF1
                        (if found = true then
                          T.P 1
                            (T.add (T.card_times 1 (T.one_del sum))
                              (T.early_collapse a0)) (trans a)
                        else if a0 = T.Z then T.P 0 T.Z (trans a)
                        else T.P 0 a0 (trans a)) at ht
                      change ∀ y : T,
                        y ∈ T.G1 0
                            (if found = true then
                              T.P 1
                                (T.add (T.card_times 1 (T.one_del sum))
                                  (T.early_collapse a0)) (trans a)
                            else if a0 = T.Z then T.P 0 T.Z (trans a)
                            else T.P 0 a0 (trans a)) →
                          (y <
                              (if found = true then
                                T.P 1
                                  (T.add (T.card_times 1 (T.one_del sum))
                                    (T.early_collapse a0)) (trans a)
                              else if a0 = T.Z then T.P 0 T.Z (trans a)
                              else T.P 0 a0 (trans a)) ∨
                            ∃ z : new.T (k + 1),
                              z ∈ new.T.G (new.T.P v a) ∧ y ≤ trans z)
                      by_cases_dec hf : found = true
                      · rw [ite_eq_left hf] at ht ⊢
                        let A := T.card_times 1 (T.one_del sum)
                        let E := T.early_collapse a0
                        let M := T.add A E
                        have hMclosed := pn_aux_found_middle_closed v hcoord
                          found sum a0 haux hf
                        change T.isNF1 (T.P 1 M (trans a)) at ht
                        have hMwrap : M < T.P 1 M T.Z :=
                          cs_self_lt_wrap M hMclosed.1 hMclosed.2.1 hMclosed.2.2
                        have hMfull : M < T.P 1 M (trans a) :=
                          lt_of_lt_of_le_thm T M (T.P 1 M T.Z)
                            (T.P 1 M (trans a)) hMwrap (ts_P1Z_le_tail M (trans a))
                        intro y hy
                        change y ∈ T.G1 0 (T.P 1 M (trans a)) at hy
                        rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
                          List.mem_append, List.mem_append] at hy
                        cases hy with
                        | inl hleft =>
                            cases hleft with
                            | inl hmid =>
                                have hym : y = M := List.mem_singleton.mp hmid
                                rw [hym]
                                exact Or.inl hMfull
                            | inr hGM =>
                                unfold M at hGM
                                rw [bridge_G1_add_eq] at hGM
                                cases List.mem_append.mp hGM with
                                | inl hA =>
                                    have hdec := hauxSupp.2 y hA
                                    cases hdec with
                                    | inl hlt =>
                                        have hAle : A ≤ T.add A E := wt_add_self_le A E
                                        have hLift := bridge_lift_P1_le A (T.add A E) hAle
                                        have hyMZ : y < T.P 1 M T.Z := by
                                          unfold M
                                          exact lt_of_lt_of_le_thm T y (T.P 1 A T.Z)
                                            (T.P 1 (T.add A E) T.Z) hlt hLift
                                        exact Or.inl (lt_of_lt_of_le_thm T y
                                          (T.P 1 M T.Z) (T.P 1 M (trans a))
                                          hyMZ (ts_P1Z_le_tail M (trans a)))
                                    | inr hw =>
                                        obtain ⟨z, hz, hyz⟩ := hw
                                        exact Or.inr ⟨z, ts_coord_mem_G v a z hz, hyz⟩
                                | inr hE =>
                                    have ha0good := hauxInv.1
                                    have ha0G := hauxInv.2.1
                                    have hy0 : y ≤ a0 :=
                                      sg_early_G0_le a0 ha0good ha0G y hE
                                    let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                                    have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                                      new.Vec.idx_mem_toList v i0
                                    have htrans0 : trans (v.idx i0) = a0 := by
                                      exact ha0eq.symm
                                    exact Or.inr ⟨v.idx i0,
                                      ts_coord_mem_G v a (v.idx i0) hiMem,
                                      by rw [htrans0]; exact hy0⟩
                        | inr htail =>
                            cases htailDecomp y htail with
                            | inl hya =>
                                have htle := T.isNF1_tail_le
                                  (T.P 1 M (trans a)) ht 1 M (trans a) rfl
                                exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                                  (T.P 1 M (trans a)) hya htle)
                            | inr hw =>
                                obtain ⟨z, hz, hyz⟩ := hw
                                exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩
                      · rw [ite_eq_right hf] at ht ⊢
                        by_cases_dec ha0z : a0 = T.Z
                        · rw [ite_eq_left ha0z] at ht ⊢
                          intro y hy
                          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                            List.mem_append, List.mem_append] at hy
                          cases hy with
                          | inl hleft =>
                              cases hleft with
                              | inl hz =>
                                  have hyz : y = T.Z := List.mem_singleton.mp hz
                                  rw [hyz]
                                  exact Or.inl (T.Lt.Z_lt_P 0 T.Z (trans a))
                              | inr hzG =>
                                  rw [T.G1.eq_1] at hzG
                                  cases hzG
                          | inr htail =>
                              cases htailDecomp y htail with
                              | inl hya =>
                                  have htle := T.isNF1_tail_le
                                    (T.P 0 T.Z (trans a)) ht 0 T.Z (trans a) rfl
                                  exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                                    (T.P 0 T.Z (trans a)) hya htle)
                              | inr hw =>
                                  obtain ⟨z, hz, hyz⟩ := hw
                                  exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩
                        · rw [ite_eq_right ha0z] at ht ⊢
                          intro y hy
                          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                            List.mem_append, List.mem_append] at hy
                          cases hy with
                          | inl hleft =>
                              cases hleft with
                              | inl ha0mem =>
                                  have hya0 : y = a0 := List.mem_singleton.mp ha0mem
                                  let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                                  have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                                    new.Vec.idx_mem_toList v i0
                                  exact Or.inr ⟨v.idx i0,
                                    ts_coord_mem_G v a (v.idx i0) hiMem,
                                    by
                                      rw [hya0, ← ha0eq]
                                      exact Or.inr rfl⟩
                              | inr hGa0 =>
                                  let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                                  have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                                    new.Vec.idx_mem_toList v i0
                                  have hgood0 := hcoord (v.idx i0) hiMem
                                  have htrans0 : trans (v.idx i0) = a0 := ha0eq.symm
                                  have hlt0 : y < a0 := hauxInv.2.1 y hGa0
                                  exact Or.inr ⟨v.idx i0,
                                    ts_coord_mem_G v a (v.idx i0) hiMem,
                                    Or.inl (by rw [htrans0]; exact hlt0)⟩
                          | inr htail =>
                              cases htailDecomp y htail with
                              | inl hya =>
                                  have htle := T.isNF1_tail_le
                                    (T.P 0 a0 (trans a)) ht 0 a0 (trans a) rfl
                                  exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                                    (T.P 0 a0 (trans a)) hya htle)
                              | inr hw =>
                                  obtain ⟨z, hz, hyz⟩ := hw
                                  exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩

#print axioms ts_support_decomp_step



-- extracted from Subsp/new/stop_bound_order.lean
theorem bo_order_preserve_bounded {lam : Nat} (N : Nat)
    (hgood : ∀ x : new.T lam, new.T.size x < N → new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.size s ≤ N → new.T.size t ≤ N →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.size s ≤ N → new.T.size t ≤ N →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s t hsize hsN htN hs ht hst
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
                  have hsx : new.T.size x < new.T.size (new.T.P v a) :=
                    oc_mem_size_lt_P v a x hx
                  have hxN : new.T.size x < N :=
                    Nat.lt_of_lt_of_le hsx hsN
                  exact hgood x hxN ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have htx : new.T.size x < new.T.size (new.T.P w b) :=
                    oc_mem_size_lt_P w b x hx
                  have hxN : new.T.size x < N :=
                    Nat.lt_of_lt_of_le htx htN
                  exact hgood x hxN ⟨hwNF x hx, hwG x hx⟩
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
                  have hxN : new.T.size x ≤ N :=
                    Nat.le_trans (Nat.le_of_lt hsx) hsN
                  have hyN : new.T.size y ≤ N :=
                    Nat.le_trans (Nat.le_of_lt hty) htN
                  exact ih (new.T.size x + new.T.size y) hsum'
                    x y rfl hxN hyN (hvNF x hx) (hwNF y hy) hxy
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
                have haN : new.T.size a ≤ N :=
                  Nat.le_trans (Nat.le_of_lt hsa) hsN
                have hbN : new.T.size b ≤ N :=
                  Nat.le_trans (Nat.le_of_lt htb) htN
                have htail := ih (new.T.size a + new.T.size b) hsum'
                  a b rfl haN hbN haNF hbNF hst
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
  intro s t hsN htN hs ht hst
  exact main (new.T.size s + new.T.size t) s t rfl hsN htN hs ht hst

#print axioms bo_order_preserve_bounded

theorem bo_transAux_a0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (transAux v).2.2 = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  intro k
  induction k with
  | zero =>
      intro v
      cases v with
      | @snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2]
              rfl
  | succ m ih =>
      intro v
      cases v with
      | @snoc n xs a =>
          rw [transAux.eq_3]
          cases haux : transAux xs with
          | mk found rest =>
              cases rest with
              | mk sum a0 =>
                  change a0 = trans (new.Vec.idx (new.Vec.snoc (m + 1) xs a)
                    ⟨0, Nat.zero_lt_succ (m + 1)⟩)
                  change a0 = trans (new.Vec.idx xs ⟨0, Nat.zero_lt_succ m⟩)
                  have h := ih xs
                  rw [haux] at h
                  exact h

#print axioms bo_transAux_a0



-- extracted from Subsp/new/stop_global_nf.lean
theorem gnf_all {lam : Nat} :
    ∀ s : new.T lam,
      (new.T.isNF s → T.isNF1 (trans s)) ∧
      (new.T.isNF s →
        ∀ y : T, y ∈ T.G1 0 (trans s) →
          y < trans s ∨
            ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z) ∧
      (new.T.isNFComp s →
        T.isNF1 (trans s) ∧
          (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s)) := by
  let motive : Nat → Prop := fun n =>
    ∀ s : new.T lam, new.T.size s = n →
      (new.T.isNF s → T.isNF1 (trans s)) ∧
      (new.T.isNF s →
        ∀ y : T, y ∈ T.G1 0 (trans s) →
          y < trans s ∨
            ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z) ∧
      (new.T.isNFComp s →
        T.isNF1 (trans s) ∧
          (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s))
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s hsize
      have hsmall :
          ∀ x : new.T lam, new.T.size x < new.T.size s →
            (new.T.isNF x → T.isNF1 (trans x)) ∧
            (new.T.isNF x →
              ∀ y : T, y ∈ T.G1 0 (trans x) →
                y < trans x ∨
                  ∃ z : new.T lam, z ∈ new.T.G x ∧ y ≤ trans z) ∧
            (new.T.isNFComp x →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) := by
        intro x hx
        have hxn : new.T.size x < n := by
          rw [← hsize]
          exact hx
        exact ih (new.T.size x) hxn x rfl
      have hgoodSmall :
          ∀ x : new.T lam, new.T.size x < new.T.size s →
            new.T.isNFComp x →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
        intro x hx hcomp
        exact (hsmall x hx).2.2 hcomp
      have hpresBound :
          ∀ x y : new.T lam,
            new.T.size x ≤ new.T.size s →
            new.T.size y ≤ new.T.size s →
            new.T.isNF x → new.T.isNF y →
            x < y → trans x < trans y := by
        exact bo_order_preserve_bounded (new.T.size s) hgoodSmall
      have hNF : new.T.isNF s → T.isNF1 (trans s) := by
        intro hs
        cases s with
        | Z =>
            rw [_root_.trans.eq_1]
            exact T.isNF1.z
        | P v a =>
            exact nfcore_NF_step v a hs
              (fun x hx hnx => (hsmall x hx).1 hnx)
              hgoodSmall
              (fun x y hx hy hnx hny hxy =>
                hpresBound x y (Nat.le_of_lt hx) (Nat.le_of_lt hy)
                  hnx hny hxy)
      have hDecomp :
          new.T.isNF s →
            ∀ y : T, y ∈ T.G1 0 (trans s) →
              y < trans s ∨
                ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z := by
        intro hs
        exact ts_support_decomp_step s hs (hNF hs)
          hgoodSmall
          (fun x hx hnx => (hsmall x hx).2.1 hnx)
      have hGood :
          new.T.isNFComp s →
            T.isNF1 (trans s) ∧
              (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s) := by
        intro hscomp
        constructor
        · exact hNF hscomp.1
        · intro y hy
          cases hDecomp hscomp.1 y hy with
          | inl hlt => exact hlt
          | inr hw =>
              obtain ⟨z, hz, hyz⟩ := hw
              have hzComp : new.T.isNFComp z :=
                new.T.isNF_G_isNFComp s hscomp.1 z hz
              have hzsSize : new.T.size z < new.T.size s :=
                new.T.G_size_lt s z hz
              have hzs : z < s := hscomp.2 z hz
              have htrans : trans z < trans s :=
                hpresBound z s (Nat.le_of_lt hzsSize) (Nat.le_refl _) hzComp.1 hscomp.1 hzs
              exact lt_of_le_of_lt_thm T y (trans z) (trans s) hyz htrans
      exact ⟨hNF, hDecomp, hGood⟩)
  intro s
  exact main (new.T.size s) s rfl

#print axioms gnf_all

theorem gnf_NF_is_NF1 {lam : Nat} (s : new.T lam) :
    new.T.isNF s → T.isNF1 (trans s) := by
  exact (gnf_all s).1

#print axioms gnf_NF_is_NF1

theorem gnf_good {lam : Nat} (s : new.T lam) :
    new.T.isNFComp s →
      T.isNF1 (trans s) ∧
        (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s) := by
  exact (gnf_all s).2.2

#print axioms gnf_good

theorem gnf_order_embedding {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  exact oc_order_embedding_core (fun x hx => gnf_good x hx) s t hs ht

#print axioms gnf_order_embedding

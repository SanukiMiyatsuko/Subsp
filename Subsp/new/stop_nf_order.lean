import Subsp.new.stop_algebra

/-! Normal-form preservation, order embedding, translation bounds, and well-foundedness. -/

/-! Principal normal forms and order comparison. -/

section NormalFormAndOrder

open T

theorem cb_shift_le_of_le (k : Nat) (a c : T)
    (ha : T.isNF1 a) (hc : T.isNF1 c)
    (hgc : ∀ x : T, x ∈ T.G1 0 c → x < c)
    (hca : c ≤ a) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse c) ≤
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a) := by
  rcases hca with hlt | heq
  · exact Or.inl (bridge_add_left_lt
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
      (T.early_collapse c) (T.early_collapse a)
      (bridge_early_collapse_lt c a hc hgc ha hlt))
  · rw [heq]
    exact Or.inr rfl

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
    wt_add_self_le _ c
  have hwrap :
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z ≤
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) c) T.Z := by
    rcases hpref with hlt | heq
    · exact Or.inl (T.Lt.p_mid 1 _ _ T.Z T.Z hlt)
    · have hterm :
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
      intro L _ _ hL hiL hgL hbound
      change T.isNF1 L ∧ T.index_Prop1 1 L ∧
        (∀ x : T, x ∈ T.G1 1 L → x < L) ∧
        L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z
      exact ⟨hL, hiL, hgL,
        lt_trans_thm L
          (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z)
          (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z)
          hbound (cb_threshold_step n)⟩
  | P p a b _ ihb =>
      intro L hE hiE hL hiL hgL hbound
      cases hiE with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        cases hp0
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
                cases hq0
                have hbc := T.isNF1_P_inv 0 c d hbNF
                have hcNF := hbc.1
                have hcG0 := hbc.2.2.1
                have hca := bridge_P0_head_mid_le a c d hinv.2.2.2
                have hshift := cb_shift_le_of_le n a c haNF hcNF hcG0 hca
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
                rcases hshift with hlt | heq
                · exact Or.inl (T.Lt.p_mid 1 _ _ T.Z T.Z hlt)
                · rw [heq]; exact Or.inr rfl
        have hwholeNF : T.isNF1 (T.P 1 M Rtail) :=
          T.isNF1.p 1 M Rtail hmNF htailNF hmG hhead
        have hwholeG : ∀ x : T, x ∈ T.G1 1 (T.P 1 M Rtail) →
            x < T.P 1 M Rtail := by
          intro x hx
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
            List.mem_append, List.mem_append] at hx
          rcases hx with (hmemb | hxM) | hxt
          · have heq : x = M := List.mem_singleton.mp hmemb
            rw [heq]
            unfold M
            exact bridge_shift_lt_outer n (T.early_collapse a) Rtail hec.2.1
          · have hxm := hmG x hxM
            have hmwhole : M < T.P 1 M Rtail := by
              unfold M
              exact bridge_shift_lt_outer n (T.early_collapse a) Rtail hec.2.1
            exact lt_trans_thm x M _ hxm hmwhole
          · have hxt' := htailG x hxt
            have htle := T.isNF1_tail_le (T.P 1 M Rtail) hwholeNF
              1 M Rtail rfl
            exact lt_of_lt_of_le_thm T x Rtail (T.P 1 M Rtail) hxt' htle
        have hupper : T.P 1 M Rtail <
            T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z := by
          unfold M
          have hrank :=
            bridge_shift_level_lt n (n + 1) (Nat.lt_succ_self n)
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
          cases hp0
          exact T.Lt.p_head 0 1 c T.Z d T.Z (Nat.zero_lt_succ 0)

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
            obtain ⟨sum, a0⟩ := rest
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

theorem pn_card_times_pos_shape (q : Nat) (c : T)
    (hc : T.index_Prop1 0 c) (hne : c ≠ T.Z) :
    ∃ m tail : T, T.card_times (q + 1) c = T.P 1 m tail := by
  cases c with
  | Z => exact False.elim (hne rfl)
  | P p a b =>
      cases hc with
      | p _ _ _ hp hb =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          cases hp0
          rw [T.card_times.eq_3, ite_eq_left rfl]
          refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat q))
              (T.early_collapse a), T.card_times (q + 1) b, ?_⟩
          rw [← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
          rfl

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
            obtain ⟨sumRest, a0Rest⟩ := rest
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
                            rw [tc_card_times_zero, T.add_Z]
                            exact hec.2.1
                | succ j =>
                    obtain ⟨mid, tail, hcard⟩ := pn_card_times_pos_shape j (T.early_collapse (trans (new.T.P als aadd))) hec.2.1 hecne
                    rw [hcard, T.P_add_eq] at hshape
                    cases hshape

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
              cases hp'
              have hone : T.one_del (T.P 1 c d) = T.P 1 c d := rfl
              rw [hone]
              have hres := pn_aux_card1_sum_append v hcoord
                (T.early_collapse a0) haec.1 haec.2.1 haec.2.2 hbaseBound
              rw [haux] at hres
              exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

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
        obtain ⟨sum, a0⟩ := rest
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
  rcases hlex with hlt | heq
  · rw [hswz, T.card_times.eq_1] at hlt
    exact lt_Z_inv hlt
  · have hcz : T.card_times 1 sv = T.Z := by
      rw [hswz, T.card_times.eq_1] at heq
      exact heq.1
    exact (bridge_card_times_ne_Z 1 sv hsvne) hcz

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
  rcases hlex with hlt | heq
  · rw [hsvz, hswz] at hlt
    exact False.elim (lt_irrefl_thm T.Z hlt)
  · exact heq.2

theorem oc_one_del_P0 (a b : T) :
    T.one_del (T.P 0 a b) = if a = T.Z then b else T.P 0 a b := by
  cases a <;> rfl

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
        cases hp0
        rw [oc_one_del_P0]
        by_cases ha : a = T.Z
        · rw [ite_eq_left ha]
          have hbNF := (T.isNF1_P_inv 0 a b hs).2.1
          exact ⟨hbNF, hbidx⟩
        · rw [ite_eq_right ha]
          exact ⟨hs, T.index_Prop1.p 0 a b (Nat.le_refl 0) hbidx⟩

theorem oc_P0Z_tail_shape (b : T)
    (hbNF : T.isNF1 b) (hhead : T.head b ≤ T.P 0 T.Z T.Z) :
    b = T.Z ∨ ∃ d : T, b = T.P 0 T.Z d := by
  cases b with
  | Z => exact Or.inl rfl
  | P q c d =>
      have hq0 : q = 0 := Nat.eq_zero_of_le_zero
        (head_le_index q 0 c T.Z hhead)
      cases hq0
      have hc0 : c = T.Z := by
        rcases hhead with hlt | heq
        · cases lt_inv 0 c T.Z 0 T.Z T.Z hlt with
          | inl hh => exact False.elim (Nat.lt_irrefl 0 hh)
          | inr hor =>
            rcases hor with hm | ht
            · exact False.elim (lt_Z_inv hm.2)
            · exact ht.2.1
        · cases heq
          rfl
      cases hc0
      exact Or.inr ⟨d, rfl⟩

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
      cases hpa0
      cases b with
      | Z => exact False.elim (hbNe rfl)
      | P pb ba bb =>
        cases hbIdx with
        | p _ _ _ hpb hbbIdx =>
          have hpb0 : pb = 0 := Nat.eq_zero_of_le_zero hpb
          cases hpb0
          rw [oc_one_del_P0, oc_one_del_P0]
          by_cases haaZ : aa = T.Z
          · rw [ite_eq_left haaZ]
            by_cases hbaZ : ba = T.Z
            · rw [ite_eq_left hbaZ]
              cases haaZ
              cases hbaZ
              rcases lt_inv 0 T.Z ab 0 T.Z bb hab with hh | (hm | ht)
              · exact False.elim (Nat.lt_irrefl 0 hh)
              · exact False.elim (lt_Z_inv hm.2)
              · exact ht.2.2
            · rw [ite_eq_right hbaZ]
              cases haaZ
              have habNF := (T.isNF1_P_inv 0 T.Z ab haNF).2.1
              have hheadab := (T.isNF1_P_inv 0 T.Z ab haNF).2.2.2
              rcases oc_P0Z_tail_shape ab habNF hheadab with hz | hp
              · rw [hz]
                exact T.Lt.Z_lt_P 0 ba bb
              · obtain ⟨d, hd⟩ := hp
                rw [hd]
                exact T.Lt.p_mid 0 T.Z ba d bb (tc_Z_lt_of_ne ba hbaZ)
          · rw [ite_eq_right haaZ]
            by_cases hbaZ : ba = T.Z
            · rw [ite_eq_left hbaZ]
              cases hbaZ
              rcases lt_inv 0 aa ab 0 T.Z bb hab with hh | (hm | ht)
              · exact False.elim (Nat.lt_irrefl 0 hh)
              · exact False.elim (lt_Z_inv hm.2)
              · have heq : aa = T.Z := ht.2.1
                exact False.elim (haaZ heq)
            · rw [ite_eq_right hbaZ]
              exact hab

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
          rcases lt_inv p a b q c d hst with hpq | (hmid | htail)
          · have hp0 : p = 0 := by
              cases p with
              | zero => rfl
              | succ p' =>
                have hp'0 : p' = 0 :=
                  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hp)
                cases hp'0
                have hqgt : 1 < q := hpq
                exact False.elim ((Nat.not_lt_of_ge hq) hqgt)
            have hq1 : q = 1 := by
              cases hp0
              cases q with
              | zero => exact False.elim (Nat.not_lt_zero 0 hpq)
              | succ q' =>
                have hq'0 : q' = 0 :=
                  Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hq)
                cases hq'0
                rfl
            cases hp0
            cases hq1
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
          · have hpq : p = q := hmid.1
            cases hpq
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
              cases hp'0
              have hsdel : T.one_del (T.P 1 a b) = T.P 1 a b :=
                T.one_del.eq_2 (T.P 1 a b) (by intro s2 h; cases h)
              have htdel : T.one_del (T.P 1 c d) = T.P 1 c d :=
                T.one_del.eq_2 (T.P 1 c d) (by intro s2 h; cases h)
              rw [hsdel, htdel]
              exact hst
          · have hpq : p = q := htail.1
            cases hpq
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
              cases hp'0
              have hsdel : T.one_del (T.P 1 a b) = T.P 1 a b :=
                T.one_del.eq_2 (T.P 1 a b) (by intro s2 h; cases h)
              have htdel : T.one_del (T.P 1 c d) = T.P 1 c d :=
                T.one_del.eq_2 (T.P 1 c d) (by intro s2 h; cases h)
              rw [hsdel, htdel]
              exact hst

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
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hp) with hp0 | hp1
    · cases hp0
      have hi0 : T.index_Prop1 0 (T.P 0 a b) :=
        isNF1_index 0 0 a b hs (Nat.le_refl 0)
      have h0 := oc_one_del_NF_index0 (T.P 0 a b) hs hi0
      exact ⟨h0.1,
        Rank1Termination.index_mono (Nat.zero_le 1) (T.one_del (T.P 0 a b)) h0.2⟩
    · cases hp1
      have hne : ∀ s2 : T, T.P 1 a b = T.P 0 T.Z s2 → False := by
        intro s2 h
        cases h
      rw [T.one_del.eq_2 (T.P 1 a b) hne]
      exact ⟨hs, hi⟩

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
      cases hp0
      exact T.Lt.p_head 0 1 a T.Z b y (Nat.zero_lt_succ 0)

theorem c1_card_times_mono_index1 :
    ∀ s t : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.card_times 1 s < T.card_times 1 t := by
  intro s
  induction s with
  | Z =>
    intro t _ _ _ _ hst
    have htne : t ≠ T.Z := by
      intro heq
      rw [heq] at hst
      exact lt_Z_inv hst
    have hctne : T.card_times 1 t ≠ T.Z :=
      bridge_card_times_ne_Z 1 t htne
    rw [T.card_times.eq_1]
    rcases T.Z_le (T.card_times 1 t) with hlt | heq
    · exact hlt
    · exact False.elim (hctne heq.symm)
  | P p a b _ ihb =>
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
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hpLe) with hp0 | hp1
      · cases hp0
        rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with hq0 | hq1
        · cases hq0
          obtain ⟨haNF, hbNF, haG, _⟩ := T.isNF1_P_inv 0 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p0, c1_p0]
          rcases lt_inv 0 a b 0 e f hst with hhead | (hmid | htail)
          · exact False.elim (Nat.lt_irrefl 0 hhead)
          · have hae : a < e := hmid.2
            have hec : T.early_collapse a < T.early_collapse e :=
              bridge_early_collapse_lt a e haNF haG heNF hae
            exact T.Lt.p_mid 1 (T.early_collapse a) (T.early_collapse e)
              (T.card_times 1 b) (T.card_times 1 f) hec
          · have hae : a = e := htail.2.1
            cases hae
            have hbf : b < f := htail.2.2
            have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
            exact T.Lt.p_tail 1 (T.early_collapse a)
              (T.card_times 1 b) (T.card_times 1 f) hrec
        · cases hq1
          obtain ⟨haNF, _, haG, _⟩ := T.isNF1_P_inv 0 a b hsNF
          have hec := bridge_early_collapse_closed a haNF haG
          rw [c1_p0, c1_p1]
          have hmid : T.early_collapse a < T.P 1 T.Z e :=
            c1_idx0_lt_P1 (T.early_collapse a) e hec.2.1
          exact T.Lt.p_mid 1 (T.early_collapse a) (T.P 1 T.Z e)
            (T.card_times 1 b) (T.card_times 1 f) hmid
      · cases hp1
        rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with hq0 | hq1
        · cases hq0
          rcases lt_inv 1 a b 0 e f hst with hhead | (hmid | htail)
          · exact False.elim (Nat.not_lt_zero 1 hhead)
          · cases hmid.1
          · cases htail.1
        · cases hq1
          obtain ⟨_, hbNF, _, _⟩ := T.isNF1_P_inv 1 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 1 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p1, c1_p1]
          rcases lt_inv 1 a b 1 e f hst with hhead | (hmid | htail)
          · exact False.elim (Nat.lt_irrefl 1 hhead)
          · have hae : a < e := hmid.2
            have hinner : T.P 1 T.Z a < T.P 1 T.Z e :=
              T.Lt.p_tail 1 T.Z a e hae
            exact T.Lt.p_mid 1 (T.P 1 T.Z a) (T.P 1 T.Z e)
              (T.card_times 1 b) (T.card_times 1 f) hinner
          · have hae : a = e := htail.2.1
            cases hae
            have hbf : b < f := htail.2.2
            have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
            exact T.Lt.p_tail 1 (T.P 1 T.Z a)
              (T.card_times 1 b) (T.card_times 1 f) hrec

theorem c1_idx0_lt_outer1 (x m y : T) (hx : T.index_Prop1 0 x) :
    x < T.P 1 m y := by
  cases x with
  | Z => exact T.Lt.Z_lt_P 1 m y
  | P p a b =>
    cases hx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      cases hp0
      exact T.Lt.p_head 0 1 a m b y (Nat.zero_lt_succ 0)

theorem c1_card_append_lt_index1 :
    ∀ s t x y : T,
      T.isNF1 s → T.index_Prop1 1 s →
      T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.index_Prop1 0 x →
      T.add (T.card_times 1 s) x < T.add (T.card_times 1 t) y := by
  intro s
  induction s with
  | Z =>
    intro t x y _ _ htNF htIdx hst hxIdx
    cases t with
    | Z => exact False.elim (lt_Z_inv hst)
    | P q e f =>
      have hqLe : q ≤ 1 := by
        cases htIdx with
        | p _ _ _ hq _ => exact hq
      rw [T.card_times.eq_1, T.add.eq_1]
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with hq0 | hq1
      · cases hq0
        rw [c1_p0, T.P_add_eq]
        exact c1_idx0_lt_outer1 x (T.early_collapse e)
          (T.add (T.card_times 1 f) y) hxIdx
      · cases hq1
        rw [c1_p1, T.P_add_eq]
        exact c1_idx0_lt_outer1 x (T.P 1 T.Z e)
          (T.add (T.card_times 1 f) y) hxIdx
  | P p a b _ ihb =>
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
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hpLe) with hp0 | hp1
      · cases hp0
        rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with hq0 | hq1
        · cases hq0
          obtain ⟨haNF, hbNF, haG, _⟩ := T.isNF1_P_inv 0 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p0, c1_p0, T.P_add_eq, T.P_add_eq]
          rcases lt_inv 0 a b 0 e f hst with hhead | (hmid | htail)
          · exact False.elim (Nat.lt_irrefl 0 hhead)
          · have hae : a < e := hmid.2
            have hec : T.early_collapse a < T.early_collapse e :=
              bridge_early_collapse_lt a e haNF haG heNF hae
            exact T.Lt.p_mid 1 (T.early_collapse a) (T.early_collapse e)
              (T.add (T.card_times 1 b) x)
              (T.add (T.card_times 1 f) y) hec
          · have hae : a = e := htail.2.1
            cases hae
            have hbf : b < f := htail.2.2
            have hrec := ihb f x y hbNF hbIdx hfNF hfIdx hbf hxIdx
            exact T.Lt.p_tail 1 (T.early_collapse a)
              (T.add (T.card_times 1 b) x)
              (T.add (T.card_times 1 f) y) hrec
        · cases hq1
          obtain ⟨haNF, _, haG, _⟩ := T.isNF1_P_inv 0 a b hsNF
          have hec := bridge_early_collapse_closed a haNF haG
          rw [c1_p0, c1_p1, T.P_add_eq, T.P_add_eq]
          have hmid : T.early_collapse a < T.P 1 T.Z e :=
            c1_idx0_lt_P1 (T.early_collapse a) e hec.2.1
          exact T.Lt.p_mid 1 (T.early_collapse a) (T.P 1 T.Z e)
            (T.add (T.card_times 1 b) x)
            (T.add (T.card_times 1 f) y) hmid
      · cases hp1
        rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hqLe) with hq0 | hq1
        · cases hq0
          rcases lt_inv 1 a b 0 e f hst with hhead | (hmid | htail)
          · exact False.elim (Nat.not_lt_zero 1 hhead)
          · cases hmid.1
          · cases htail.1
        · cases hq1
          obtain ⟨_, hbNF, _, _⟩ := T.isNF1_P_inv 1 a b hsNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 1 e f htNF
          have hbIdx : T.index_Prop1 1 b := by
            cases hsIdx with
            | p _ _ _ _ hbi => exact hbi
          have hfIdx : T.index_Prop1 1 f := by
            cases htIdx with
            | p _ _ _ _ hfi => exact hfi
          rw [c1_p1, c1_p1, T.P_add_eq, T.P_add_eq]
          rcases lt_inv 1 a b 1 e f hst with hhead | (hmid | htail)
          · exact False.elim (Nat.lt_irrefl 1 hhead)
          · have hae : a < e := hmid.2
            have hinner : T.P 1 T.Z a < T.P 1 T.Z e :=
              T.Lt.p_tail 1 T.Z a e hae
            exact T.Lt.p_mid 1 (T.P 1 T.Z a) (T.P 1 T.Z e)
              (T.add (T.card_times 1 b) x)
              (T.add (T.card_times 1 f) y) hinner
          · have hae : a = e := htail.2.1
            cases hae
            have hbf : b < f := htail.2.2
            have hrec := ihb f x y hbNF hbIdx hfNF hfIdx hbf hxIdx
            exact T.Lt.p_tail 1 (T.P 1 T.Z a)
              (T.add (T.card_times 1 b) x)
              (T.add (T.card_times 1 f) y) hrec

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
  · cases havz
    rw [ite_eq_left rfl]
    by_cases hawz : aw = T.Z
    · cases hawz
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
  rcases hlex with hsum | heq
  · have hsvDel := oc_one_del_NF_index1 sv hiv.2.2.1 hiv.2.2.2.1
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
  · have hsumEq : sv = sw := heq.1
    have ha0lt : av < aw := heq.2
    cases hsumEq
    have hec : T.early_collapse av < T.early_collapse aw :=
      bridge_early_collapse_lt av aw hiv.1 hiv.2.1 hiw.1 ha0lt
    have hmid := bridge_add_left_lt (T.card_times 1 (T.one_del sv))
      (T.early_collapse av) (T.early_collapse aw) hec
    exact T.Lt.p_mid 1 _ _ (trans a) (trans b) hmid

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
    obtain ⟨sv, av⟩ := rav
    cases haw : transAux w with
    | mk fw raw =>
      obtain ⟨sw, aw⟩ := raw
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

theorem oc_mem_size_lt_P {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a x : new.T lam)
    (hx : x ∈ new.Vec.toList v) :
    new.T.size x < new.T.size (new.T.P v a) := by
  obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v x hx
  rw [← hi]
  exact new.T.idx_size_lt_P v a i

theorem bo_order_preserve_bounded {lam : Nat} (N : Nat)
    (hgood : ∀ x : new.T lam, new.T.size x < N → new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.size s ≤ N → new.T.size t ≤ N →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  intro s t hsN htN hs ht hst
  induction hs generalizing t with
  | z =>
      cases t with
      | Z => exact False.elim (strict_partial_order.irrefl new.T.Z hst)
      | P w b =>
          rw [_root_.trans.eq_1]
          exact tc_Z_lt_of_ne _ (tc_trans_ne_Z_of_ne_Z _ (by intro h; cases h))
  | p v a hvNF _ hvG _ ihv iha =>
      cases ht with
      | z => cases hst
      | p w b hwNF hbNF hwG hheadB =>
          have hvGood := fun x hx => hgood x
            (Nat.lt_of_lt_of_le (oc_mem_size_lt_P v a x hx) hsN) ⟨hvNF x hx, hvG x hx⟩
          have hwGood := fun x hx => hgood x
            (Nat.lt_of_lt_of_le (oc_mem_size_lt_P w b x hx) htN) ⟨hwNF x hx, hwG x hx⟩
          change
            (match new.compareVec v w with
            | Ordering.eq => new.compareT a b
            | ord => ord) = Ordering.lt at hst
          cases hcmp : new.compareVec v w with
          | lt =>
              apply oc_full_lt_of_compareVec_general v w a b hvGood hwGood
              · intro x y hx hy hxy
                exact ihv x hx y
                  (Nat.le_trans (Nat.le_of_lt (oc_mem_size_lt_P v a x hx)) hsN)
                  (Nat.le_trans (Nat.le_of_lt (oc_mem_size_lt_P w b y hy)) htN)
                  (hwNF y hy) hxy
              · exact hcmp
          | eq =>
              rw [hcmp] at hst
              have hvw : v = w := new.Vec_eq_sound v w hcmp
              cases hvw
              have htail := iha b
                (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P v a)) hsN)
                (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P v b)) htN) hbNF hst
              rw [tc_trans_P_add v a, tc_trans_P_add v b]
              exact bridge_add_left_lt _ _ _ htail
          | gt =>
              rw [hcmp] at hst
              cases hst

theorem oc_order_preserve_core {lam : Nat}
    (hgood : ∀ x : new.T lam, new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  intro s t hs ht hst
  exact bo_order_preserve_bounded (max (new.T.size s) (new.T.size t))
    (fun x _ => hgood x) s t (Nat.le_max_left _ _) (Nat.le_max_right _ _) hs ht hst

theorem oc_order_embedding_core {lam : Nat}
    (hgood : ∀ x : new.T lam, new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  constructor
  · exact oc_order_preserve_core hgood s t hs ht
  · intro htrans
    rcases strict_linear_order.total s t with hst | (hts | heq)
    · exact hst
    · have hrev := oc_order_preserve_core hgood t s ht hs hts
      have hloop : trans s < trans s :=
        strict_partial_order.trans (trans s) (trans t) (trans s) htrans hrev
      exact False.elim (strict_partial_order.irrefl (trans s) hloop)
    · rw [heq] at htrans
      exact False.elim (strict_partial_order.irrefl (trans t) htrans)

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

theorem nfcore_trans_PZ_shape {lam : Nat}
    (v : new.Vec (new.T lam) lam) :
    ∃ i : Nat, ∃ m : T,
      trans (new.T.P v new.T.Z) = T.P i m T.Z := by
  rw [_root_.trans.eq_2]
  cases haux : transAux v with
  | mk found rest =>
      obtain ⟨sum, a0⟩ := rest
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

theorem nfcore_add_principal (i : Nat) (m b : T)
    (hp : T.isNF1 (T.P i m T.Z))
    (hb : T.isNF1 b)
    (hhead : T.head b ≤ T.P i m T.Z) :
    T.isNF1 (T.add (T.P i m T.Z) b) := by
  obtain ⟨hm, _, hg, _⟩ := T.isNF1_P_inv i m T.Z hp
  rw [T.P_add_eq, T.add.eq_1]
  exact T.isNF1.p i m b hm hb hg hhead

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
  rcases hle with hlt | heq
  · change
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
  · have hterm : new.T.P w new.T.Z = new.T.P v new.T.Z :=
      new.T_eq_sound (new.T.P w new.T.Z) (new.T.P v new.T.Z) heq
    rw [hterm]
    exact Or.inr rfl

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

end NormalFormAndOrder

/-! Support bounds and the simultaneous normal-form/order proof. -/

section TranslationSupport

open T

theorem sg_add_interval_size_le (a b x : T)
    (hax : a ≤ x) (hxu : x < T.add a b) :
    a.size ≤ x.size := by
  induction a generalizing x with
  | Z => exact Nat.zero_le x.size
  | P p c d _ ihd =>
      cases hax with
      | inr heq =>
          rw [heq]
          exact Nat.le_refl x.size
      | inl hlt =>
          have hu : T.add (T.P p c d) b = T.P p c (T.add d b) :=
            T.P_add_eq p c d b
          rw [hu] at hxu
          obtain ⟨e, hex, hde, heu⟩ := sandwich_tail p c d x (T.add d b) hlt hxu
          rw [hex]
          have hsz : d.size ≤ e.size :=
            ihd e (Or.inl hde) heu
          change c.size + d.size + 1 ≤ c.size + e.size + 1
          exact Nat.add_le_add_right (Nat.add_le_add_left hsz c.size) 1

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
  rcases lt_total_thm x a with hxa | (hax | heq)
  · exact hxa
  · have hsz : a.size ≤ x.size := by
      apply sg_add_interval_size_le a b x (Or.inl hax)
      rw [hadd]
      exact hxs
    exact False.elim ((Nat.not_lt_of_ge hsz) hxsz)
  · rw [heq] at hxsz
    exact False.elim (Nat.lt_irrefl a.size hxsz)

theorem sg_early_G0_le (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.early_collapse s) → x ≤ s := by
  intro x hx
  cases hp : T.part s with
  | mk a b =>
      have hadd := bridge_part_add s
      rw [hp] at hadd
      have hparts := bridge_part_NF1 s hs
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
      by_cases ha : a = T.Z
      · rw [hec, ite_eq_left ha] at hx
        exact Or.inl (hmemB x hx)
      · rw [hec, ite_eq_right ha] at hx
        by_cases hkeep : T.head b ≤ T.P 0 a T.Z
        · rw [ite_eq_left hkeep] at hx
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)] at hx
          rcases List.mem_append.mp hx with hleft | hGb
          · cases List.mem_append.mp hleft with
            | inl hsingle =>
                have hxa : x = a := List.mem_singleton.mp hsingle
                rw [hxa]
                exact haLe
            | inr hGa =>
                have hgoodA := sg_good0_part_fst s hg
                rw [hp] at hgoodA
                exact Or.inl (lt_of_lt_of_le_thm T x a s
                  (hgoodA x hGa) haLe)
          · exact Or.inl (hmemB x hGb)
        · rw [ite_eq_right hkeep] at hx
          exact Or.inl (hmemB x hx)

theorem gc_tail_lt_of_NF1 (p : Nat) (a b : T)
    (h : T.isNF1 (T.P p a b)) : b < T.P p a b := by
  have hle := T.isNF1_tail_le (T.P p a b) h p a b rfl
  rcases hle with hlt | heq
  · exact hlt
  · have hsz : b.size < (T.P p a b).size := T.size_lt_size_P_right p a b
    have hszeq : b.size = (T.P p a b).size := congrArg T.size heq
    exact False.elim ((Nat.ne_of_lt hsz) hszeq)

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
      rcases hx with (hz | hzG) | htail
      · have hxz : x = T.Z := List.mem_singleton.mp hz
        rw [hxz]
        exact Or.inl (T.Lt.Z_lt_P 1 (T.P 1 T.Z
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)) tail)
      · rw [T.G1.eq_1] at hzG
        cases hzG
      · have hrec := ih x htail
        rcases hrec with hlt | hs
        · have hmid :
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
        · exact Or.inr hs

theorem cs_card_support (n : Nat) : ∀ c s : T,
    T.isNF1 c → T.index_Prop1 0 c →
    (∀ x : T, x ∈ T.G1 0 c → x ≤ s) →
    ∀ x : T, x ∈ T.G1 0 (T.card_times (n + 1) c) →
      x < T.P 1 (T.card_times (n + 1) c) T.Z ∨ x ≤ s := by
  intro c
  induction c with
  | Z =>
      intro s _ _ _ x hx
      rw [T.card_times.eq_1, T.G1.eq_1] at hx
      cases hx
  | P p a b _ ihb =>
      intro s hcNF hcIdx hsupp x hx
      cases hcIdx with
      | p _ _ _ hp hib =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          cases hp0
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
            exact bridge_good_index_lt_wrap 1 C T.Z hcard.2.1 hcard.2.2
          change x ∈ T.G1 0 C at hx
          change x < T.P 1 C T.Z ∨ x ≤ s
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
            List.mem_append, List.mem_append] at hx
          rcases hx with (hM | hGM) | htail
          · have hxM : x = M := List.mem_singleton.mp hM
            rw [hxM]
            have hMC : M < C := by
              unfold C M
              exact bridge_shift_lt_outer n (T.early_collapse a)
                (T.card_times (n + 1) b) hec.2.1
            exact Or.inl (lt_trans_thm M C (T.P 1 C T.Z) hMC hCwrap)
          · have hshift := sw_shift_support n (T.early_collapse a) a
              (T.card_times (n + 1) b) hec.2.1
              (sg_early_G0_le a haNF haG) x hGM
            rcases hshift with hxC | hxa
            · exact Or.inl (lt_trans_thm x C (T.P 1 C T.Z) hxC hCwrap)
            · have haMem : a ∈ T.G1 0 (T.P 0 a b) := by
                rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                exact List.mem_append_left (T.G1 0 b)
                  (List.mem_append_left (T.G1 0 a)
                    (List.mem_singleton_self a))
              exact Or.inr (partial_order.trans x a s hxa (hsupp a haMem))
          · have hsuppB : ∀ y : T, y ∈ T.G1 0 b → y ≤ s := by
              intro y hy
              apply hsupp y
              rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
              exact List.mem_append_right ([a] ++ T.G1 0 a) hy
            have hrec := ihb s hbNF hib hsuppB x htail
            cases hrec with
            | inr hxs => exact Or.inr hxs
            | inl hxwrap =>
                have htailLt : T.card_times (n + 1) b < C := by
                  unfold C
                  exact gc_tail_lt_of_NF1 1 M (T.card_times (n + 1) b) hcard.1
                have hlift :
                    T.P 1 (T.card_times (n + 1) b) T.Z < T.P 1 C T.Z :=
                  T.Lt.p_mid 1 (T.card_times (n + 1) b) C T.Z T.Z htailLt
                exact Or.inl (lt_trans_thm x
                  (T.P 1 (T.card_times (n + 1) b) T.Z)
                  (T.P 1 C T.Z) hxwrap hlift)

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
          cases hp0
          rw [T.card_times.eq_3, ite_eq_left rfl]
          rw [← add_eq_hAdd]
          rw [Rank1Termination.add_assoc]
          rw [T.P_add_eq, T.add]
          rfl

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
              obtain ⟨sumRest, a0Rest⟩ := rest
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
                    rcases hpair.1 x hx with hlt | hw
                    · exact Or.inl hlt
                    · obtain ⟨z, hz, hxz⟩ := hw
                      exact Or.inr ⟨z,
                        List.mem_append_left [new.T.Z] hz, hxz⟩
                  · intro x hx
                    rcases hpair.2 x hx with hlt | hw
                    · exact Or.inl hlt
                    · obtain ⟨z, hz, hxz⟩ := hw
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
                    rcases List.mem_append.mp hx with hBmem | hRmem
                    · have hcur := cs_card_support m ec
                        (trans (new.T.P als aadd)) hec.1 hec.2.1
                        (sg_early_G0_le (trans (new.T.P als aadd)) ha.1 ha.2)
                        x hBmem
                      rcases hcur with hlt | hxcoord
                      · have hLift := bridge_lift_P1_le B (T.add B R)
                          (wt_add_self_le B R)
                        exact Or.inl (lt_of_lt_of_le_thm T x
                          (T.P 1 B T.Z) (T.P 1 (T.add B R) T.Z)
                          hlt hLift)
                      · exact Or.inr ⟨new.T.P als aadd,
                          List.mem_append_right (new.Vec.toList xs)
                            (List.mem_singleton_self (new.T.P als aadd)),
                          hxcoord⟩
                    · have hrestDec := hpair.1 x hRmem
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
                                rcases hbase with hlt | hle
                                · exact Or.inl hlt
                                · exact Or.inr ⟨new.T.P als aadd,
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
              obtain ⟨sumRest, a0Rest⟩ := rest
              rw [transAux.eq_3, hrest] at haux
              have ha0eq : a0 = a0Rest :=
                congrArg (fun q : Bool × T × T => q.2.2) haux.symm
              have hrec := ih xs foundRest sumRest a0Rest hrest
              rw [ha0eq, hrec]
              change trans (new.Vec.idx xs ⟨0, Nat.zero_lt_succ m⟩) =
                trans (if h : 0 < m + 1 then
                  new.Vec.idx xs ⟨0, h⟩ else a)
              rw [dite_eq_left (Nat.zero_lt_succ m)]

theorem ts_coord_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.Vec.toList v) :
    z ∈ new.T.G (new.T.P v a) := by
  obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v z hz
  rw [new.T.G_P_eq]
  apply List.mem_append_left (new.T.G a)
  rw [← hi]
  exact new.Vec.Gres_mem_of_idx v i

theorem ts_tail_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.G a) :
    z ∈ new.T.G (new.T.P v a) := by
  rw [new.T.G_P_eq]
  exact List.mem_append_right (new.T.G.res v) hz

theorem ts_P1Z_le_tail (m tail : T) :
    T.P 1 m T.Z ≤ T.P 1 m tail := by
  rcases T.Z_le tail with hlt | heq
  · exact Or.inl (T.Lt.p_tail 1 m T.Z tail hlt)
  · rw [← heq]
    exact Or.inr rfl

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
                  rcases hy with (hz | hzG) | htail
                  · have hyz : y = T.Z := List.mem_singleton.mp hz
                    rw [hyz]
                    exact Or.inl (T.Lt.Z_lt_P 0 T.Z (trans a))
                  · rw [T.G1.eq_1] at hzG
                    cases hzG
                  · cases htailDecomp y htail with
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
                  obtain ⟨sum, a0⟩ := rest
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
                  by_cases hf : found = true
                  · rw [ite_eq_left hf] at ht ⊢
                    let A := T.card_times 1 (T.one_del sum)
                    let E := T.early_collapse a0
                    let M := T.add A E
                    have hMclosed := pn_aux_found_middle_closed v hcoord
                      found sum a0 haux hf
                    change T.isNF1 (T.P 1 M (trans a)) at ht
                    have hMwrap : M < T.P 1 M T.Z :=
                      bridge_good_index_lt_wrap 1 M T.Z hMclosed.2.1 hMclosed.2.2
                    have hMfull : M < T.P 1 M (trans a) :=
                      lt_of_lt_of_le_thm T M (T.P 1 M T.Z)
                        (T.P 1 M (trans a)) hMwrap (ts_P1Z_le_tail M (trans a))
                    intro y hy
                    change y ∈ T.G1 0 (T.P 1 M (trans a)) at hy
                    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1),
                      List.mem_append, List.mem_append] at hy
                    rcases hy with (hmid | hGM) | htail
                    · have hym : y = M := List.mem_singleton.mp hmid
                      rw [hym]
                      exact Or.inl hMfull
                    · unfold M at hGM
                      rw [bridge_G1_add_eq] at hGM
                      rcases List.mem_append.mp hGM with hA | hE
                      · have hdec := hauxSupp.2 y hA
                        rcases hdec with hlt | hw
                        · have hAle : A ≤ T.add A E := wt_add_self_le A E
                          have hLift := bridge_lift_P1_le A (T.add A E) hAle
                          have hyMZ : y < T.P 1 M T.Z := by
                            unfold M
                            exact lt_of_lt_of_le_thm T y (T.P 1 A T.Z)
                              (T.P 1 (T.add A E) T.Z) hlt hLift
                          exact Or.inl (lt_of_lt_of_le_thm T y
                            (T.P 1 M T.Z) (T.P 1 M (trans a))
                            hyMZ (ts_P1Z_le_tail M (trans a)))
                        · obtain ⟨z, hz, hyz⟩ := hw
                          exact Or.inr ⟨z, ts_coord_mem_G v a z hz, hyz⟩
                      · have ha0good := hauxInv.1
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
                    · cases htailDecomp y htail with
                      | inl hya =>
                          have htle := T.isNF1_tail_le
                            (T.P 1 M (trans a)) ht 1 M (trans a) rfl
                          exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                            (T.P 1 M (trans a)) hya htle)
                      | inr hw =>
                          obtain ⟨z, hz, hyz⟩ := hw
                          exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩
                  · rw [ite_eq_right hf] at ht ⊢
                    by_cases ha0z : a0 = T.Z
                    · rw [ite_eq_left ha0z] at ht ⊢
                      intro y hy
                      rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0),
                        List.mem_append, List.mem_append] at hy
                      rcases hy with (hz | hzG) | htail
                      · have hyz : y = T.Z := List.mem_singleton.mp hz
                        rw [hyz]
                        exact Or.inl (T.Lt.Z_lt_P 0 T.Z (trans a))
                      · rw [T.G1.eq_1] at hzG
                        cases hzG
                      · cases htailDecomp y htail with
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
                      rcases hy with (ha0mem | hGa0) | htail
                      · have hya0 : y = a0 := List.mem_singleton.mp ha0mem
                        let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                        have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                          new.Vec.idx_mem_toList v i0
                        exact Or.inr ⟨v.idx i0,
                          ts_coord_mem_G v a (v.idx i0) hiMem,
                          by
                            rw [hya0, ← ha0eq]
                            exact Or.inr rfl⟩
                      · let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                        have hiMem : v.idx i0 ∈ new.Vec.toList v :=
                          new.Vec.idx_mem_toList v i0
                        have htrans0 : trans (v.idx i0) = a0 := ha0eq.symm
                        have hlt0 : y < a0 := hauxInv.2.1 y hGa0
                        exact Or.inr ⟨v.idx i0,
                          ts_coord_mem_G v a (v.idx i0) hiMem,
                          Or.inl (by rw [htrans0]; exact hlt0)⟩
                      · cases htailDecomp y htail with
                        | inl hya =>
                            have htle := T.isNF1_tail_le
                              (T.P 0 a0 (trans a)) ht 0 a0 (trans a) rfl
                            exact Or.inl (lt_of_lt_of_le_thm T y (trans a)
                              (T.P 0 a0 (trans a)) hya htle)
                        | inr hw =>
                            obtain ⟨z, hz, hyz⟩ := hw
                            exact Or.inr ⟨z, ts_tail_mem_G v a z hz, hyz⟩

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
          rcases hDecomp hscomp.1 y hy with hlt | hw
          · exact hlt
          · obtain ⟨z, hz, hyz⟩ := hw
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

theorem gnf_NF_is_NF1 {lam : Nat} (s : new.T lam) :
    new.T.isNF s → T.isNF1 (trans s) := by
  exact (gnf_all s).1

theorem gnf_good {lam : Nat} (s : new.T lam) :
    new.T.isNFComp s →
      T.isNF1 (trans s) ∧
        (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s) := by
  exact (gnf_all s).2.2

theorem gnf_order_embedding {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  exact oc_order_embedding_core (fun x hx => gnf_good x hx) s t hs ht

theorem gnf_trans_injective {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (heq : trans s = trans t) : s = t := by
  rcases new.T_total s t with hst | (hts | he)
  · have htr := (gnf_order_embedding s t hs ht).mp hst
    rw [heq] at htr
    exact False.elim (strict_partial_order.irrefl (trans t) htr)
  · have htr := (gnf_order_embedding t s ht hs).mp hts
    rw [heq] at htr
    exact False.elim (strict_partial_order.irrefl (trans t) htr)
  · exact he

theorem gnf_reflect_le {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (hle : trans s ≤ trans t) : s ≤ t := by
  rcases hle with hlt | heq
  · exact Or.inl ((gnf_order_embedding s t hs ht).mpr hlt)
  · rw [gnf_trans_injective s t hs ht heq]
    exact Or.inr (new.T_refl t)

theorem gnf_le_iff {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t) : s ≤ t ↔ trans s ≤ trans t := by
  constructor
  · intro h
    rcases h with hlt | heq
    · exact Or.inl ((gnf_order_embedding s t hs ht).mp hlt)
    · exact Or.inr (congrArg trans (new.T_eq_sound s t heq))
  · exact gnf_reflect_le s t hs ht

end TranslationSupport

/-! Dimension-dependent upper bounds and coordinate-zero translation. -/

section TranslationBounds

open T

def ot_trans_bound : Nat → T
  | 0 => T.P 0 T.Z T.Z
  | 1 => T.P 1 T.Z T.Z
  | k + 2 => T.P 1 (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z) T.Z

theorem ot_one_del_card_bound (s l b : T)
    (hnf : T.isNF1 (T.add (T.card_times 1 s) l))
    (hb : T.add (T.card_times 1 s) l < b) :
    T.add (T.card_times 1 (T.one_del s)) l < b := by
  cases s with
  | Z => exact hb
  | P p a d =>
      cases p with
      | zero =>
          cases a with
          | Z =>
              have heq : T.add (T.card_times 1 (T.P 0 T.Z d)) l =
                  T.P 1 T.Z (T.add (T.card_times 1 d) l) := by
                rw [T.card_times.eq_3, ite_eq_left rfl]
                change T.add (T.add (T.P 1 T.Z T.Z) (T.card_times 1 d)) l = _
                rw [T.P_add_eq, T.add.eq_1, T.P_add_eq]
              rw [heq] at hnf hb
              exact lt_trans_thm _ _ b (gc_tail_lt_of_NF1 1 T.Z _ hnf) hb
          | P q c e => exact hb
      | succ p => exact hb

theorem ot_trans_global_bound {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s) (hpos : 0 < lam) :
    trans s < ot_trans_bound lam := by
  cases lam with
  | zero => exact False.elim (Nat.lt_irrefl 0 hpos)
  | succ k =>
      cases s with
      | Z =>
          cases k with
          | zero => exact T.Lt.Z_lt_P 1 T.Z T.Z
          | succ k => exact T.Lt.Z_lt_P 1 _ T.Z
      | P v add =>
          have hcoords : ∀ x, x ∈ new.Vec.toList v →
              T.isNF1 (trans x) ∧ (∀ y, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v x hx
            rw [← hi]
            exact gnf_good (v.idx i) (new.T.isNF_P_coord_NFComp v add hs i)
          cases k with
          | zero =>
              cases v with
              | snoc n xs a =>
                  cases xs with
                  | nil =>
                      rw [_root_.trans.eq_2, transAux.eq_2]
                      change (if trans a = T.Z then T.P 0 T.Z (trans add)
                        else T.P 0 (trans a) (trans add)) < T.P 1 T.Z T.Z
                      by_cases ha : trans a = T.Z
                      · rw [ite_eq_left ha]
                        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
                      · rw [ite_eq_right ha]
                        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
          | succ k =>
              cases haux : transAux v with
              | mk found rest =>
                  obtain ⟨sum, a0⟩ := rest
                  have hi := tc_transAux_inv v hcoords found sum a0 haux
                  have hec := bridge_early_collapse_closed a0 hi.1 hi.2.1
                  have hb := pn_aux_card1_sum_append v hcoords
                    (T.early_collapse a0) hec.1 hec.2.1 hec.2.2
                    (pn_index0_lt_threshold0 _ hec.2.1)
                  rw [haux] at hb
                  have hmid := ot_one_del_card_bound sum (T.early_collapse a0)
                    (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z)
                    hb.1 hb.2.2.2
                  rw [_root_.trans.eq_2, haux]
                  cases found with
                  | false =>
                      change (if a0 = T.Z then T.P 0 T.Z (trans add)
                        else T.P 0 a0 (trans add)) < T.P 1 _ T.Z
                      by_cases ha : a0 = T.Z
                      · rw [ite_eq_left ha]
                        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
                      · rw [ite_eq_right ha]
                        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
                  | true =>
                      exact T.Lt.p_mid 1 _ _ _ _ hmid

def ot_v0 {lam : Nat} (k : Nat) (a : new.T lam) : new.Vec (new.T lam) (k + 1) :=
  new.Vec.ofFn (k + 1) (fun i => if i.val = 0 then a else new.T.Z)

theorem ot_transAux_v0 {lam : Nat} (k : Nat) (a : new.T lam) :
    transAux (ot_v0 k a) = (false, T.Z, trans a) := by
  induction k with
  | zero =>
      unfold ot_v0
      rw [new.Vec.ofFn]
      change transAux (new.Vec.snoc 0 new.Vec.nil a) = _
      rw [transAux.eq_2]
  | succ k ih =>
      unfold ot_v0 at ih ⊢
      rw [new.Vec.ofFn]
      have hlast : (Fin.last (k + 1)).val ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_succ k)
      rw [ite_eq_right hlast]
      change transAux (new.Vec.snoc (k + 1)
        (new.Vec.ofFn (k + 1) (fun i => if i.val = 0 then a else new.T.Z)) new.T.Z) = _
      rw [transAux.eq_3, ih, _root_.trans.eq_1]
      change (false, T.add (T.card_times k (T.early_collapse T.Z)) T.Z, trans a) = _
      rw [T.early_collapse, T.part, ite_eq_left rfl, T.card_times.eq_1, T.add.eq_1]

theorem ot_trans_v0 (k : Nat) (a b : new.T (k + 1)) :
    trans (new.T.P (ot_v0 k a) b) = T.P 0 (trans a) (trans b) := by
  rw [_root_.trans.eq_2, ot_transAux_v0]
  change (if trans a = T.Z then T.P 0 T.Z (trans b)
    else T.P 0 (trans a) (trans b)) = _
  by_cases h : trans a = T.Z
  · rw [ite_eq_left h, h]
  · rw [ite_eq_right h]

end TranslationBounds

/-! Well-foundedness and the public normal-form interface. -/

section NormalFormInterface

theorem ot_new_well_founded_NF (lam : Nat) :
    WellFounded (fun s t : {x : new.T lam // new.T.isNF x} => s.1 < t.1) := by
  exact Subrelation.wf
    (fun {s t} h => (gnf_order_embedding s.val t.val s.property t.property).mp h)
    (InvImage.wf
      (fun s : {x : new.T lam // new.T.isNF x} =>
        (⟨trans s.val, gnf_NF_is_NF1 s.val s.property⟩ : T.NF1))
      T.well_founded_NF1)

theorem NF_is_NF1 (lam : Nat) (s : new.T lam) :
  new.T.isNF s → T.isNF1 (trans s) := by
  exact gnf_NF_is_NF1 s

theorem order_embeding (lam : Nat) (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
  s < t ↔ trans s < trans t := by
  exact gnf_order_embedding s t hs ht

theorem trans_injective_on_NF {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (htrans : trans s = trans t) : s = t := by
  exact gnf_trans_injective s t hs ht htrans

def new.T.NF (lam : Nat) := { s : T lam // isNF s }

theorem wellfounded_NF (lam : Nat) : WellFounded (fun s t : new.T.NF lam => s.val < t.val) := by
  exact ot_new_well_founded_NF lam

end NormalFormInterface

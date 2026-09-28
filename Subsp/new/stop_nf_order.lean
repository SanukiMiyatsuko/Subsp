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
  exact bridge_add_left_le _ _ _ (bridge_early_collapse_le c a hc hgc ha hca)

theorem cb_threshold_step (n : Nat) :
    T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z <
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z := by
  rw [mul_succ_shape 1 T.Z n]
  exact T.Lt.p_mid _ _ _ _ _ (tail_lt_wrap 1 T.Z n)

theorem cb_lower_head_le_shift (n : Nat) (L c : T)
    (hL : L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z) :
    T.head L ≤
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) c) T.Z := by
  exact partial_order.trans _ _ _ (T.head_mono hL) (bridge_lift_P1_le _ _ (wt_add_self_le _ c))

theorem cb_card_append_lower (n : Nat) : ∀ E L : T,
    T.isNF1 E → T.index_Prop1 0 E →
    T.isNF1 L → T.index_Prop1 1 L →
    (∀ x : T, x ∈ T.G1 1 L → x < L) →
    L < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) T.Z →
    let R := T.add (T.card_times (n + 1) E) L
    T.isNF1 R ∧ T.index_Prop1 1 R ∧
      (∀ x : T, x ∈ T.G1 1 R → x < R) ∧
      R < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) T.Z := by
  intro E L hE hiE hL hiL hgL hbound
  have hsmall : ∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z → L < T.card_times (n + 1) z := by
    intro z _ hi hn
    cases hi with
    | z => exact False.elim (hn rfl)
    | p p a b hp _ =>
        have hp0 : p = 0 := by omega
        subst p
        simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]
        exact lt_of_lt_of_le_thm T _ _ _ hbound (partial_order.trans _ _ _
          (bridge_lift_P1_le _ _ (wt_add_self_le _ (T.early_collapse a)))
          (bridge_head_le_self (T.P 1 _ (T.card_times (n + 1) b))))
  have hr := bridge_card_times_succ_append n E L hE hiE hL hiL hgL hsmall
  refine ⟨hr.1, hr.2.1, hr.2.2, ?_⟩
  cases hiE with
  | z => exact lt_trans_thm _ _ _ hbound (cb_threshold_step n)
  | p p a b hp _ =>
      have hp0 : p = 0 := by omega
      subst p
      have ha := T.isNF1_P_inv _ _ _ hE
      have hec := bridge_early_collapse_closed a ha.1 ha.2.2.1
      have hmid := bridge_shift_level_lt n (n + 1) (Nat.lt_succ_self n) _ T.Z hec.2.1 T.index_Prop1.z
      rw [T.add_Z] at hmid
      rw [wt_expand_card_succ_add]
      exact T.Lt.p_mid _ _ _ _ _ hmid

theorem pn_index0_lt_threshold0 (a : T)
    (ha : T.index_Prop1 0 a) :
    a < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0)) T.Z := by
  exact index_Prop1_lt_succ 0 a ha

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
      intro v _ L hL hi hg hb
      cases v with
      | snoc _ xs a => cases xs; exact ⟨hL, Rank1Termination.index_mono (Nat.zero_le 1) L hi, hg, hb⟩
  | succ m ih =>
      intro v hv L hL hi hg hb
      cases v with
      | snoc _ xs a =>
          have ha := hv a (by simp [new.Vec.toList])
          have hr := ih xs (fun x hx => hv x (List.mem_append_left [a] hx)) L hL hi hg hb
          have hec := bridge_early_collapse_closed _ ha.1 ha.2
          rcases haux : transAux xs with ⟨found, sum, a0⟩
          simp only [haux] at hr
          simpa only [transAux.eq_3, haux, ← add_eq_hAdd, ca_card_times_add, ca_card_times_one_comp,
            Rank1Termination.add_assoc] using cb_card_append_lower m _ _ hec.1 hec.2.1 hr.1 hr.2.1 hr.2.2.1 hr.2.2.2

theorem pn_card_times_pos_shape (q : Nat) (c : T)
    (hc : T.index_Prop1 0 c) (hne : c ≠ T.Z) :
    ∃ m tail : T, T.card_times (q + 1) c = T.P 1 m tail := by
  cases hc with
  | z => exact False.elim (hne rfl)
  | p p a b hp _ =>
      have hp0 : p = 0 := by omega
      subst p
      simp [T.card_times, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1]

theorem pn_aux_sum_P0_index0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        ∀ c d : T, sum = T.P 0 c d → T.index_Prop1 0 sum := by
  intro k v hv found sum a0 haux c d hshape
  subst sum
  exact isNF1_index 0 0 c d (tc_transAux_inv v hv found _ a0 haux).2.2.1 (Nat.le_refl 0)

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
  have hec := bridge_early_collapse_closed a0 hi.1 hi.2.1
  have hb := pn_index0_lt_threshold0 _ hec.2.1
  cases sum with
  | Z => exact False.elim (hi.2.2.2.2.2.2.1 hf rfl)
  | P p c d =>
      cases p with
      | zero =>
          have hdel := ec_one_del_NF_index_good1 _ hi.2.2.1
            (pn_aux_sum_P0_index0 v hcoord found _ a0 haux c d rfl) hi.2.2.2.2.1
          have hr := cb_card_append_lower 0 _ _ hdel.1 hdel.2.1 hec.1
            (Rank1Termination.index_mono (Nat.zero_le 1) _ hec.2.1) hec.2.2 hb
          exact ⟨hr.1, hr.2.1, hr.2.2.1⟩
      | succ p =>
          have hr := pn_aux_card1_sum_append v hcoord _ hec.1 hec.2.1 hec.2.2 hb
          rw [haux] at hr
          exact ⟨hr.1, hr.2.1, hr.2.2.1⟩

theorem pn_principal_NF {lam : Nat} (v : new.Vec (new.T lam) lam)
    (hcoord : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    T.isNF1 (trans (new.T.P v new.T.Z)) := by
  have hz : T.isNF1 (T.P 0 T.Z T.Z) := T.isNF1.p _ _ _ T.isNF1.z T.isNF1.z (by intro x hx; cases hx) (T.Z_le _)
  cases lam with
  | zero => cases v; exact hz
  | succ k =>
      rw [_root_.trans.eq_2]
      rcases haux : transAux v with ⟨found, sum, a0⟩
      dsimp only
      split
      · have hm := pn_aux_found_middle_closed v hcoord found sum a0 haux ‹_›
        exact T.isNF1.p _ _ _ hm.1 T.isNF1.z hm.2.2 (T.Z_le _)
      · have hi := tc_transAux_inv v hcoord found sum a0 haux
        split
        · exact hz
        · exact T.isNF1.p _ _ _ hi.1 T.isNF1.z hi.2.1 (T.Z_le _)

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
  have hlex := ao_transAux_lex v w hv hw hmono hcmp true false sv av sw aw hav haw
  have hn := (tc_transAux_inv v hv true sv av hav).2.2.2.2.2.2.1 rfl
  rw [(tc_transAux_inv w hw false sw aw haw).2.2.2.2.2.2.2 rfl] at hlex
  exact hlex.elim lt_Z_inv (fun h => hn h.1)

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
  have hlex := ao_transAux_lex v w hv hw hmono hcmp false false sv av sw aw hav haw
  rw [(tc_transAux_inv w hw false sw aw haw).2.2.2.2.2.2.2 rfl] at hlex
  exact hlex.elim (fun h => False.elim (lt_Z_inv h)) And.right

theorem oc_one_del_P0 (a b : T) :
    T.one_del (T.P 0 a b) = if a = T.Z then b else T.P 0 a b := by
  cases a <;> rfl

theorem oc_one_del_NF_index0 (s : T)
    (hs : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    T.isNF1 (T.one_del s) ∧ T.index_Prop1 0 (T.one_del s) := by
  have h := ec_one_del_NF_index_good1 s hs hi (by simp [index_Prop1_G1_empty 0 s hi 1 (by omega)])
  exact ⟨h.1, h.2.1⟩

theorem oc_P0Z_tail_shape (b : T)
    (hbNF : T.isNF1 b) (hhead : T.head b ≤ T.P 0 T.Z T.Z) :
    b = T.Z ∨ ∃ d : T, b = T.P 0 T.Z d := by
  cases b with
  | Z => exact Or.inl rfl
  | P q c d =>
      have hq : q = 0 := by have h := head_le_index q 0 c T.Z hhead; omega
      subst q
      have hc : c = T.Z := (bridge_P0_head_mid_le T.Z c d hhead).elim (fun h => False.elim (lt_Z_inv h)) id
      subst c
      exact Or.inr ⟨d, rfl⟩

theorem oc_one_del_lt_index0 (a b : T)
    (haNF : T.isNF1 a) (haIdx : T.index_Prop1 0 a) (haNe : a ≠ T.Z)
    (hbNF : T.isNF1 b) (hbIdx : T.index_Prop1 0 b) (hbNe : b ≠ T.Z)
    (hab : a < b) :
    T.one_del a < T.one_del b := by
  cases haIdx with
  | z => exact False.elim (haNe rfl)
  | p p a b hp _ =>
      cases hbIdx with
      | z => exact False.elim (hbNe rfl)
      | p q c d hq _ =>
          have hp0 : p = 0 := by omega
          have hq0 : q = 0 := by omega
          subst p; subst q
          rw [oc_one_del_P0, oc_one_del_P0]
          cases hab with
          | p_head _ _ _ _ _ _ h => exact False.elim (Nat.lt_irrefl _ h)
          | p_mid _ _ _ _ _ h =>
              have hc : c ≠ T.Z := by intro he; rw [he] at h; exact lt_Z_inv h
              rw [ite_eq_right hc]
              split
              · exact lt_of_le_of_lt_thm T _ _ _ (T.isNF1_tail_le _ haNF _ _ _ rfl) (T.Lt.p_mid _ _ _ _ _ h)
              · exact T.Lt.p_mid _ _ _ _ _ h
          | p_tail _ _ _ _ h =>
              by_cases ha : a = T.Z
              · simp only [ite_eq_left ha]; exact h
              · simp only [ite_eq_right ha]; exact T.Lt.p_tail _ _ _ _ h

theorem oc_P1ZZ_le (c d : T) : T.P 1 T.Z T.Z ≤ T.P 1 c d := by
  exact partial_order.trans _ _ _ (bridge_lift_P1_le _ _ (T.Z_le c)) (bridge_head_le_self (T.P 1 c d))

theorem oc_one_del_lt_index1 (s t : T)
    (hsNF : T.isNF1 s) (hsIdx : T.index_Prop1 1 s) (hsNe : s ≠ T.Z)
    (htNF : T.isNF1 t) (htIdx : T.index_Prop1 1 t) (htNe : t ≠ T.Z)
    (hst : s < t) :
    T.one_del s < T.one_del t := by
  cases hsIdx with
  | z => exact False.elim (hsNe rfl)
  | p p a b hp _ =>
      cases htIdx with
      | z => exact False.elim (htNe rfl)
      | p q c d hq _ =>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl <;>
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
          · exact oc_one_del_lt_index0 _ _ hsNF (isNF1_index 0 0 a b hsNF (Nat.le_refl 0)) hsNe
              htNF (isNF1_index 0 0 c d htNF (Nat.le_refl 0)) htNe hst
          · have hi := (oc_one_del_NF_index0 _ hsNF (isNF1_index 0 0 a b hsNF (Nat.le_refl 0))).2
            exact lt_of_lt_of_le_thm T _ _ _ (index_Prop1_lt_succ 0 _ hi) (oc_P1ZZ_le c d)
          · cases hst with
            | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
          · exact hst

theorem oc_one_del_NF_index1 (s : T)
    (hs : T.isNF1 s) (hi : T.index_Prop1 1 s) :
    T.isNF1 (T.one_del s) ∧ T.index_Prop1 1 (T.one_del s) := by
  cases hi with
  | z => exact ⟨hs, T.index_Prop1.z⟩
  | p p a b hp hb =>
      cases p with
      | zero =>
          rw [oc_one_del_P0]
          split
          · exact ⟨(T.isNF1_P_inv _ _ _ hs).2.1, hb⟩
          · exact ⟨hs, T.index_Prop1.p _ _ _ hp hb⟩
      | succ p => exact ⟨hs, T.index_Prop1.p _ _ _ hp hb⟩

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
  have h := oc_false_false_a0_lt v w hv hw hmono hcmp sv av sw aw hav haw
  by_cases ha : av = T.Z <;> by_cases hb : aw = T.Z <;>
    simpa [_root_.trans.eq_2, hav, haw, ha, hb] using
      (show T.P 0 av (trans a) < T.P 0 aw (trans b) from T.Lt.p_mid _ _ _ _ _ h)

theorem oc_full_lt_false_true {k : Nat}
    (v w : new.Vec (new.T (k + 1)) (k + 1))
    (a b : new.T (k + 1))
    (sv av sw aw : T)
    (hav : transAux v = (false, sv, av))
    (haw : transAux w = (true, sw, aw)) :
    _root_.trans (new.T.P v a) < _root_.trans (new.T.P w b) := by
  simp only [_root_.trans.eq_2, hav, haw, Bool.false_eq_true, ite_false, ite_true]
  split <;> exact T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)

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
  have hiv := tc_transAux_inv v hv true sv av hav
  have hiw := tc_transAux_inv w hw true sw aw haw
  rw [_root_.trans.eq_2, hav, _root_.trans.eq_2, haw]
  apply T.Lt.p_mid
  rcases ao_transAux_lex v w hv hw hmono hcmp true true sv av sw aw hav haw with h | ⟨rfl, h⟩
  · have hvs := oc_one_del_NF_index1 sv hiv.2.2.1 hiv.2.2.2.1
    have hws := oc_one_del_NF_index1 sw hiw.2.2.1 hiw.2.2.2.1
    exact c1_card_append_lt_index1 _ _ _ _ hvs.1 hvs.2 hws.1 hws.2
      (oc_one_del_lt_index1 sv sw hiv.2.2.1 hiv.2.2.2.1 (hiv.2.2.2.2.2.2.1 rfl)
        hiw.2.2.1 hiw.2.2.2.1 (hiw.2.2.2.2.2.2.1 rfl) h)
      (bridge_early_collapse_closed av hiv.1 hiv.2.1).2.1
  · exact bridge_add_left_lt _ _ _ (bridge_early_collapse_lt av aw hiv.1 hiv.2.1 hiw.1 h)

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
  rcases hav : transAux v with ⟨fv, sv, av⟩
  rcases haw : transAux w with ⟨fw, sw, aw⟩
  cases fv <;> cases fw
  · exact oc_full_lt_false_false v w a b hv hw hmono hcmp sv av sw aw hav haw
  · exact oc_full_lt_false_true v w a b sv av sw aw hav haw
  · exact False.elim (oc_true_false_absurd v w hv hw hmono hcmp sv av sw aw hav haw)
  · exact oc_full_lt_true_true v w a b hv hw hmono hcmp sv av sw aw hav haw

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
  | zero => cases v; cases w; cases hcmp
  | succ k => exact oc_full_lt_of_compareVec v w a b hv hw hmono hcmp

theorem oc_mem_size_lt_P {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a x : new.T lam)
    (hx : x ∈ new.Vec.toList v) :
    new.T.size x < new.T.size (new.T.P v a) := by
  obtain ⟨i, rfl⟩ := new.Vec.mem_toList_exists_idx v x hx
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
      | Z => cases hst
      | P w b => exact tc_Z_lt_of_ne _ (tc_trans_ne_Z_of_ne_Z _ (by intro h; cases h))
  | p v a hvNF _ hvG _ ihv iha =>
      cases ht with
      | z => cases hst
      | p w b hwNF hbNF hwG hheadB =>
          have hvGood := fun x hx => hgood x
            (Nat.lt_of_lt_of_le (oc_mem_size_lt_P v a x hx) hsN) ⟨hvNF x hx, hvG x hx⟩
          have hwGood := fun x hx => hgood x
            (Nat.lt_of_lt_of_le (oc_mem_size_lt_P w b x hx) htN) ⟨hwNF x hx, hwG x hx⟩
          change (match new.compareVec v w with
            | .eq => new.compareT a b | ord => ord) = .lt at hst
          cases hcmp : new.compareVec v w with
          | lt =>
              apply oc_full_lt_of_compareVec_general v w a b hvGood hwGood ?_ hcmp
              intro x y hx hy hxy
              exact ihv x hx y
                (Nat.le_of_lt (Nat.lt_of_lt_of_le (oc_mem_size_lt_P v a x hx) hsN))
                (Nat.le_of_lt (Nat.lt_of_lt_of_le (oc_mem_size_lt_P w b y hy) htN)) (hwNF y hy) hxy
          | eq =>
              rw [hcmp] at hst
              obtain rfl := new.Vec_eq_sound v w hcmp
              rw [tc_trans_P_add v a, tc_trans_P_add v b]
              exact bridge_add_left_lt _ _ _ (iha b
                (Nat.le_of_lt (Nat.lt_of_lt_of_le (new.T.add_size_lt_P v a) hsN))
                (Nat.le_of_lt (Nat.lt_of_lt_of_le (new.T.add_size_lt_P v b) htN)) hbNF hst)
          | gt => simp [hcmp] at hst

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
  refine ⟨oc_order_preserve_core hgood s t hs ht, fun h => ?_⟩
  rcases strict_linear_order.total s t with hst | hts | rfl
  · exact hst
  · exact False.elim (lt_asymm_thm h (oc_order_preserve_core hgood t s ht hs hts))
  · exact False.elim (lt_irrefl_thm _ h)

theorem nfcore_head_NF {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s) :
    new.T.isNF (new.T.head s) := by
  cases hs with
  | z => exact new.T.isNF.z
  | p ls a hnf _ hg _ => exact new.T.isNF.p ls new.T.Z hnf new.T.isNF.z hg (Or.inl rfl)

theorem nfcore_trans_PZ_shape {lam : Nat}
    (v : new.Vec (new.T lam) lam) :
    ∃ i : Nat, ∃ m : T,
      trans (new.T.P v new.T.Z) = T.P i m T.Z := by
  rw [_root_.trans.eq_2]
  rcases transAux v with ⟨found, sum, a0⟩
  cases found <;> by_cases h : a0 = T.Z <;> simp [h, _root_.trans.eq_1]

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
  have hp := pn_principal_NF v hv
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
  rcases hle with h | h
  · have hc : new.compareVec w v = .lt := by
      change (match new.compareVec w v with | .eq => Ordering.eq | ord => ord) = .lt at h
      cases hc : new.compareVec w v <;> simp_all
    exact Or.inl (oc_full_lt_of_compareVec_general w v new.T.Z new.T.Z hw hv hmono hc)
  · exact Or.inr (congrArg _root_.trans (new.T_eq_sound _ _ h))

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
  | p _ _ hv ha hg hh =>
      have hvGood := fun x hx => hgoodSmall x (oc_mem_size_lt_P v a x hx) ⟨hv x hx, hg x hx⟩
      apply nfcore_trans_P_of_components v a hvGood (hnfSmall a (new.T.add_size_lt_P v a) ha)
      cases ha with
      | z => exact T.Z_le _
      | p w b hw _ hgw _ =>
          have hsize := fun x hx => Nat.lt_trans (oc_mem_size_lt_P w b x hx) (new.T.add_size_lt_P v (new.T.P w b))
          apply nfcore_trans_head_le_P w v b
          · exact fun x hx => hgoodSmall x (hsize x hx) ⟨hw x hx, hgw x hx⟩
          · exact hvGood
          · exact fun x y hx hy => hpresSmall x y (hsize x hx) (oc_mem_size_lt_P v _ y hy) (hw x hx) (hv y hy)
          · exact hh

end NormalFormAndOrder

/-! Support bounds and the simultaneous normal-form/order proof. -/

section TranslationSupport

open T

theorem sg_add_interval_size_le (a b x : T)
    (hax : a ≤ x) (hxu : x < T.add a b) :
    a.size ≤ x.size := by
  apply Nat.le_of_not_gt
  intro hsz
  have hn : a ≠ T.Z := by intro h; simp [h, T.size] at hsz
  have hxa := bridge_lt_add_left_of_size_lt a b x hn hsz hxu
  rcases hax with h | rfl
  · exact lt_asymm_thm h hxa
  · exact lt_irrefl_thm _ hxa

theorem sg_good0_part_fst (s : T)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.part s).1 → x < (T.part s).1 := by
  intro x hx
  apply bridge_lt_add_left_of_size_lt (T.part s).1 (T.part s).2 x
  · intro h; simp [h, T.G1] at hx
  · exact G1_size_lt 0 _ x hx
  · rw [bridge_part_add]
    apply hg
    rw [← bridge_part_add s, bridge_G1_add_eq]
    exact List.mem_append_left _ hx

theorem sg_early_G0_le (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.early_collapse s) → x ≤ s := by
  intro x hx
  rcases hp : T.part s with ⟨a, b⟩
  have hb : T.isNF1 b := by simpa [hp] using (bridge_part_NF1 s hs).2
  have hmem : ∀ x ∈ T.G1 0 a ++ T.G1 0 b, x < s := by
    intro x hx
    apply hg
    rwa [← bridge_part_add s, hp, bridge_G1_add_eq]
  rw [bridge_early_collapse_part s a b hp hb] at hx
  split at hx
  · exact Or.inl (hmem x (List.mem_append_right _ hx))
  · split at hx
    · simp [T.G1] at hx
      rcases hx with rfl | hx | hx
      · simpa [hp] using bridge_part_fst_le_self s
      · exact Or.inl (hmem x (List.mem_append_left _ hx))
      · exact Or.inl (hmem x (List.mem_append_right _ hx))
    · exact Or.inl (hmem x (List.mem_append_right _ hx))

theorem gc_tail_lt_of_NF1 (p : Nat) (a b : T)
    (h : T.isNF1 (T.P p a b)) : b < T.P p a b := by
  rcases T.isNF1_tail_le (T.P p a b) h p a b rfl with hlt | heq
  · exact hlt
  · exact False.elim ((Nat.ne_of_lt (T.size_lt_size_P_right p a b)) (congrArg T.size heq))

theorem sw_shift_support (k : Nat) (c s tail : T)
    (hc : T.index_Prop1 0 c)
    (hsupp : ∀ x : T, x ∈ T.G1 0 c → x ≤ s) :
    ∀ x : T,
      x ∈ T.G1 0 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) →
        x < T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail ∨
          x ≤ s := by
  induction k with
  | zero => exact fun x hx => Or.inr (hsupp x hx)
  | succ k ih =>
      intro x hx
      rw [mul_succ_shape, T.P_add_eq] at hx ⊢
      simp [T.G1] at hx
      rcases hx with rfl | hx
      · exact Or.inl (T.Lt.Z_lt_P _ _ _)
      · exact (ih x hx).imp
          (fun h => lt_trans_thm _ _ _ h (T.Lt.p_mid _ _ _ _ _ (bridge_shift_lt_wrap k c hc))) id

theorem cs_card_support (n : Nat) : ∀ c s : T,
    T.isNF1 c → T.index_Prop1 0 c →
    (∀ x : T, x ∈ T.G1 0 c → x ≤ s) →
    ∀ x : T, x ∈ T.G1 0 (T.card_times (n + 1) c) →
      x < T.P 1 (T.card_times (n + 1) c) T.Z ∨ x ≤ s := by
  intro c s hnf hi hsupp
  induction hi with
  | z => intro x hx; cases hx
  | p p a b hp hb ih =>
      have hp0 : p = 0 := by omega
      subst p
      have ha := T.isNF1_P_inv _ _ _ hnf
      have hec := bridge_early_collapse_closed a ha.1 ha.2.2.1
      have hcard := bridge_card_times_closed (n + 1) _ hnf (T.index_Prop1.p _ _ _ (Nat.le_refl _) hb)
      intro x hx
      simp only [T.card_times, ite_true, ← add_eq_hAdd, T.P_add_eq, T.add.eq_1] at hx hcard ⊢
      have hwrap := bridge_good_index_lt_wrap 1 _ T.Z hcard.2.1 hcard.2.2
      simp only [T.G1.eq_2, ite_eq_left (Nat.zero_le 1), List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · exact Or.inl (lt_trans_thm _ _ _ (bridge_shift_lt_outer n _ _ hec.2.1) hwrap)
      · rcases sw_shift_support n _ a _ hec.2.1 (sg_early_G0_le a ha.1 ha.2.2.1) x hx with h | h
        · exact Or.inl (lt_trans_thm _ _ _ h hwrap)
        · exact Or.inr (partial_order.trans _ _ _ h (hsupp a (by simp [T.G1])))
      · have hr := ih ha.2.1 (fun y hy => hsupp y (by simp [T.G1, hy])) x hx
        exact hr.imp (fun h => lt_trans_thm _ _ _ h (T.Lt.p_mid _ _ _ _ _ (gc_tail_lt_of_NF1 _ _ _ hcard.1))) id

theorem cs_one_del_G0 (s x : T)
    (hx : x ∈ T.G1 0 (T.one_del s)) :
    x ∈ T.G1 0 s := by
  cases s with
  | Z => exact hx
  | P p a b =>
      cases p with
      | zero => cases a <;> simp_all [T.one_del, T.G1]
      | succ p => exact hx

theorem cs_one_del_card_succ_add (k : Nat) (c y : T)
    (hcIdx : T.index_Prop1 0 c) (hcNe : c ≠ T.Z) :
    T.one_del (T.add (T.card_times (k + 1) c) y) =
      T.add (T.card_times (k + 1) c) y := by
  obtain ⟨m, tail, h⟩ := pn_card_times_pos_shape k c hcIdx hcNe
  rw [h, T.P_add_eq]
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
      intro v _ found sum a0 haux
      rw [co_len1_sum_zero v found sum a0 haux]
      constructor <;> intro x hx <;> cases hx
  | succ m ih =>
      intro v hv found sum a0 haux
      cases v with
      | snoc _ xs a =>
          have hxs := fun z hz => hv z (List.mem_append_left [a] hz)
          have ha := hv a (by simp [new.Vec.toList])
          rcases hrest : transAux xs with ⟨fr, sr, ar⟩
          have hp := ih xs hxs fr sr ar hrest
          have hr := sc_transAux_card1_inv xs hxs fr sr ar hrest
          rw [transAux.eq_3, hrest] at haux
          cases a with
          | Z =>
              change (fr, sr, ar) = (found, sum, a0) at haux
              cases haux
              constructor <;> intro x hx
              · exact (hp.1 x hx).imp id (fun ⟨z, hz, h⟩ => ⟨z, List.mem_append_left _ hz, h⟩)
              · exact (hp.2 x hx).imp id (fun ⟨z, hz, h⟩ => ⟨z, List.mem_append_left _ hz, h⟩)
          | P ls b =>
              let ec := T.early_collapse (trans (new.T.P ls b))
              have hec := bridge_early_collapse_closed _ ha.1 ha.2
              have hn := bridge_early_collapse_ne_Z _ (tc_trans_ne_Z_of_ne_Z (new.T.P ls b) (by intro h; cases h))
              cases haux
              have hU : ∀ x ∈ T.G1 0 (T.add (T.card_times (m + 1) ec) (T.card_times 1 sr)),
                  x < T.P 1 (T.add (T.card_times (m + 1) ec) (T.card_times 1 sr)) T.Z ∨
                    ∃ z : new.T lam, z ∈ new.Vec.toList xs ++ [new.T.P ls b] ∧ x ≤ trans z := by
                intro x hx
                rw [bridge_G1_add_eq, List.mem_append] at hx
                rcases hx with hx | hx
                · rcases cs_card_support m ec _ hec.1 hec.2.1 (sg_early_G0_le _ ha.1 ha.2) x hx with h | h
                  · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h (bridge_lift_P1_le _ _ (wt_add_self_le _ _)))
                  · exact Or.inr ⟨new.T.P ls b, by simp, h⟩
                · rcases hp.1 x hx with h | ⟨z, hz, h⟩
                  · have hlt := lt_of_lt_of_le_thm T _ _ _ (hr.2.2.2 ec hec.1 hec.2.1 hn)
                      (wt_add_self_le _ (T.card_times 1 sr))
                    exact Or.inl (lt_trans_thm _ _ _ h (T.Lt.p_mid _ _ _ _ _ hlt))
                  · exact Or.inr ⟨z, List.mem_append_left _ hz, h⟩
              constructor
              · simpa only [← add_eq_hAdd, ca_card_times_add, ca_card_times_one_comp, ec, new.Vec.toList] using hU
              · cases m with
                | zero =>
                    simp only [← add_eq_hAdd, co_len1_sum_zero xs fr sr a0 hrest, tc_card_times_zero, T.add_Z]
                    have hd := oc_one_del_NF_index0 ec hec.1 hec.2.1
                    intro x hx
                    have hc := cs_card_support 0 (T.one_del ec) _ hd.1 hd.2
                      (fun y hy => sg_early_G0_le _ ha.1 ha.2 y (cs_one_del_G0 ec y hy)) x hx
                    exact hc.imp id (fun h => ⟨new.T.P ls b, by simp [new.Vec.toList], h⟩)
                | succ j =>
                    simp only [← add_eq_hAdd]
                    rw [cs_one_del_card_succ_add j _ _ hec.2.1 hn]
                    simpa only [ca_card_times_add, ca_card_times_one_comp, ec, new.Vec.toList] using hU

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
      | snoc _ xs a => cases xs; cases haux; rfl
  | succ m ih =>
      intro v found sum a0 haux
      cases v with
      | snoc _ xs a =>
          rcases hrest : transAux xs with ⟨fr, sr, ar⟩
          rw [transAux.eq_3, hrest] at haux
          cases haux
          simpa [new.Vec.idx] using ih xs fr sr a0 hrest

theorem ts_coord_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.Vec.toList v) :
    z ∈ new.T.G (new.T.P v a) := by
  obtain ⟨i, rfl⟩ := new.Vec.mem_toList_exists_idx v z hz
  rw [new.T.G_P_eq]
  exact List.mem_append_left _ (new.Vec.Gres_mem_of_idx v i)

theorem ts_tail_mem_G {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.G a) :
    z ∈ new.T.G (new.T.P v a) := by
  exact List.mem_append_right _ hz

theorem ts_P1Z_le_tail (m tail : T) :
    T.P 1 m T.Z ≤ T.P 1 m tail := by
  exact bridge_head_le_self (T.P 1 m tail)

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
  cases hs with
  | z => intro y hy; cases hy
  | p v a hv ha hg _ =>
      have hcoord := fun z hz => hgoodSmall z (oc_mem_size_lt_P v a z hz) ⟨hv z hz, hg z hz⟩
      have hple : trans (new.T.P v new.T.Z) ≤ trans (new.T.P v a) := by
        rw [tc_trans_P_add v a]
        exact wt_add_self_le _ _
      have htle : trans a ≤ trans (new.T.P v a) := by
        obtain ⟨i, m, hp⟩ := nfcore_trans_PZ_shape v
        rw [tc_trans_P_add v a, hp, T.P_add_eq, T.add.eq_1] at ht ⊢
        exact T.isNF1_tail_le _ ht _ _ _ rfl
      intro y hy
      rw [tc_trans_P_add v a, bridge_G1_add_eq, List.mem_append] at hy
      rcases hy with hy | hy
      · suffices y < trans (new.T.P v new.T.Z) ∨ ∃ z, z ∈ new.T.G (new.T.P v a) ∧ y ≤ trans z by
          exact this.imp (fun h => lt_of_lt_of_le_thm T _ _ _ h hple) id
        cases lam with
        | zero =>
            cases v
            have hz : y = T.Z := by simpa [_root_.trans, transAux, T.G1] using hy
            subst y
            exact Or.inl (T.Lt.Z_lt_P _ _ _)
        | succ k =>
            rcases haux : transAux v with ⟨found, sum, a0⟩
            have hi := tc_transAux_inv v hcoord found sum a0 haux
            have hzero : ∀ y : T, y ≤ a0 → ∃ z, z ∈ new.T.G (new.T.P v a) ∧ y ≤ trans z := by
              intro y hy
              refine ⟨v.idx ⟨0, Nat.zero_lt_succ k⟩, ts_coord_mem_G v a _ (new.Vec.idx_mem_toList v _), ?_⟩
              rwa [← ts_transAux_a0 v found sum a0 haux]
            cases found with
            | false =>
                have he : trans (new.T.P v new.T.Z) = T.P 0 a0 T.Z := by
                  by_cases h : a0 = T.Z <;> simp [_root_.trans.eq_2, haux, h, _root_.trans.eq_1]
                rw [he] at hy ⊢
                simp [T.G1] at hy
                rcases hy with rfl | hy
                · exact Or.inr (hzero y (Or.inr rfl))
                · exact Or.inr (hzero y (Or.inl (hi.2.1 y hy)))
            | true =>
                let A := T.card_times 1 (T.one_del sum)
                let E := T.early_collapse a0
                let M := T.add A E
                have he : trans (new.T.P v new.T.Z) = T.P 1 M T.Z := by simp [_root_.trans.eq_2, haux, M, A, E, add_eq_hAdd, _root_.trans.eq_1]
                rw [he] at hy ⊢
                simp [T.G1] at hy
                rcases hy with rfl | hy
                · have hm := pn_aux_found_middle_closed v hcoord true sum a0 haux rfl
                  exact Or.inl (bridge_good_index_lt_wrap 1 M T.Z hm.2.1 hm.2.2)
                · rw [bridge_G1_add_eq, List.mem_append] at hy
                  rcases hy with hy | hy
                  · rcases (as_card1_support_pair v hcoord true sum a0 haux).2 y hy with h | ⟨z, hz, h⟩
                    · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h (bridge_lift_P1_le A M (wt_add_self_le A E)))
                    · exact Or.inr ⟨z, ts_coord_mem_G v a z hz, h⟩
                  · exact Or.inr (hzero y (sg_early_G0_le a0 hi.1 hi.2.1 y hy))
      · rcases hdecompSmall a (new.T.add_size_lt_P v a) ha y hy with h | ⟨z, hz, h⟩
        · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h htle)
        · exact Or.inr ⟨z, ts_tail_mem_G v a z hz, h⟩

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
  intro s
  induction s using (measure new.T.size).wf.induction with
  | h s ih =>
      have hgood := fun x hx => (ih x hx).2.2
      have hpres := bo_order_preserve_bounded (new.T.size s) hgood
      have hNF : new.T.isNF s → T.isNF1 (trans s) := by
        intro hs
        cases s with
        | Z => exact T.isNF1.z
        | P v a =>
            exact nfcore_NF_step v a hs (fun x hx => (ih x hx).1) hgood
              (fun x y hx hy => hpres x y (Nat.le_of_lt hx) (Nat.le_of_lt hy))
      have hdec := fun hs => ts_support_decomp_step s hs (hNF hs) hgood (fun x hx => (ih x hx).2.1)
      refine ⟨hNF, hdec, fun hs => ⟨hNF hs.1, ?_⟩⟩
      intro y hy
      rcases hdec hs.1 y hy with h | ⟨z, hz, h⟩
      · exact h
      · exact lt_of_le_of_lt_thm T _ _ _ h (hpres z s (Nat.le_of_lt (new.T.G_size_lt s z hz))
          (Nat.le_refl _) (new.T.isNF_G_isNFComp s hs.1 z hz).1 hs.1 (hs.2 z hz))

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
  rcases new.T_total s t with h | h | h
  · have htr := (gnf_order_embedding s t hs ht).mp h
    rw [heq] at htr
    exact False.elim (lt_irrefl_thm _ htr)
  · have htr := (gnf_order_embedding t s ht hs).mp h
    rw [heq] at htr
    exact False.elim (lt_irrefl_thm _ htr)
  · exact h

theorem gnf_reflect_le {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (hle : trans s ≤ trans t) : s ≤ t := by
  rcases hle with hlt | heq
  · exact Or.inl ((gnf_order_embedding s t hs ht).mpr hlt)
  · rw [gnf_trans_injective s t hs ht heq]
    exact Or.inr (new.T_refl t)

theorem gnf_le_iff {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t) : s ≤ t ↔ trans s ≤ trans t := by
  exact ⟨fun h => h.imp (gnf_order_embedding s t hs ht).mp (fun h => congrArg trans (new.T_eq_sound s t h)),
    gnf_reflect_le s t hs ht⟩

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
              simp only [c1_p0, T.early_collapse, T.part, ite_true, T.P_add_eq] at hnf hb
              exact lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 _ _ _ hnf) hb
          | P q c e => exact hb
      | succ p => exact hb

theorem ot_trans_global_bound {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s) (hpos : 0 < lam) :
    trans s < ot_trans_bound lam := by
  cases lam with
  | zero => exact False.elim (Nat.lt_irrefl _ hpos)
  | succ k =>
      cases hs with
      | z => cases k <;> exact T.Lt.Z_lt_P _ _ _
      | p v a hv _ hg _ =>
          have hcoords := fun x hx => gnf_good x ⟨hv x hx, hg x hx⟩
          cases k with
          | zero =>
              cases v with
              | snoc _ xs b =>
                  cases xs
                  rw [_root_.trans.eq_2, transAux.eq_2]
                  simp only [Bool.false_eq_true, ite_false]
                  split <;> exact T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
          | succ k =>
              rcases haux : transAux v with ⟨found, sum, a0⟩
              have hi := tc_transAux_inv v hcoords found sum a0 haux
              have hec := bridge_early_collapse_closed a0 hi.1 hi.2.1
              have hb := pn_aux_card1_sum_append v hcoords _ hec.1 hec.2.1 hec.2.2 (pn_index0_lt_threshold0 _ hec.2.1)
              rw [haux] at hb
              have hmid := ot_one_del_card_bound sum _ _ hb.1 hb.2.2.2
              rw [_root_.trans.eq_2, haux]
              dsimp only
              split
              · exact T.Lt.p_mid _ _ _ _ _ hmid
              · split <;> exact T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)

def ot_v0 {lam : Nat} (k : Nat) (a : new.T lam) : new.Vec (new.T lam) (k + 1) :=
  new.Vec.ofFn (k + 1) (fun i => if i.val = 0 then a else new.T.Z)

theorem ot_transAux_v0 {lam : Nat} (k : Nat) (a : new.T lam) :
    transAux (ot_v0 k a) = (false, T.Z, trans a) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      unfold ot_v0 at ih ⊢
      rw [new.Vec.ofFn]
      simp only [Fin.val_last, Fin.val_castSucc, Nat.add_one_ne_zero, ite_false]
      rw [transAux.eq_3, ih]
      rfl

theorem ot_trans_v0 (k : Nat) (a b : new.T (k + 1)) :
    trans (new.T.P (ot_v0 k a) b) = T.P 0 (trans a) (trans b) := by
  by_cases h : trans a = T.Z <;> simp [_root_.trans.eq_2, ot_transAux_v0, h]

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

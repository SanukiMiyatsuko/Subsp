import Subsp.old.stop_translation

/-! Exact outer-shape facts for the legacy translation. -/

namespace LegacyTranslation

theorem p_zero_add (p : Nat) (a y : T) :
    T.add (T.P p a T.Z) y = T.P p a y := by
  cases y <;> rfl

theorem transAux_snoc_zero {lam m : Nat}
    (v : new.Vec (new.T lam) (m + 1)) :
    transAux (new.Vec.snoc (m + 1) v new.T.Z) = transAux v := by
  simp only [transAux, _root_.trans, T.early_collapse, T.part]
  change ((transAux v).1, (transAux v).2) = transAux v
  exact Prod.eta _

theorem transAux_countable_exact {lam k : Nat}
    (v : new.Vec (new.T lam) (k + 1))
    (hv : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z) :
    transAux v =
      transAux
        (new.Vec.snoc 0 new.Vec.nil
          (v.idx ⟨0, Nat.zero_lt_succ k⟩)) := by
  induction k with
  | zero =>
      cases v with
      | snoc _ xs a =>
          cases xs
          rfl
  | succ k ih =>
      cases v with
      | snoc _ xs a =>
          have ha : a = new.T.Z := by
            have h := hv (Fin.last (k + 1)) (Nat.zero_lt_succ k)
            simpa [new.Vec.idx] using h
          subst a
          rw [transAux_snoc_zero]
          have hxs : ∀ i : Fin (k + 1), 0 < i.val → xs.idx i = new.T.Z := by
            intro i hi
            have h := hv i.castSucc hi
            simpa [new.Vec.idx, i.isLt] using h
          simpa [new.Vec.idx] using ih xs hxs

theorem transAux_zeros {lam : Nat} (k : Nat) :
    transAux
      (new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))) =
      (T.P 0 T.Z T.Z, T.Z) := by
  cases k with
  | zero => rfl
  | succ k =>
      have hv :
          ∀ i : Fin (k + 1), 0 < i.val →
            (new.Vec.ofFn (k + 1)
              (fun _ => (new.T.Z : new.T lam))).idx i = new.T.Z := by
        intro i hi
        rw [new.Vec.ofFn_idx]
      rw [transAux_countable_exact _ hv]
      simp [new.Vec.ofFn_idx, transAux, _root_.trans,
        T.early_collapse, T.part]

theorem transAux_countable_head_exact {lam k : Nat}
    (v : new.Vec (new.T lam) (k + 1))
    (hv : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z) :
    (transAux v).1 =
      T.P 0 (trans (v.idx ⟨0, Nat.zero_lt_succ k⟩)) T.Z := by
  rw [transAux_countable_exact v hv]
  cases h0 : v.idx ⟨0, Nat.zero_lt_succ k⟩ with
  | Z => simp [transAux, _root_.trans]
  | P ls add => simp [transAux, _root_.trans]

theorem trans_countable_P {k : Nat}
    (v : new.Vec (new.T (k + 1)) (k + 1)) (b : new.T (k + 1))
    (hv : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z) :
    trans (new.T.P v b) =
      T.P 0 (trans (v.idx ⟨0, Nat.zero_lt_succ k⟩)) (trans b) := by
  rw [trans_as_add, transAux_countable_head_exact v hv, T.P_add_eq, zero_add]

theorem trans_base_succ (k n : Nat) :
    trans
      (new.T.P
        (new.Vec.ofFn (k + 1)
          (fun i =>
            if i.val = 0 then new.T.LF (k + 1) n
            else new.T.Z))
        new.T.Z) =
      T.P 0 (trans (new.T.LF (k + 1) n)) T.Z := by
  have hv :
      ∀ i : Fin (k + 1), 0 < i.val →
        (new.Vec.ofFn (k + 1)
          (fun j =>
            if j.val = 0 then new.T.LF (k + 1) n
            else new.T.Z)).idx i = new.T.Z := by
    intro i hi
    rw [new.Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hi)]
  rw [trans_countable_P _ _ hv, new.Vec.ofFn_idx]
  rfl

theorem compareVec_countable_succ {lam k : Nat}
    (v w : new.Vec (new.T lam) (k + 1))
    (hv : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z)
    (hw : ∀ i : Fin (k + 1), 0 < i.val → w.idx i = new.T.Z) :
    new.compareVec v w =
      new.compareT
        (v.idx ⟨0, Nat.zero_lt_succ k⟩)
        (w.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  induction k with
  | zero =>
      cases v with
      | snoc _ xs a =>
          cases xs
          cases w with
          | snoc _ ys b =>
              cases ys
              cases h : new.compareT a b <;>
                simp [new.compareVec, new.Vec.idx, h]
  | succ k ih =>
      cases v with
      | snoc _ xs a =>
          cases w with
          | snoc _ ys b =>
              have ha : a = new.T.Z := by
                have h := hv (Fin.last (k + 1)) (Nat.zero_lt_succ k)
                simpa [new.Vec.idx] using h
              have hb : b = new.T.Z := by
                have h := hw (Fin.last (k + 1)) (Nat.zero_lt_succ k)
                simpa [new.Vec.idx] using h
              subst a
              subst b
              have hxs : ∀ i : Fin (k + 1), 0 < i.val → xs.idx i = new.T.Z := by
                intro i hi
                have h := hv i.castSucc hi
                simpa [new.Vec.idx, i.isLt] using h
              have hys : ∀ i : Fin (k + 1), 0 < i.val → ys.idx i = new.T.Z := by
                intro i hi
                have h := hw i.castSucc hi
                simpa [new.Vec.idx, i.isLt] using h
              simpa [new.compareVec, new.Vec.idx, new.T_refl] using
                ih xs ys hxs hys

theorem trans_ofNat {lam : Nat} (n : Nat) :
    trans (new.T.ofNat (lam := lam) n) = T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases lam with
      | zero =>
          rw [new.T.ofNat, trans_as_add]
          simp only [new.Vec.ofFn, transAux]
          rw [ih, T.P_add_eq, zero_add]
          rfl
      | succ k =>
          have hv :
              ∀ i : Fin (k + 1), 0 < i.val →
                (new.Vec.ofFn (k + 1)
                  (fun _ => (new.T.Z : new.T (k + 1)))).idx i = new.T.Z := by
            intro i hi
            rw [new.Vec.ofFn_idx]
          rw [new.T.ofNat, trans_countable_P _ _ hv, new.Vec.ofFn_idx, ih]
          rfl

theorem trans_eq_zero_iff {lam : Nat} (s : new.T lam) :
    trans s = T.Z ↔ s = new.T.Z := by
  cases s with
  | Z => simp [_root_.trans]
  | P v b =>
      obtain ⟨p, a, hp, _⟩ := aux_principal v
      constructor
      · intro h
        rw [trans_as_add, hp, T.P_add_eq, zero_add] at h
        cases h
      · intro h
        cases h

theorem trans_ne_zero_of_ne_zero {lam : Nat} (s : new.T lam)
    (hs : s ≠ new.T.Z) : trans s ≠ T.Z := by
  intro h
  exact hs ((trans_eq_zero_iff s).mp h)

end LegacyTranslation

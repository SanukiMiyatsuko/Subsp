import Subsp.new.stop_nf_order_c

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
            cases new.Vec.mem_toList_exists_idx v x hx with
            | intro i hi =>
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
                      apply Decidable.byCases (p := trans a = T.Z)
                      · intro ha
                        rw [ite_eq_left ha]
                        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
                      · intro ha
                        rw [ite_eq_right ha]
                        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
          | succ k =>
              cases haux : transAux v with
              | mk found rest =>
                  cases rest with
                  | mk sum a0 =>
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
                          apply Decidable.byCases (p := a0 = T.Z)
                          · intro ha
                            rw [ite_eq_left ha]
                            exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
                          · intro ha
                            rw [ite_eq_right ha]
                            exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
                      | true =>
                          exact T.Lt.p_mid 1 _ _ _ _ hmid

#print axioms ot_trans_global_bound

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
  apply Decidable.byCases (p := trans a = T.Z)
  · intro h
    rw [ite_eq_left h, h]
  · intro h
    rw [ite_eq_right h]

#print axioms ot_trans_v0

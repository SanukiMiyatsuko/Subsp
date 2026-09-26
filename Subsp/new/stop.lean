import Subsp.order
import Subsp.Buchholz.Base
import Subsp.Buchholz.Rank1
import Subsp.new.Base
import Subsp.new.subsp
import Subsp.new.trans
import Subsp.new.stop_nf_order_c
import Subsp.new.stop_ot_downward
import Subsp.new.stop_trans_bounds
import Subsp.new.stop_surj_low
import Subsp.new.stop_surj_general

theorem NF_is_NF1 (lam : Nat) (s : new.T lam) :
  new.T.isNF s → T.isNF1 (trans s) := by
  exact gnf_NF_is_NF1 s

theorem order_embeding (lam : Nat) (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
  s < t ↔ trans s < trans t := by
  exact gnf_order_embedding s t hs ht

theorem trans_injective_on_NF {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (htrans : trans s = trans t) : s = t := by
  cases strict_linear_order.total s t with
  | inl hst =>
      have htr : trans s < trans t :=
        (order_embeding lam s t hs ht).mp hst
      rw [htrans] at htr
      exact False.elim (strict_partial_order.irrefl (trans t) htr)
  | inr hrest =>
      cases hrest with
      | inl hts =>
          have htr : trans t < trans s :=
            (order_embeding lam t s ht hs).mp hts
          rw [htrans] at htr
          exact False.elim (strict_partial_order.irrefl (trans t) htr)
      | inr heq =>
          exact heq

def new.T.NF (lam : Nat) := { s : T lam // isNF s }

theorem wellfounded_NF (lam : Nat) : WellFounded (fun s t : new.T.NF lam => s.val < t.val) := by
  let R1 := fun x y : T.NF1 => x.1 < y.1
  let RN := fun x y : new.T.NF lam => x.1 < y.1
  have hacc :
      ∀ a : T.NF1, ∀ s : new.T.NF lam,
        trans s.1 = a.1 → Acc RN s := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
      intro s heq
      constructor
      intro t hts
      have htrans : trans t.1 < trans s.1 :=
        (order_embeding lam t.1 s.1 t.2 s.2).mp hts
      have htrans' : trans t.1 < a.1 := by
        rw [← heq]
        exact htrans
      let ta : T.NF1 := ⟨trans t.1, NF_is_NF1 lam t.1 t.2⟩
      exact ih ta htrans' t rfl
  constructor
  intro s
  let a : T.NF1 := ⟨trans s.1, NF_is_NF1 lam s.1 s.2⟩
  exact hacc a s rfl

#print axioms wellfounded_NF

theorem ot_bound_coords_zero {lam : Nat}
    (_hlam : 1 < lam) (ls : new.Vec (new.T lam) lam) (add : new.T lam)
    (_hnf : new.T.isNF (new.T.P ls add))
    (hb : new.T.P ls add < ot_bound lam) :
    ∀ j : Fin lam, 0 < j.val → ls.idx j = new.T.Z := by
  have hvec :
      new.compareVec ls
        (new.Vec.ofFn lam (fun x =>
          if x.val = 1 then ot_unit lam else new.T.Z)) = Ordering.lt := by
    change
      (match new.compareVec ls
        (new.Vec.ofFn lam (fun x =>
          if x.val = 1 then ot_unit lam else new.T.Z)) with
      | Ordering.eq => new.compareT add new.T.Z
      | ord => ord) = Ordering.lt at hb
    cases hc : new.compareVec ls
        (new.Vec.ofFn lam (fun x =>
          if x.val = 1 then ot_unit lam else new.T.Z)) with
    | lt => exact rfl
    | eq =>
        rw [hc] at hb
        change add < new.T.Z at hb
        exact False.elim (ot_lt_Z_inv add hb)
    | gt =>
        rw [hc] at hb
        cases hb
  cases new.Vec.compare_lt_has_pivot ls
      (new.Vec.ofFn lam (fun x =>
        if x.val = 1 then ot_unit lam else new.T.Z)) hvec with
  | intro q hq =>
      cases hq with
      | intro hAbove hLt =>
          have hq0 : q.val ≠ 0 := by
            intro hzero
            have hbad := hLt
            rw [new.Vec.ofFn_idx] at hbad
            have hq1 : q.val ≠ 1 := by
              intro hone
              rw [hzero] at hone
              cases hone
            rw [ite_eq_right hq1] at hbad
            exact ot_lt_Z_inv (ls.idx q) hbad
          have hqNotGt : ¬ 1 < q.val := by
            intro hgt
            have hbad := hLt
            rw [new.Vec.ofFn_idx] at hbad
            have hq1 : q.val ≠ 1 := Nat.ne_of_gt hgt
            rw [ite_eq_right hq1] at hbad
            exact ot_lt_Z_inv (ls.idx q) hbad
          have hqle : q.val ≤ 1 := Nat.le_of_not_gt hqNotGt
          have hqge : 1 ≤ q.val := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hq0)
          have hqval : q.val = 1 := Nat.le_antisymm hqle hqge
          have hqLtUnit : ls.idx q < ot_unit lam := by
            have h := hLt
            rw [new.Vec.ofFn_idx, ite_eq_left hqval] at h
            exact h
          have hqz : ls.idx q = new.T.Z := by
            apply Decidable.byCases (p := ls.idx q = new.T.Z)
            · intro hz
              exact hz
            · intro hne
              have hunit : ot_unit lam ≤ ls.idx q :=
                ot_unit_le_of_ne_Z (ls.idx q) hne
              have hbad : ot_unit lam < ot_unit lam :=
                new.T.lt_of_le_of_lt (ot_unit lam) (ls.idx q)
                  (ot_unit lam) hunit hqLtUnit
              exact False.elim (strict_partial_order.irrefl (ot_unit lam) hbad)
          intro j hj
          cases Nat.lt_trichotomy j.val q.val with
          | inl hjq =>
              rw [hqval] at hjq
              have hjzero : j.val = 0 :=
                Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hjq)
              rw [hjzero] at hj
              exact False.elim (Nat.lt_irrefl 0 hj)
          | inr hrel =>
              cases hrel with
              | inl hjeq =>
                  have hjqeq : j = q := Fin.eq_of_val_eq hjeq
                  cases hjqeq
                  exact hqz
              | inr hqj =>
                  have heq := hAbove j hqj
                  rw [new.Vec.ofFn_idx] at heq
                  have hj1 : j.val ≠ 1 := by
                    intro he
                    rw [he, hqval] at hqj
                    exact Nat.lt_irrefl 1 hqj
                  rw [ite_eq_right hj1] at heq
                  exact heq

#print axioms ot_bound_coords_zero

theorem ot_base_succ_cofinal (k : Nat) (s : new.T (k + 1))
    (hs : new.T.isNF s)
    (hbound : 1 < k + 1 → s < ot_bound (k + 1)) :
    ∃ n : Nat,
      s < new.T.P
        (new.Vec.ofFn (k + 1)
          (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
        new.T.Z := by
  cases s with
  | Z =>
      refine ⟨0, ?_⟩
      rfl
  | P ls add =>
      let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
      have hcoord0 : new.T.isNF (ls.idx i0) :=
        (new.T.isNF_P_coord_NFComp ls add hs i0).1
      cases ot_new_LF_cofinal (k + 1) (ls.idx i0) hcoord0 with
      | intro n hn =>
          refine ⟨n, ?_⟩
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot ls
            (new.Vec.ofFn (k + 1)
              (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z)) i0
          · intro j hij
            change 0 < j.val at hij
            cases k with
            | zero =>
                have hjle : j.val ≤ 0 := Nat.le_of_lt_succ j.isLt
                exact False.elim ((Nat.not_lt_of_ge hjle) hij)
            | succ k' =>
                have hlam : 1 < (k' + 1) + 1 := by
                  exact Nat.succ_lt_succ (Nat.zero_lt_succ k')
                have hz : ls.idx j = new.T.Z :=
                  ot_bound_coords_zero hlam ls add hs (hbound hlam) j hij
                rw [new.Vec.ofFn_idx]
                have hj0 : j.val ≠ 0 := Nat.ne_of_gt hij
                rw [ite_eq_right hj0]
                exact hz
          · rw [new.Vec.ofFn_idx]
            have hi0 : i0.val = 0 := rfl
            rw [ite_eq_left hi0]
            exact hn

#print axioms ot_base_succ_cofinal

theorem new.T.OT_iff_NF (lam : Nat) (s : T lam) :
  isOT lam s ↔ isNF s ∧
    (1 < lam → s < P (Vec.ofFn lam (fun x => if x.val = 1 then P (Vec.ofFn lam (fun _ => Z)) Z else Z)) Z) := by
  constructor
  · exact ot_new_isOT_sound lam s
  · intro h
    cases lam with
    | zero =>
        cases ot_new_LF_cofinal 0 s h.1 with
        | intro n hn =>
            exact ot_new_isOT_downward (new.T.LF 0 n) s
              (new.T.isOT.base_0 n) h.1 (Or.inl hn)
    | succ k =>
        have hb : 1 < k + 1 → s < ot_bound (k + 1) := by
          intro hk
          exact h.2 hk
        cases ot_base_succ_cofinal k s h.1 hb with
        | intro n hn =>
            exact ot_new_isOT_downward
              (new.T.P
                (new.Vec.ofFn (k + 1)
                  (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
                new.T.Z)
              s (new.T.isOT.base_succ k n) h.1 (Or.inl hn)

#print axioms new.T.OT_iff_NF

def new.T.OT (lam : Nat) := { s : T lam // isOT lam s }

theorem wellfounded_OT (lam : Nat) : WellFounded (fun s t : new.T.OT lam => s.val < t.val) := by
  let RN := fun x y : new.T.NF lam => x.1 < y.1
  let RO := fun x y : new.T.OT lam => x.1 < y.1
  have hacc :
      ∀ s : new.T.NF lam, ∀ hs : new.T.isOT lam s.1,
        Acc RO ⟨s.1, hs⟩ := by
    intro s
    induction s using (wellfounded_NF lam).induction with
    | h s ih =>
      intro hs
      constructor
      intro t hts
      have htnf : new.T.isNF t.1 :=
        ((new.T.OT_iff_NF lam t.1).mp t.2).1
      exact ih ⟨t.1, htnf⟩ hts t.2
  constructor
  intro s
  have hsnf : new.T.isNF s.1 :=
    ((new.T.OT_iff_NF lam s.1).mp s.2).1
  exact hacc ⟨s.1, hsnf⟩ s.2

def T.isSubNF (n : Nat) (s : T) :=
  isNF1 s ∧
    match n with
    | 0 => s < P 0 (P 0 Z Z) Z
    | 1 => s < P 0 (P 1 Z Z) Z
    | n' + 1 => s < P 0 (P 1 (P 1 (mul (P 1 Z Z) (ofNat n')) Z) Z) Z

theorem OT_imp_NF1 (lam : Nat) (s : new.T lam) : new.T.isOT lam s → T.isSubNF lam (trans s) := by
  intro hs
  have hnf := (new.T.OT_iff_NF lam s).mp hs
  constructor
  · exact NF_is_NF1 lam s hnf.1
  · cases lam with
    | zero =>
        cases s with
        | Z => exact T.Lt.Z_lt_P 0 _ T.Z
        | P v add =>
            cases v with
            | nil =>
                change T.P 0 T.Z (trans add) < T.P 0 (T.P 0 T.Z T.Z) T.Z
                exact T.Lt.p_mid 0 _ _ _ _ (T.Lt.Z_lt_P 0 T.Z T.Z)
    | succ k =>
        cases s with
        | Z =>
            cases k with
            | zero => exact T.Lt.Z_lt_P 0 _ T.Z
            | succ k => exact T.Lt.Z_lt_P 0 _ T.Z
        | P v add =>
            let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
            have hv : v = ot_v0 k (v.idx i0) := by
              apply ot_vec_ext
              intro i
              unfold ot_v0
              rw [new.Vec.ofFn_idx]
              apply Decidable.byCases (p := i.val = 0)
              · intro hi
                rw [ite_eq_left hi]
                have heq : i = i0 := Fin.eq_of_val_eq hi
                rw [heq]
              · intro hi
                rw [ite_eq_right hi]
                cases k with
                | zero =>
                    exact False.elim (hi (Nat.eq_zero_of_le_zero
                      (Nat.le_of_lt_succ i.isLt)))
                | succ k =>
                    have hk : 1 < k + 1 + 1 :=
                      Nat.succ_lt_succ (Nat.zero_lt_succ k)
                    exact ot_bound_coords_zero hk v add hnf.1 (hnf.2 hk)
                      i (Nat.pos_of_ne_zero hi)
            have ha := new.T.isNF_P_coord_NFComp v add hnf.1 i0
            have hb := ot_trans_global_bound (v.idx i0) ha.1 (Nat.zero_lt_succ k)
            have htrans : trans (new.T.P v add) = T.P 0 (trans (v.idx i0)) (trans add) := by
              have hh := ot_trans_v0 k (v.idx i0) add
              rw [← hv] at hh
              exact hh
            rw [htrans]
            cases k with
            | zero => exact T.Lt.p_mid 0 _ _ _ _ hb
            | succ k => exact T.Lt.p_mid 0 _ _ _ _ hb

#print axioms OT_imp_NF1

theorem exists_OT_of_SubNF_zero (t : T) (ht : T.isSubNF 0 t) :
    ∃ s, new.T.isOT 0 s ∧ trans s = t := by
  cases StopSurjLow.surj_SubNF0_raw t ht.1 ht.2 with
  | intro s hs =>
      refine ⟨s, ?_, hs.2⟩
      apply (new.T.OT_iff_NF 0 s).mpr
      refine ⟨hs.1, ?_⟩
      intro h
      exact False.elim (Nat.not_lt_zero 1 h)

theorem exists_OT_of_SubNF_one (t : T) (ht : T.isSubNF 1 t) :
    ∃ s, new.T.isOT 1 s ∧ trans s = t := by
  cases (StopSurjLow.surj1_pair t ht.1).1 ht.2 with
  | intro s hs =>
      refine ⟨s, ?_, hs.2⟩
      apply (new.T.OT_iff_NF 1 s).mpr
      refine ⟨hs.1, ?_⟩
      intro h
      exact False.elim (Nat.lt_irrefl 1 h)

#print axioms exists_OT_of_SubNF_zero
#print axioms exists_OT_of_SubNF_one

theorem ot_bound_NF (lam : Nat) : new.T.isNF (ot_bound lam) := by
  apply new.T.isNF_PZ_of_coords
  intro i
  rw [new.Vec.ofFn_idx]
  apply Decidable.byCases (p := i.val = 1)
  · intro hi
    rw [ite_eq_left hi]
    exact ot_new_ofNat_NFComp 1
  · intro hi
    rw [ite_eq_right hi]
    exact new.T.isNFComp_Z

theorem transAux_ot_bound {lam : Nat} (k : Nat) (u : new.T lam)
    (hu : trans u = T.P 0 T.Z T.Z) :
    transAux (new.Vec.ofFn (k + 2) (fun i => if i.val = 1 then u else new.T.Z)) =
      (true, T.P 0 T.Z T.Z, T.Z) := by
  induction k with
  | zero =>
      change transAux (new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil new.T.Z) u) = _
      rw [transAux.eq_3, transAux.eq_2]
      cases u with
      | Z => cases hu
      | P v a => rw [hu]; rfl
  | succ k ih =>
      rw [new.Vec.ofFn]
      have hlast : (Fin.last (k + 2)).val ≠ 1 :=
        Nat.ne_of_gt (Nat.succ_lt_succ (Nat.zero_lt_succ k))
      rw [ite_eq_right hlast]
      change transAux (new.Vec.snoc (k + 2)
        (new.Vec.ofFn (k + 2) (fun i => if i.val = 1 then u else new.T.Z)) new.T.Z) = _
      rw [transAux.eq_3, ih]
      change (true, T.add (T.card_times (k + 1) T.Z) (T.P 0 T.Z T.Z), T.Z) = _
      rw [T.card_times.eq_1, T.add.eq_1]

theorem trans_ot_bound (k : Nat) : trans (ot_bound (k + 2)) = T.P 1 T.Z T.Z := by
  unfold ot_bound
  rw [_root_.trans.eq_2, transAux_ot_bound k (ot_unit (k + 2))
    (StopSurjPrincipal.trans_one (k + 2))]
  rfl

theorem exists_OT_of_SubNF_succ_succ (k : Nat) (t : T)
    (ht : T.isSubNF (k + 2) t) :
    ∃ s, new.T.isOT (k + 2) s ∧ trans s = t := by
  have hsmall : StopSurjCard.Small (ot_trans_bound (k + 2)) t ∧ t < T.P 1 T.Z T.Z := by
    cases t with
    | Z =>
        refine ⟨⟨T.Lt.Z_lt_P 1 _ T.Z, ?_⟩, T.Lt.Z_lt_P 1 T.Z T.Z⟩
        intro y hy
        cases hy
    | P p a b =>
        have hb : T.P p a b < T.P 0 (ot_trans_bound (k + 2)) T.Z := ht.2
        have hshape : p = 0 ∧ a < ot_trans_bound (k + 2) := by
          cases lt_inv p a b 0 (ot_trans_bound (k + 2)) T.Z hb with
          | inl hp => exact False.elim (Nat.not_lt_zero p hp)
          | inr hr =>
              cases hr with
              | inl hm => exact hm
              | inr htail => exact False.elim (lt_Z_inv htail.2.2)
        have hp0 := hshape.1
        cases hp0
        refine ⟨⟨T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0), ?_⟩,
          T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)⟩
        intro y hy
        have hya := StopUncollapse.support_le_of_head (T.P 0 a b) a ht.1 (Or.inr rfl) y hy
        exact lt_of_le_of_lt_thm T _ _ _ hya hshape.2
  cases StopSurjGeneral.exists_preimage k t ht.1 hsmall.1 with
  | intro s hs =>
      have hsb : s < ot_bound (k + 2) := by
        apply (order_embeding (k + 2) s (ot_bound (k + 2)) hs.1 (ot_bound_NF (k + 2))).mpr
        rw [hs.2.1, trans_ot_bound]
        exact hsmall.2
      refine ⟨s, ?_, hs.2.1⟩
      exact (new.T.OT_iff_NF (k + 2) s).mpr ⟨hs.1, fun _ => hsb⟩

#print axioms exists_OT_of_SubNF_succ_succ

theorem exists_OT_of_SubNF (lam : Nat) (t : T)
    (ht : T.isSubNF lam t) :
    ∃ s, new.T.isOT lam s ∧ trans s = t := by
  cases lam with
  | zero => exact exists_OT_of_SubNF_zero t ht
  | succ k =>
      cases k with
      | zero => exact exists_OT_of_SubNF_one t ht
      | succ k => exact exists_OT_of_SubNF_succ_succ k t ht

#print axioms exists_OT_of_SubNF

theorem trans_injective_OT (lam : Nat) (s t : new.T lam)
    (hs : new.T.isOT lam s)
    (ht : new.T.isOT lam t)
    (h : trans s = trans t) :
    s = t := by
  exact trans_injective_on_NF s t
    ((new.T.OT_iff_NF lam s).mp hs).1
    ((new.T.OT_iff_NF lam t).mp ht).1 h

#print axioms trans_injective_OT

def T.SubNF (lam : Nat) := { t : T // isSubNF lam t }

/-- The translation restricted to the two systems of ordinal notations. -/
def trans_OT (lam : Nat) (s : new.T.OT lam) : T.SubNF lam :=
  ⟨trans s.val, OT_imp_NF1 lam s.val s.property⟩

theorem trans_OT_injective (lam : Nat) (s t : new.T.OT lam)
    (h : trans_OT lam s = trans_OT lam t) : s = t := by
  apply Subtype.ext
  exact trans_injective_OT lam s.val t.val s.property t.property
    (congrArg Subtype.val h)

theorem trans_OT_surjective (lam : Nat) (t : T.SubNF lam) :
    ∃ s : new.T.OT lam, trans_OT lam s = t := by
  cases exists_OT_of_SubNF lam t.val t.property with
  | intro s hs =>
      refine ⟨⟨s, hs.1⟩, ?_⟩
      apply Subtype.ext
      exact hs.2

theorem trans_OT_lt_iff (lam : Nat) (s t : new.T.OT lam) :
    s.val < t.val ↔ (trans_OT lam s).val < (trans_OT lam t).val := by
  exact order_embeding lam s.val t.val
    ((new.T.OT_iff_NF lam s.val).mp s.property).1
    ((new.T.OT_iff_NF lam t.val).mp t.property).1

theorem trans_OT_le_iff (lam : Nat) (s t : new.T.OT lam) :
    s.val ≤ t.val ↔ (trans_OT lam s).val ≤ (trans_OT lam t).val := by
  constructor
  · intro h
    cases h with
    | inl hlt => exact Or.inl ((trans_OT_lt_iff lam s t).mp hlt)
    | inr heq => exact Or.inr (congrArg trans (new.T_eq_sound s.val t.val heq))
  · intro h
    cases h with
    | inl hlt => exact Or.inl ((trans_OT_lt_iff lam s t).mpr hlt)
    | inr heq =>
        have hst := trans_injective_OT lam s.val t.val s.property t.property heq
        rw [hst]
        exact Or.inr (new.T_refl t.val)

theorem OT_SubNF_order_iso (lam : Nat) :
    ∃ f : new.T.OT lam → T.SubNF lam,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  exact ⟨trans_OT lam, trans_OT_injective lam,
    trans_OT_surjective lam, trans_OT_lt_iff lam⟩

#print axioms OT_SubNF_order_iso

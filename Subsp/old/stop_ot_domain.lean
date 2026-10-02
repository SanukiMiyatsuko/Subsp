import Subsp.old.stop_ot_shape

/-! Domain correspondence for legacy OT-shaped source terms. -/

namespace LegacyTranslation

theorem target_dom1_add_right (a b : T) (hb : b ≠ T.Z) :
    T.dom1 (T.add a b) = T.dom1 b := by
  induction a with
  | Z => rfl
  | P p x y ihx ihy =>
      rw [T.P_add_eq]
      have htail : T.add y b ≠ T.Z := by
        cases y <;> cases b <;> simp_all [T.add]
      simp [T.dom1, htail, ihy]

theorem target_dom1_P0_ne_zero (a : T) (ha : a ≠ T.Z) :
    T.dom1 (T.P 0 a T.Z) = .ω := by
  cases hd : T.dom1 a with
  | Zero => exact False.elim (ha (dom1_Zero_imp_eq_Z a hd))
  | One => simp [T.dom1, hd]
  | ω => simp [T.dom1, hd]
  | Ω l => simp [T.dom1, hd]

end LegacyTranslation

namespace new

theorem T.outerChain_dom1_trans {lam : Nat}
    (s : T lam) (hs : T.outerChain s) :
    match T.dom s with
    | .zero => _root_.T.dom1 (_root_.trans s) = .Zero
    | .one => _root_.T.dom1 (_root_.trans s) = .One
    | .omega => _root_.T.dom1 (_root_.trans s) = .ω
    | .Omega _ => False := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z => rfl
      | P ls add =>
          have hls : Vec.outer0 ls := hs.1
          have ha : T.outerChain add := hs.2
          by_cases hadd : add = T.Z
          · subst add
            cases lam with
            | zero =>
                cases ls
                rfl
            | succ k =>
                let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
                have hcount :
                    ∀ i : Fin (k + 1), 0 < i.val → ls.idx i = T.Z := by
                  intro i hi
                  exact hls i (Nat.ne_of_gt hi)
                have htr := LegacyTranslation.trans_countable_P ls T.Z hcount
                cases hmin : T.domVecMinIdx ls with
                | none =>
                    have hzdom := T.domVecMinIdx_none_all_zero ls hmin
                    have hz : ls.idx i0 = T.Z := T.dom_zero_eq_Z _ (hzdom i0)
                    have hshape :
                        _root_.trans (T.P ls T.Z) =
                          _root_.T.P 0 _root_.T.Z _root_.T.Z := by
                      rw [htr, hz, _root_.trans]
                    rw [T.dom, ite_eq_left rfl, hmin, hshape]
                    rfl
                | some md =>
                    obtain ⟨m, d⟩ := md
                    have hm0 := Vec.outer0_min_index_zero ls hls m d hmin
                    have hm : m = i0 := Fin.eq_of_val_eq hm0
                    have hspec := T.domVecMinIdx_some_spec ls m d hmin
                    have hne0 : ls.idx i0 ≠ T.Z := by
                      rw [← hm]
                      intro hz
                      have hd := hspec.2.1
                      rw [hz] at hd
                      exact hspec.1 hd.symm
                    have htrne : _root_.trans (ls.idx i0) ≠ _root_.T.Z :=
                      LegacyTranslation.trans_ne_zero_of_ne_zero _ hne0
                    have hshape :
                        _root_.trans (T.P ls T.Z) =
                          _root_.T.P 0 (_root_.trans (ls.idx i0)) _root_.T.Z := by
                      dsimp [i0]
                      simpa [_root_.trans] using htr
                    have htarget :
                        _root_.T.dom1 (_root_.trans (T.P ls T.Z)) = .ω := by
                      rw [hshape]
                      exact LegacyTranslation.target_dom1_P0_ne_zero _ htrne
                    rw [T.dom, ite_eq_left rfl, hmin]
                    cases d with
                    | zero => exact False.elim (hspec.1 rfl)
                    | one =>
                        simp only [hm0, ite_true]
                        exact htarget
                    | omega => exact htarget
                    | Omega i =>
                        have hnot : ¬ i ≤ m :=
                          T.outer0_Omega_not_le ls hls m i hmin
                        simp only [hnot, ite_false]
                        exact htarget
          · have hta : _root_.trans add ≠ _root_.T.Z :=
              LegacyTranslation.trans_ne_zero_of_ne_zero add hadd
            have hdomEq :
                _root_.T.dom1 (_root_.trans (T.P ls add)) =
                  _root_.T.dom1 (_root_.trans add) := by
              rw [LegacyTranslation.trans_as_add]
              exact LegacyTranslation.target_dom1_add_right
                (transAux ls).1 (_root_.trans add) hta
            rw [T.dom, ite_eq_right hadd, hdomEq]
            exact ih add (T.add_size_lt_P ls add) ha

theorem T.isOT_dom1_trans {lam : Nat} {s : T lam}
    (hs : T.isOT lam s) :
    match T.dom s with
    | .zero => _root_.T.dom1 (_root_.trans s) = .Zero
    | .one => _root_.T.dom1 (_root_.trans s) = .One
    | .omega => _root_.T.dom1 (_root_.trans s) = .ω
    | .Omega _ => False :=
  T.outerChain_dom1_trans s (T.isOT_outerChain hs)

end new


namespace LegacyTranslation

theorem OT_lt_rank1_limit {lam : Nat} (s : new.T lam)
    (hs : new.T.isOT lam s) :
    trans s < T.P 1 T.Z T.Z := by
  exact lt_trans_thm _ _ _ (OT_bound lam s hs)
    (T.Lt.p_head 0 1 (T.P lam T.Z T.Z) T.Z T.Z T.Z (Nat.zero_lt_succ 0))

theorem OT_dom1_not_Omega {lam : Nat} (s : new.T lam)
    (hs : new.T.isOT lam s) (l : Nat) :
    T.dom1 (trans s) ≠ .Ω l := by
  intro hdom
  cases hsdom : new.T.dom s with
  | zero =>
      have h := new.T.isOT_dom1_trans hs
      rw [hsdom] at h
      rw [h] at hdom
      cases hdom
  | one =>
      have h := new.T.isOT_dom1_trans hs
      rw [hsdom] at h
      rw [h] at hdom
      cases hdom
  | omega =>
      have h := new.T.isOT_dom1_trans hs
      rw [hsdom] at h
      rw [h] at hdom
      cases hdom
  | Omega i =>
      exact new.T.isOT_dom_not_Omega lam s hs i hsdom

end LegacyTranslation


namespace LegacyTranslation

theorem SubNF_lt_rank1_limit (lam : Nat) (t : T.SubNF lam) :
    t.val < T.P 1 T.Z T.Z := by
  exact lt_trans_thm _ _ _ t.property.2
    (T.Lt.p_head 0 1 (T.P lam T.Z T.Z) T.Z T.Z T.Z
      (Nat.zero_lt_succ 0))

theorem SubNF_isOT1 (lam : Nat) (t : T.SubNF lam) :
    T.isOT1 t.val := by
  exact (T.isOT1_iff_isNF1 t.val).2
    ⟨t.property.1, SubNF_lt_rank1_limit lam t⟩

theorem SubNF_fund1_closed (lam : Nat) (t : T.SubNF lam) (z : T)
    (hz : T.isNF1 z) (hv : T.ValidArg1 t.val z) :
    T.isSubNF lam (T.fund1 t.val z) := by
  exact ⟨T.fund1_NF1_closed t.val z t.property.1 hz hv,
    lt_trans_thm _ _ _ (T.fund1_fall t.val z hv) t.property.2⟩

end LegacyTranslation



namespace LegacyTranslation

def sourceUnit (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z

theorem trans_sourceUnit (lam : Nat) :
    trans (sourceUnit lam) = T.P 0 T.Z T.Z := by
  unfold sourceUnit
  rw [trans_as_add, transAux_zeros]
  rfl

theorem transAux_otBound {lam : Nat} (k : Nat) (u : new.T lam)
    (hu : trans u = T.P 0 T.Z T.Z) :
    transAux
      (new.Vec.ofFn (k + 2)
        (fun i => if i.val = 1 then u else new.T.Z)) =
      (T.P 1 T.Z T.Z, T.P 1 T.Z T.Z) := by
  induction k with
  | zero =>
      change transAux
        (new.Vec.snoc 1
          (new.Vec.snoc 0 new.Vec.nil new.T.Z) u) = _
      cases u with
      | Z => cases hu
      | P ls add =>
          simp [transAux, hu, _root_.trans.eq_1, T.early_collapse,
            T.part, T.card_times, T.one_del]
          constructor <;> rfl
  | succ k ih =>
      rw [new.Vec.ofFn]
      simp only [Fin.val_last, Fin.val_castSucc,
        show k + 2 ≠ 1 by omega, ite_false]
      rw [transAux_snoc_zero]
      exact ih

theorem trans_otBound (k : Nat) :
    trans (new.T.otBound (k + 2)) = T.P 1 T.Z T.Z := by
  change trans
    (new.T.P
      (new.Vec.ofFn (k + 2)
        (fun i => if i.val = 1 then sourceUnit (k + 2) else new.T.Z))
      new.T.Z) = _
  rw [trans_as_add,
    transAux_otBound k (sourceUnit (k + 2)) (trans_sourceUnit (k + 2))]
  rfl

end LegacyTranslation

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

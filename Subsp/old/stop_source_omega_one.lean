import Subsp.old.stop_source_lower_level

/-! The positive one-domain branch of indexed uncountable fundamental sequences. -/

namespace new

theorem T.fund_PZ_one_pos_NFComp {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam) (m : Fin lam) (z : T lam)
    (hmin : T.domVecMinIdx ls = some (m, .one))
    (hm : 0 < m.val) (hmu : m.val ≤ u)
    (hs : T.isNFComp u (T.P ls T.Z))
    (hz : T.isNFComp 0 z) :
    T.isNFComp u (T.fund (T.P ls T.Z) z) := by
  have hspec := T.domVecMinIdx_some_spec ls m (.one : Dom lam) hmin
  have hc : T.isNFComp m.val (ls.idx m) :=
    T.isNFComp_coord_at_index ls T.Z hs.1 m
  have hb : T.isNFComp m.val (T.fund (ls.idx m) T.Z) :=
    T.fund_one_NFComp_closed m.val (ls.idx m) hc hspec.2.1
  have hbaseNF :
      T.isNF (T.P (ls.rplc m (T.fund (ls.idx m) T.Z)) T.Z) :=
    T.rplc_NF_closed ls m _ hs.1 hb
  have hbaseSDom :
      T.SDom T.Z
        (T.P (ls.rplc m (T.fund (ls.idx m) T.Z)) T.Z)
        (T.P ls T.Z) :=
    T.SDom_rplc_min T.Z ls m .one _ hmin
      (T.fund_one_SDom (ls.idx m) hspec.2.1)
  have hbaseComp :
      T.isNFComp u
        (T.P (ls.rplc m (T.fund (ls.idx m) T.Z)) T.Z) :=
    T.NFComp_of_SDom_zero u _ _ hbaseNF hs hbaseSDom
  obtain ⟨mv, mh⟩ := m
  cases mv with
  | zero => omega
  | succ r =>
      let j : Fin lam := ⟨r, Nat.lt_of_succ_lt mh⟩
      have hzj : T.isNFComp j.val z :=
        T.isNFComp_mono 0 j.val (Nat.zero_le _) z hz
      have hfinalNF :
          T.isNF
            (T.P
              ((ls.rplc ⟨r + 1, mh⟩
                  (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z)).rplc j z)
              T.Z) :=
        T.rplc_NF_closed
          (ls.rplc ⟨r + 1, mh⟩
            (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z))
          j z hbaseNF hzj
      have hfinalComp :
          T.isNFComp u
            (T.P
              ((ls.rplc ⟨r + 1, mh⟩
                  (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z)).rplc j z)
              T.Z) :=
        T.isNFComp_rplc_lower u
          (ls.rplc ⟨r + 1, mh⟩
            (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z))
          j z (by dsimp [j]; omega) hbaseComp hfinalNF
      rw [T.fund, ite_eq_left rfl, hmin]
      exact hfinalComp

end new

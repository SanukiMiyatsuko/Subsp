import Subsp.old.stop_source_omega_one

/-! Assembly of the nested indexed-Omega principal branch. -/

namespace new

theorem T.fund_PZ_Omega_le_master_of_inner {lam : Nat}
    (ls : Vec (T lam) lam) (m j : Fin lam) (z : T lam)
    (hmin : T.domVecMinIdx ls = some (m, .Omega j))
    (hjm : j ≤ m)
    (hs : T.isNF (T.P ls T.Z))
    (hcomp : T.isNFComp m.val (T.fund (ls.idx m) z))
    (hsd : T.SDom z (T.fund (ls.idx m) z) (ls.idx m)) :
    T.isNF (T.fund (T.P ls T.Z) z) ∧
      T.SDom z (T.fund (T.P ls T.Z) z) (T.P ls T.Z) := by
  simp only [T.fund, hmin, hjm, ite_true]
  exact ⟨T.rplc_NF_closed ls m _ hs hcomp,
    T.SDom_rplc_min z ls m (.Omega j) _ hmin hsd⟩

end new

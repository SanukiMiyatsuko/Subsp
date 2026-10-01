import Subsp.old.stop_source_omega_master

/-! Closure of indexed legacy normal forms under countable fundamental sequences. -/

namespace new

theorem T.fund_iter_NFComp {lam : Nat} (u : Nat) (s t : T lam) (i : Fin lam)
    (hui : u < i.val) (hs : T.isNFComp u s) (hd : T.dom s = .Omega i) :
    T.isNFComp u (T.fund s (T.iter (T.fund s) t)) ∧
      T.WDom T.Z (T.fund s (T.iter (T.fund s) t)) s := by
  have step (r : T lam) (hr : T.isNFComp u (T.iter (T.fund s) r))
      (hw : T.WDom T.Z (T.iter (T.fund s) r) s) :
      T.isNFComp u (T.fund s (T.iter (T.fund s) r)) ∧
        T.WDom T.Z (T.fund s (T.iter (T.fund s) r)) s := by
    obtain ⟨hnf, hwd, _⟩ := T.fund_Omega_master s hs.1 i _ hd
      (T.isNFComp_mono u (i.val - 1) (by omega) _ hr)
    have hlt := T.iter_fund_lt_next s r i hd
    exact ⟨T.NFComp_of_IDom u _ _ s hnf hs hr (hwd u) hlt,
      fun v => T.IDom_eliminate v _ _ s (hwd v) (hw v) hlt⟩
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      apply step T.Z (T.isNFComp_Z u)
      intro v
      apply T.IDom_zero
      cases s with
      | Z => cases hd
      | P ls add => rfl
  | P ls add _ ih => exact step (T.P ls add) ih.1 ih.2
  | nil => trivial
  | snoc => trivial

theorem T.fund_omega_master {lam : Nat} (s : T lam) (hs : T.isNF s) :
    T.dom s = .omega → ∀ t : T lam,
      T.isNF (T.fund s t) ∧ T.WDom T.Z (T.fund s t) s := by
  induction hs with
  | z => intro hd; cases hd
  | p ls add hcoords haddNF hsupport hhead ihls ihadd =>
      intro hd t
      by_cases hadd : add = T.Z
      · subst add
        have hp := T.isNF.p ls T.Z hcoords haddNF hsupport hhead
        obtain ⟨m, d, hmin, hcase⟩ := T.dom_PZ_omega_split ls hd
        have hspec := T.domVecMinIdx_some_spec ls m d hmin
        have hc := (T.isNF_P_inv ls T.Z hp).1 m
        rcases hcase with ⟨rfl, hm0⟩ | rfl | ⟨j, rfl, hjm⟩
        · have hpred := T.fund_one_NFComp_closed m.val (ls.idx m) hc hspec.2.1
          have hbNF := T.rplc_NF_closed ls m _ hp hpred
          have hbSD := T.SDom_rplc_min T.Z ls m .one _ hmin
            (T.fund_one_SDom (ls.idx m) hspec.2.1)
          obtain ⟨mv, mh⟩ := m
          change mv = 0 at hm0
          subst mv
          rw [T.fund, ite_eq_left rfl, hmin]
          refine ⟨T.mul_PZ_NF_closed _ hbNF t, ?_⟩
          intro u
          apply T.SDom_IDom
          apply T.SDom_mul_PZ _ _ t _ hbSD
          exact Vec.compare_rplc_lt _ _ _ (T.fund_one_SDom _ hspec.2.1).1
        · obtain ⟨hnf, hwd⟩ := ihls m hspec.2.1 t
          have hcomp := T.NFComp_of_IDom_zero m.val _ _ hnf hc (hwd m.val)
          rw [T.fund, ite_eq_left rfl, hmin]
          exact ⟨T.rplc_NF_closed ls m _ hp hcomp,
            fun u => T.IDom_rplc_min u T.Z ls m .omega _ hmin (hwd u).1 (fun _ => hwd u)⟩
        · have hmj : m.val < j.val := Nat.lt_of_not_ge hjm
          obtain ⟨hcomp, hwd⟩ := T.fund_iter_NFComp m.val (ls.idx m) t j hmj hc hspec.2.1
          simp only [T.fund, hmin, hjm, ite_false, ite_true]
          exact ⟨T.rplc_NF_closed ls m _ hp hcomp,
            fun u => T.IDom_rplc_min u T.Z ls m (.Omega j) _ hmin (hwd u).1 (fun _ => hwd u)⟩
      · obtain ⟨hnf, hwd⟩ := ihadd (by simpa [T.dom, hadd] using hd) t
        have hf := T.isNF.p ls _ hcoords hnf hsupport
          (T.le_trans _ _ _ (T.head_fund_le add t) hhead)
        rw [T.fund_P_tail_eq ls add t hadd]
        exact ⟨hf, fun u => T.IDom_tail u T.Z _ add ls (T.NF_tail_lt _ _ hf) (hwd u)⟩

theorem T.fund_omega_NFComp_closed {lam : Nat} (u : Nat) (s t : T lam)
    (hs : T.isNFComp u s) (hd : T.dom s = .omega) : T.isNFComp u (T.fund s t) := by
  obtain ⟨hnf, hwd⟩ := T.fund_omega_master s hs.1 hd t
  exact T.NFComp_of_IDom_zero u _ s hnf hs (hwd u)

theorem T.fund_NF_closed {lam : Nat} (s t : T lam)
    (hs : T.isNF s) (ht : T.isNFComp 0 t) : T.isNF (T.fund s t) := by
  cases hd : T.dom s with
  | zero => rw [T.dom_zero_eq_Z s hd, T.fund]; exact .z
  | one => rw [T.fund_one_arg_irrel s t hd]; exact T.fund_one_NF s hs hd
  | omega => exact (T.fund_omega_master s hs hd t).1
  | Omega i => exact (T.fund_Omega_master s hs i t hd
      (T.isNFComp_mono 0 (i.val - 1) (Nat.zero_le _) t ht)).1

theorem T.isOT_isNF {lam : Nat} (s : T lam) (hs : T.isOT lam s) : T.isNF s := by
  induction hs with
  | base_0 n => exact T.LF_isNF 0 n
  | base_succ k n => exact T.base_succ_isNF k n
  | step lam s _ n ih => exact T.fund_NF_closed s (T.ofNat n) ih (T.ofNat_isNFComp 0 n)

end new

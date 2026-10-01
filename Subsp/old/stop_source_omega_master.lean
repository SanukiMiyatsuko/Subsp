import Subsp.old.stop_source_interpolation_lift

/-! Indexed uncountable fundamental sequences preserve normal forms and support intervals. -/

namespace new

theorem T.fund_PZ_one_pos_master {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam) (z : T lam)
    (hmin : T.domVecMinIdx ls = some (m, .one)) (hm : 0 < m.val)
    (hs : T.isNF (T.P ls T.Z)) (hz : T.isNFComp (m.val - 1) z) :
    T.isNF (T.fund (T.P ls T.Z) z) ∧
      T.WDom z (T.fund (T.P ls T.Z) z) (T.P ls T.Z) ∧
      ∀ u, m.val ≤ u → T.IDom u T.Z (T.fund (T.P ls T.Z) z) (T.P ls T.Z) := by
  have hspec := T.domVecMinIdx_some_spec ls m .one hmin
  have hc := T.fund_one_NFComp_closed m.val (ls.idx m)
    ((T.isNF_P_inv ls T.Z hs).1 m) hspec.2.1
  have hbNF := T.rplc_NF_closed ls m _ hs hc
  have hbSD := T.SDom_rplc_min T.Z ls m .one _ hmin
    (T.fund_one_SDom (ls.idx m) hspec.2.1)
  cases m with
  | mk mv mh =>
    cases mv with
    | zero => simp at hm
    | succ r =>
      let j : Fin lam := ⟨r, Nat.lt_of_succ_lt mh⟩
      have hzj : T.isNFComp j.val z := hz
      have hjm : j.val < (⟨r + 1, mh⟩ : Fin lam).val := Nat.lt_succ_self r
      have hfNF := T.rplc_NF_closed _ j z hbNF hzj
      have hfSD := T.SDom_rplc_lower z ls ⟨r + 1, mh⟩ j .one _ hjm hmin
        (T.fund_one_SDom (ls.idx ⟨r + 1, mh⟩) hspec.2.1)
      have hjzero : (ls.rplc ⟨r + 1, mh⟩ (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z)).idx j = T.Z := by
        rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hjm)]
        exact T.dom_zero_eq_Z _ (hspec.2.2 j hjm)
      rw [T.fund, ite_eq_left rfl, hmin]
      refine ⟨hfNF, (fun u => T.SDom_IDom u _ _ _ hfSD), ?_⟩
      intro u hmu
      refine ⟨hfSD.1, ?_⟩
      intro c hl hh x hx
      have hju : j.val < u := Nat.lt_of_lt_of_le hjm hmu
      have hxb := (T.mem_Gi_PZ_rplc_lower_iff u _ j z x hju).mp hx
      exact Or.inr (hbSD.2 u c
        (T.le_trans _ _ _ (T.PZ_le_rplc_zero _ j z hjzero) hl) hh x hxb)

theorem T.fund_Omega_master {lam : Nat} (s : T lam) (hs : T.isNF s) :
    ∀ (i : Fin lam) (z : T lam), T.dom s = .Omega i → T.isNFComp (i.val - 1) z →
      T.isNF (T.fund s z) ∧ T.WDom z (T.fund s z) s ∧
      ∀ u, i.val ≤ u → T.IDom u T.Z (T.fund s z) s := by
  induction hs with
  | z => intro i z hd _; cases hd
  | p ls add hcoords haddNF hsupport hhead ihls ihadd =>
      intro i z hd hz
      by_cases hadd : add = T.Z
      · subst add
        have hparent := T.isNF.p ls T.Z hcoords haddNF hsupport hhead
        obtain ⟨m, d, hmin, hcase⟩ := T.dom_PZ_Omega_split ls i hd
        rcases hcase with ⟨rfl, hm, rfl⟩ | ⟨j, rfl, hjm, rfl⟩
        · exact T.fund_PZ_one_pos_master ls i z hmin hm hparent hz
        · have hspec := T.domVecMinIdx_some_spec ls m (.Omega i) hmin
          obtain ⟨hnf, hwd, hhigh⟩ := ihls m i z hspec.2.1 hz
          have hcomp := T.NFComp_of_IDom_zero m.val _ _ hnf
            ((T.isNF_P_inv ls T.Z hparent).1 m) (hhigh m.val hjm)
          simp only [T.fund, hmin, hjm, ite_true]
          refine ⟨T.rplc_NF_closed ls m _ hparent hcomp, ?_, ?_⟩
          · intro u
            exact T.IDom_rplc_min u z ls m (.Omega i) _ hmin (hwd u).1 (fun _ => hwd u)
          · intro u hju
            exact T.IDom_rplc_min u T.Z ls m (.Omega i) _ hmin (hwd u).1
              (fun _ => hhigh u hju)
      · obtain ⟨hnf, hwd, hhigh⟩ := ihadd i z (by simpa [T.dom, hadd] using hd) hz
        have hf := T.isNF.p ls _ hcoords hnf hsupport
          (T.le_trans _ _ _ (T.head_fund_le add z) hhead)
        rw [T.fund_P_tail_eq ls add z hadd]
        exact ⟨hf, (fun u => T.IDom_tail u z _ add ls (T.NF_tail_lt _ _ hf) (hwd u)),
          fun u hu => T.IDom_tail u T.Z _ add ls (T.NF_tail_lt _ _ hf) (hhigh u hu)⟩

end new

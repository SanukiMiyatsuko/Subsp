import Subsp.old.stop_surj
import Subsp.old.stop_source_ot_bound
import Subsp.old.stop_source_domain_split
import Subsp.old.stop_source_successor
import Subsp.old.stop_low_dims

/-! Source cofinality: legacy OT terms are exactly the countable indexed normal forms. -/

namespace LegacyTranslation

open T

/-! Well-foundedness of indexed source normal forms. -/

def NFsrc (lam : Nat) := { s : new.T lam // new.T.isNF s }

theorem wf_NFsrc (lam : Nat) : WellFounded (fun s t : NFsrc lam => s.1 < t.1) := by
  have h := InvImage.wf (fun s : NFsrc lam => (⟨trans s.1, trans_isNF1 s.1 s.2⟩ : T.NF1))
    T.well_founded_NF1
  exact Subrelation.wf (fun {a b} hab => trans_lt_of_lt a.1 b.1 a.2 b.2 hab) h

/-! Successor cofinality. -/

theorem mul_cofinal_src {lam : Nat} (ls : new.Vec (new.T lam) lam) :
    ∀ b : new.T lam, new.T.isNF b → new.T.head b ≤ new.T.P ls new.T.Z →
      ∃ n : Nat, b < new.T.mul (new.T.P ls new.T.Z) (new.T.ofNat n) := by
  intro b hnf
  induction hnf with
  | z => exact fun _ => ⟨1, rfl⟩
  | p ws tail _ _ _ htailHead _ ih =>
      intro hhead
      rcases new.T.vector_rel_of_P_le_P ws ls _ _ hhead with hvec | rfl
      · exact ⟨1, new.T.P_lt_P_of_compareVec_lt _ _ _ _ hvec⟩
      · obtain ⟨n, hn⟩ := ih htailHead
        exact ⟨n + 1, new.T.P_tail_lt _ _ _ hn⟩

theorem head_le_one_base_src {lam : Nat}
    (ls : new.Vec (new.T lam) lam) (m : Fin lam)
    (hmin : new.T.domVecMinIdx ls = some (m, new.Dom.one)) (hm0 : m.val = 0)
    (b : new.T lam) (hba : b < new.T.P ls new.T.Z) :
    new.T.head b ≤ new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z := by
  cases b with
  | Z => exact new.T.Z_le _
  | P ws tail =>
      obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
        (new.T.vector_lt_of_P_lt_PZ ws ls tail hba)
      have hspec := new.T.domVecMinIdx_some_spec ls m _ hmin
      by_cases hqm : q.val = m.val
      · obtain rfl := Fin.eq_of_val_eq hqm
        rcases new.T.fund_one_upper _ hspec.2.1 _ hLt with hlt | heq
        · apply Or.inl
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot _ _ q
          · intro j hj
            rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)]
            exact hAbove j hj
          · rw [new.Vec.rplc_idx_same]; exact hlt
        · have hv : ws = ls.rplc q (new.T.fund (ls.idx q) new.T.Z) := by
            apply new.Vec.ext_idx
            intro j
            by_cases hj : j.val = q.val
            · obtain rfl := Fin.eq_of_val_eq hj
              rw [new.Vec.rplc_idx_same]
              exact new.T_eq_sound _ _ heq
            · rw [new.Vec.rplc_idx_of_ne _ _ _ _ hj]
              exact hAbove j (by omega)
          rw [hv]
          exact new.T.le_refl _
      · apply Or.inl
        apply new.T.P_lt_P_of_compareVec_lt
        apply new.Vec.compare_lt_of_pivot _ _ q
        · intro j hj
          rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by omega)]
          exact hAbove j hj
        · simpa only [new.Vec.rplc_idx_of_ne _ _ _ _ hqm] using hLt

/-! Iterated fundamental sequences at uncountable domains. -/

theorem iter_ofNat_succ_src {lam : Nat} (F : new.T lam → new.T lam) (n : Nat) :
    new.T.iter F (new.T.ofNat (n + 1)) = F (new.T.iter F (new.T.ofNat n)) := by
  rw [new.T.ofNat, new.T.iter]

theorem coord_below_min_Z {lam : Nat} (ls : new.Vec (new.T lam) lam) (m : Fin lam)
    (d : new.Dom lam) (hmin : new.T.domVecMinIdx ls = some (m, d)) (q : Fin lam)
    (hq : q.val < m.val) : ls.idx q = new.T.Z :=
  new.T.dom_zero_eq_Z _ ((new.T.domVecMinIdx_some_spec ls m d hmin).2.2 q hq)

theorem pivot_ge_min {lam : Nat} (ls ws : new.Vec (new.T lam) lam) (m : Fin lam)
    (d : new.Dom lam) (hmin : new.T.domVecMinIdx ls = some (m, d)) (q : Fin lam)
    (hLt : ws.idx q < ls.idx q) : m.val ≤ q.val := by
  apply Nat.le_of_not_gt
  intro h
  rw [coord_below_min_Z ls m d hmin q h] at hLt
  exact new.T.lt_Z_false _ hLt

theorem iteration_cofinal_src {lam : Nat} (a : new.T lam) (ha : new.T.isNF a) (i : Fin lam)
    (hd : new.T.dom a = .Omega i) :
    ∀ b : new.T lam, new.T.isNFComp (i.val - 1) b → b < a →
      ∃ n : Nat, b < new.T.fund a (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
  have hi0 := new.T.dom_Omega_pos a i hd
  intro b
  induction b using (measure new.T.size).wf.induction with
  | h b ih =>
      intro hbcomp hba
      have descend : ∀ cur : new.T lam, new.T.isNF cur → new.T.dom cur = .Omega i →
          ∀ tgt : new.T lam, new.T.isNF tgt → tgt < cur →
          (∀ x ∈ new.T.Gi (i.val - 1) tgt, x ∈ new.T.Gi (i.val - 1) b) →
          ∃ n, tgt < new.T.fund cur
            (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
        intro cur hcur
        induction hcur with
        | z => intro h; cases h
        | p ls add hcoords haddNF hsupport hhead ihls ihadd =>
            intro hcdom tgt htgnf htgc hmem
            by_cases hadd : add = new.T.Z
            · subst add
              obtain ⟨m, d, hmin, hcase⟩ := new.T.dom_PZ_Omega_split ls i hcdom
              have hspec := new.T.domVecMinIdx_some_spec ls m d hmin
              cases tgt with
              | Z =>
                  exact ⟨0, Z_lt_of_ne _ (new.T.fund_Omega_ne_Z _ _ i hcdom)⟩
              | P ws tail =>
                  obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
                    (new.T.vector_lt_of_P_lt_PZ ws ls tail htgc)
                  have hmq := pivot_ge_min ls ws m d hmin q hLt
                  rcases hcase with ⟨hd1, hm0, him⟩ | ⟨j, hdj, hjm, hij⟩
                  · subst hd1
                    obtain ⟨mv, mh⟩ := m
                    cases mv with
                    | zero => exact absurd hm0 (Nat.lt_irrefl 0)
                    | succ r =>
                        have hrl : r < lam := Nat.lt_of_succ_lt mh
                        have he (z : new.T lam) : new.T.fund (new.T.P ls new.T.Z) z =
                            new.T.P ((ls.rplc ⟨r + 1, mh⟩
                              (new.T.fund (ls.idx ⟨r + 1, mh⟩) new.T.Z)).rplc ⟨r, hrl⟩ z) new.T.Z := by
                          rw [new.T.fund, ite_eq_left rfl, hmin]; rfl
                        have habove (z : new.T lam) (j : Fin lam) (hj : r + 1 < j.val) :
                            ((ls.rplc ⟨r + 1, mh⟩ (new.T.fund (ls.idx ⟨r + 1, mh⟩) new.T.Z)).rplc
                              ⟨r, hrl⟩ z).idx j = ls.idx j := by
                          rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by simp; omega)]
                          exact new.Vec.rplc_idx_of_ne _ _ _ _ (by simp; omega)
                        by_cases hqm : q.val = r + 1
                        · have hq : q = ⟨r + 1, mh⟩ := Fin.eq_of_val_eq hqm
                          subst hq
                          rcases new.T.fund_one_upper _ hspec.2.1 _ hLt with hstrict | heq
                          · refine ⟨0, ?_⟩
                            rw [he]
                            apply new.T.P_lt_P_of_compareVec_lt
                            apply new.Vec.compare_lt_of_pivot _ _ ⟨r + 1, mh⟩
                            · intro j hj
                              rw [habove _ j hj]; exact hAbove j hj
                            · rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.succ_ne_self r), new.Vec.rplc_idx_same]
                              exact hstrict
                          · have hir : i.val - 1 = r := by
                              have : i.val = r + 1 := by rw [him]
                              omega
                            have hcMem : ws.idx ⟨r, hrl⟩ ∈ new.T.Gi (i.val - 1) (new.T.P ws tail) :=
                              (new.T.mem_Gi_P _ ws tail _).mpr
                                (Or.inl ⟨⟨r, hrl⟩, by simp [hir], Or.inl rfl⟩)
                            have hbMem := hmem _ hcMem
                            have hcomp : new.T.isNFComp (i.val - 1) (ws.idx ⟨r, hrl⟩) := by
                              rw [hir]
                              exact new.T.isNF_P_coord_NFComp ws tail htgnf ⟨r, hrl⟩
                            obtain ⟨n, hn⟩ := ih (ws.idx ⟨r, hrl⟩)
                              (new.T.Gi_size_lt (i.val - 1) b _ hbMem) hcomp
                              (strict_partial_order.trans _ _ _ (hbcomp.2 _ hbMem) hba)
                            refine ⟨n + 1, ?_⟩
                            rw [he]
                            apply new.T.P_lt_P_of_compareVec_lt
                            apply new.Vec.compare_lt_of_pivot _ _ ⟨r, hrl⟩
                            · intro j hj
                              by_cases hjq : j.val = r + 1
                              · have hj2 : j = ⟨r + 1, mh⟩ := Fin.eq_of_val_eq hjq
                                subst hj2
                                rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.succ_ne_self r), new.Vec.rplc_idx_same]
                                exact new.T_eq_sound _ _ heq
                              · have hj2 : r + 1 < j.val := by simp at hj; omega
                                rw [habove _ j hj2]
                                exact hAbove j hj2
                            · rw [new.Vec.rplc_idx_same, iter_ofNat_succ_src]
                              exact hn
                        · refine ⟨0, ?_⟩
                          have hq2 : r + 1 < q.val := by simp at hmq; omega
                          rw [he]
                          apply new.T.P_lt_P_of_compareVec_lt
                          apply new.Vec.compare_lt_of_pivot _ _ q
                          · intro j hj
                            rw [habove _ j (by omega)]
                            exact hAbove j hj
                          · rw [habove _ q hq2]
                            exact hLt
                  · subst hdj
                    have he (z : new.T lam) : new.T.fund (new.T.P ls new.T.Z) z =
                        new.T.P (ls.rplc m (new.T.fund (ls.idx m) z)) new.T.Z := by
                      rw [new.T.fund, ite_eq_left rfl, hmin]
                      simp only [hjm, ite_true]
                      rfl
                    by_cases hqm : q.val = m.val
                    · obtain rfl := Fin.eq_of_val_eq hqm
                      have hiq : i.val ≤ q.val := by rw [hij]; exact hjm
                      obtain ⟨n, hn⟩ := ihls q (by rw [hspec.2.1, hij]) (ws.idx q)
                        (new.T.isNF_P_coord_NFComp ws tail htgnf q).1 hLt
                        (fun x hx => hmem x ((new.T.mem_Gi_P _ ws tail x).mpr
                          (Or.inl ⟨q, by omega, Or.inr hx⟩)))
                      refine ⟨n, ?_⟩
                      rw [he]
                      apply new.T.P_lt_P_of_compareVec_lt
                      apply new.Vec.compare_lt_of_pivot _ _ q
                      · intro j hj
                        rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)]
                        exact hAbove j hj
                      · rw [new.Vec.rplc_idx_same]; exact hn
                    · refine ⟨0, ?_⟩
                      rw [he]
                      apply new.T.P_lt_P_of_compareVec_lt
                      apply new.Vec.compare_lt_of_pivot _ _ q
                      · intro j hj
                        rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by omega)]
                        exact hAbove j hj
                      · rw [new.Vec.rplc_idx_of_ne _ _ _ _ hqm]; exact hLt
            · have hdadd : new.T.dom add = .Omega i := by
                simpa only [new.T.dom, hadd, ite_false] using hcdom
              cases tgt with
              | Z => exact ⟨0, by rw [new.T.fund_P_tail_eq _ _ _ hadd]; rfl⟩
              | P ws tail =>
                  change (match new.compareVec ws ls with
                    | .eq => new.compareT tail add | ord => ord) = .lt at htgc
                  cases hc : new.compareVec ws ls with
                  | lt =>
                      refine ⟨0, ?_⟩
                      rw [new.T.fund_P_tail_eq _ _ _ hadd]
                      exact new.T.P_lt_P_of_compareVec_lt _ _ _ _ hc
                  | gt => simp [hc] at htgc
                  | eq =>
                      rw [hc] at htgc
                      obtain rfl := new.Vec_eq_sound ws ls hc
                      obtain ⟨_, htl, _⟩ := new.T.isNF_P_inv ws tail htgnf
                      obtain ⟨n, hn⟩ := ihadd hdadd tail htl htgc
                        (fun x hx => hmem x ((new.T.mem_Gi_P _ ws tail x).mpr (Or.inr hx)))
                      exact ⟨n, by rw [new.T.fund_P_tail_eq _ _ _ hadd]; exact new.T.P_tail_lt _ _ _ hn⟩
      exact descend a ha hd b hbcomp.1 hba (fun _ hx => hx)

/-! Cofinality at countable limits. -/

theorem fund_omega_cofinal_src {lam : Nat} : ∀ a : new.T lam, new.T.isNF a →
    new.T.dom a = .omega →
    ∀ b : new.T lam, new.T.isNF b → b < a → ∃ n : Nat, b < new.T.fund a (new.T.ofNat n) := by
  intro a ha
  induction ha with
  | z => intro h; cases h
  | p ls add hvNF haddNF hvG hhead ihls ihadd =>
      intro hdom b hb hba
      by_cases hadd : add = new.T.Z
      · subst add
        obtain ⟨m, d, hmin, hcase⟩ := new.T.dom_PZ_omega_split ls hdom
        have hspec := new.T.domVecMinIdx_some_spec ls m d hmin
        have lift (f : Nat → new.T lam)
            (hf : ∀ x, new.T.isNFComp m.val x → x < ls.idx m → ∃ n, x < f n)
            (he : ∀ n, new.T.fund (new.T.P ls new.T.Z) (new.T.ofNat n) =
              new.T.P (ls.rplc m (f n)) new.T.Z) :
            ∃ n, b < new.T.fund (new.T.P ls new.T.Z) (new.T.ofNat n) := by
          cases b with
          | Z => exact ⟨0, by rw [he]; rfl⟩
          | P ws tail =>
              obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
                (new.T.vector_lt_of_P_lt_PZ ws ls tail hba)
              have hmq := pivot_ge_min ls ws m d hmin q hLt
              by_cases hqm : q.val = m.val
              · obtain rfl := Fin.eq_of_val_eq hqm
                obtain ⟨n, hn⟩ := hf _ (new.T.isNF_P_coord_NFComp _ _ hb q) hLt
                refine ⟨n, ?_⟩
                rw [he]
                apply new.T.P_lt_P_of_compareVec_lt
                apply new.Vec.compare_lt_of_pivot _ _ q
                · intro j hj
                  rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)]
                  exact hAbove j hj
                · simpa only [new.Vec.rplc_idx_same] using hn
              · refine ⟨0, ?_⟩
                rw [he]
                apply new.T.P_lt_P_of_compareVec_lt
                apply new.Vec.compare_lt_of_pivot _ _ q
                · intro j hj
                  rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by omega)]
                  exact hAbove j hj
                · simpa only [new.Vec.rplc_idx_of_ne _ _ _ _ hqm] using hLt
        rcases hcase with ⟨hd1, hm0⟩ | hd1 | ⟨j, hdj, hjm⟩
        · subst hd1
          obtain ⟨n, hn⟩ := mul_cofinal_src _ b hb (head_le_one_base_src ls m hmin hm0 b hba)
          refine ⟨n, ?_⟩
          obtain ⟨mv, mh⟩ := m
          change mv = 0 at hm0
          subst mv
          rw [new.T.fund, ite_eq_left rfl, hmin]
          exact hn
        · subst hd1
          apply lift (fun n => new.T.fund (ls.idx m) (new.T.ofNat n))
          · exact fun x hx hlt => ihls m hspec.2.1 x hx.1 hlt
          · intro n
            rw [new.T.fund, ite_eq_left rfl, hmin]
            rfl
        · subst hdj
          have hj0 := new.T.dom_Omega_pos (ls.idx m) j hspec.2.1
          have hmj : m.val < j.val := by
            have : ¬ j.val ≤ m.val := hjm
            omega
          apply lift (fun n => new.T.fund (ls.idx m)
            (new.T.iter (fun x => new.T.fund (ls.idx m) x) (new.T.ofNat n)))
          · intro x hx hlt
            exact iteration_cofinal_src (ls.idx m) (hvNF m) j hspec.2.1 x
              (new.T.isNFComp_mono m.val (j.val - 1) (by omega) x hx) hlt
          · intro n
            rw [new.T.fund, ite_eq_left rfl, hmin]
            simp only [hjm, ite_false]
            rfl
      · have hdadd : new.T.dom add = .omega := by
          simpa only [new.T.dom, hadd, ite_false] using hdom
        cases b with
        | Z => exact ⟨0, by rw [new.T.fund_P_tail_eq _ _ _ hadd]; rfl⟩
        | P ws tail =>
            change (match new.compareVec ws ls with
              | .eq => new.compareT tail add | ord => ord) = .lt at hba
            cases hc : new.compareVec ws ls with
            | lt =>
                refine ⟨0, ?_⟩
                rw [new.T.fund_P_tail_eq _ _ _ hadd]
                exact new.T.P_lt_P_of_compareVec_lt _ _ _ _ hc
            | gt => simp [hc] at hba
            | eq =>
                rw [hc] at hba
                obtain rfl := new.Vec_eq_sound ws ls hc
                obtain ⟨_, htl, _⟩ := new.T.isNF_P_inv ws tail hb
                obtain ⟨n, hn⟩ := ihadd hdadd tail htl hba
                exact ⟨n, by rw [new.T.fund_P_tail_eq _ _ _ hadd]; exact new.T.P_tail_lt _ _ _ hn⟩

theorem fund_countable_cofinal_src {lam : Nat} (a b : new.T lam) (ha : new.T.isNF a)
    (hb : new.T.isNF b) (hnO : ∀ i, new.T.dom a ≠ .Omega i) (hba : b < a) :
    ∃ n : Nat, new.T.fund a (new.T.ofNat n) < a ∧ b ≤ new.T.fund a (new.T.ofNat n) := by
  have hane : a ≠ new.T.Z := by
    intro h; subst h; exact new.T.lt_Z_false b hba
  cases hd : new.T.dom a with
  | zero => exact False.elim (hane (new.T.dom_zero_eq_Z a hd))
  | one => exact ⟨0, new.T.fund_lt_self _ _ hane, new.T.fund_one_upper a hd b hba⟩
  | omega =>
      obtain ⟨n, hn⟩ := fund_omega_cofinal_src a ha hd b hb hba
      exact ⟨n, new.T.fund_lt_self _ _ hane, Or.inl hn⟩
  | Omega i => exact False.elim (hnO i hd)

/-! Downward closure of OT among indexed normal forms. -/

theorem isOT_downward_src {lam : Nat} (a b : new.T lam) (ha : new.T.isOT lam a)
    (hb : new.T.isNF b) (hba : b ≤ a) : new.T.isOT lam b := by
  suffices H : ∀ a0 : NFsrc lam, new.T.isOT lam a0.1 →
      ∀ b0, new.T.isNF b0 → b0 ≤ a0.1 → new.T.isOT lam b0 by
    exact H ⟨a, new.T.isOT_isNF a ha⟩ ha b hb hba
  intro a0
  induction a0 using (wf_NFsrc lam).induction with
  | h a0 ih =>
      intro ha0 b0 hb0 hba0
      rcases hba0 with hlt | heq
      · obtain ⟨n, hfall, hupper⟩ := fund_countable_cofinal_src a0.1 b0 a0.2 hb0
          (new.T.isOT_dom_not_Omega lam a0.1 ha0) hlt
        have hn := new.T.isOT.step lam a0.1 ha0 n
        exact ih ⟨_, new.T.isOT_isNF _ hn⟩ hfall hn b0 hb0 hupper
      · rwa [new.T_eq_sound _ _ heq]

/-! Bounds and bases. -/

theorem lt_unit_eq_Z {lam : Nat} (x : new.T lam)
    (h : x < new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z) : x = new.T.Z := by
  cases x with
  | Z => rfl
  | P w c =>
      obtain ⟨i, _, hi⟩ := new.Vec.compare_lt_has_pivot _ _ (new.T.vector_lt_of_P_lt_PZ w _ c h)
      rw [new.Vec.ofFn_idx] at hi
      exact absurd hi (new.T.lt_Z_false _)

theorem otBound_coords_zero {lam : Nat} (ls : new.Vec (new.T lam) lam) (add : new.T lam)
    (hb : new.T.P ls add < new.T.otBound lam) : ∀ j : Fin lam, 0 < j.val → ls.idx j = new.T.Z := by
  obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
    (new.T.vector_lt_of_P_lt_PZ ls _ add hb)
  have hq1 : q.val = 1 := by
    by_cases h : q.val = 1
    · exact h
    · rw [new.Vec.ofFn_idx, ite_eq_right h] at hLt
      exact absurd hLt (new.T.lt_Z_false _)
  rw [new.Vec.ofFn_idx, ite_eq_left hq1] at hLt
  have hqz := lt_unit_eq_Z _ hLt
  intro j hj
  by_cases heq : j.val = q.val
  · rw [Fin.eq_of_val_eq heq]; exact hqz
  · have hjq : q.val < j.val := by omega
    rw [hAbove j hjq, new.Vec.ofFn_idx, ite_eq_right (by omega)]

theorem countable_of_bound {lam : Nat} : ∀ s : new.T lam, new.T.isNF s →
    s < new.T.otBound lam → new.T.Countable s
  | .Z, _, _ => .z
  | .P ls add, hs, hb =>
      .p ls add (otBound_coords_zero ls add hb)
        (countable_of_bound add (new.T.isNF_P_inv ls add hs).2.1
          (strict_partial_order.trans _ _ _ (new.T.NF_tail_lt ls add hs) hb))

theorem LF_cofinal_src (k : Nat) : ∀ a : new.T (k + 1), ∃ n, a < new.T.LF (k + 1) n := by
  intro a
  induction a using (measure new.T.size).wf.induction with
  | h a ih =>
      cases a with
      | Z => exact ⟨1, rfl⟩
      | P ls add =>
          obtain ⟨m, hm⟩ := ih (ls.idx (Fin.last k)) (new.T.idx_size_lt_P ls add (Fin.last k))
          refine ⟨m + 1, ?_⟩
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot _ _ (Fin.last k)
          · intro j hj
            have := j.isLt
            simp only [Fin.val_last] at hj
            omega
          · simpa only [new.T.LF, new.Vec.ofFn_idx, Fin.val_last, ite_true] using hm

theorem base_cofinal_src (k : Nat) (s : new.T (k + 1)) (hs : new.T.isNF s)
    (hbound : 1 < k + 1 → s < new.T.otBound (k + 1)) :
    ∃ n : Nat, s < new.T.P (new.Vec.ofFn (k + 1)
      (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z)) new.T.Z := by
  cases s with
  | Z => exact ⟨0, rfl⟩
  | P ls add =>
      let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
      obtain ⟨n, hn⟩ := LF_cofinal_src k (ls.idx i0)
      refine ⟨n, new.T.P_lt_P_of_compareVec_lt _ _ _ _ ?_⟩
      apply new.Vec.compare_lt_of_pivot _ _ i0
      · intro j hj
        change 0 < j.val at hj
        rw [new.Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hj)]
        exact otBound_coords_zero ls add (hbound (by have := j.isLt; omega)) j hj
      · simpa only [new.Vec.ofFn_idx, show i0.val = 0 from rfl, ite_true] using hn

/-- Legacy OT terms are exactly the indexed normal forms below the countable bound. -/
theorem OT_iff_NF_src (lam : Nat) (s : new.T lam) :
    new.T.isOT lam s ↔ new.T.isNF s ∧ (1 < lam → s < new.T.otBound lam) := by
  refine ⟨new.T.isOT_sound_bound lam s, fun h => ?_⟩
  cases lam with
  | zero => exact LegacyZero.isOT s
  | succ k =>
      obtain ⟨n, hn⟩ := base_cofinal_src k s h.1 h.2
      exact isOT_downward_src _ s (new.T.isOT.base_succ k n) h.1 (Or.inl hn)

end LegacyTranslation

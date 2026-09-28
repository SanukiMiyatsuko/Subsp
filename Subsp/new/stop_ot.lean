import Subsp.new.stop_nf_order

/-! OT bases, cofinality, downward closure, and characterization by bounded normal forms. -/

/-! Finite terms and the defining cofinal bases. -/

section OTBases

open T

theorem ot_new_ofNat_step_lt {lam : Nat} (n : Nat) :
    new.T.ofNat (lam := lam) n < new.T.ofNat (lam := lam) (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact new.T.P_tail_lt _ _ _ ih

theorem ot_NFComp_P {lam : Nat} (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hv : ∀ i, new.T.isNFComp (v.idx i) ∧ v.idx i < new.T.P v a)
    (ha : new.T.isNFComp a) (hh : new.T.head a ≤ new.T.P v new.T.Z)
    (hlt : a < new.T.P v a) : new.T.isNFComp (new.T.P v a) := by
  have hc : ∀ x ∈ new.Vec.toList v, new.T.isNFComp x := by
    intro x hx
    obtain ⟨i, rfl⟩ := new.Vec.mem_toList_exists_idx v x hx
    exact (hv i).1
  refine ⟨new.T.isNF.p v a (fun x hx => (hc x hx).1) ha.1 (fun x hx => (hc x hx).2) hh, ?_⟩
  intro y hy
  rcases (new.T.mem_G_P v a y).mp hy with ⟨i, rfl | hG⟩ | ht
  · exact (hv i).2
  · exact strict_partial_order.trans _ _ _ ((hv i).1.2 y hG) (hv i).2
  · exact strict_partial_order.trans _ _ _ (ha.2 y ht) hlt

theorem ot_new_ofNat_NFComp {lam : Nat} (n : Nat) :
    new.T.isNFComp (new.T.ofNat (lam := lam) n) := by
  induction n with
  | zero => exact new.T.isNFComp_Z
  | succ n ih =>
      refine ot_NFComp_P _ _ ?_ ih ?_ (ot_new_ofNat_step_lt n)
      · intro i; rw [new.Vec.ofFn_idx]; exact ⟨new.T.isNFComp_Z, rfl⟩
      · cases n with
        | zero => exact new.T.Z_le _
        | succ n => exact new.T.le_refl _

theorem ot_new_LF_step_lt (lam n : Nat) :
    new.T.LF lam n < new.T.LF lam (n + 1) := by
  induction n with
  | zero => cases lam <;> rfl
  | succ n ih =>
      cases lam with
      | zero => exact new.T.P_tail_lt _ _ _ ih
      | succ k =>
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot _ _ (Fin.last k)
          · intro j hj
            exfalso; have := j.isLt; simp only [Fin.val_last] at hj; omega
          · simpa only [new.Vec.ofFn_idx, Fin.val_last, ite_true] using ih

theorem ot_new_LF_NFComp (lam n : Nat) :
    new.T.isNFComp (new.T.LF lam n) := by
  induction n with
  | zero => exact new.T.isNFComp_Z
  | succ n ih =>
      cases lam with
      | zero =>
          refine ot_NFComp_P _ _ (fun i => i.elim0) ih ?_ (ot_new_LF_step_lt 0 n)
          cases n with
          | zero => exact new.T.Z_le _
          | succ n => exact new.T.le_refl _
      | succ k =>
          refine ot_NFComp_P _ _ ?_ new.T.isNFComp_Z (new.T.Z_le _) rfl
          intro i
          simp only [new.Vec.ofFn_idx]
          split
          · exact ⟨ih, ot_new_LF_step_lt (k + 1) n⟩
          · exact ⟨new.T.isNFComp_Z, rfl⟩

theorem ot_new_base_succ_NF (k n : Nat) :
    new.T.isNF
      (new.T.P
        (new.Vec.ofFn (k + 1)
          (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
        new.T.Z) := by
  apply new.T.isNF_PZ_of_coords
  intro i
  simp only [new.Vec.ofFn_idx]
  split
  · exact ot_new_LF_NFComp (k + 1) n
  · exact new.T.isNFComp_Z

theorem ot_new_base_succ_bound (k n : Nat) (hk : 1 < k + 1) :
    new.T.P
      (new.Vec.ofFn (k + 1)
        (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
      new.T.Z <
    new.T.P
      (new.Vec.ofFn (k + 1)
        (fun i => if i.val = 1 then
          new.T.P (new.Vec.ofFn (k + 1) (fun _ => new.T.Z)) new.T.Z
        else new.T.Z))
      new.T.Z := by
  apply new.T.P_lt_P_of_compareVec_lt
  apply new.Vec.compare_lt_of_pivot _ _ ⟨1, hk⟩
  · intro j hj
    change 1 < j.val at hj
    simp only [new.Vec.ofFn_idx, show j.val ≠ 0 by omega,
      show j.val ≠ 1 by omega, ite_false]
  · simp only [new.Vec.ofFn_idx, Nat.one_ne_zero, ite_false, ite_true]
    rfl

theorem ot_new_isOT_sound (lam : Nat) (s : new.T lam)
    (hs : new.T.isOT lam s) :
    new.T.isNF s ∧
      (1 < lam →
        s < new.T.P
          (new.Vec.ofFn lam
            (fun x => if x.val = 1 then
              new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z
            else new.T.Z))
          new.T.Z) := by
  induction hs with
  | base_0 n => exact ⟨(ot_new_LF_NFComp 0 n).1, by intro h; exfalso; omega⟩
  | base_succ k n => exact ⟨ot_new_base_succ_NF k n, ot_new_base_succ_bound k n⟩
  | step lam a _ n ih =>
      refine ⟨new.T.fund_NF_closed a (new.T.ofNat n) ih.1 (fun _ => ot_new_ofNat_NFComp n), ?_⟩
      intro hlam
      by_cases haz : a = new.T.Z
      · subst a; rw [new.T.fund]; rfl
      · exact strict_partial_order.trans _ _ _ (new.T.fund_lt_self _ _ haz) (ih.2 hlam)

theorem ot_new_LF_cofinal (lam : Nat) (s : new.T lam)
    (hs : new.T.isNF s) : ∃ n : Nat, s < new.T.LF lam n := by
  induction hs with
  | z => exact ⟨1, ot_new_LF_step_lt lam 0⟩
  | p ls add _ _ _ _ ihls ihadd =>
      cases lam with
      | zero =>
          cases ls
          obtain ⟨n, hn⟩ := ihadd
          exact ⟨n + 1, new.T.P_tail_lt _ _ _ hn⟩
      | succ k =>
          obtain ⟨n, hn⟩ := ihls _ (new.Vec.idx_mem_toList ls (Fin.last k))
          refine ⟨n + 1, new.T.P_lt_P_of_compareVec_lt _ _ _ _ ?_⟩
          apply new.Vec.compare_lt_of_pivot _ _ (Fin.last k)
          · intro j hj
            exfalso; have := j.isLt; simp only [Fin.val_last] at hj; omega
          · simpa only [new.Vec.ofFn_idx, Fin.val_last, ite_true] using hn

end OTBases

/-! Successor fundamental sequences and multiplication. -/

section SuccessorCofinality

open T

theorem ot_lt_Z_inv {lam : Nat} (x : new.T lam) (h : x < new.T.Z) : False := by
  cases x <;> cases h

theorem ot_vector_lt_of_P_lt_PZ {lam : Nat}
    (v w : new.Vec (new.T lam) lam) (a : new.T lam)
    (h : new.T.P v a < new.T.P w new.T.Z) : new.compareVec v w = Ordering.lt := by
  change (match new.compareVec v w with
    | .eq => new.compareT a new.T.Z
    | ord => ord) = .lt at h
  cases hc : new.compareVec v w <;> simp_all
  exact ot_lt_Z_inv a h

theorem ot_fund_one_upper {lam : Nat} :
    ∀ a : new.T lam, new.T.dom a = .one →
      ∀ b : new.T lam, b < a → b ≤ new.T.fund a new.T.Z := by
  intro a
  induction a using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => intro h; cases h
  | P ls add _ ih =>
      intro hdom b hba
      by_cases hadd : add = new.T.Z
      · subst add
        have hnone := (new.T.dom_PZ_one_iff ls).mp hdom
        rw [new.T.fund_PZ_none ls new.T.Z hnone]
        cases b with
        | Z => exact new.T.le_refl _
        | P ws tail =>
            obtain ⟨i, _, hi⟩ := new.Vec.compare_lt_has_pivot ws ls
              (ot_vector_lt_of_P_lt_PZ ws ls tail hba)
            rw [new.T.dom_zero_eq_Z _ (new.T.domVecMinIdx_none_all_zero ls hnone i)] at hi
            exact False.elim (ot_lt_Z_inv _ hi)
      · rw [new.T.fund_P_tail_eq ls add new.T.Z hadd]
        have hdadd : new.T.dom add = .one := by simpa [new.T.dom, hadd] using hdom
        cases b with
        | Z => exact new.T.Z_le _
        | P ws tail =>
            change (match new.compareVec ws ls with
              | .eq => new.compareT tail add | ord => ord) = .lt at hba
            cases hc : new.compareVec ws ls with
            | lt => exact Or.inl (new.T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
            | eq =>
                rw [hc] at hba
                obtain rfl := new.Vec_eq_sound ws ls hc
                exact (new.T.P_same_le_iff _ _ _).mpr (ih hdadd tail hba)
            | gt => simp [hc] at hba
  | nil => trivial
  | snoc => trivial

theorem ot_mul_cofinal {lam : Nat}
    (ls : new.Vec (new.T lam) lam) :
    ∀ b : new.T lam, new.T.isNF b →
      new.T.head b ≤ new.T.P ls new.T.Z →
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

end SuccessorCofinality

/-! Vector comparison and the countable OT bound. -/

section OTBounds

open T

theorem oti_zeroVec_not_gt {lam : Nat} (v : new.Vec (new.T lam) lam) :
    new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) v ≠ Ordering.gt := by
  intro hgt
  rcases new.Vec_total (new.Vec.ofFn lam (fun _ => new.T.Z)) v with hlt | hlt | rfl
  · simp [hgt] at hlt
  · obtain ⟨i, _, hi⟩ := new.Vec.compare_lt_has_pivot _ _ hlt
    rw [new.Vec.ofFn_idx] at hi
    exact ot_lt_Z_inv _ hi
  · simp [new.Vec_refl] at hgt

theorem ot_tail_lt_of_NF {lam : Nat} :
    ∀ (ls : new.Vec (new.T lam) lam) (add : new.T lam),
      new.T.isNF (new.T.P ls add) → add ≠ new.T.Z →
        add < new.T.P ls add := by
  intro ls add
  induction add using new.T.rec (motive_2 := fun _ _ => True) generalizing ls with
  | Z => exact fun _ h => False.elim (h rfl)
  | P ws tail _ ih =>
      intro hnf _
      cases hnf with
      | p _ _ _ ha _ hh =>
          rcases new.T.vector_rel_of_P_le_P ws ls _ _ hh with h | rfl
          · exact new.T.P_lt_P_of_compareVec_lt _ _ _ _ h
          · apply new.T.P_tail_lt ws
            by_cases hz : tail = new.T.Z
            · subst tail; rfl
            · exact ih ws ha hz
  | nil => trivial
  | snoc => trivial

def ot_unit (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z

theorem ot_unit_le_P {lam : Nat} (ls : new.Vec (new.T lam) lam)
    (add : new.T lam) : ot_unit lam ≤ new.T.P ls add := by
  cases hc : new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
  | lt => exact Or.inl (new.T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
  | eq =>
      obtain rfl := new.Vec_eq_sound _ _ hc
      exact (new.T.P_same_le_iff _ _ _).mpr (new.T.Z_le add)
  | gt => exact False.elim (oti_zeroVec_not_gt ls hc)

theorem ot_unit_le_of_ne_Z {lam : Nat} (s : new.T lam)
    (hne : s ≠ new.T.Z) : ot_unit lam ≤ s := by
  cases s with
  | Z => exact False.elim (hne rfl)
  | P ls add => exact ot_unit_le_P ls add

def ot_bound (lam : Nat) : new.T lam :=
  new.T.P
    (new.Vec.ofFn lam (fun x =>
      if x.val = 1 then ot_unit lam else new.T.Z))
    new.T.Z

theorem ot_bound_coords_zero {lam : Nat}
    (ls : new.Vec (new.T lam) lam) (add : new.T lam)
    (hb : new.T.P ls add < ot_bound lam) :
    ∀ j : Fin lam, 0 < j.val → ls.idx j = new.T.Z := by
  obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _ (ot_vector_lt_of_P_lt_PZ ls _ add hb)
  have hqval : q.val = 1 := by
    by_cases h : q.val = 1
    · exact h
    · rw [new.Vec.ofFn_idx, ite_eq_right h] at hLt
      exact False.elim (ot_lt_Z_inv _ hLt)
  rw [new.Vec.ofFn_idx, ite_eq_left hqval] at hLt
  have hqz : ls.idx q = new.T.Z := by
    by_cases hz : ls.idx q = new.T.Z
    · exact hz
    · exact False.elim (strict_partial_order.irrefl _
        (new.T.lt_of_le_of_lt _ _ _ (ot_unit_le_of_ne_Z _ hz) hLt))
  intro j hj
  by_cases heq : q.val = j.val
  · simpa only [Fin.eq_of_val_eq heq] using hqz
  · simpa only [new.Vec.ofFn_idx, show j.val ≠ 1 by omega, ite_false]
      using hAbove j (by omega)

theorem ot_dom_Omega_not_countable {lam : Nat} :
    ∀ s : new.T lam, new.T.isNF s →
      (1 < lam → s < ot_bound lam) →
      new.T.dom s ≠ .Omega := by
  intro s
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => intro _ _ h; cases h
  | P ls add _ ih =>
      intro hnf hbound hOmega
      by_cases hadd : add = new.T.Z
      · subst add
        obtain ⟨k, hk, hmin⟩ := new.T.dom_PZ_Omega ls hOmega
        have hz := ot_bound_coords_zero ls new.T.Z (hbound (by omega)) ⟨k + 1, hk⟩ (by simp)
        have hc := (new.T.domVecMinIdx_some_spec ls ⟨k + 1, hk⟩ new.Dom.one hmin).2.1
        rw [hz] at hc; cases hc
      · have hlt := ot_tail_lt_of_NF ls add hnf hadd
        cases hnf with
        | p _ _ _ ha _ _ =>
            apply ih ha (fun hlam => strict_partial_order.trans _ _ _ hlt (hbound hlam))
            simpa [new.T.dom, hadd] using hOmega
  | nil => trivial
  | snoc => trivial

theorem ot_vec_ext {lam m : Nat} (v w : new.Vec (new.T lam) m)
    (h : ∀ i : Fin m, v.idx i = w.idx i) : v = w := by
  induction m with
  | zero => cases v; cases w; rfl
  | succ k ih =>
      cases v with
      | snoc _ vs vx =>
        cases w with
        | snoc _ ws wx =>
          have hlast : vx = wx := by simpa [new.Vec.idx] using h (Fin.last k)
          have hpref : vs = ws := ih vs ws (fun i => by
            simpa [new.Vec.idx, i.isLt] using h i.castSucc)
          cases hpref; cases hlast; rfl

theorem ot_head_le_one_base {lam : Nat}
    (ls : new.Vec (new.T lam) lam) (m : Fin lam)
    (hmin : new.T.domVecMinIdx ls = some (m, new.Dom.one))
    (hm0 : m.val = 0)
    (b : new.T lam) (hb : new.T.isNF b)
    (hba : b < new.T.P ls new.T.Z) :
    new.T.head b ≤
      new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z := by
  cases b with
  | Z => exact new.T.Z_le _
  | P ws tail =>
      obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
        (ot_vector_lt_of_P_lt_PZ ws ls tail hba)
      by_cases hqm : q.val = m.val
      · obtain rfl := Fin.eq_of_val_eq hqm
        rcases ot_fund_one_upper _ (new.T.domVecMinIdx_some_spec ls q _ hmin).2.1 _ hLt with hlt | heq
        · apply Or.inl
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot _ _ q
          · intro j hj
            rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)]
            exact hAbove j hj
          · rw [new.Vec.rplc_idx_same]; exact hlt
        · have hv : ws = ls.rplc q (new.T.fund (ls.idx q) new.T.Z) := by
            apply ot_vec_ext
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

end OTBounds

/-! Cofinality of iterated fundamental sequences. -/

section IterationCofinality

open T

theorem ot_iter_ofNat_succ {lam : Nat} (a : new.T lam) (n : Nat) :
    new.T.iter (fun x => new.T.fund a x) (new.T.ofNat (n + 1)) =
      new.T.fund a (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
  rw [new.T.ofNat, new.T.iter]

theorem ot_iteration_cofinal {lam : Nat} (a : new.T lam)
    (ha : new.T.isNFComp a) (hd : new.T.dom a = .Omega) :
    ∀ b : new.T lam, new.T.isNFComp b → b < a →
      ∃ n : Nat,
        b < new.T.fund a
          (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
  let F := new.T.fund a
  intro b
  induction b using (measure new.T.size).wf.induction with
  | h b ih =>
      intro hbcomp hba
      have descend : ∀ cur, new.T.isNF cur → new.T.dom cur = .Omega →
          ∀ tgt, new.T.isNF tgt → tgt < cur →
          (∀ x ∈ new.T.G tgt, x ∈ new.T.G b) →
          ∃ n, tgt < new.T.fund cur (new.T.iter F (new.T.ofNat n)) := by
        intro cur hnf
        induction hnf with
        | z => intro h; cases h
        | p ls add _ haddNF _ _ _ dih =>
            intro hcdom tgt htgnf htgc hmem
            by_cases hadd : add = new.T.Z
            · subst add
              obtain ⟨r, mh, hmin⟩ := new.T.dom_PZ_Omega ls hcdom
              let mi : Fin lam := ⟨r + 1, mh⟩
              let mj : Fin lam := ⟨r, Nat.lt_of_succ_lt mh⟩
              let base := ls.rplc mi (new.T.fund (ls.idx mi) new.T.Z)
              have hspec := new.T.domVecMinIdx_some_spec ls mi new.Dom.one hmin
              have he (z) : new.T.fund (new.T.P ls new.T.Z) z =
                  new.T.P (base.rplc mj z) new.T.Z := by
                rw [new.T.fund, ite_eq_left rfl, hmin]; rfl
              have habove (z) (j : Fin lam) (hj : r + 1 < j.val) :
                  (base.rplc mj z).idx j = ls.idx j := by
                rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by dsimp [mj]; omega)]
                exact new.Vec.rplc_idx_of_ne _ _ _ _ (by dsimp [mi]; omega)
              cases tgt with
              | Z => exact ⟨0, by rw [he]; rfl⟩
              | P ws tail =>
                  obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
                    (ot_vector_lt_of_P_lt_PZ ws ls tail htgc)
                  have hmq : r + 1 ≤ q.val := by
                    apply Nat.le_of_not_gt
                    intro h
                    rw [new.T.dom_zero_eq_Z _ (hspec.2.2 q h)] at hLt
                    exact ot_lt_Z_inv _ hLt
                  by_cases hqm : q.val = mi.val
                  · obtain rfl := Fin.eq_of_val_eq hqm
                    rcases ot_fund_one_upper _ hspec.2.1 _ hLt with hstrict | heq
                    · refine ⟨0, ?_⟩
                      rw [he]
                      apply new.T.P_lt_P_of_compareVec_lt
                      apply new.Vec.compare_lt_of_pivot _ _ mi
                      · intro j hj
                        rw [habove _ j hj]; exact hAbove j hj
                      · rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by dsimp [mj]; omega)]
                        change ws.idx mi < (ls.rplc mi (new.T.fund (ls.idx mi) new.T.Z)).idx mi
                        rw [new.Vec.rplc_idx_same]; exact hstrict
                    · have hcMem := hmem (ws.idx mj) ((new.T.mem_G_P ws tail _).mpr (Or.inl ⟨mj, Or.inl rfl⟩))
                      obtain ⟨n, hn⟩ := ih (ws.idx mj) (new.T.G_size_lt b _ hcMem)
                        (new.T.isNF_G_isNFComp b hbcomp.1 _ hcMem)
                        (strict_partial_order.trans _ _ _ (hbcomp.2 _ hcMem) hba)
                      refine ⟨n + 1, ?_⟩
                      rw [he]
                      apply new.T.P_lt_P_of_compareVec_lt
                      apply new.Vec.compare_lt_of_pivot _ _ mj
                      · intro j hj
                        by_cases hjq : j.val = mi.val
                        · rw [Fin.eq_of_val_eq hjq]
                          rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by dsimp [mj]; omega)]
                          change ws.idx mi = (ls.rplc mi (new.T.fund (ls.idx mi) new.T.Z)).idx mi
                          rw [new.Vec.rplc_idx_same]
                          exact new.T_eq_sound _ _ heq
                        · have hjq' : mi.val < j.val := by dsimp [mi, mj] at hj hjq ⊢; omega
                          rw [habove _ j hjq']; exact hAbove j hjq'
                      · rw [new.Vec.rplc_idx_same, ot_iter_ofNat_succ]
                        exact hn
                  · refine ⟨0, ?_⟩
                    rw [he]
                    apply new.T.P_lt_P_of_compareVec_lt
                    apply new.Vec.compare_lt_of_pivot _ _ q
                    · intro j hj
                      rw [habove _ j (by dsimp [mi] at hqm; omega)]
                      exact hAbove j hj
                    · rw [habove _ q (by dsimp [mi] at hqm; omega)]
                      exact hLt
            · have hdadd : new.T.dom add = .Omega := by simpa [new.T.dom, hadd] using hcdom
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
                      cases htgnf with
                      | p _ _ _ ht _ _ =>
                          obtain ⟨n, hn⟩ := dih hdadd tail ht htgc
                            (fun x hx => hmem x ((new.T.mem_G_P ws tail x).mpr (Or.inr hx)))
                          exact ⟨n, by rw [new.T.fund_P_tail_eq _ _ _ hadd]; exact new.T.P_tail_lt _ _ _ hn⟩
      exact descend a ha.1 hd b hbcomp.1 hba (fun _ hx => hx)

end IterationCofinality

/-! Cofinality at omega-domain terms. -/

section LimitCofinality

open T

theorem ot_fund_omega_cofinal {lam : Nat} :
    ∀ a : new.T lam, new.T.isNF a → new.T.dom a = .omega →
      ∀ b : new.T lam, new.T.isNF b → b < a →
        ∃ n : Nat, b < new.T.fund a (new.T.ofNat n) := by
  intro a ha
  induction ha with
  | z => intro h; cases h
  | p ls add hvNF haddNF hvG hhead ihls ihadd =>
      intro hdom b hb hba
      by_cases hadd : add = new.T.Z
      · subst add
        cases hmin : new.T.domVecMinIdx ls with
        | none => simp [new.T.dom, hmin] at hdom
        | some md =>
            obtain ⟨m, d⟩ := md
            have hspec := new.T.domVecMinIdx_some_spec ls m d hmin
            have lift (f : Nat → new.T lam)
                (hf : ∀ x, new.T.isNFComp x → x < ls.idx m → ∃ n, x < f n)
                (he : ∀ n, new.T.fund (new.T.P ls new.T.Z) (new.T.ofNat n) =
                  new.T.P (ls.rplc m (f n)) new.T.Z) :
                ∃ n, b < new.T.fund (new.T.P ls new.T.Z) (new.T.ofNat n) := by
              cases b with
              | Z => exact ⟨0, by rw [he]; rfl⟩
              | P ws tail =>
                  obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
                    (ot_vector_lt_of_P_lt_PZ ws ls tail hba)
                  have hmq : m.val ≤ q.val := by
                    apply Nat.le_of_not_gt
                    intro h
                    rw [new.T.dom_zero_eq_Z _ (hspec.2.2 q h)] at hLt
                    exact ot_lt_Z_inv _ hLt
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
            cases d with
            | zero => exact False.elim (hspec.1 rfl)
            | one =>
                have hm0 : m.val = 0 := by
                  by_cases hm : m.val = 0 <;> simp_all [new.T.dom]
                obtain ⟨n, hn⟩ := ot_mul_cofinal _ b hb (ot_head_le_one_base ls m hmin hm0 b hb hba)
                refine ⟨n, ?_⟩
                obtain ⟨mv, mh⟩ := m
                change mv = 0 at hm0
                subst mv
                rw [new.T.fund, ite_eq_left rfl, hmin]
                exact hn
            | omega =>
                apply lift (fun n => new.T.fund (ls.idx m) (new.T.ofNat n))
                · exact fun x hx => ihls _ (new.Vec.idx_mem_toList ls m) hspec.2.1 x hx.1
                · intro n; rw [new.T.fund, ite_eq_left rfl, hmin]; rfl
            | Omega =>
                apply lift (fun n => new.T.fund (ls.idx m)
                  (new.T.iter (new.T.fund (ls.idx m)) (new.T.ofNat n)))
                · exact ot_iteration_cofinal _ ⟨hvNF _ (new.Vec.idx_mem_toList ls m),
                    hvG _ (new.Vec.idx_mem_toList ls m)⟩ hspec.2.1
                · intro n; rw [new.T.fund, ite_eq_left rfl, hmin]; rfl
      · have hdadd : new.T.dom add = .omega := by simpa [new.T.dom, hadd] using hdom
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
                cases hb with
                | p _ _ _ ht _ _ =>
                    obtain ⟨n, hn⟩ := ihadd hdadd tail ht hba
                    exact ⟨n, by rw [new.T.fund_P_tail_eq _ _ _ hadd]; exact new.T.P_tail_lt _ _ _ hn⟩

end LimitCofinality

/-! Cofinality and downward closure of OT. -/

section OTDownwardClosure

open T

theorem ot_fund_countable_cofinal {lam : Nat}
    (a b : new.T lam) (ha : new.T.isNF a) (hb : new.T.isNF b)
    (hbound : 1 < lam → a < ot_bound lam) (hba : b < a) :
    ∃ n : Nat,
      new.T.fund a (new.T.ofNat n) < a ∧
        b ≤ new.T.fund a (new.T.ofNat n) := by
  have hane : a ≠ new.T.Z := by rintro rfl; exact ot_lt_Z_inv b hba
  cases hd : new.T.dom a with
  | zero => exact False.elim (hane (new.T.dom_zero_eq_Z a hd))
  | one =>
      refine ⟨0, new.T.fund_lt_self _ _ hane, ?_⟩
      rw [new.T.fund_one_arg_irrel _ _ hd]
      exact ot_fund_one_upper a hd b hba
  | omega =>
      obtain ⟨n, hn⟩ := ot_fund_omega_cofinal a ha hd b hb hba
      exact ⟨n, new.T.fund_lt_self _ _ hane, Or.inl hn⟩
  | Omega => exact False.elim (ot_dom_Omega_not_countable a ha hbound hd)

theorem ot_new_isOT_downward {lam : Nat}
    (a b : new.T lam) (ha : new.T.isOT lam a)
    (hb : new.T.isNF b) (hba : b ≤ a) :
    new.T.isOT lam b := by
  suffices H : ∀ a0 : new.T.NF lam, new.T.isOT lam a0.1 →
      ∀ b0, new.T.isNF b0 → b0 ≤ a0.1 → new.T.isOT lam b0 by
    exact H ⟨a, (ot_new_isOT_sound lam a ha).1⟩ ha b hb hba
  intro a0
  induction a0 using (ot_new_well_founded_NF lam).induction with
  | h a0 ih =>
      intro ha0 b0 hb0 hba0
      rcases hba0 with hlt | heq
      · obtain ⟨n, hfall, hupper⟩ := ot_fund_countable_cofinal a0.1 b0 a0.2 hb0
          (ot_new_isOT_sound lam _ ha0).2 hlt
        have hn := new.T.isOT.step lam a0.1 ha0 n
        exact ih ⟨_, (ot_new_isOT_sound lam _ hn).1⟩ hfall hn b0 hb0 hupper
      · rwa [new.T_eq_sound _ _ heq]

end OTDownwardClosure

/-! The OT normal-form characterization and well-foundedness. -/

section OTCharacterization

theorem ot_base_succ_cofinal (k : Nat) (s : new.T (k + 1))
    (hs : new.T.isNF s)
    (hbound : 1 < k + 1 → s < ot_bound (k + 1)) :
    ∃ n : Nat,
      s < new.T.P
        (new.Vec.ofFn (k + 1)
          (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
        new.T.Z := by
  cases s with
  | Z => exact ⟨0, rfl⟩
  | P ls add =>
      let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
      obtain ⟨n, hn⟩ := ot_new_LF_cofinal _ _ (new.T.isNF_P_coord_NFComp ls add hs i0).1
      refine ⟨n, new.T.P_lt_P_of_compareVec_lt _ _ _ _ ?_⟩
      apply new.Vec.compare_lt_of_pivot _ _ i0
      · intro j hj
        change 0 < j.val at hj
        rw [new.Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hj)]
        exact ot_bound_coords_zero ls add (hbound (by have := j.isLt; omega)) j hj
      · simpa only [new.Vec.ofFn_idx, show i0.val = 0 from rfl, ite_true] using hn

theorem new.T.OT_iff_NF (lam : Nat) (s : T lam) :
  isOT lam s ↔ isNF s ∧
    (1 < lam → s < P (Vec.ofFn lam (fun x => if x.val = 1 then P (Vec.ofFn lam (fun _ => Z)) Z else Z)) Z) := by
  constructor
  · exact ot_new_isOT_sound lam s
  · intro h
    cases lam with
    | zero =>
        obtain ⟨n, hn⟩ := ot_new_LF_cofinal 0 s h.1
        exact ot_new_isOT_downward _ s (new.T.isOT.base_0 n) h.1 (Or.inl hn)
    | succ k =>
        obtain ⟨n, hn⟩ := ot_base_succ_cofinal k s h.1 h.2
        exact ot_new_isOT_downward _ s (new.T.isOT.base_succ k n) h.1 (Or.inl hn)

def new.T.OT (lam : Nat) := { s : T lam // isOT lam s }

theorem wellfounded_OT (lam : Nat) : WellFounded (fun s t : new.T.OT lam => s.val < t.val) := by
  exact InvImage.wf
    (fun s : new.T.OT lam => (⟨s.val, (ot_new_isOT_sound lam s.val s.property).1⟩ : new.T.NF lam))
    (wellfounded_NF lam)

end OTCharacterization

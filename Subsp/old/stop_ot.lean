import Subsp.old.stop_surjectivity

/-! Legacy ordinal-term characterization and cofinality results.
This corresponds to `Subsp.new.stop_ot`.
-/

-- Merged from Subsp/old/stop_ot_char.lean
/-! Source cofinality: legacy OT terms are exactly the countable indexed normal forms. -/

namespace LegacyTranslation

open T

/-! Well-foundedness of indexed source normal forms. -/

def NFsrc (lam : Nat) := { s : new.T lam // new.T.isNF s }

theorem wf_NFsrc (lam : Nat) : WellFounded (fun s t : NFsrc lam => s.1 < t.1) :=
  Subrelation.wf (fun {a b} hab => trans_lt_of_lt a.1 b.1 a.2 b.2 hab)
    (InvImage.wf (fun s : NFsrc lam => (⟨trans s.1, trans_isNF1 s.1 s.2⟩ : T.NF1))
      T.well_founded_NF1)

/-! Comparisons at a pivot coordinate. -/

theorem lt_PZ_of_pivot {lam : Nat} (ws v : new.Vec (new.T lam) lam) (tail : new.T lam)
    (q : Fin lam) (hAbove : ∀ j : Fin lam, q.val < j.val → ws.idx j = v.idx j)
    (hq : ws.idx q < v.idx q) : new.T.P ws tail < new.T.P v new.T.Z :=
  new.T.P_lt_P_of_compareVec_lt _ _ _ _ (new.Vec.compare_lt_of_pivot _ _ q hAbove hq)

theorem lt_rplc_of_pivot {lam : Nat} (ws ls : new.Vec (new.T lam) lam) (tail X : new.T lam)
    (q m : Fin lam) (hAbove : ∀ j : Fin lam, q.val < j.val → ws.idx j = ls.idx j)
    (hLt : ws.idx q < ls.idx q) (hmq : m.val ≤ q.val) (hX : q = m → ws.idx q < X) :
    new.T.P ws tail < new.T.P (ls.rplc m X) new.T.Z := by
  refine lt_PZ_of_pivot _ _ _ q (fun j hj => (hAbove j hj).trans
    (new.Vec.rplc_idx_of_ne _ _ _ _ (by omega)).symm) ?_
  by_cases hqm : q.val = m.val
  · obtain rfl := Fin.eq_of_val_eq hqm
    rw [new.Vec.rplc_idx_same]; exact hX rfl
  · rwa [new.Vec.rplc_idx_of_ne _ _ _ _ hqm]

theorem pivot_ge_min {lam : Nat} (ls ws : new.Vec (new.T lam) lam) (m : Fin lam)
    (d : new.Dom lam) (hmin : new.T.domVecMinIdx ls = some (m, d)) (q : Fin lam)
    (hLt : ws.idx q < ls.idx q) : m.val ≤ q.val :=
  Nat.le_of_not_gt fun h => by
    rw [new.T.dom_zero_eq_Z _ ((new.T.domVecMinIdx_some_spec ls m d hmin).2.2 q h)] at hLt
    exact new.T.lt_Z_false _ hLt

/-- Cofinality in the tail of a non-principal term. -/
theorem cofinal_tail {lam : Nat} (ls : new.Vec (new.T lam) lam) (add : new.T lam)
    (hadd : add ≠ new.T.Z) (f : Nat → new.T lam) (Q : new.T lam → Prop)
    (hQ : ∀ tail, Q (new.T.P ls tail) → Q tail) (tgt : new.T lam) (htgnf : new.T.isNF tgt)
    (htg : tgt < new.T.P ls add) (hq : Q tgt)
    (ih : ∀ tail, new.T.isNF tail → tail < add → Q tail → ∃ n, tail < new.T.fund add (f n)) :
    ∃ n, tgt < new.T.fund (new.T.P ls add) (f n) := by
  simp only [new.T.fund_P_tail_eq _ _ _ hadd]
  cases tgt with
  | Z => exact ⟨0, rfl⟩
  | P ws tail =>
      change (match new.compareVec ws ls with
        | .eq => new.compareT tail add | ord => ord) = .lt at htg
      cases hc : new.compareVec ws ls with
      | lt => exact ⟨0, new.T.P_lt_P_of_compareVec_lt _ _ _ _ hc⟩
      | gt => simp [hc] at htg
      | eq =>
          rw [hc] at htg
          obtain rfl := new.Vec_eq_sound ws ls hc
          obtain ⟨n, hn⟩ := ih tail (new.T.isNF_P_inv ws tail htgnf).2.1 htg (hQ tail hq)
          exact ⟨n, new.T.P_tail_lt _ _ _ hn⟩

/-! Iterated fundamental sequences at uncountable domains. -/

theorem iteration_cofinal_src {lam : Nat} (a : new.T lam) (ha : new.T.isNF a) (i : Fin lam)
    (hd : new.T.dom a = .Omega i) :
    ∀ b : new.T lam, new.T.isNFComp (i.val - 1) b → b < a →
      ∃ n : Nat, b < new.T.fund a (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
  intro b
  induction b using (measure new.T.size).wf.induction with
  | h b ih =>
      intro hbcomp hba
      suffices descend : ∀ cur : new.T lam, new.T.isNF cur → new.T.dom cur = .Omega i →
          ∀ tgt : new.T lam, new.T.isNF tgt → tgt < cur →
          (∀ x ∈ new.T.Gi (i.val - 1) tgt, x ∈ new.T.Gi (i.val - 1) b) →
          ∃ n, tgt < new.T.fund cur (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) from
        descend a ha hd b hbcomp.1 hba (fun _ hx => hx)
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
            | Z => exact ⟨0, Z_lt_of_ne _ (new.T.fund_Omega_ne_Z _ _ i hcdom)⟩
            | P ws tail =>
                obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
                  (new.T.vector_lt_of_P_lt_PZ ws ls tail htgc)
                have hmq := pivot_ge_min ls ws m d hmin q hLt
                rcases hcase with ⟨rfl, hm0, him⟩ | ⟨j, rfl, hjm, hij⟩
                · obtain ⟨_ | r, mh⟩ := m
                  · exact absurd hm0 (Nat.lt_irrefl 0)
                  have hrl : r < lam := Nat.lt_of_succ_lt mh
                  have he (z : new.T lam) : new.T.fund (new.T.P ls new.T.Z) z =
                      new.T.P ((ls.rplc ⟨r + 1, mh⟩
                        (new.T.fund (ls.idx ⟨r + 1, mh⟩) new.T.Z)).rplc ⟨r, hrl⟩ z) new.T.Z := by
                    rw [new.T.fund, ite_eq_left rfl, hmin]; rfl
                  have habove (z : new.T lam) (j : Fin lam) (hj : r + 1 < j.val) :
                      ((ls.rplc ⟨r + 1, mh⟩ (new.T.fund (ls.idx ⟨r + 1, mh⟩) new.T.Z)).rplc
                        ⟨r, hrl⟩ z).idx j = ls.idx j := by
                    rw [new.Vec.rplc_idx_of_ne _ _ _ _ (by simp; omega),
                      new.Vec.rplc_idx_of_ne _ _ _ _ (by simp; omega)]
                  have hmid (z : new.T lam) : ((ls.rplc ⟨r + 1, mh⟩
                      (new.T.fund (ls.idx ⟨r + 1, mh⟩) new.T.Z)).rplc ⟨r, hrl⟩ z).idx ⟨r + 1, mh⟩ =
                      new.T.fund (ls.idx ⟨r + 1, mh⟩) new.T.Z := by
                    rw [new.Vec.rplc_idx_of_ne _ _ _ _ (Nat.succ_ne_self r), new.Vec.rplc_idx_same]
                  by_cases hqm : q.val = r + 1
                  · obtain rfl : q = ⟨r + 1, mh⟩ := Fin.eq_of_val_eq hqm
                    rcases (new.T.fund_one_props _ hspec.2.1).2.1 _ hLt with hstrict | heq
                    · exact ⟨0, by
                        rw [he]
                        exact lt_PZ_of_pivot _ _ _ _ (fun j hj => (hAbove j hj).trans
                          (habove _ j hj).symm) (by rw [hmid]; exact hstrict)⟩
                    · have hir : i.val - 1 = r := by subst him; rfl
                      have hbMem := hmem _ ((new.T.mem_Gi_P _ ws tail _).mpr
                        (Or.inl ⟨⟨r, hrl⟩, by simp [hir], Or.inl rfl⟩))
                      obtain ⟨n, hn⟩ := ih (ws.idx ⟨r, hrl⟩)
                        (new.T.Gi_size_lt (i.val - 1) b _ hbMem)
                        (hir ▸ (new.T.isNF_P_inv ws tail htgnf).1 ⟨r, hrl⟩)
                        (strict_partial_order.trans _ _ _ (hbcomp.2 _ hbMem) hba)
                      refine ⟨n + 1, ?_⟩
                      rw [he]
                      refine lt_PZ_of_pivot _ _ _ ⟨r, hrl⟩ (fun j hj => ?_)
                        (by rw [new.Vec.rplc_idx_same]; exact hn)
                      by_cases hjq : j.val = r + 1
                      · obtain rfl : j = ⟨r + 1, mh⟩ := Fin.eq_of_val_eq hjq
                        rw [hmid]; exact new.T_eq_sound _ _ heq
                      · have hj2 : r + 1 < j.val := by simp at hj; omega
                        rw [habove _ j hj2]; exact hAbove j hj2
                  · have hq2 : r + 1 < q.val := by simp at hmq; omega
                    exact ⟨0, by
                      rw [he]
                      exact lt_PZ_of_pivot _ _ _ q (fun j hj => (hAbove j hj).trans
                        (habove _ j (by omega)).symm) (by rw [habove _ q hq2]; exact hLt)⟩
                · have he (z : new.T lam) : new.T.fund (new.T.P ls new.T.Z) z =
                      new.T.P (ls.rplc m (new.T.fund (ls.idx m) z)) new.T.Z := by
                    rw [new.T.fund, ite_eq_left rfl, hmin]
                    simp only [hjm, ite_true]
                    rfl
                  by_cases hqm : q = m
                  · subst hqm
                    obtain ⟨n, hn⟩ := ihls q (by rw [hspec.2.1, hij]) (ws.idx q)
                      ((new.T.isNF_P_inv ws tail htgnf).1 q).1 hLt
                      (fun x hx => hmem x ((new.T.mem_Gi_P _ ws tail x).mpr
                        (Or.inl ⟨q, by rw [hij] at *; omega, Or.inr hx⟩)))
                    refine ⟨n, ?_⟩
                    rw [he]; exact lt_rplc_of_pivot _ _ _ _ _ _ hAbove hLt hmq fun _ => hn
                  · refine ⟨0, ?_⟩
                    rw [he]; exact lt_rplc_of_pivot _ _ _ _ _ _ hAbove hLt hmq fun h => absurd h hqm
          · exact cofinal_tail ls add hadd _ _ (fun tail h x hx => h x ((new.T.mem_Gi_P _ ls tail x).mpr
              (Or.inr hx))) tgt htgnf htgc hmem fun tail htl hlt hm =>
                ihadd (by simpa only [new.T.dom, hadd, ite_false] using hcdom) tail htl hlt hm

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
              by_cases hqm : q = m
              · subst hqm
                obtain ⟨n, hn⟩ := hf _ ((new.T.isNF_P_inv _ _ hb).1 q) hLt
                exact ⟨n, by rw [he]; exact lt_rplc_of_pivot _ _ _ _ _ _ hAbove hLt hmq fun _ => hn⟩
              · exact ⟨0, by
                  rw [he]; exact lt_rplc_of_pivot _ _ _ _ _ _ hAbove hLt hmq fun h => absurd h hqm⟩
        rcases hcase with ⟨rfl, hm0⟩ | rfl | ⟨j, rfl, hjm⟩
        · -- successor coordinate at index zero: the multiples of the predecessor are cofinal
          have hhead : new.T.head b ≤ new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z := by
            cases b with
            | Z => exact new.T.Z_le _
            | P ws tail =>
                obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
                  (new.T.vector_lt_of_P_lt_PZ ws ls tail hba)
                have hmq := pivot_ge_min ls ws m _ hmin q hLt
                by_cases hqm : q = m
                · subst hqm
                  rcases (new.T.fund_one_props _ hspec.2.1).2.1 _ hLt with hlt | heq
                  · exact Or.inl (lt_rplc_of_pivot _ _ _ _ _ _ hAbove hLt hmq fun _ => hlt)
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
                · exact Or.inl (lt_rplc_of_pivot _ _ _ _ _ _ hAbove hLt hmq fun h => absurd h hqm)
          have hmul : ∀ b : new.T lam, new.T.isNF b →
              new.T.head b ≤ new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z →
              ∃ n : Nat, b <
                new.T.mul (new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z)
                  (new.T.ofNat n) := by
            intro b hnf
            induction hnf with
            | z => exact fun _ => ⟨1, rfl⟩
            | p ws tail _ _ _ htailHead _ ih =>
                intro hhead
                rcases new.T.vector_rel_of_P_le_P ws _ _ _ hhead with hvec | rfl
                · exact ⟨1, new.T.P_lt_P_of_compareVec_lt _ _ _ _ hvec⟩
                · obtain ⟨n, hn⟩ := ih htailHead
                  exact ⟨n + 1, new.T.P_tail_lt _ _ _ hn⟩
          obtain ⟨n, hn⟩ := hmul b hb hhead
          refine ⟨n, ?_⟩
          obtain ⟨mv, mh⟩ := m
          change mv = 0 at hm0
          subst mv
          rw [new.T.fund, ite_eq_left rfl, hmin]
          exact hn
        · apply lift (fun n => new.T.fund (ls.idx m) (new.T.ofNat n))
          · exact fun x hx hlt => ihls m hspec.2.1 x hx.1 hlt
          · intro n
            rw [new.T.fund, ite_eq_left rfl, hmin]
            rfl
        · have hj0 := new.T.dom_Omega_pos (ls.idx m) j hspec.2.1
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
      · exact cofinal_tail ls add hadd _ (fun _ => True) (fun _ _ => trivial) b hb hba trivial
          fun tail htl hlt _ =>
            ihadd (by simpa only [new.T.dom, hadd, ite_false] using hdom) tail htl hlt

theorem fund_countable_cofinal_src {lam : Nat} (a b : new.T lam) (ha : new.T.isNF a)
    (hb : new.T.isNF b) (hnO : ∀ i, new.T.dom a ≠ .Omega i) (hba : b < a) :
    ∃ n : Nat, new.T.fund a (new.T.ofNat n) < a ∧ b ≤ new.T.fund a (new.T.ofNat n) := by
  have hane : a ≠ new.T.Z := by
    intro h; subst h; exact new.T.lt_Z_false b hba
  cases hd : new.T.dom a with
  | zero => exact False.elim (hane (new.T.dom_zero_eq_Z a hd))
  | one => exact ⟨0, new.T.fund_lt_self _ _ hane, (new.T.fund_one_props a hd).2.1 b hba⟩
  | omega =>
      obtain ⟨n, hn⟩ := fund_omega_cofinal_src a ha hd b hb hba
      exact ⟨n, new.T.fund_lt_self _ _ hane, Or.inl hn⟩
  | Omega i => exact False.elim (hnO i hd)

/-! Downward closure of OT among indexed normal forms. -/

theorem isOT_downward_src {lam : Nat} (a b : new.T lam) (ha : new.T.isOT lam a)
    (hb : new.T.isNF b) (hba : b ≤ a) : new.T.isOT lam b := by
  suffices H : ∀ a0 : NFsrc lam, new.T.isOT lam a0.1 →
      ∀ b0, new.T.isNF b0 → b0 ≤ a0.1 → new.T.isOT lam b0 from
    H ⟨a, new.T.isOT_isNF a ha⟩ ha b hb hba
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

theorem base_cofinal_src (k : Nat) (s : new.T (k + 1)) (hs : new.T.isNF s)
    (hbound : 1 < k + 1 → s < new.T.otBound (k + 1)) :
    ∃ n : Nat, s < new.T.P (new.Vec.ofFn (k + 1)
      (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z)) new.T.Z := by
  have hLF : ∀ a : new.T (k + 1), ∃ n, a < new.T.LF (k + 1) n := by
    intro a
    induction a using (measure new.T.size).wf.induction with
    | h a ih =>
        cases a with
        | Z => exact ⟨1, rfl⟩
        | P ls add =>
            obtain ⟨m, hm⟩ := ih (ls.idx (Fin.last k)) (new.T.idx_size_lt_P ls add (Fin.last k))
            refine ⟨m + 1, lt_PZ_of_pivot _ _ _ (Fin.last k) (fun j hj => ?_)
              (by simpa only [new.T.LF, new.Vec.ofFn_idx, Fin.val_last, ite_true] using hm)⟩
            have := j.isLt
            simp only [Fin.val_last] at hj
            omega
  cases s with
  | Z => exact ⟨0, rfl⟩
  | P ls add =>
      have hzero : ∀ j : Fin (k + 1), 0 < j.val → ls.idx j = new.T.Z := by
        intro j hj
        obtain ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot _ _
          (new.T.vector_lt_of_P_lt_PZ ls _ add (hbound (by have := j.isLt; omega)))
        have hq1 : q.val = 1 := by
          by_cases h : q.val = 1
          · exact h
          · rw [new.Vec.ofFn_idx, ite_eq_right h] at hLt
            exact absurd hLt (new.T.lt_Z_false _)
        rw [new.Vec.ofFn_idx, ite_eq_left hq1] at hLt
        have hqz : ls.idx q = new.T.Z := by
          cases hc : ls.idx q with
          | Z => rfl
          | P w c =>
              rw [hc] at hLt
              obtain ⟨i, _, hi⟩ := new.Vec.compare_lt_has_pivot _ _
                (new.T.vector_lt_of_P_lt_PZ w _ c hLt)
              rw [new.Vec.ofFn_idx] at hi
              exact absurd hi (new.T.lt_Z_false _)
        by_cases heq : j.val = q.val
        · rw [Fin.eq_of_val_eq heq]; exact hqz
        · rw [hAbove j (by omega), new.Vec.ofFn_idx, ite_eq_right (by omega)]
      let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
      obtain ⟨n, hn⟩ := hLF (ls.idx i0)
      refine ⟨n, lt_PZ_of_pivot _ _ _ i0 (fun j (hj : 0 < j.val) => ?_)
        (by simpa only [new.Vec.ofFn_idx, show i0.val = 0 from rfl, ite_true] using hn)⟩
      rw [new.Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hj)]
      exact hzero j hj

/-- Legacy OT terms are exactly the indexed normal forms below the countable bound. -/
theorem OT_iff_NF_src (k : Nat) (s : new.T (k + 1)) :
    new.T.isOT (k + 1) s ↔ new.T.isNF s ∧ (1 < k + 1 → s < new.T.otBound (k + 1)) := by
  refine ⟨new.T.isOT_sound_bound (k + 1) s, fun h => ?_⟩
  obtain ⟨n, hn⟩ := base_cofinal_src k s h.1 h.2
  exact isOT_downward_src _ s (new.T.isOT.base_succ k n) h.1 (Or.inl hn)

end LegacyTranslation

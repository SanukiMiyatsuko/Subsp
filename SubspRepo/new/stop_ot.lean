import Subsp.new.stop_nf_order

/-! OT bases, cofinality, downward closure, and characterization by bounded normal forms. -/

/-! Finite terms and the defining cofinal bases. -/

section OTBases

open T

theorem ot_new_ofNat_step_lt {lam : Nat} (n : Nat) :
    new.T.ofNat (lam := lam) n < new.T.ofNat (lam := lam) (n + 1) := by
  induction n with
  | zero =>
      change new.T.Z < new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z
      rfl
  | succ n ih =>
      rw [new.T.ofNat, new.T.ofNat]
      exact new.T.P_tail_lt (new.Vec.ofFn lam (fun _ => new.T.Z))
        (new.T.ofNat n) (new.T.ofNat (n + 1)) ih

theorem ot_NFComp_P {lam : Nat} (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hv : ∀ i, new.T.isNFComp (v.idx i) ∧ v.idx i < new.T.P v a)
    (ha : new.T.isNFComp a) (hh : new.T.head a ≤ new.T.P v new.T.Z)
    (hlt : a < new.T.P v a) : new.T.isNFComp (new.T.P v a) := by
  have hc : ∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x := by
    intro x hx
    cases new.Vec.mem_toList_exists_idx v x hx with
    | intro i hi => rw [← hi]; exact (hv i).1
  refine ⟨new.T.isNF.p v a (fun x hx => (hc x hx).1) ha.1
    (fun x hx => (hc x hx).2) hh, ?_⟩
  intro y hy
  cases (new.T.mem_G_P v a y).mp hy with
  | inl hvec =>
      cases hvec with
      | intro i hi =>
          cases hi with
          | inl heq => rw [heq]; exact (hv i).2
          | inr hG => exact strict_partial_order.trans y (v.idx i) _ ((hv i).1.2 y hG) (hv i).2
  | inr htail => exact strict_partial_order.trans y a _ (ha.2 y htail) hlt

theorem ot_new_ofNat_NFComp {lam : Nat} (n : Nat) :
    new.T.isNFComp (new.T.ofNat (lam := lam) n) := by
  induction n with
  | zero => exact new.T.isNFComp_Z
  | succ n ih =>
      apply ot_NFComp_P (new.Vec.ofFn lam (fun _ => new.T.Z)) (new.T.ofNat n)
      · intro i
        rw [new.Vec.ofFn_idx]
        exact ⟨new.T.isNFComp_Z, rfl⟩
      · exact ih
      · cases n with
        | zero => exact new.T.Z_le _
        | succ n => exact new.T.le_refl _
      · exact ot_new_ofNat_step_lt n
theorem ot_new_LF_step_lt (lam n : Nat) :
    new.T.LF lam n < new.T.LF lam (n + 1) := by
  induction n with
  | zero =>
      cases lam with
      | zero =>
          change new.T.Z < new.T.P new.Vec.nil new.T.Z
          rfl
      | succ k =>
          change new.T.Z < new.T.P
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.Z else new.T.Z)) new.T.Z
          rfl
  | succ n ih =>
      cases lam with
      | zero =>
          rw [new.T.LF, new.T.LF]
          exact new.T.P_tail_lt new.Vec.nil (new.T.LF 0 n) (new.T.LF 0 (n + 1)) ih
      | succ k =>
          rw [new.T.LF, new.T.LF]
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.LF (k + 1) n else new.T.Z))
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.LF (k + 1) (n + 1) else new.T.Z))
            (Fin.last k)
          · intro j hj
            have hjle : j.val ≤ k := Nat.lt_succ_iff.mp j.isLt
            have hnot : ¬ k < j.val := Nat.not_lt_of_ge hjle
            exact False.elim (hnot hj)
          · rw [new.Vec.ofFn_idx, new.Vec.ofFn_idx]
            have heq : (Fin.last k : Fin (k + 1)) = k := rfl
            rw [ite_eq_left heq, ite_eq_left heq]
            exact ih

theorem ot_new_LF_NFComp (lam n : Nat) :
    new.T.isNFComp (new.T.LF lam n) := by
  induction n with
  | zero => exact new.T.isNFComp_Z
  | succ n ih =>
      cases lam with
      | zero =>
          apply ot_NFComp_P new.Vec.nil (new.T.LF 0 n)
          · intro i
            exact i.elim0
          · exact ih
          · cases n with
            | zero => exact new.T.Z_le _
            | succ n => exact new.T.le_refl _
          · exact ot_new_LF_step_lt 0 n
      | succ k =>
          apply ot_NFComp_P
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.LF (k + 1) n else new.T.Z))
            new.T.Z
          · intro i
            rw [new.Vec.ofFn_idx]
            apply Decidable.byCases (p := i.val = k)
            · intro hi
              rw [ite_eq_left hi]
              exact ⟨ih, ot_new_LF_step_lt (k + 1) n⟩
            · intro hi
              rw [ite_eq_right hi]
              exact ⟨new.T.isNFComp_Z, rfl⟩
          · exact new.T.isNFComp_Z
          · exact new.T.Z_le _
          · rfl
theorem ot_new_base_succ_NF (k n : Nat) :
    new.T.isNF
      (new.T.P
        (new.Vec.ofFn (k + 1)
          (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
        new.T.Z) := by
  apply new.T.isNF_PZ_of_coords
  intro i
  rw [new.Vec.ofFn_idx]
  apply Decidable.byCases (p := i.val = 0)
  · intro hi
    rw [ite_eq_left hi]
    exact (ot_new_LF_NFComp (k + 1) n)
  · intro hi
    rw [ite_eq_right hi]
    exact new.T.isNFComp_Z

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
  let q : Fin (k + 1) := ⟨1, hk⟩
  apply new.Vec.compare_lt_of_pivot
    (new.Vec.ofFn (k + 1)
      (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
    (new.Vec.ofFn (k + 1)
      (fun i => if i.val = 1 then
        new.T.P (new.Vec.ofFn (k + 1) (fun _ => new.T.Z)) new.T.Z
      else new.T.Z)) q
  · intro j hj
    rw [new.Vec.ofFn_idx, new.Vec.ofFn_idx]
    have hj0 : j.val ≠ 0 := by
      intro heq
      rw [heq] at hj
      exact Nat.not_lt_zero 1 hj
    have hj1 : j.val ≠ 1 := by
      intro heq
      rw [heq] at hj
      exact Nat.lt_irrefl 1 hj
    rw [ite_eq_right hj0, ite_eq_right hj1]
  · rw [new.Vec.ofFn_idx, new.Vec.ofFn_idx]
    have hq0 : q.val ≠ 0 := by
      intro h
      change (1 : Nat) = 0 at h
      cases h
    have hq1 : q.val = 1 := rfl
    rw [ite_eq_right hq0, ite_eq_left hq1]
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
  | base_0 n =>
      constructor
      · exact (ot_new_LF_NFComp 0 n).1
      · intro h
        exact False.elim (Nat.not_lt_zero 1 h)
  | base_succ k n =>
      constructor
      · exact ot_new_base_succ_NF k n
      · intro hk
        exact ot_new_base_succ_bound k n hk
  | step lam a _ n ih =>
      constructor
      · apply new.T.fund_NF_closed a (new.T.ofNat n) ih.1
        intro _
        exact ot_new_ofNat_NFComp n
      · intro hlam
        apply Decidable.byCases (p := a = new.T.Z)
        · intro haz
          rw [haz, new.T.fund]
          rfl
        · intro haz
          have hfall : new.T.fund a (new.T.ofNat n) < a :=
            new.T.fund_lt_self a (new.T.ofNat n) haz
          exact strict_partial_order.trans
            (new.T.fund a (new.T.ofNat n)) a
            (new.T.P
              (new.Vec.ofFn lam
                (fun x => if x.val = 1 then
                  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z
                else new.T.Z))
              new.T.Z)
            hfall (ih.2 hlam)

theorem ot_new_LF_cofinal (lam : Nat) (s : new.T lam)
    (hs : new.T.isNF s) : ∃ n : Nat, s < new.T.LF lam n := by
  induction hs with
  | z => exact ⟨1, ot_new_LF_step_lt lam 0⟩
  | p ls add _ _ _ _ ihls ihadd =>
      cases lam with
      | zero =>
          cases ls with
          | nil =>
              let ⟨n, hn⟩ := ihadd
              exact ⟨n + 1, new.T.P_tail_lt new.Vec.nil add (new.T.LF 0 n) hn⟩
      | succ k =>
          let q : Fin (k + 1) := Fin.last k
          let ⟨n, hn⟩ := ihls (ls.idx q) (new.Vec.idx_mem_toList ls q)
          refine ⟨n + 1, ?_⟩
          rw [new.T.LF]
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot ls
            (new.Vec.ofFn (k + 1)
              (fun i => if i.val = k then new.T.LF (k + 1) n else new.T.Z)) q
          · intro j hj
            exact False.elim (Nat.not_lt_of_ge (Nat.lt_succ_iff.mp j.isLt) hj)
          · rw [new.Vec.ofFn_idx, ite_eq_left (show q.val = k from rfl)]
            exact hn

end OTBases

/-! Successor fundamental sequences and multiplication. -/

section SuccessorCofinality

open T

theorem ot_lt_Z_inv {lam : Nat} (x : new.T lam) (h : x < new.T.Z) : False := by
  cases x with
  | Z =>
      change Ordering.eq = Ordering.lt at h
      cases h
  | P ls add =>
      change Ordering.gt = Ordering.lt at h
      cases h

theorem ot_vector_lt_of_P_lt_PZ {lam : Nat}
    (v w : new.Vec (new.T lam) lam) (a : new.T lam)
    (h : new.T.P v a < new.T.P w new.T.Z) : new.compareVec v w = Ordering.lt := by
  change (match new.compareVec v w with
    | Ordering.eq => new.compareT a new.T.Z
    | ord => ord) = Ordering.lt at h
  cases hc : new.compareVec v w with
  | lt => rfl
  | eq => rw [hc] at h; exact False.elim (ot_lt_Z_inv a h)
  | gt => rw [hc] at h; cases h

theorem ot_fund_one_upper {lam : Nat} :
    ∀ a : new.T lam, new.T.dom a = .one →
      ∀ b : new.T lam, b < a → b ≤ new.T.fund a new.T.Z := by
  intro a
  induction a using new.T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      intro hdom b _
      change new.Dom.zero = new.Dom.one at hdom
      cases hdom
  | P ls add _ ih =>
      intro hdom b hba
      apply Decidable.byCases (p := add = new.T.Z)
      · intro hadd
        cases hadd
        have hnone : new.T.domVecMinIdx ls = none := by
          cases hmin : new.T.domVecMinIdx ls with
          | none => exact rfl
          | some md =>
              let ⟨i, d⟩ := md
              have hd := hdom
              rw [new.T.dom, ite_eq_left rfl, hmin] at hd
              change
                (if d = new.Dom.one then
                  if i.val = 0 then new.Dom.omega else new.Dom.Omega
                else new.Dom.omega) = new.Dom.one at hd
              apply Decidable.byCases (p := d = new.Dom.one)
              · intro hd1
                rw [ite_eq_left hd1] at hd
                apply Decidable.byCases (p := i.val = 0)
                · intro hi0
                  rw [ite_eq_left hi0] at hd
                  cases hd
                · intro hi0
                  rw [ite_eq_right hi0] at hd
                  cases hd
              · intro hd1
                rw [ite_eq_right hd1] at hd
                cases hd
        rw [new.T.fund_PZ_none ls new.T.Z hnone]
        cases b with
        | Z => exact Or.inr rfl
        | P ws tail =>
            change
              (match new.compareVec ws ls with
              | Ordering.eq => new.compareT tail new.T.Z
              | ord => ord) = Ordering.lt at hba
            cases hc : new.compareVec ws ls with
            | lt =>
                let ⟨i, _, hiLt⟩ :=
                  new.Vec.compare_lt_has_pivot ws ls hc
                have hdz : new.T.dom (ls.idx i) = new.Dom.zero :=
                  new.T.domVecMinIdx_none_all_zero ls hnone i
                have hiz : ls.idx i = new.T.Z :=
                  new.T.dom_zero_eq_Z (ls.idx i) hdz
                rw [hiz] at hiLt
                exact False.elim (ot_lt_Z_inv (ws.idx i) hiLt)
            | eq =>
                rw [hc] at hba
                exact False.elim (ot_lt_Z_inv tail hba)
            | gt =>
                rw [hc] at hba
                cases hba
      · intro hadd
        have hdadd : new.T.dom add = .one := by
          rw [new.T.dom, ite_eq_right hadd] at hdom
          exact hdom
        have hrec := ih hdadd
        rw [new.T.fund_P_tail_eq ls add new.T.Z hadd]
        cases b with
        | Z => exact new.T.Z_le _
        | P ws tail =>
            change
              (match new.compareVec ws ls with
              | Ordering.eq => new.compareT tail add
              | ord => ord) = Ordering.lt at hba
            cases hc : new.compareVec ws ls with
            | lt =>
                apply Or.inl
                change
                  (match new.compareVec ws ls with
                  | Ordering.eq => new.compareT tail (new.T.fund add new.T.Z)
                  | ord => ord) = Ordering.lt
                rw [hc]
            | eq =>
                rw [hc] at hba
                have hvec : ws = ls := new.Vec_eq_sound ws ls hc
                cases hvec
                exact (new.T.P_same_le_iff ls tail (new.T.fund add new.T.Z)).mpr
                  (hrec tail hba)
            | gt =>
                rw [hc] at hba
                cases hba
  | nil => exact True.intro
  | snoc _ _ _ _ _ => exact True.intro

theorem ot_mul_cofinal {lam : Nat}
    (ls : new.Vec (new.T lam) lam) :
    ∀ b : new.T lam, new.T.isNF b →
      new.T.head b ≤ new.T.P ls new.T.Z →
      ∃ n : Nat, b < new.T.mul (new.T.P ls new.T.Z) (new.T.ofNat n) := by
  intro b hnf
  induction hnf with
  | z =>
      intro _
      exact ⟨1, rfl⟩
  | p ws tail _ _ _ htailHead _ ih =>
      intro hhead
      cases new.T.vector_rel_of_P_le_P ws ls new.T.Z new.T.Z hhead with
      | inl hvecLt =>
          exact ⟨1, new.T.P_lt_P_of_compareVec_lt ws ls tail new.T.Z hvecLt⟩
      | inr hvecEq =>
          cases hvecEq
          let ⟨k, hk⟩ := ih htailHead
          exact ⟨k + 1, new.T.P_tail_lt ls tail
            (new.T.mul (new.T.P ls new.T.Z) (new.T.ofNat k)) hk⟩

end SuccessorCofinality

/-! Vector comparison and the countable OT bound. -/

section OTBounds

open T

theorem oti_zeroVec_not_gt {lam : Nat} (v : new.Vec (new.T lam) lam) :
    new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) v ≠ Ordering.gt := by
  intro hgt
  have htot := new.Vec_total (new.Vec.ofFn lam (fun _ => new.T.Z)) v
  cases htot with
  | inl hlt =>
      rw [hgt] at hlt
      cases hlt
  | inr hr =>
      cases hr with
      | inl hvlt =>
          let ⟨i, _, hi⟩ := new.Vec.compare_lt_has_pivot v
            (new.Vec.ofFn lam (fun _ => new.T.Z)) hvlt
          rw [new.Vec.ofFn_idx] at hi
          exact ot_lt_Z_inv (v.idx i) hi
      | inr heq =>
          rw [← heq] at hgt
          have href := new.Vec_refl (n := lam) (new.Vec.ofFn lam (fun _ => new.T.Z))
          rw [href] at hgt
          cases hgt

open T

theorem ot_tail_lt_of_NF {lam : Nat} :
    ∀ (ls : new.Vec (new.T lam) lam) (add : new.T lam),
      new.T.isNF (new.T.P ls add) → add ≠ new.T.Z →
        add < new.T.P ls add := by
  intro ls add
  induction add using new.T.rec (motive_2 := fun _ _ => True) generalizing ls with
  | Z => intro _ hne; exact False.elim (hne rfl)
  | P ws tail _ ih =>
      intro hnf _
      cases hnf with
      | p _ _ _ hadd _ hhead =>
          cases new.T.vector_rel_of_P_le_P ws ls new.T.Z new.T.Z hhead with
          | inl hvec => exact new.T.P_lt_P_of_compareVec_lt ws ls tail _ hvec
          | inr hveq =>
              cases hveq
              apply new.T.P_tail_lt ws
              apply Decidable.byCases (p := tail = new.T.Z)
              · intro hz; rw [hz]; rfl
              · intro hz; exact ih ws hadd hz
  | nil => exact True.intro
  | snoc _ _ _ _ _ => exact True.intro
def ot_unit (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z

theorem ot_unit_le_P {lam : Nat} (ls : new.Vec (new.T lam) lam)
    (add : new.T lam) : ot_unit lam ≤ new.T.P ls add := by
  cases hc : new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
  | lt =>
      exact Or.inl (new.T.P_lt_P_of_compareVec_lt
        (new.Vec.ofFn lam (fun _ => new.T.Z)) ls new.T.Z add hc)
  | eq =>
      have hv : new.Vec.ofFn lam (fun _ => new.T.Z) = ls :=
        new.Vec_eq_sound _ _ hc
      rw [← hv]
      exact new.T.P_same_le_iff
        (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z add |>.mpr (new.T.Z_le add)
  | gt =>
      exact False.elim ((oti_zeroVec_not_gt ls) hc)

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
  have hvec := ot_vector_lt_of_P_lt_PZ ls _ add hb
  let ⟨q, hAbove, hLt⟩ := new.Vec.compare_lt_has_pivot ls
    (new.Vec.ofFn lam (fun x => if x.val = 1 then ot_unit lam else new.T.Z)) hvec
  have hqval : q.val = 1 := by
    apply Decidable.byCases (p := q.val = 1)
    · intro h; exact h
    · intro h
      rw [new.Vec.ofFn_idx, ite_eq_right h] at hLt
      exact False.elim (ot_lt_Z_inv (ls.idx q) hLt)
  rw [new.Vec.ofFn_idx, ite_eq_left hqval] at hLt
  have hqz : ls.idx q = new.T.Z := by
    apply Decidable.byCases (p := ls.idx q = new.T.Z)
    · intro hz; exact hz
    · intro hne
      exact False.elim (strict_partial_order.irrefl (ot_unit lam)
        (new.T.lt_of_le_of_lt _ _ _ (ot_unit_le_of_ne_Z _ hne) hLt))
  intro j hj
  have hqj : q.val ≤ j.val := by rw [hqval]; exact hj
  cases Nat.eq_or_lt_of_le hqj with
  | inl heq =>
      have hqeq : q = j := Fin.eq_of_val_eq heq
      rw [← hqeq]
      exact hqz
  | inr hlt =>
      have heq := hAbove j hlt
      have hj1 : j.val ≠ 1 := by rw [← hqval]; exact Nat.ne_of_gt hlt
      rw [new.Vec.ofFn_idx, ite_eq_right hj1] at heq
      exact heq

theorem ot_dom_Omega_not_countable {lam : Nat} :
    ∀ s : new.T lam, new.T.isNF s →
      (1 < lam → s < ot_bound lam) →
      new.T.dom s ≠ .Omega := by
  intro s
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      intro _ _ hOmega
      change new.Dom.zero = new.Dom.Omega at hOmega
      cases hOmega
  | P ls add _ ih =>
      intro hnf hbound hOmega
      apply Decidable.byCases (p := add = new.T.Z)
      · intro hadd
        cases hadd
        cases hmin : new.T.domVecMinIdx ls with
        | none =>
            have hd := hOmega
            rw [new.T.dom, ite_eq_left rfl, hmin] at hd
            change new.Dom.one = new.Dom.Omega at hd
            cases hd
        | some md =>
            let ⟨m, d⟩ := md
            have hd := hOmega
            rw [new.T.dom, ite_eq_left rfl, hmin] at hd
            change
              (if d = new.Dom.one then
                if m.val = 0 then new.Dom.omega else new.Dom.Omega
              else new.Dom.omega) = new.Dom.Omega at hd
            have hd1 : d = new.Dom.one := by
              apply Decidable.byCases (p := d = new.Dom.one)
              · intro h
                exact h
              · intro h
                rw [ite_eq_right h] at hd
                cases hd
            have hm0 : m.val ≠ 0 := by
              rw [ite_eq_left hd1] at hd
              intro hm
              rw [ite_eq_left hm] at hd
              cases hd
            have hmpos : 0 < m.val := Nat.pos_of_ne_zero hm0
            have hlam : 1 < lam := Nat.lt_of_le_of_lt hmpos m.isLt
            have hz := ot_bound_coords_zero ls new.T.Z (hbound hlam) m hmpos
            have hchildDom := (new.T.domVecMinIdx_some_spec ls m d hmin).2.1
            rw [hz, hd1] at hchildDom
            cases hchildDom
      · intro hadd
        have haddNF : new.T.isNF add := by
          cases hnf with
          | p _ _ _ ha _ _ => exact ha
        have haddLt : add < new.T.P ls add :=
          ot_tail_lt_of_NF ls add hnf hadd
        have haddBound : 1 < lam → add < ot_bound lam := by
          intro hlam
          exact strict_partial_order.trans add (new.T.P ls add) (ot_bound lam)
            haddLt (hbound hlam)
        have hrec := ih haddNF haddBound
        have hdadd : new.T.dom add = new.Dom.Omega := by
          rw [new.T.dom, ite_eq_right hadd] at hOmega
          exact hOmega
        exact hrec hdadd
  | nil => exact True.intro
  | snoc _ _ _ _ _ => exact True.intro

theorem ot_vec_ext {lam m : Nat} (v w : new.Vec (new.T lam) m)
    (h : ∀ i : Fin m, v.idx i = w.idx i) : v = w := by
  induction m with
  | zero =>
      cases v
      cases w
      rfl
  | succ k ih =>
      cases v with
      | snoc _ vs vx =>
        cases w with
        | snoc _ ws wx =>
          have hlast := h (Fin.last k)
          change
            (if hlt : k < k then vs.idx ⟨k, hlt⟩ else vx) =
            (if hlt : k < k then ws.idx ⟨k, hlt⟩ else wx) at hlast
          rw [dite_eq_right (Nat.lt_irrefl k), dite_eq_right (Nat.lt_irrefl k)] at hlast
          have hpref : ∀ i : Fin k, vs.idx i = ws.idx i := by
            intro i
            have hi := h i.castSucc
            change
              (if hlt : i.val < k then vs.idx ⟨i.val, hlt⟩ else vx) =
              (if hlt : i.val < k then ws.idx ⟨i.val, hlt⟩ else wx) at hi
            rw [dite_eq_left i.isLt, dite_eq_left i.isLt] at hi
            exact hi
          have hvw := ih vs ws hpref
          rw [hvw, hlast]

theorem ot_head_le_one_base {lam : Nat}
    (ls : new.Vec (new.T lam) lam) (m : Fin lam)
    (hmin : new.T.domVecMinIdx ls = some (m, new.Dom.one))
    (hm0 : m.val = 0)
    (b : new.T lam) (hb : new.T.isNF b)
    (hba : b < new.T.P ls new.T.Z) :
    new.T.head b ≤
      new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z := by
  cases b with
  | Z =>
      exact new.T.Z_le _
  | P ws tail =>
      have hvec := ot_vector_lt_of_P_lt_PZ ws ls tail hba
      let ⟨q, hqAbove, hqLt⟩ := new.Vec.compare_lt_has_pivot ws ls hvec
      apply Decidable.byCases (p := q.val = m.val)
      · intro hqm
        have hqeq : q = m := Fin.eq_of_val_eq hqm
        cases hqeq
        have hchildDom : new.T.dom (ls.idx m) = new.Dom.one :=
          (new.T.domVecMinIdx_some_spec ls m new.Dom.one hmin).2.1
        have hupper : ws.idx m ≤ new.T.fund (ls.idx m) new.T.Z :=
          ot_fund_one_upper (ls.idx m) hchildDom (ws.idx m) hqLt
        cases hupper with
        | inl hlt =>
            apply Or.inl
            apply new.T.P_lt_P_of_compareVec_lt
            apply new.Vec.compare_lt_of_pivot ws
              (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) m
            · intro j hmj
              have hjm : j.val ≠ m.val := Nat.ne_of_gt hmj
              rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
              exact hqAbove j hmj
            · rw [new.Vec.rplc_idx_same]
              exact hlt
        | inr heq =>
            have htermEq : ws.idx m = new.T.fund (ls.idx m) new.T.Z :=
              new.T_eq_sound _ _ heq
            have hvecEq : ws = ls.rplc m (new.T.fund (ls.idx m) new.T.Z) := by
              apply ot_vec_ext
              intro j
              apply Decidable.byCases (p := j.val = m.val)
              · intro hjm
                have hjEq : j = m := Fin.eq_of_val_eq hjm
                cases hjEq
                rw [new.Vec.rplc_idx_same]
                exact htermEq
              · intro hjm
                have hmj : m.val < j.val := by
                  have hmzero : m.val = 0 := hm0
                  rw [hmzero]
                  have hjpos : 0 < j.val := Nat.pos_of_ne_zero (by
                    intro hjz
                    apply hjm
                    rw [hmzero, hjz])
                  exact hjpos
                rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                exact hqAbove j hmj
            rw [hvecEq]
            exact new.T.le_refl _
      · intro hqm
        have hmq : m.val < q.val := by
          rw [hm0]
          have hq0 : q.val ≠ 0 := by
            intro hqz
            apply hqm
            rw [hm0, hqz]
          exact Nat.pos_of_ne_zero hq0
        apply Or.inl
        apply new.T.P_lt_P_of_compareVec_lt
        apply new.Vec.compare_lt_of_pivot ws
          (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) q
        · intro j hqj
          have hjm : j.val ≠ m.val := by
            exact Nat.ne_of_gt (Nat.lt_trans hmq hqj)
          rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
          exact hqAbove j hqj
        · have hqmne : q.val ≠ m.val := hqm
          rw [new.Vec.rplc_idx_of_ne ls m q _ hqmne]
          exact hqLt

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
  let F := fun x : new.T lam => new.T.fund a x
  let motive : Nat → Prop := fun n =>
    ∀ b : new.T lam, new.T.size b = n → new.T.isNFComp b → b < a →
      ∃ k : Nat, b < F (new.T.iter F (new.T.ofNat k))
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro b hbsize hbcomp hba
      have descend :
          ∀ cur : new.T lam,
            new.T.isNF cur → new.T.dom cur = .Omega →
            ∀ tgt : new.T lam, new.T.isNF tgt → tgt < cur →
              (∀ x : new.T lam, x ∈ new.T.G tgt → x ∈ new.T.G b) →
              ∃ k : Nat, tgt < new.T.fund cur
                (new.T.iter F (new.T.ofNat k)) := by
        intro cur
        induction cur using new.T.rec (motive_2 := fun _ _ => True) with
        | Z =>
            intro _ hcdom tgt _ _ _
            change new.Dom.zero = new.Dom.Omega at hcdom
            cases hcdom
        | P ls add _ dih =>
            intro hcnf hcdom tgt htgnf htgc hmem
            apply Decidable.byCases (p := add = new.T.Z)
            · intro hadd
              cases hadd
              cases hmin : new.T.domVecMinIdx ls with
              | none =>
                  have hh := hcdom
                  rw [new.T.dom, ite_eq_left rfl, hmin] at hh
                  change new.Dom.one = new.Dom.Omega at hh
                  cases hh
              | some md =>
                  cases md with
                  | mk mi d =>
                    have hh := hcdom
                    rw [new.T.dom, ite_eq_left rfl, hmin] at hh
                    change
                      (if d = new.Dom.one then
                        if mi.val = 0 then new.Dom.omega else new.Dom.Omega
                      else new.Dom.omega) = new.Dom.Omega at hh
                    have hd1 : d = new.Dom.one := by
                      apply Decidable.byCases (p := d = new.Dom.one)
                      · intro h
                        exact h
                      · intro h
                        rw [ite_eq_right h] at hh
                        cases hh
                    have hmi0 : mi.val ≠ 0 := by
                      rw [ite_eq_left hd1] at hh
                      intro hz
                      rw [ite_eq_left hz] at hh
                      cases hh
                    have hspec := new.T.domVecMinIdx_some_spec ls mi d hmin
                    have hchildDom : new.T.dom (ls.idx mi) = new.Dom.one := by
                      rw [hspec.2.1, hd1]
                    cases mi with
                    | mk mv mh =>
                        cases mv with
                        | zero => exact False.elim (hmi0 rfl)
                        | succ r =>
                            let mi' : Fin lam := ⟨r + 1, mh⟩
                            let mj : Fin lam := ⟨r, Nat.lt_of_succ_lt mh⟩
                            let base := ls.rplc mi'
                              (new.T.fund (ls.idx mi') new.T.Z)
                            cases tgt with
                            | Z =>
                                refine ⟨0, ?_⟩
                                have hne :
                                    new.T.fund (new.T.P ls new.T.Z)
                                        (new.T.iter F (new.T.ofNat 0)) ≠ new.T.Z :=
                                  new.T.fund_Omega_ne_Z (new.T.P ls new.T.Z)
                                    (new.T.iter F (new.T.ofNat 0)) hcdom
                                cases new.T.Z_le
                                    (new.T.fund (new.T.P ls new.T.Z)
                                      (new.T.iter F (new.T.ofNat 0))) with
                                | inl hlt => exact hlt
                                | inr heq =>
                                    have hz := new.T_eq_sound new.T.Z
                                      (new.T.fund (new.T.P ls new.T.Z)
                                        (new.T.iter F (new.T.ofNat 0))) heq
                                    exact False.elim (hne hz.symm)
                            | P ws tail =>
                                have hvec := ot_vector_lt_of_P_lt_PZ ws ls tail htgc
                                let ⟨q, hqAbove, hqLt⟩ :=
                                  new.Vec.compare_lt_has_pivot ws ls hvec
                                have hfundShape : ∀ z : new.T lam,
                                    new.T.fund (new.T.P ls new.T.Z) z =
                                      new.T.P (base.rplc mj z) new.T.Z := by
                                  intro z
                                  rw [new.T.fund, ite_eq_left rfl, hmin]
                                  rw [hd1]
                                  change
                                    new.T.P
                                      ((ls.rplc mi'
                                        (new.T.fund (ls.idx mi') new.T.Z)).rplc mj z)
                                      new.T.Z =
                                    new.T.P (base.rplc mj z) new.T.Z
                                  rfl
                                cases Nat.lt_trichotomy q.val (r + 1) with
                                | inl hqmi =>
                                    have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                                      hspec.2.2 q hqmi
                                    have hqz := new.T.dom_zero_eq_Z (ls.idx q) hqDom
                                    rw [hqz] at hqLt
                                    exact False.elim (ot_lt_Z_inv (ws.idx q) hqLt)
                                | inr hrel =>
                                    cases hrel with
                                    | inr hmiq =>
                                        refine ⟨0, ?_⟩
                                        rw [hfundShape]
                                        apply new.T.P_lt_P_of_compareVec_lt
                                        apply new.Vec.compare_lt_of_pivot ws
                                          (base.rplc mj
                                            (new.T.iter F (new.T.ofNat 0))) q
                                        · intro j hqj
                                          have hjmi : j.val ≠ r + 1 :=
                                            Nat.ne_of_gt (Nat.lt_trans hmiq hqj)
                                          have hjmj : j.val ≠ r :=
                                            Nat.ne_of_gt
                                              (Nat.lt_trans (Nat.lt_succ_self r)
                                                (Nat.lt_trans hmiq hqj))
                                          unfold base
                                          rw [new.Vec.rplc_idx_of_ne _ mj j _ hjmj]
                                          rw [new.Vec.rplc_idx_of_ne ls mi' j _ hjmi]
                                          exact hqAbove j hqj
                                        · have hqmiNe : q.val ≠ r + 1 := Nat.ne_of_gt hmiq
                                          have hqmjNe : q.val ≠ r := by
                                            intro hqr
                                            rw [hqr] at hmiq
                                            exact Nat.lt_irrefl r
                                              (Nat.lt_trans (Nat.lt_succ_self r) hmiq)
                                          unfold base
                                          rw [new.Vec.rplc_idx_of_ne _ mj q _ hqmjNe]
                                          rw [new.Vec.rplc_idx_of_ne ls mi' q _ hqmiNe]
                                          exact hqLt
                                    | inl hqmiEq =>
                                        have hqEq : q = mi' := by
                                          apply Fin.eq_of_val_eq
                                          exact hqmiEq
                                        cases hqEq
                                        have hupper : ws.idx mi' ≤
                                            new.T.fund (ls.idx mi') new.T.Z :=
                                          ot_fund_one_upper (ls.idx mi') hchildDom
                                            (ws.idx mi') hqLt
                                        cases hupper with
                                        | inl hstrict =>
                                            refine ⟨0, ?_⟩
                                            rw [hfundShape]
                                            apply new.T.P_lt_P_of_compareVec_lt
                                            apply new.Vec.compare_lt_of_pivot ws
                                              (base.rplc mj
                                                (new.T.iter F (new.T.ofNat 0))) mi'
                                            · intro j hmij
                                              have hjmj : j.val ≠ r := by
                                                exact Nat.ne_of_gt
                                                  (Nat.lt_trans (Nat.lt_succ_self r) hmij)
                                              have hjmi : j.val ≠ r + 1 := Nat.ne_of_gt hmij
                                              unfold base
                                              rw [new.Vec.rplc_idx_of_ne _ mj j _ hjmj]
                                              rw [new.Vec.rplc_idx_of_ne ls mi' j _ hjmi]
                                              exact hqAbove j hmij
                                            · have hmjmi : mi'.val ≠ mj.val := by
                                                change r + 1 ≠ r
                                                exact Nat.ne_of_gt (Nat.lt_succ_self r)
                                              rw [new.Vec.rplc_idx_of_ne base mj mi' _ hmjmi]
                                              unfold base
                                              rw [new.Vec.rplc_idx_same]
                                              exact hstrict
                                        | inr heq =>
                                            have hcoordEq : ws.idx mi' =
                                                new.T.fund (ls.idx mi') new.T.Z :=
                                              new.T_eq_sound _ _ heq
                                            let c0 := ws.idx mj
                                            have hcMemTgt : c0 ∈ new.T.G (new.T.P ws tail) := by
                                              apply (new.T.mem_G_P ws tail c0).mpr
                                              exact Or.inl ⟨mj, Or.inl rfl⟩
                                            have hcMemB : c0 ∈ new.T.G b :=
                                              hmem c0 hcMemTgt
                                            have hcComp : new.T.isNFComp c0 :=
                                              new.T.isNF_G_isNFComp b hbcomp.1 c0 hcMemB
                                            have hcLtB : c0 < b := hbcomp.2 c0 hcMemB
                                            have hcLtA : c0 < a :=
                                              strict_partial_order.trans c0 b a hcLtB hba
                                            have hcSize : new.T.size c0 < n := by
                                              have hs := new.T.G_size_lt b c0 hcMemB
                                              rw [hbsize] at hs
                                              exact hs
                                            let ⟨k, hk⟩ :=
                                              ih (new.T.size c0) hcSize c0 rfl hcComp hcLtA
                                            refine ⟨k + 1, ?_⟩
                                            rw [hfundShape]
                                            apply new.T.P_lt_P_of_compareVec_lt
                                            apply new.Vec.compare_lt_of_pivot ws
                                              (base.rplc mj
                                                (new.T.iter F (new.T.ofNat (k + 1)))) mj
                                            · intro j hmjj
                                              have hmiLeJ : r + 1 ≤ j.val :=
                                                Nat.succ_le_of_lt hmjj
                                              cases Nat.eq_or_lt_of_le hmiLeJ with
                                              | inl hEq =>
                                                  have hjmi : j = mi' := by
                                                    apply Fin.eq_of_val_eq
                                                    exact hEq.symm
                                                  cases hjmi
                                                  have hmjmi : mi'.val ≠ mj.val := by
                                                    change r + 1 ≠ r
                                                    exact Nat.ne_of_gt (Nat.lt_succ_self r)
                                                  rw [new.Vec.rplc_idx_of_ne base mj mi' _ hmjmi]
                                                  unfold base
                                                  rw [new.Vec.rplc_idx_same]
                                                  exact hcoordEq
                                              | inr hmiJ =>
                                                  have hjmj : j.val ≠ r :=
                                                    Nat.ne_of_gt (Nat.lt_trans
                                                      (Nat.lt_succ_self r) hmiJ)
                                                  have hjmi : j.val ≠ r + 1 := Nat.ne_of_gt hmiJ
                                                  unfold base
                                                  rw [new.Vec.rplc_idx_of_ne _ mj j _ hjmj]
                                                  rw [new.Vec.rplc_idx_of_ne ls mi' j _ hjmi]
                                                  exact hqAbove j hmiJ
                                            · rw [new.Vec.rplc_idx_same]
                                              change c0 < new.T.iter F (new.T.ofNat (k + 1))
                                              rw [ot_iter_ofNat_succ a k]
                                              exact hk
            · intro hadd
              have haddDom : new.T.dom add = new.Dom.Omega := by
                rw [new.T.dom, ite_eq_right hadd] at hcdom
                exact hcdom
              have haddNF : new.T.isNF add := by
                cases hcnf with
                | p _ _ _ haTail _ _ => exact haTail
              cases tgt with
              | Z =>
                  refine ⟨0, ?_⟩
                  rw [new.T.fund_P_tail_eq ls add
                    (new.T.iter F (new.T.ofNat 0)) hadd]
                  rfl
              | P ws tail =>
                  change
                    (match new.compareVec ws ls with
                    | Ordering.eq => new.compareT tail add
                    | ord => ord) = Ordering.lt at htgc
                  cases hc : new.compareVec ws ls with
                  | lt =>
                      refine ⟨0, ?_⟩
                      rw [new.T.fund_P_tail_eq ls add
                        (new.T.iter F (new.T.ofNat 0)) hadd]
                      exact new.T.P_lt_P_of_compareVec_lt ws ls tail
                        (new.T.fund add (new.T.iter F (new.T.ofNat 0))) hc
                  | gt =>
                      rw [hc] at htgc
                      cases htgc
                  | eq =>
                      rw [hc] at htgc
                      have hws : ws = ls := new.Vec_eq_sound ws ls hc
                      cases hws
                      have htailNF : new.T.isNF tail := by
                        cases htgnf with
                        | p _ _ _ ht _ _ => exact ht
                      have hmemTail :
                          ∀ x : new.T lam, x ∈ new.T.G tail → x ∈ new.T.G b := by
                        intro x hx
                        apply hmem x
                        apply (new.T.mem_G_P ls tail x).mpr
                        exact Or.inr hx
                      let ⟨k, hk⟩ :=
                        dih haddNF haddDom
                          tail htailNF htgc hmemTail
                      refine ⟨k, ?_⟩
                      rw [new.T.fund_P_tail_eq ls add
                        (new.T.iter F (new.T.ofNat k)) hadd]
                      exact new.T.P_tail_lt ls tail
                        (new.T.fund add (new.T.iter F (new.T.ofNat k))) hk
        | nil => exact True.intro
        | snoc _ _ _ _ _ => exact True.intro
      exact descend a ha.1 hd b hbcomp.1 hba
        (fun x hx => hx))
  intro b hb hba
  exact main (new.T.size b) b rfl hb hba

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
  | z =>
      intro hdom
      cases hdom
  | p ls add hvNF haddNF hvG hhead ihls ihadd =>
      intro hdom b hb hba
      have hcoords := fun i =>
        And.intro (hvNF (ls.idx i) (new.Vec.idx_mem_toList ls i))
          (hvG (ls.idx i) (new.Vec.idx_mem_toList ls i))
      apply Decidable.byCases (p := add = new.T.Z)
      · intro hadd
        cases hadd
        cases hmin : new.T.domVecMinIdx ls with
        | none =>
            have hh := hdom
            rw [new.T.dom, ite_eq_left rfl, hmin] at hh
            change new.Dom.one = new.Dom.omega at hh
            cases hh
        | some md =>
            cases md with
            | mk m d =>
              have hspec := new.T.domVecMinIdx_some_spec ls m d hmin
              have hh := hdom
              rw [new.T.dom, ite_eq_left rfl, hmin] at hh
              cases d with
              | zero =>
                  exact False.elim (hspec.1 rfl)
              | one =>
                  change
                    (if m.val = 0 then new.Dom.omega else new.Dom.Omega) =
                      new.Dom.omega at hh
                  have hm0 : m.val = 0 := by
                    apply Decidable.byCases (p := m.val = 0)
                    · intro hm
                      exact hm
                    · intro hm
                      rw [ite_eq_right hm] at hh
                      cases hh
                  have hhead := ot_head_le_one_base ls m hmin hm0 b hb hba
                  let ⟨k, hk⟩ :=
                    ot_mul_cofinal
                      (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) b hb hhead
                  refine ⟨k, ?_⟩
                  cases m with
                  | mk mv mh =>
                      change mv = 0 at hm0
                      cases hm0
                      rw [new.T.fund, ite_eq_left rfl, hmin]
                      exact hk
              | omega =>
                  have hchildDom : new.T.dom (ls.idx m) = new.Dom.omega :=
                    hspec.2.1
                  cases b with
                  | Z =>
                      refine ⟨0, ?_⟩
                      rw [new.T.fund, ite_eq_left rfl, hmin]
                      rfl
                  | P ws tail =>
                      have hvec := ot_vector_lt_of_P_lt_PZ ws ls tail hba
                      let ⟨q, hqAbove, hqLt⟩ :=
                        new.Vec.compare_lt_has_pivot ws ls hvec
                      cases Nat.lt_trichotomy q.val m.val with
                      | inl hqm =>
                          have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                            hspec.2.2 q hqm
                          have hqz := new.T.dom_zero_eq_Z (ls.idx q) hqDom
                          rw [hqz] at hqLt
                          exact False.elim (ot_lt_Z_inv (ws.idx q) hqLt)
                      | inr hrel =>
                          cases hrel with
                          | inr hmq =>
                              refine ⟨0, ?_⟩
                              rw [new.T.fund, ite_eq_left rfl, hmin]
                              apply new.T.P_lt_P_of_compareVec_lt
                              apply new.Vec.compare_lt_of_pivot ws
                                (ls.rplc m (new.T.fund (ls.idx m) (new.T.ofNat 0))) q
                              · intro j hqj
                                have hjm : j.val ≠ m.val :=
                                  Nat.ne_of_gt (Nat.lt_trans hmq hqj)
                                rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                exact hqAbove j hqj
                              · have hqmNe : q.val ≠ m.val := Nat.ne_of_gt hmq
                                rw [new.Vec.rplc_idx_of_ne ls m q _ hqmNe]
                                exact hqLt
                          | inl hqmEq =>
                              have hqEq : q = m := Fin.eq_of_val_eq hqmEq
                              cases hqEq
                              have htargetComp : new.T.isNFComp (ws.idx m) :=
                                new.T.isNF_P_coord_NFComp ws tail hb m
                              let ⟨k, hk⟩ :=
                                ihls (ls.idx m) (new.Vec.idx_mem_toList ls m) hchildDom
                                  (ws.idx m) htargetComp.1 hqLt
                              refine ⟨k, ?_⟩
                              rw [new.T.fund, ite_eq_left rfl, hmin]
                              apply new.T.P_lt_P_of_compareVec_lt
                              apply new.Vec.compare_lt_of_pivot ws
                                (ls.rplc m (new.T.fund (ls.idx m) (new.T.ofNat k))) m
                              · intro j hmj
                                have hjm : j.val ≠ m.val := Nat.ne_of_gt hmj
                                rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                exact hqAbove j hmj
                              · rw [new.Vec.rplc_idx_same]
                                exact hk
              | Omega =>
                  have hchildDom : new.T.dom (ls.idx m) = new.Dom.Omega :=
                    hspec.2.1
                  have hchildComp : new.T.isNFComp (ls.idx m) := hcoords m
                  cases b with
                  | Z =>
                      refine ⟨0, ?_⟩
                      rw [new.T.fund, ite_eq_left rfl, hmin]
                      rfl
                  | P ws tail =>
                      have hvec := ot_vector_lt_of_P_lt_PZ ws ls tail hba
                      let ⟨q, hqAbove, hqLt⟩ :=
                        new.Vec.compare_lt_has_pivot ws ls hvec
                      cases Nat.lt_trichotomy q.val m.val with
                      | inl hqm =>
                          have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                            hspec.2.2 q hqm
                          have hqz := new.T.dom_zero_eq_Z (ls.idx q) hqDom
                          rw [hqz] at hqLt
                          exact False.elim (ot_lt_Z_inv (ws.idx q) hqLt)
                      | inr hrel =>
                          cases hrel with
                          | inr hmq =>
                              refine ⟨0, ?_⟩
                              rw [new.T.fund, ite_eq_left rfl, hmin]
                              apply new.T.P_lt_P_of_compareVec_lt
                              apply new.Vec.compare_lt_of_pivot ws
                                (ls.rplc m
                                  (new.T.fund (ls.idx m)
                                    (new.T.iter (fun x => new.T.fund (ls.idx m) x)
                                      (new.T.ofNat 0)))) q
                              · intro j hqj
                                have hjm : j.val ≠ m.val :=
                                  Nat.ne_of_gt (Nat.lt_trans hmq hqj)
                                rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                exact hqAbove j hqj
                              · have hqmNe : q.val ≠ m.val := Nat.ne_of_gt hmq
                                rw [new.Vec.rplc_idx_of_ne ls m q _ hqmNe]
                                exact hqLt
                          | inl hqmEq =>
                              have hqEq : q = m := Fin.eq_of_val_eq hqmEq
                              cases hqEq
                              have htargetComp : new.T.isNFComp (ws.idx m) :=
                                new.T.isNF_P_coord_NFComp ws tail hb m
                              let ⟨k, hk⟩ :=
                                ot_iteration_cofinal (ls.idx m) hchildComp hchildDom
                                  (ws.idx m) htargetComp hqLt
                              refine ⟨k, ?_⟩
                              rw [new.T.fund, ite_eq_left rfl, hmin]
                              apply new.T.P_lt_P_of_compareVec_lt
                              apply new.Vec.compare_lt_of_pivot ws
                                (ls.rplc m
                                  (new.T.fund (ls.idx m)
                                    (new.T.iter (fun x => new.T.fund (ls.idx m) x)
                                      (new.T.ofNat k)))) m
                              · intro j hmj
                                have hjm : j.val ≠ m.val := Nat.ne_of_gt hmj
                                rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                exact hqAbove j hmj
                              · rw [new.Vec.rplc_idx_same]
                                exact hk
      · intro hadd
        have haddDom : new.T.dom add = new.Dom.omega := by
          rw [new.T.dom, ite_eq_right hadd] at hdom
          exact hdom
        cases b with
        | Z =>
            refine ⟨0, ?_⟩
            rw [new.T.fund_P_tail_eq ls add (new.T.ofNat 0) hadd]
            rfl
        | P ws tail =>
            change
              (match new.compareVec ws ls with
              | Ordering.eq => new.compareT tail add
              | ord => ord) = Ordering.lt at hba
            cases hc : new.compareVec ws ls with
            | lt =>
                refine ⟨0, ?_⟩
                rw [new.T.fund_P_tail_eq ls add (new.T.ofNat 0) hadd]
                exact new.T.P_lt_P_of_compareVec_lt ws ls tail
                  (new.T.fund add (new.T.ofNat 0)) hc
            | gt =>
                rw [hc] at hba
                cases hba
            | eq =>
                rw [hc] at hba
                have hws : ws = ls := new.Vec_eq_sound ws ls hc
                cases hws
                have htailNF : new.T.isNF tail := by
                  cases hb with
                  | p _ _ _ ht _ _ => exact ht
                let ⟨k, hk⟩ :=
                  ihadd haddDom
                    tail htailNF hba
                refine ⟨k, ?_⟩
                rw [new.T.fund_P_tail_eq ls add (new.T.ofNat k) hadd]
                exact new.T.P_tail_lt ls tail (new.T.fund add (new.T.ofNat k)) hk

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
  cases hd : new.T.dom a with
  | zero =>
      have haz : a = new.T.Z := new.T.dom_zero_eq_Z a hd
      rw [haz] at hba
      exact False.elim (ot_lt_Z_inv b hba)
  | one =>
      have hane : a ≠ new.T.Z := by
        intro haz
        rw [haz] at hd
        cases hd
      refine ⟨0, new.T.fund_lt_self a (new.T.ofNat 0) hane, ?_⟩
      rw [new.T.fund_one_arg_irrel a (new.T.ofNat 0) hd]
      exact ot_fund_one_upper a hd b hba
  | omega =>
      let ⟨n, hn⟩ := ot_fund_omega_cofinal a ha hd b hb hba
      have hane : a ≠ new.T.Z := by
        intro haz
        rw [haz] at hd
        cases hd
      exact ⟨n, new.T.fund_lt_self a (new.T.ofNat n) hane, Or.inl hn⟩
  | Omega =>
      exact False.elim ((ot_dom_Omega_not_countable a ha hbound) hd)

theorem ot_new_isOT_downward {lam : Nat}
    (a b : new.T lam) (ha : new.T.isOT lam a)
    (hb : new.T.isNF b) (hba : b ≤ a) :
    new.T.isOT lam b := by
  let NF := {x : new.T lam // new.T.isNF x}
  have main :
      ∀ a0 : NF, new.T.isOT lam a0.1 →
        ∀ b0 : new.T lam, new.T.isNF b0 → b0 ≤ a0.1 →
          new.T.isOT lam b0 := by
    intro a0
    induction a0 using (ot_new_well_founded_NF lam).induction with
    | h a0 ih =>
        intro ha0 b0 hb0 hba0
        cases hba0 with
        | inl hlt =>
            have hsound := ot_new_isOT_sound lam a0.1 ha0
            let ⟨n, hfall, hupper⟩ :=
              ot_fund_countable_cofinal a0.1 b0 a0.2 hb0
                hsound.2 hlt
            have hn : new.T.isOT lam (new.T.fund a0.1 (new.T.ofNat n)) :=
              new.T.isOT.step lam a0.1 ha0 n
            have hfnf : new.T.isNF (new.T.fund a0.1 (new.T.ofNat n)) :=
              (ot_new_isOT_sound lam _ hn).1
            exact ih ⟨new.T.fund a0.1 (new.T.ofNat n), hfnf⟩
              hfall hn b0 hb0 hupper
        | inr heq =>
            have hterm : b0 = a0.1 := new.T_eq_sound b0 a0.1 heq
            rw [hterm]
            exact ha0
  have hanf : new.T.isNF a := (ot_new_isOT_sound lam a ha).1
  exact main ⟨a, hanf⟩ ha b hb hba

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
                  ot_bound_coords_zero ls add (hbound hlam) j hij
                rw [new.Vec.ofFn_idx]
                have hj0 : j.val ≠ 0 := Nat.ne_of_gt hij
                rw [ite_eq_right hj0]
                exact hz
          · rw [new.Vec.ofFn_idx]
            have hi0 : i0.val = 0 := rfl
            rw [ite_eq_left hi0]
            exact hn

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
        cases ot_base_succ_cofinal k s h.1 h.2 with
        | intro n hn =>
            exact ot_new_isOT_downward
              (new.T.P
                (new.Vec.ofFn (k + 1)
                  (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
                new.T.Z)
              s (new.T.isOT.base_succ k n) h.1 (Or.inl hn)

def new.T.OT (lam : Nat) := { s : T lam // isOT lam s }

theorem wellfounded_OT (lam : Nat) : WellFounded (fun s t : new.T.OT lam => s.val < t.val) := by
  exact InvImage.wf
    (fun s : new.T.OT lam => (⟨s.val, (ot_new_isOT_sound lam s.val s.property).1⟩ : new.T.NF lam))
    (wellfounded_NF lam)

end OTCharacterization

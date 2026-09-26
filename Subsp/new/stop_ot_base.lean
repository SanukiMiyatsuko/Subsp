import Subsp.new.stop_nf_order_c

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

theorem ot_new_ofNat_NFComp {lam : Nat} (n : Nat) :
    new.T.isNFComp (new.T.ofNat (lam := lam) n) := by
  induction n with
  | zero =>
      exact new.T.isNFComp_Z
  | succ n ih =>
      let zs : new.Vec (new.T lam) lam :=
        new.Vec.ofFn lam (fun _ => new.T.Z)
      have hnf : new.T.isNF (new.T.P zs (new.T.ofNat n)) := by
        apply new.T.isNF.p zs (new.T.ofNat n)
        · intro x hx
          let ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx zs x hx
          have hz : zs.idx i = new.T.Z := by
            unfold zs
            rw [new.Vec.ofFn_idx]
          rw [← hi, hz]
          exact new.T.isNF.z
        · exact ih.1
        · intro x hx y hy
          let ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx zs x hx
          have hz : zs.idx i = new.T.Z := by
            unfold zs
            rw [new.Vec.ofFn_idx]
          rw [← hi, hz] at hy
          change y ∈ ([] : List (new.T lam)) at hy
          cases hy
        · cases n with
          | zero =>
              change new.T.Z ≤ new.T.P zs new.T.Z
              exact new.T.Z_le (new.T.P zs new.T.Z)
          | succ k =>
              change new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z ≤
                new.T.P zs new.T.Z
              unfold zs
              exact new.T.le_refl (new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z)
      constructor
      · change new.T.isNF (new.T.P zs (new.T.ofNat n))
        exact hnf
      · intro y hy
        change y ∈ new.T.G (new.T.P zs (new.T.ofNat n)) at hy
        cases (new.T.mem_G_P zs (new.T.ofNat n) y).mp hy with
        | inl hv =>
            let ⟨i, hcase⟩ := hv
            have hz : zs.idx i = new.T.Z := by
              unfold zs
              rw [new.Vec.ofFn_idx]
            cases hcase with
            | inl heq =>
                rw [heq, hz]
                rfl
            | inr hG =>
                rw [hz] at hG
                change y ∈ ([] : List (new.T lam)) at hG
                cases hG
        | inr hadd =>
            have hylt : y < new.T.ofNat n := ih.2 y hadd
            have hstep : new.T.ofNat (lam := lam) n < new.T.ofNat (lam := lam) (n + 1) :=
              ot_new_ofNat_step_lt (lam := lam) n
            change y < new.T.P zs (new.T.ofNat n)
            have htrans : y < new.T.ofNat (lam := lam) (n + 1) :=
              strict_partial_order.trans y (new.T.ofNat (lam := lam) n) (new.T.ofNat (lam := lam) (n + 1)) hylt hstep
            change y < new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) (new.T.ofNat n) at htrans
            exact htrans

#print axioms ot_new_ofNat_NFComp

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

#print axioms ot_new_LF_step_lt

theorem ot_new_LF_NFComp (lam n : Nat) :
    new.T.isNFComp (new.T.LF lam n) := by
  induction n with
  | zero =>
      exact new.T.isNFComp_Z
  | succ n ih =>
      cases lam with
      | zero =>
          have hnf : new.T.isNF (new.T.P new.Vec.nil (new.T.LF 0 n)) := by
            apply new.T.isNF.p new.Vec.nil (new.T.LF 0 n)
            · intro x hx
              cases hx
            · exact ih.1
            · intro x hx
              cases hx
            · cases n with
              | zero =>
                  change new.T.Z ≤ new.T.P new.Vec.nil new.T.Z
                  exact new.T.Z_le (new.T.P new.Vec.nil new.T.Z)
              | succ m =>
                  change new.T.P new.Vec.nil new.T.Z ≤ new.T.P new.Vec.nil new.T.Z
                  exact new.T.le_refl (new.T.P new.Vec.nil new.T.Z)
          constructor
          · change new.T.isNF (new.T.P new.Vec.nil (new.T.LF 0 n))
            exact hnf
          · intro y hy
            change y ∈ new.T.G (new.T.P new.Vec.nil (new.T.LF 0 n)) at hy
            cases (new.T.mem_G_P new.Vec.nil (new.T.LF 0 n) y).mp hy with
            | inl hv =>
                let ⟨i, _⟩ := hv
                exact i.elim0
            | inr hadd =>
                have hylt : y < new.T.LF 0 n := ih.2 y hadd
                have hstep : new.T.LF 0 n < new.T.LF 0 (n + 1) :=
                  ot_new_LF_step_lt 0 n
                have htrans : y < new.T.LF 0 (n + 1) :=
                  strict_partial_order.trans y (new.T.LF 0 n) (new.T.LF 0 (n + 1)) hylt hstep
                change y < new.T.P new.Vec.nil (new.T.LF 0 n) at htrans
                exact htrans
      | succ k =>
          let v : new.Vec (new.T (k + 1)) (k + 1) :=
            new.Vec.ofFn (k + 1)
              (fun i => if i = k then new.T.LF (k + 1) n else new.T.Z)
          have hcoord : ∀ i : Fin (k + 1), new.T.isNFComp (v.idx i) := by
            intro i
            unfold v
            rw [new.Vec.ofFn_idx]
            apply Decidable.byCases (p := i.val = k)
            · intro hi
              rw [ite_eq_left hi]
              exact ih
            · intro hi
              rw [ite_eq_right hi]
              exact new.T.isNFComp_Z
          have hnf : new.T.isNF (new.T.P v new.T.Z) :=
            new.T.isNF_PZ_of_coords v hcoord
          constructor
          · change new.T.isNF (new.T.P v new.T.Z)
            exact hnf
          · intro y hy
            change y ∈ new.T.G (new.T.P v new.T.Z) at hy
            cases (new.T.mem_G_P v new.T.Z y).mp hy with
            | inl hv =>
                let ⟨i, hcase⟩ := hv
                apply Decidable.byCases (p := i.val = k)
                · intro hi
                  have hvi : v.idx i = new.T.LF (k + 1) n := by
                    unfold v
                    rw [new.Vec.ofFn_idx, ite_eq_left hi]
                  cases hcase with
                  | inl heq =>
                      rw [heq, hvi]
                      have hstep : new.T.LF (k + 1) n < new.T.LF (k + 1) (n + 1) :=
                        ot_new_LF_step_lt (k + 1) n
                      change new.T.LF (k + 1) n < new.T.P v new.T.Z
                      change new.T.LF (k + 1) n <
                        new.T.P
                          (new.Vec.ofFn (k + 1)
                            (fun j => if j = k then new.T.LF (k + 1) n else new.T.Z))
                          new.T.Z
                      exact hstep
                  | inr hG =>
                      rw [hvi] at hG
                      have hylt : y < new.T.LF (k + 1) n := ih.2 y hG
                      have hstep : new.T.LF (k + 1) n < new.T.LF (k + 1) (n + 1) :=
                        ot_new_LF_step_lt (k + 1) n
                      have htrans : y < new.T.LF (k + 1) (n + 1) :=
                        strict_partial_order.trans y (new.T.LF (k + 1) n)
                          (new.T.LF (k + 1) (n + 1)) hylt hstep
                      change y < new.T.P v new.T.Z
                      change y <
                        new.T.P
                          (new.Vec.ofFn (k + 1)
                            (fun j => if j = k then new.T.LF (k + 1) n else new.T.Z))
                          new.T.Z
                      exact htrans
                · intro hi
                  have hvi : v.idx i = new.T.Z := by
                    unfold v
                    rw [new.Vec.ofFn_idx, ite_eq_right hi]
                  cases hcase with
                  | inl heq =>
                      rw [heq, hvi]
                      rfl
                  | inr hG =>
                      rw [hvi] at hG
                      change y ∈ ([] : List (new.T (k + 1))) at hG
                      cases hG
            | inr hz =>
                change y ∈ ([] : List (new.T (k + 1))) at hz
                cases hz

#print axioms ot_new_LF_NFComp

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
  | step lam a ha n ih =>
      constructor
      · apply new.T.fund_NF_closed a (new.T.ofNat n) ih.1
        intro hd
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

#print axioms ot_new_isOT_sound

theorem ot_new_LF_cofinal (lam : Nat) (s : new.T lam)
    (hs : new.T.isNF s) : ∃ n : Nat, s < new.T.LF lam n := by
  let motive : Nat → Prop :=
    fun m => ∀ (k : Nat) (a : new.T k), new.T.size a = m →
      new.T.isNF a → ∃ n : Nat, a < new.T.LF k n
  have main : ∀ m : Nat, motive m := by
    intro m
    exact Nat.strongRecOn m (motive := motive) (fun m ih => by
      intro k a hsize ha
      cases a with
      | Z =>
          exact ⟨1, ot_new_LF_step_lt k 0⟩
      | P ls add =>
          cases k with
          | zero =>
              cases ls with
              | nil =>
                  have hadd : new.T.isNF add := by
                    cases ha with
                    | p _ _ _ h1 _ _ => exact h1
                  have hsz : new.T.size add < m := by
                    have hh := new.T.add_size_lt_P new.Vec.nil add
                    rw [hsize] at hh
                    exact hh
                  let ⟨n, hn⟩ := ih (new.T.size add) hsz 0 add rfl hadd
                  refine ⟨n + 1, ?_⟩
                  rw [new.T.LF]
                  exact new.T.P_tail_lt new.Vec.nil add (new.T.LF 0 n) hn
          | succ k =>
              let q : Fin (k + 1) := Fin.last k
              have hqnf : new.T.isNF (ls.idx q) := by
                have hc := new.T.isNF_P_coord_NFComp ls add ha q
                exact hc.1
              have hqsz : new.T.size (ls.idx q) < m := by
                have hh : new.T.size (ls[q]) < new.T.size (new.T.P ls add) :=
                  new.T.idx_size_lt_P ls add q
                rw [new.Vec.getElem_eq_idx] at hh
                rw [hsize] at hh
                exact hh
              let ⟨n, hn⟩ := ih (new.T.size (ls.idx q)) hqsz
                (k + 1) (ls.idx q) rfl hqnf
              refine ⟨n + 1, ?_⟩
              rw [new.T.LF]
              apply new.T.P_lt_P_of_compareVec_lt
              apply new.Vec.compare_lt_of_pivot ls
                (new.Vec.ofFn (k + 1)
                  (fun i => if i.val = k then new.T.LF (k + 1) n else new.T.Z)) q
              · intro j hj
                have hjle : j.val ≤ k := Nat.lt_succ_iff.mp j.isLt
                have hnot : ¬ k < j.val := Nat.not_lt_of_ge hjle
                exact False.elim (hnot hj)
              · rw [new.Vec.ofFn_idx]
                have hq : q.val = k := rfl
                rw [ite_eq_left hq]
                exact hn)
  exact main (new.T.size s) lam s rfl hs

#print axioms ot_new_LF_cofinal

import SubspRepo.stop_surj_decode

open T

theorem surj_part_fst_oneChain (s : T)
    (hi : T.index_Prop1 1 s) : T.oneChain (T.part s).1 := by
  induction hi with
  | z =>
      exact True.intro
  | p p a b hp hb ih =>
      apply Decidable.byCases (p := p = 0)
      · intro hp0
        rw [T.part, ite_eq_left hp0]
        exact True.intro
      · intro hp0
        have hp1 : p = 1 := by
          have hle : p ≤ 1 := hp
          cases p with
          | zero => exact False.elim (hp0 rfl)
          | succ q =>
              have hq0 : q = 0 :=
                Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hle)
              rw [hq0]
        rw [T.part, ite_eq_right hp0]
        cases hpart : T.part b with
        | mk c d =>
            rw [hpart] at ih
            change p = 1 ∧ T.oneChain c
            exact ⟨hp1, ih⟩

#print axioms surj_part_fst_oneChain

def surj_v0Aux {lam : Nat} (k : Nat) (a : new.T lam) :
    new.Vec (new.T lam) (k + 1) :=
  new.Vec.ofFn (k + 1) (fun i => if i.val = 0 then a else new.T.Z)

def surj_v0 (k : Nat) (a : new.T (k + 1)) :
    new.Vec (new.T (k + 1)) (k + 1) :=
  surj_v0Aux k a

theorem surj_transAux_v0Aux {lam : Nat} (k : Nat) (a : new.T lam) :
    transAux (surj_v0Aux k a) = (false, T.Z, trans a) := by
  induction k with
  | zero =>
      unfold surj_v0Aux
      rw [new.Vec.ofFn]
      change transAux (new.Vec.snoc 0 new.Vec.nil a) = _
      rw [transAux.eq_2]
  | succ k ih =>
      unfold surj_v0Aux at ih ⊢
      rw [new.Vec.ofFn]
      have hlast : (Fin.last (k + 1)).val ≠ 0 := by
        exact Nat.ne_of_gt (Nat.zero_lt_succ k)
      rw [ite_eq_right hlast]
      change transAux
          (new.Vec.snoc (k + 1)
            (new.Vec.ofFn (k + 1)
              (fun i => if i.val = 0 then a else new.T.Z))
            new.T.Z) = _
      rw [transAux.eq_3, ih, _root_.trans.eq_1]
      change
        (false,
          T.add (T.card_times k (T.early_collapse T.Z)) T.Z,
          trans a) = (false, T.Z, trans a)
      rw [T.early_collapse, T.part, ite_eq_left rfl]
      rw [T.card_times.eq_1, T.add.eq_1]

theorem surj_transAux_v0 (k : Nat) (a : new.T (k + 1)) :
    transAux (surj_v0 k a) = (false, T.Z, trans a) := by
  exact surj_transAux_v0Aux k a

theorem surj_trans_v0 (k : Nat) (a b : new.T (k + 1)) :
    trans (new.T.P (surj_v0 k a) b) =
      T.P 0 (trans a) (trans b) := by
  rw [_root_.trans.eq_2, surj_transAux_v0]
  change (if false then _ else if trans a = T.Z then
      T.P 0 T.Z (trans b) else T.P 0 (trans a) (trans b)) = _
  rw [ite_eq_right (by intro h; cases h)]
  apply Decidable.byCases (p := trans a = T.Z)
  · intro h
    rw [ite_eq_left h, h]
  · intro h
    rw [ite_eq_right h]

#print axioms surj_transAux_v0Aux
#print axioms surj_trans_v0

theorem surj_v0_idx (k : Nat) (a : new.T (k + 1)) (i : Fin (k + 1)) :
    (surj_v0 k a).idx i = if i.val = 0 then a else new.T.Z := by
  unfold surj_v0 surj_v0Aux
  rw [new.Vec.ofFn_idx]

theorem surj_v0_all_comp (k : Nat) (a : new.T (k + 1))
    (ha : new.T.isNFComp a) :
    ∀ i : Fin (k + 1), new.T.isNFComp ((surj_v0 k a).idx i) := by
  intro i
  rw [surj_v0_idx]
  apply Decidable.byCases (p := i.val = 0)
  · intro hi
    rw [ite_eq_left hi]
    exact ha
  · intro hi
    rw [ite_eq_right hi]
    exact new.T.isNFComp_Z

#print axioms surj_v0_all_comp

theorem surj_P0_NF_of_preimages (k : Nat) (c d : T)
    (sc sd : new.T (k + 1))
    (hsc : new.T.isNFComp sc) (hsd : new.T.isNF sd)
    (hscTrans : trans sc = c) (hsdTrans : trans sd = d)
    (hhead : T.head d ≤ T.P 0 c T.Z) :
    new.T.isNF (new.T.P (surj_v0 k sc) sd) ∧
      trans (new.T.P (surj_v0 k sc) sd) = T.P 0 c d := by
  have hpNF : new.T.isNF (new.T.P (surj_v0 k sc) new.T.Z) := by
    apply new.T.isNF_PZ_of_coords
    exact surj_v0_all_comp k sc hsc
  have hheadTrans :
      trans (new.T.head sd) ≤ trans (new.T.P (surj_v0 k sc) new.T.Z) := by
    rw [tc_trans_head sd, surj_trans_v0, hsdTrans, hscTrans,
      _root_.trans.eq_1]
    exact hhead
  have hheadNew :
      new.T.head sd ≤ new.T.P (surj_v0 k sc) new.T.Z := by
    cases hheadTrans with
    | inl hlt =>
        exact Or.inl ((gnf_order_embedding (new.T.head sd)
          (new.T.P (surj_v0 k sc) new.T.Z)
          (nfcore_head_NF sd hsd) hpNF).mpr hlt)
    | inr heq =>
        have hEq : new.T.head sd = new.T.P (surj_v0 k sc) new.T.Z := by
          cases new.T_total (new.T.head sd)
              (new.T.P (surj_v0 k sc) new.T.Z) with
          | inl hlt =>
              have htr := (gnf_order_embedding (new.T.head sd)
                (new.T.P (surj_v0 k sc) new.T.Z)
                (nfcore_head_NF sd hsd) hpNF).mp hlt
              rw [heq] at htr
              exact False.elim (strict_partial_order.irrefl _ htr)
          | inr hr =>
              cases hr with
              | inl hgt =>
                  have htr := (gnf_order_embedding
                    (new.T.P (surj_v0 k sc) new.T.Z) (new.T.head sd)
                    hpNF (nfcore_head_NF sd hsd)).mp hgt
                  rw [heq] at htr
                  exact False.elim (strict_partial_order.irrefl _ htr)
              | inr hEq => exact hEq
        rw [hEq]
        exact Or.inr (new.T_refl _)
  have houtNF : new.T.isNF (new.T.P (surj_v0 k sc) sd) := by
    apply new.T.isNF.p (surj_v0 k sc) sd
    · intro x hx
      obtain ⟨i, hi⟩ :=
        new.Vec.mem_toList_exists_idx (surj_v0 k sc) x hx
      rw [← hi]
      exact (surj_v0_all_comp k sc hsc i).1
    · exact hsd
    · intro x hx y hy
      obtain ⟨i, hi⟩ :=
        new.Vec.mem_toList_exists_idx (surj_v0 k sc) x hx
      rw [← hi] at hy
      have hcomp := surj_v0_all_comp k sc hsc i
      have hlt := hcomp.2 y hy
      rw [hi] at hlt
      exact hlt
    · exact hheadNew
  constructor
  · exact houtNF
  · rw [surj_trans_v0, hscTrans, hsdTrans]

#print axioms surj_P0_NF_of_preimages

theorem surj_tail_le_parent {lam : Nat} (v : new.Vec (new.T lam) lam) :
    ∀ d : new.T lam, new.T.isNF d →
      new.T.head d ≤ new.T.P v new.T.Z → d ≤ new.T.P v d := by
  let motive : Nat → Prop := fun n =>
    ∀ d : new.T lam, new.T.size d = n → new.T.isNF d →
      new.T.head d ≤ new.T.P v new.T.Z → d ≤ new.T.P v d
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro d hsize hnf hhead
      cases d with
      | Z =>
          exact Or.inl rfl
      | P w e =>
          cases hnf with
          | p _ _ hwNF heNF hwG heHead =>
              cases new.T.vector_rel_of_P_le_P w v new.T.Z new.T.Z hhead with
              | inl hwv =>
                  apply Or.inl
                  change
                    (match new.compareVec w v with
                    | Ordering.eq => new.compareT e (new.T.P w e)
                    | ord => ord) = Ordering.lt
                  rw [hwv]
              | inr hweq =>
                  cases hweq
                  have hesize : new.T.size e < n := by
                    have h := new.T.add_size_lt_P v e
                    rw [hsize] at h
                    exact h
                  have heLe : e ≤ new.T.P v e :=
                    ih (new.T.size e) hesize e rfl heNF heHead
                  exact (new.T.P_same_le_iff v e (new.T.P v e)).mpr heLe)
  intro d hnf hhead
  exact main (new.T.size d) d rfl hnf hhead

#print axioms surj_tail_le_parent

theorem surj_P0_Comp_of_preimages (k : Nat) (c d : T)
    (sc sd : new.T (k + 1))
    (hsc : new.T.isNFComp sc) (hsd : new.T.isNFComp sd)
    (hscTrans : trans sc = c) (hsdTrans : trans sd = d)
    (hnf : T.isNF1 (T.P 0 c d))
    (hgood : ∀ x : T, x ∈ T.G1 0 (T.P 0 c d) → x < T.P 0 c d) :
    new.T.isNFComp (new.T.P (surj_v0 k sc) sd) ∧
      trans (new.T.P (surj_v0 k sc) sd) = T.P 0 c d := by
  have hinv := T.isNF1_P_inv 0 c d hnf
  have hbase := surj_P0_NF_of_preimages k c d sc sd hsc hsd.1
    hscTrans hsdTrans hinv.2.2.2
  have hparentNF := hbase.1
  have hparentTrans := hbase.2
  have hcMem : c ∈ T.G1 0 (T.P 0 c d) := by
    rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
    exact List.mem_append_left (T.G1 0 d)
      (List.mem_append_left (T.G1 0 c) (List.mem_singleton_self c))
  have hcLt : c < T.P 0 c d := hgood c hcMem
  have hscLt : sc < new.T.P (surj_v0 k sc) sd := by
    have htr : trans sc < trans (new.T.P (surj_v0 k sc) sd) := by
      rw [hscTrans, hparentTrans]
      exact hcLt
    exact (gnf_order_embedding sc (new.T.P (surj_v0 k sc) sd)
      hsc.1 hparentNF).mpr htr
  have htailLe : sd ≤ new.T.P (surj_v0 k sc) sd := by
    cases hparentNF with
    | p _ _ hcoords htail hg hhead =>
        exact surj_tail_le_parent (surj_v0 k sc) sd hsd.1 hhead
  constructor
  · constructor
    · exact hparentNF
    · intro y hy
      cases (new.T.mem_G_P (surj_v0 k sc) sd y).mp hy with
      | inl hcoord =>
          cases hcoord with
          | intro i hi =>
              apply Decidable.byCases (p := i.val = 0)
              · intro hi0
                have hidx : (surj_v0 k sc).idx i = sc := by
                  rw [surj_v0_idx, ite_eq_left hi0]
                cases hi with
                | inl heq =>
                    rw [heq, hidx]
                    exact hscLt
                | inr hmem =>
                    rw [hidx] at hmem
                    have hysc := hsc.2 y hmem
                    exact strict_partial_order.trans y sc
                      (new.T.P (surj_v0 k sc) sd) hysc hscLt
              · intro hi0
                have hidx : (surj_v0 k sc).idx i = new.T.Z := by
                  rw [surj_v0_idx, ite_eq_right hi0]
                cases hi with
                | inl heq =>
                    rw [heq, hidx]
                    rfl
                | inr hmem =>
                    rw [hidx] at hmem
                    cases hmem
      | inr htail =>
          have hyTail := hsd.2 y htail
          exact new.T.lt_of_lt_of_le y sd
            (new.T.P (surj_v0 k sc) sd) hyTail htailLe
  · exact hparentTrans

#print axioms surj_P0_Comp_of_preimages

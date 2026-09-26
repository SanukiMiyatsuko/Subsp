import Subsp.new.stop

open T

def B1 : T := T.P 0 (T.P 1 T.Z T.Z) T.Z
def C1 : T := T.P 1 T.Z T.Z

def v1 (a : new.T 1) : new.Vec (new.T 1) 1 :=
  new.Vec.snoc 0 new.Vec.nil a

theorem trans_v1 (a b : new.T 1) :
    trans (new.T.P (v1 a) b) = T.P 0 (trans a) (trans b) := by
  unfold v1
  rw [_root_.trans.eq_2, transAux.eq_2]
  change (if false then _ else if trans a = T.Z then
      T.P 0 T.Z (trans b) else T.P 0 (trans a) (trans b)) = _
  rw [ite_eq_right (by intro h; cases h)]
  apply Decidable.byCases (p := trans a = T.Z)
  · intro h
    rw [ite_eq_left h, h]
  · intro h
    rw [ite_eq_right h]

#print axioms trans_v1

theorem trans_injective_NF {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (heq : trans s = trans t) : s = t := by
  cases new.T_total s t with
  | inl hst =>
      have htr : trans s < trans t :=
        (gnf_order_embedding s t hs ht).mp hst
      rw [heq] at htr
      exact False.elim (strict_partial_order.irrefl (trans t) htr)
  | inr hrest =>
      cases hrest with
      | inl hts =>
          have htr : trans t < trans s :=
            (gnf_order_embedding t s ht hs).mp hts
          rw [heq] at htr
          exact False.elim (strict_partial_order.irrefl (trans t) htr)
      | inr he =>
          exact he

#print axioms trans_injective_NF

theorem reflect_le_NF {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (hle : trans s ≤ trans t) : s ≤ t := by
  cases hle with
  | inl hlt =>
      exact Or.inl ((gnf_order_embedding s t hs ht).mpr hlt)
  | inr heq =>
      have hst : s = t := trans_injective_NF s t hs ht heq
      rw [hst]
      exact Or.inr (new.T_refl t)

#print axioms reflect_le_NF

theorem lt_B1_inv (p : Nat) (a b : T)
    (h : T.P p a b < B1) : p = 0 ∧ a < C1 := by
  unfold B1 at h
  unfold C1
  cases lt_inv p a b 0 (T.P 1 T.Z T.Z) T.Z h with
  | inl hp =>
      exact False.elim (Nat.not_lt_zero p hp)
  | inr hr =>
      cases hr with
      | inl hm =>
          exact ⟨hm.1, hm.2⟩
      | inr ht =>
          exact False.elim (lt_Z_inv ht.2.2)

#print axioms lt_B1_inv

theorem lt_C1_head_zero (p : Nat) (a b : T)
    (h : T.P p a b < C1) : p = 0 := by
  unfold C1 at h
  cases lt_inv p a b 1 T.Z T.Z h with
  | inl hp =>
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
  | inr hr =>
      cases hr with
      | inl hm =>
          exact False.elim (lt_Z_inv hm.2)
      | inr ht =>
          exact False.elim (lt_Z_inv ht.2.2)

#print axioms lt_C1_head_zero

theorem trans_G_lam1 {s y : new.T 1}
    (hy : y ∈ new.T.G s) : trans y ∈ T.G1 0 (trans s) := by
  let motive : Nat → Prop := fun n =>
    ∀ s : new.T 1, new.T.size s = n →
      ∀ y : new.T 1, y ∈ new.T.G s → trans y ∈ T.G1 0 (trans s)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s hsize y hy
      cases s with
      | Z =>
          cases hy
      | P ls add =>
          cases ls with
          | snoc k xs a =>
              cases xs with
              | nil =>
                  have haSize : new.T.size a < n := by
                    rw [← hsize]
                    exact new.T.idx_size_lt_P (v1 a) add
                      ⟨0, Nat.zero_lt_succ 0⟩
                  have haddSize : new.T.size add < n := by
                    rw [← hsize]
                    exact new.T.add_size_lt_P (v1 a) add
                  change trans y ∈ T.G1 0 (trans (new.T.P (v1 a) add))
                  rw [trans_v1]
                  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                  cases (new.T.mem_G_P (v1 a) add y).mp hy with
                  | inl hc =>
                      cases hc with
                      | intro i hi =>
                          have hival : i.val = 0 :=
                            Nat.eq_zero_of_le_zero
                              (Nat.le_of_lt_succ i.isLt)
                          have hi0 : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
                            Fin.eq_of_val_eq hival
                          cases hi0
                          cases hi with
                          | inl heq =>
                              change y = a at heq
                              rw [heq]
                              exact List.mem_append_left (T.G1 0 (trans add))
                                (List.mem_append_left (T.G1 0 (trans a))
                                  (List.mem_singleton_self (trans a)))
                          | inr hga =>
                              have hmem :=
                                ih (new.T.size a) haSize a rfl y hga
                              exact List.mem_append_left (T.G1 0 (trans add))
                                (List.mem_append_right [trans a] hmem)
                  | inr htail =>
                      have hmem :=
                        ih (new.T.size add) haddSize add rfl y htail
                      exact List.mem_append_right
                        ([trans a] ++ T.G1 0 (trans a)) hmem)
  exact main (new.T.size s) s rfl y hy

#print axioms trans_G_lam1

theorem surj1_pair :
    ∀ a : T, T.isNF1 a →
      ((a < B1 → ∃ s : new.T 1, new.T.isNF s ∧ trans s = a) ∧
       ((∀ y : T, y ∈ T.G1 0 a → y < a) → a < C1 →
          ∃ s : new.T 1, new.T.isNFComp s ∧ trans s = a)) := by
  let motive : Nat → Prop := fun n =>
    ∀ a : T, T.size a = n → T.isNF1 a →
      ((a < B1 → ∃ s : new.T 1, new.T.isNF s ∧ trans s = a) ∧
       ((∀ y : T, y ∈ T.G1 0 a → y < a) → a < C1 →
          ∃ s : new.T 1, new.T.isNFComp s ∧ trans s = a))
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a hsize hnf
      cases a with
      | Z =>
          constructor
          · intro hb
            exact ⟨new.T.Z, new.T.isNF.z, rfl⟩
          · intro hgood hc
            exact ⟨new.T.Z, new.T.isNFComp_Z, rfl⟩
      | P p c d =>
          have hinv := T.isNF1_P_inv p c d hnf
          have hcNF : T.isNF1 c := hinv.1
          have hdNF : T.isNF1 d := hinv.2.1
          have hcGoodP : ∀ x : T, x ∈ T.G1 p c → x < c :=
            hinv.2.2.1
          have hheadD : T.head d ≤ T.P p c T.Z := hinv.2.2.2
          have hcSize : T.size c < n := by
            rw [← hsize]
            exact T.size_lt_size_P_left p c d
          have hdSize : T.size d < n := by
            rw [← hsize]
            exact T.size_lt_size_P_right p c d
          have ihc := ih (T.size c) hcSize c rfl hcNF
          have ihd := ih (T.size d) hdSize d rfl hdNF
          constructor
          · intro hb
            have hshape := lt_B1_inv p c d hb
            have hp0 : p = 0 := hshape.1
            cases hp0
            have hcGood : ∀ x : T, x ∈ T.G1 0 c → x < c := hcGoodP
            have hcs := ihc.2 hcGood hshape.2
            cases hcs with
            | intro sc hsc =>
                have hdt : d < T.P 0 c d :=
                  gc_tail_lt_of_NF1 0 c d hnf
                have hdB : d < B1 :=
                  lt_trans_thm d (T.P 0 c d) B1 hdt hb
                have hds := ihd.1 hdB
                cases hds with
                | intro sd hsd =>
                    let v := v1 sc
                    have hpNF : new.T.isNF (new.T.P v new.T.Z) := by
                      apply new.T.isNF_PZ_of_coords
                      intro i
                      have hival : i.val = 0 :=
                        Nat.eq_zero_of_le_zero
                          (Nat.le_of_lt_succ i.isLt)
                      have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
                        Fin.eq_of_val_eq hival
                      cases hi
                      exact hsc.1
                    have hheadTrans :
                        trans (new.T.head sd) ≤
                          trans (new.T.P v new.T.Z) := by
                      rw [tc_trans_head sd, trans_v1, hsd.2, hsc.2]
                      exact hheadD
                    have hheadNew :
                        new.T.head sd ≤ new.T.P v new.T.Z :=
                      reflect_le_NF (new.T.head sd) (new.T.P v new.T.Z)
                        (nfcore_head_NF sd hsd.1) hpNF hheadTrans
                    have houtNF : new.T.isNF (new.T.P v sd) := by
                      apply new.T.isNF.p v sd
                      · intro x hx
                        have hxsc : x = sc := by
                          change x ∈ [sc] at hx
                          exact List.mem_singleton.mp hx
                        rw [hxsc]
                        exact hsc.1.1
                      · exact hsd.1
                      · intro x hx y hy
                        have hxsc : x = sc := by
                          change x ∈ [sc] at hx
                          exact List.mem_singleton.mp hx
                        rw [hxsc] at hy
                        rw [hxsc]
                        exact hsc.1.2 y hy
                      · exact hheadNew
                    refine ⟨new.T.P v sd, houtNF, ?_⟩
                    rw [trans_v1, hsc.2, hsd.2]
          · intro hgood hcBound
            have hp0 : p = 0 := lt_C1_head_zero p c d hcBound
            cases hp0
            have hcMem : c ∈ T.G1 0 (T.P 0 c d) := by
              rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
              exact List.mem_append_left (T.G1 0 d)
                (List.mem_append_left (T.G1 0 c)
                  (List.mem_singleton_self c))
            have hcLt : c < T.P 0 c d := hgood c hcMem
            have hcBound' : c < C1 :=
              lt_trans_thm c (T.P 0 c d) C1 hcLt hcBound
            have hcGood : ∀ x : T, x ∈ T.G1 0 c → x < c := hcGoodP
            have hcs := ihc.2 hcGood hcBound'
            cases hcs with
            | intro sc hsc =>
                have hprincipalB : T.P 0 c T.Z < B1 := by
                  unfold B1
                  exact T.Lt.p_mid 0 c C1 T.Z T.Z hcBound'
                have hheadDB : T.head d < B1 :=
                  lt_of_le_of_lt_thm T (T.head d) (T.P 0 c T.Z)
                    B1 hheadD hprincipalB
                have hdB : d < B1 := by
                  cases d with
                  | Z => exact T.Lt.Z_lt_P 0 C1 T.Z
                  | P q e f =>
                      change T.P q e T.Z < B1 at hheadDB
                      unfold B1 at hheadDB ⊢
                      cases lt_inv q e T.Z 0 C1 T.Z hheadDB with
                      | inl hq =>
                          exact False.elim (Nat.not_lt_zero q hq)
                      | inr hr =>
                          cases hr with
                          | inl hm =>
                              cases hm.1
                              exact T.Lt.p_mid 0 e C1 f T.Z hm.2
                          | inr ht =>
                              exact False.elim (lt_Z_inv ht.2.2)
                have hds := ihd.1 hdB
                cases hds with
                | intro sd hsd =>
                    let v := v1 sc
                    have hpNF : new.T.isNF (new.T.P v new.T.Z) := by
                      apply new.T.isNF_PZ_of_coords
                      intro i
                      have hival : i.val = 0 :=
                        Nat.eq_zero_of_le_zero
                          (Nat.le_of_lt_succ i.isLt)
                      have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
                        Fin.eq_of_val_eq hival
                      cases hi
                      exact hsc.1
                    have hheadTrans :
                        trans (new.T.head sd) ≤
                          trans (new.T.P v new.T.Z) := by
                      rw [tc_trans_head sd, trans_v1, hsd.2, hsc.2]
                      exact hheadD
                    have hheadNew :
                        new.T.head sd ≤ new.T.P v new.T.Z :=
                      reflect_le_NF (new.T.head sd) (new.T.P v new.T.Z)
                        (nfcore_head_NF sd hsd.1) hpNF hheadTrans
                    have houtNF : new.T.isNF (new.T.P v sd) := by
                      apply new.T.isNF.p v sd
                      · intro x hx
                        have hxsc : x = sc := by
                          change x ∈ [sc] at hx
                          exact List.mem_singleton.mp hx
                        rw [hxsc]
                        exact hsc.1.1
                      · exact hsd.1
                      · intro x hx y hy
                        have hxsc : x = sc := by
                          change x ∈ [sc] at hx
                          exact List.mem_singleton.mp hx
                        rw [hxsc] at hy
                        rw [hxsc]
                        exact hsc.1.2 y hy
                      · exact hheadNew
                    have houtTrans :
                        trans (new.T.P v sd) = T.P 0 c d := by
                      rw [trans_v1, hsc.2, hsd.2]
                    have houtComp :
                        new.T.isNFComp (new.T.P v sd) := by
                      constructor
                      · exact houtNF
                      · intro y hy
                        have hyNFComp :=
                          new.T.isNF_G_isNFComp
                            (new.T.P v sd) houtNF y hy
                        have hyMemT :
                            trans y ∈ T.G1 0 (T.P 0 c d) := by
                          rw [← houtTrans]
                          exact trans_G_lam1 hy
                        have hyLtT : trans y < T.P 0 c d :=
                          hgood (trans y) hyMemT
                        have hyLtImg :
                            trans y < trans (new.T.P v sd) := by
                          rw [houtTrans]
                          exact hyLtT
                        exact (gnf_order_embedding y (new.T.P v sd)
                          hyNFComp.1 houtNF).mpr hyLtImg
                    exact ⟨new.T.P v sd, houtComp, houtTrans⟩)
  intro a hnf
  exact main (T.size a) a rfl hnf

#print axioms surj1_pair

theorem surj_SubNF1 (t : T) (ht : T.isSubNF 1 t) :
    ∃ s : new.T 1, new.T.isOT 1 s ∧ trans s = t := by
  have hs := (surj1_pair t ht.1).1
  have hex := hs ht.2
  cases hex with
  | intro s h =>
      have hot : new.T.isOT 1 s :=
        (new.T.OT_iff_NF 1 s).mpr ⟨h.1, by
          intro hbad
          exact False.elim (Nat.lt_irrefl 1 hbad)⟩
      exact ⟨s, hot, h.2⟩

#print axioms surj_SubNF1

def B0 : T := T.P 0 (T.P 0 T.Z T.Z) T.Z

theorem trans_v0 (b : new.T 0) :
    trans (new.T.P new.Vec.nil b) = T.P 0 T.Z (trans b) := by
  rw [_root_.trans.eq_2, transAux.eq_1]
  rfl

#print axioms trans_v0

theorem lt_B0_inv (p : Nat) (a b : T)
    (h : T.P p a b < B0) : p = 0 ∧ a < T.P 0 T.Z T.Z := by
  unfold B0 at h
  cases lt_inv p a b 0 (T.P 0 T.Z T.Z) T.Z h with
  | inl hp =>
      exact False.elim (Nat.not_lt_zero p hp)
  | inr hr =>
      cases hr with
      | inl hm => exact ⟨hm.1, hm.2⟩
      | inr ht => exact False.elim (lt_Z_inv ht.2.2)

#print axioms lt_B0_inv

theorem surj_SubNF0_raw :
    ∀ t : T, T.isNF1 t → t < B0 →
      ∃ s : new.T 0, new.T.isNF s ∧ trans s = t := by
  let motive : Nat → Prop := fun n =>
    ∀ t : T, T.size t = n → T.isNF1 t → t < B0 →
      ∃ s : new.T 0, new.T.isNF s ∧ trans s = t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro t hsize hnf hbound
      cases t with
      | Z =>
          exact ⟨new.T.Z, new.T.isNF.z, rfl⟩
      | P p a b =>
          have hinv := T.isNF1_P_inv p a b hnf
          have hshape := lt_B0_inv p a b hbound
          have hp0 : p = 0 := hshape.1
          cases hp0
          have haZ : a = T.Z := bridge_lt_P0ZZ_eq_Z a hshape.2
          cases haZ
          have hbSize : T.size b < n := by
            rw [← hsize]
            exact T.size_lt_size_P_right 0 T.Z b
          have hbLt : b < T.P 0 T.Z b :=
            gc_tail_lt_of_NF1 0 T.Z b hnf
          have hbBound : b < B0 :=
            lt_trans_thm b (T.P 0 T.Z b) B0 hbLt hbound
          have hbPre := ih (T.size b) hbSize b rfl hinv.2.1 hbBound
          cases hbPre with
          | intro sb hsb =>
              have hpNF :
                  new.T.isNF (new.T.P new.Vec.nil new.T.Z) := by
                apply new.T.isNF_PZ_of_coords
                intro i
                exact i.elim0
              have hheadTrans :
                  trans (new.T.head sb) ≤
                    trans (new.T.P new.Vec.nil new.T.Z) := by
                rw [tc_trans_head sb, trans_v0, hsb.2]
                exact hinv.2.2.2
              have hheadNew :
                  new.T.head sb ≤ new.T.P new.Vec.nil new.T.Z :=
                reflect_le_NF (new.T.head sb)
                  (new.T.P new.Vec.nil new.T.Z)
                  (nfcore_head_NF sb hsb.1) hpNF hheadTrans
              have houtNF :
                  new.T.isNF (new.T.P new.Vec.nil sb) := by
                apply new.T.isNF.p new.Vec.nil sb
                · intro x hx
                  cases hx
                · exact hsb.1
                · intro x hx
                  cases hx
                · exact hheadNew
              refine ⟨new.T.P new.Vec.nil sb, houtNF, ?_⟩
              rw [trans_v0, hsb.2])
  intro t hnf hbound
  exact main (T.size t) t rfl hnf hbound

#print axioms surj_SubNF0_raw

theorem surj_SubNF0 (t : T) (ht : T.isSubNF 0 t) :
    ∃ s : new.T 0, new.T.isOT 0 s ∧ trans s = t := by
  have hex := surj_SubNF0_raw t ht.1 ht.2
  cases hex with
  | intro s hs =>
      have hot : new.T.isOT 0 s :=
        (new.T.OT_iff_NF 0 s).mpr ⟨hs.1, by
          intro hbad
          exact False.elim (Nat.not_lt_zero 1 hbad)⟩
      exact ⟨s, hot, hs.2⟩

#print axioms surj_SubNF0

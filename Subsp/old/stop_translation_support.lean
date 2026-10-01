import Subsp.old.stop_nf_core
import Subsp.old.stop_source_fund_nf

/-! Basic support embeddings used by the legacy translation support proof. -/

namespace LegacyTranslation

theorem source_vec_idx_mem_Gi {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (i : Fin k) (hui : u ≤ i.val) :
    v.idx i ∈ new.Vec.Gi u v := by
  exact (new.Vec.mem_Gi_iff u v (v.idx i)).2
    ⟨i, hui, Or.inl rfl⟩

theorem source_coord_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val) :
    v.idx i ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a (v.idx i)).2
    (Or.inl ⟨i, hui, Or.inl rfl⟩)

theorem source_coord_support_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val)
    (hz : z ∈ new.T.Gi u (v.idx i)) :
    z ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a z).2
    (Or.inl ⟨i, hui, Or.inr hz⟩)

theorem source_tail_support_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.Gi u a) :
    z ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a z).2 (Or.inr hz)

theorem trans_tail_le {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (h : T.isNF1 (trans (new.T.P v a))) :
    trans a ≤ trans (new.T.P v a) := by
  rw [trans_as_add]
  exact add_right_le_of_NF _ _ h

theorem trans_head_support_mem {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam) (x : T)
    (hx : x ∈ T.G1 u (transAux v).1) :
    x ∈ T.G1 u (trans (new.T.P v a)) := by
  rw [trans_as_add, G1_add]
  exact List.mem_append_left _ hx

theorem trans_tail_support_mem {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam) (x : T)
    (hx : x ∈ T.G1 u (trans a)) :
    x ∈ T.G1 u (trans (new.T.P v a)) := by
  rw [trans_as_add, G1_add]
  exact List.mem_append_right _ hx


theorem cardArg_head_or_eq (n p : Nat) (a b tail : T)
    (hs : T.isNF1 (T.P p a b)) :
    cardArg n p a < T.P (max p n) (cardArg n p a) tail ∨
      (n ≤ p ∧ cardArg n p a = a) := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  by_cases hpn : p < n
  · apply Or.inl
    have hm : max p n = n := Nat.max_eq_right (Nat.le_of_lt hpn)
    have hiP := cardArg_index_of_lt n p a ha hga hpn
    have hiN : T.index_Prop1 n (cardArg n p a) :=
      Rank1Termination.index_mono (Nat.le_of_lt hpn) _ hiP
    have hclosed := cardArg_closed n p a ha hga
    have hgood : ∀ x : T, x ∈ T.G1 n (cardArg n p a) → x < cardArg n p a := by
      simpa only [hm] using hclosed.2
    rw [hm]
    exact good_index_lt_wrap n _ tail hiN hgood
  · have hnp : n ≤ p := Nat.le_of_not_gt hpn
    rw [Nat.max_eq_left hnp]
    unfold cardArg
    rw [ite_eq_right hpn]
    split
    · apply Or.inl
      obtain ⟨rfl, _⟩ := ‹p = n ∧ _›
      exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)
    · exact Or.inr ⟨hnp, rfl⟩

theorem card_times_support_decomp (u n : Nat) (hun : u ≤ n)
    (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) :
    ∀ s c : T, T.isNF1 s → s ≤ c →
      (∀ y : T, y ∈ T.G1 u s → y < c ∨ R y) →
      ∀ x : T, x ∈ T.G1 u (T.card_times n s) →
        x < T.card_times n s ∨ x < c ∨ R x := by
  intro s c hs hsc hdec
  induction hs generalizing c with
  | z =>
      intro x hx
      cases hx
  | p p a b ha hb hga hh _ ih =>
      have hsfull : T.isNF1 (T.P p a b) := .p p a b ha hb hga hh
      rw [card_times_P]
      intro x hx
      have hum : u ≤ max p n := Nat.le_trans hun (Nat.le_max_right p n)
      simp only [T.G1, hum, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · rcases cardArg_head_or_eq n p a b (T.card_times n b) hsfull with h | ⟨hnp, heq⟩
        · exact Or.inl h
        · rw [heq]
          have hup : u ≤ p := Nat.le_trans hun hnp
          rcases hdec a (by simp [T.G1, hup]) with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · obtain ⟨y, hy, hxy⟩ :=
          cardArg_support_witness u n p a b hun hsfull x hx
        rcases hdec y hy with h | h
        · exact Or.inr (Or.inl (lt_of_le_of_lt_thm T _ _ _ hxy h))
        · exact Or.inr (Or.inr (hR x y hxy h))
      · have hb_le_c : b ≤ c := partial_order.trans _ _ _
          (T.isNF1_tail_le _ hsfull p a b rfl) hsc
        have hdec_b : ∀ y : T, y ∈ T.G1 u b → y < c ∨ R y := by
          intro y hy
          apply hdec y
          by_cases hup : u ≤ p <;> simp [T.G1, hup, hy]
        rcases ih c hb_le_c hdec_b x hx with h | h | h
        · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)


def VecWitness {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (x : T) : Prop :=
  ∃ z : new.T lam, z ∈ new.Vec.Gi u v ∧ x ≤ trans z

theorem VecWitness_mono {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (x y : T)
    (hxy : x ≤ y) (hy : VecWitness u v y) :
    VecWitness u v x := by
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hz, partial_order.trans _ _ _ hxy hyz⟩

theorem VecWitness_prefix {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (a : new.T lam) (x : T)
    (h : VecWitness u v x) :
    VecWitness u (.snoc k v a) x := by
  obtain ⟨z, hz, hxz⟩ := h
  exact ⟨z, by
    rw [new.Vec.Gi]
    exact List.mem_append_left _ hz, hxz⟩

theorem VecWitness_last {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (a : new.T lam)
    (huk : u ≤ k) (x : T) (hx : x ≤ trans a) :
    VecWitness u (.snoc k v a) x := by
  refine ⟨a, ?_, hx⟩
  simp [new.Vec.Gi, huk]

theorem VecWitness_last_support {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (a z : new.T lam)
    (huk : u ≤ k) (x : T)
    (hz : z ∈ new.T.Gi u a) (hx : x ≤ trans z) :
    VecWitness u (.snoc k v a) x := by
  refine ⟨z, ?_, hx⟩
  simp [new.Vec.Gi, huk, hz]

theorem early_collapse_coord_decomp {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (a : new.T lam)
    (huk : u ≤ k) (ha : GoodAt k a)
    (hdec : ∀ y : T, y ∈ T.G1 u (trans a) →
      y < trans a ∨
        ∃ z : new.T lam, z ∈ new.T.Gi u a ∧ y ≤ trans z) :
    ∀ y : T, y ∈ T.G1 u (T.early_collapse k (trans a)) →
      y < trans a ∨ VecWitness u (.snoc k v a) y := by
  intro y hy
  rcases early_collapse_support_source u k (trans a) huk ha.1 y hy with h | h
  · exact Or.inr (VecWitness_last u v a huk y h)
  · rcases hdec y h with hlt | ⟨z, hz, hyz⟩
    · exact Or.inl hlt
    · exact Or.inr (VecWitness_last_support u v a z huk y hz hyz)

theorem card_early_support_decomp {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (a : new.T lam)
    (huk : u ≤ k) (ha : GoodAt k a)
    (hdec : ∀ y : T, y ∈ T.G1 u (trans a) →
      y < trans a ∨
        ∃ z : new.T lam, z ∈ new.T.Gi u a ∧ y ≤ trans z) :
    ∀ x : T,
      x ∈ T.G1 u (T.card_times k (T.early_collapse k (trans a))) →
      x < T.card_times k (T.early_collapse k (trans a)) ∨
        VecWitness u (.snoc k v a) x := by
  have hec := early_collapse_closed k (trans a) ha.1 ha.2
  have hdecEc :
      ∀ y : T, y ∈ T.G1 u (T.early_collapse k (trans a)) →
        y < trans a ∨ VecWitness u (.snoc k v a) y :=
    early_collapse_coord_decomp u v a huk ha hdec
  intro x hx
  rcases card_times_support_decomp u k huk
      (VecWitness u (.snoc k v a))
      (fun x y hxy hy => VecWitness_mono u _ x y hxy hy)
      (T.early_collapse k (trans a)) (trans a) hec.1
      (early_collapse_le_self k (trans a) ha.1) hdecEc x hx with
    h | h | h
  · exact Or.inl h
  · exact Or.inr (VecWitness_last u v a huk x (Or.inl h))
  · exact Or.inr h

theorem aux_lower_support_decomp {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (hv : VecGood v) :
    (∀ i : Fin k, u ≤ i.val →
      ∀ y : T, y ∈ T.G1 u (trans (v.idx i)) →
        y < trans (v.idx i) ∨
          ∃ z : new.T lam, z ∈ new.T.Gi u (v.idx i) ∧ y ≤ trans z) →
    ∀ x : T, x ∈ T.G1 u (transAux v).2 →
      x < (transAux v).2 ∨ VecWitness u v x := by
  induction v with
  | nil =>
      intro _ x hx
      cases hx
  | snoc k v a ih =>
      intro hdec
      have ha := VecGood_last v a hv
      have hp := VecGood_prefix v a hv
      have hdecPrefix :
          ∀ i : Fin k, u ≤ i.val →
            ∀ y : T, y ∈ T.G1 u (trans (v.idx i)) →
              y < trans (v.idx i) ∨
                ∃ z : new.T lam, z ∈ new.T.Gi u (v.idx i) ∧ y ≤ trans z := by
        intro i hui y hy
        simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
          hdec i.castSucc hui y hy
      by_cases hku : k < u
      · have hi := (aux_lower_closed (.snoc k v a) hv).2.1
        have hemp : T.G1 u (transAux (.snoc k v a)).2 = [] := by
          apply index_Prop1_G1_empty k _ ?_ u hku
          simpa using hi
        rw [hemp]
        intro x hx
        cases hx
      · have huk : u ≤ k := Nat.le_of_not_gt hku
        have hdecLast :
            ∀ y : T, y ∈ T.G1 u (trans a) →
              y < trans a ∨
                ∃ z : new.T lam, z ∈ new.T.Gi u a ∧ y ≤ trans z := by
          simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using
            hdec (Fin.last k) huk
        cases k with
        | zero =>
            cases v
            rw [aux_single]
            intro x hx
            rcases early_collapse_coord_decomp u new.Vec.nil a huk ha hdecLast x hx with h | h
            · exact Or.inr (VecWitness_last u new.Vec.nil a huk x (Or.inl h))
            · exact Or.inr h
        | succ k =>
            rw [aux_lower_snoc]
            intro x hx
            rw [G1_add] at hx
            rcases hx with hx | hx
            · rcases card_early_support_decomp u v a huk ha hdecLast x hx with h | h
              · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h (add_self_le _ _))
              · exact Or.inr h
            · rcases ih hp hdecPrefix x hx with h | h
              · have hnf := (aux_lower_closed (.snoc (k + 1) v a) hv).1
                rw [aux_lower_snoc] at hnf
                exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h
                  (add_right_le_of_NF _ _ hnf))
              · exact Or.inr (VecWitness_prefix u v a x h)


theorem aux_positive_middle_lt {lam k : Nat}
    (v : new.Vec (new.T lam) (k + 1)) (a tail : new.T lam)
    (hv : VecGood (.snoc (k + 1) v a))
    (hane : a ≠ new.T.Z)
    (halt : trans a < trans (new.T.P (.snoc (k + 1) v a) tail)) :
    let M := T.add
      (T.card_times (k + 1) (T.one_del (trans a))) (transAux v).2
    M < T.P (k + 1) M T.Z := by
  let M := T.add
    (T.card_times (k + 1) (T.one_del (trans a))) (transAux v).2
  have ha := VecGood_last v a hv
  have hp := VecGood_prefix v a hv
  have htrane : trans a ≠ T.Z := trans_ne_zero_of_ne_zero a hane
  cases hta : trans a with
  | Z => exact False.elim (htrane hta)
  | P p c d =>
      have hhead :
          T.head (trans a) ≤
            T.head (trans (new.T.P (.snoc (k + 1) v a) tail)) :=
        T.head_mono_le _ _ (Or.inl halt)
      rw [trans_P_head, aux_head_snoc v a hane] at hhead
      change T.P p c T.Z ≤ T.P (k + 1) M T.Z at hhead
      have hpk : p ≤ k + 1 := T.head_le_index p (k + 1) c M hhead
      have htaNF : T.isNF1 (T.P p c d) := by simpa [hta] using ha.1
      have hidxTa : T.index_Prop1 (k + 1) (trans a) := by
        rw [hta]
        exact T.isNF1_index (k + 1) p c d htaNF hpk
      have hdelIdx : T.index_Prop1 (k + 1) (T.one_del (trans a)) :=
        one_del_index (k + 1) _ hidxTa
      have hcardIdx :
          T.index_Prop1 (k + 1)
            (T.card_times (k + 1) (T.one_del (trans a))) := by
        simpa only [Nat.max_self] using
          card_times_index (k + 1) (k + 1) _ hdelIdx
      have hlower := aux_lower_closed v hp
      have hlowerIdx :
          T.index_Prop1 (k + 1) (transAux v).2 :=
        Rank1Termination.index_mono (by omega) _ hlower.2.1
      have hMIdx : T.index_Prop1 (k + 1) M := by
        dsimp only [M]
        exact Rank1Termination.index_add (k + 1) _ _ hcardIdx hlowerIdx
      have hdelNF : T.isNF1 (T.one_del (trans a)) := one_del_NF _ ha.1
      have hdelGood :
          ∀ x : T, x ∈ T.G1 (k + 1) (T.one_del (trans a)) →
            x < T.one_del (trans a) :=
        one_del_good_pos (k + 1) (Nat.zero_lt_succ k) _ ha.1 ha.2
      have hMGood :
          ∀ x : T, x ∈ T.G1 (k + 1) M → x < M := by
        dsimp only [M]
        exact card_times_append_good (k + 1) k (Nat.lt_succ_self k)
          _ _ hdelNF hdelGood hlower.2.1
      exact good_index_lt_wrap (k + 1) M T.Z hMIdx hMGood


theorem aux_positive_middle_lt_of_head {lam k : Nat}
    (v : new.Vec (new.T lam) (k + 1)) (a : new.T lam)
    (hv : VecGood (.snoc (k + 1) v a))
    (hane : a ≠ new.T.Z) (C : T)
    (hheadC : T.head C = (transAux (.snoc (k + 1) v a)).1)
    (halt : trans a < C) :
    let M := T.add
      (T.card_times (k + 1) (T.one_del (trans a))) (transAux v).2
    M < T.P (k + 1) M T.Z := by
  let M := T.add
    (T.card_times (k + 1) (T.one_del (trans a))) (transAux v).2
  have ha := VecGood_last v a hv
  have hp := VecGood_prefix v a hv
  have htrane : trans a ≠ T.Z := trans_ne_zero_of_ne_zero a hane
  cases hta : trans a with
  | Z => exact False.elim (htrane hta)
  | P p c d =>
      have hhead : T.head (trans a) ≤ T.head C :=
        T.head_mono_le _ _ (Or.inl halt)
      rw [hheadC, aux_head_snoc v a hane] at hhead
      change T.P p c T.Z ≤ T.P (k + 1) M T.Z at hhead
      have hpk : p ≤ k + 1 := T.head_le_index p (k + 1) c M hhead
      have htaNF : T.isNF1 (T.P p c d) := by simpa [hta] using ha.1
      have hidxTa : T.index_Prop1 (k + 1) (trans a) := by
        rw [hta]
        exact T.isNF1_index (k + 1) p c d htaNF hpk
      have hdelIdx : T.index_Prop1 (k + 1) (T.one_del (trans a)) :=
        one_del_index (k + 1) _ hidxTa
      have hcardIdx :
          T.index_Prop1 (k + 1)
            (T.card_times (k + 1) (T.one_del (trans a))) := by
        simpa only [Nat.max_self] using
          card_times_index (k + 1) (k + 1) _ hdelIdx
      have hlower := aux_lower_closed v hp
      have hlowerIdx :
          T.index_Prop1 (k + 1) (transAux v).2 :=
        Rank1Termination.index_mono (by omega) _ hlower.2.1
      have hMIdx : T.index_Prop1 (k + 1) M := by
        dsimp only [M]
        exact Rank1Termination.index_add (k + 1) _ _ hcardIdx hlowerIdx
      have hdelNF : T.isNF1 (T.one_del (trans a)) := one_del_NF _ ha.1
      have hdelGood :
          ∀ x : T, x ∈ T.G1 (k + 1) (T.one_del (trans a)) →
            x < T.one_del (trans a) :=
        one_del_good_pos (k + 1) (Nat.zero_lt_succ k) _ ha.1 ha.2
      have hMGood :
          ∀ x : T, x ∈ T.G1 (k + 1) M → x < M := by
        dsimp only [M]
        exact card_times_append_good (k + 1) k (Nat.lt_succ_self k)
          _ _ hdelNF hdelGood hlower.2.1
      exact good_index_lt_wrap (k + 1) M T.Z hMIdx hMGood

theorem aux_head_support_decomp {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (hv : VecGood v)
    (C : T) (hheadC : T.head C = (transAux v).1)
    (hcoord : ∀ i : Fin k, u ≤ i.val → trans (v.idx i) < C) :
    (∀ i : Fin k, u ≤ i.val →
      ∀ y : T, y ∈ T.G1 u (trans (v.idx i)) →
        y < trans (v.idx i) ∨
          ∃ z : new.T lam, z ∈ new.T.Gi u (v.idx i) ∧ y ≤ trans z) →
    ∀ x : T, x ∈ T.G1 u (transAux v).1 →
      x < (transAux v).1 ∨ VecWitness u v x := by
  induction v with
  | nil =>
      intro _ x hx
      by_cases hu : u ≤ 0
      · simp [transAux, T.G1, hu] at hx
        subst x
        exact Or.inl (T.Lt.Z_lt_P _ _ _)
      · simp [transAux, T.G1, hu] at hx
  | snoc k v a ih =>
      intro hdec
      have ha := VecGood_last v a hv
      have hp := VecGood_prefix v a hv
      have hdecPrefix :
          ∀ i : Fin k, u ≤ i.val →
            ∀ y : T, y ∈ T.G1 u (trans (v.idx i)) →
              y < trans (v.idx i) ∨
                ∃ z : new.T lam, z ∈ new.T.Gi u (v.idx i) ∧ y ≤ trans z := by
        intro i hui y hy
        simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
          hdec i.castSucc hui y hy
      have hcoordPrefix :
          ∀ i : Fin k, u ≤ i.val → trans (v.idx i) < C := by
        intro i hui
        simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
          hcoord i.castSucc hui
      cases k with
      | zero =>
          cases v
          by_cases hu : u ≤ 0
          · have hdecLast :
                ∀ y : T, y ∈ T.G1 u (trans a) →
                  y < trans a ∨
                    ∃ z : new.T lam, z ∈ new.T.Gi u a ∧ y ≤ trans z := by
              simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using
                hdec (Fin.last 0) hu
            rw [aux_single]
            intro x hx
            simp only [T.G1, hu, ite_true, List.append_nil,
              List.mem_append, List.mem_singleton] at hx
            rcases hx with rfl | hx
            · exact Or.inr (VecWitness_last u new.Vec.nil a hu _ (Or.inr rfl))
            · rcases hdecLast x hx with h | ⟨z, hz, hxz⟩
              · exact Or.inr (VecWitness_last u new.Vec.nil a hu x (Or.inl h))
              · exact Or.inr
                  (VecWitness_last_support u new.Vec.nil a z hu x hz hxz)
          · rw [aux_single]
            intro x hx
            simp [T.G1, hu] at hx
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            have hheadPrefix : T.head C = (transAux v).1 := by
              rw [← aux_zero_tail v]
              exact hheadC
            intro x hx
            rw [aux_zero_tail] at hx
            rcases ih hp C hheadPrefix hcoordPrefix hdecPrefix x hx with h | h
            · exact Or.inl h
            · exact Or.inr (VecWitness_prefix u v new.T.Z x h)
          · have htrane : trans a ≠ T.Z := trans_ne_zero_of_ne_zero a haz
            have hlastCoord :
                ∀ hle : u ≤ k + 1, trans a < C := by
              intro hle
              simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using
                hcoord (Fin.last (k + 1)) hle
            by_cases huk : u ≤ k + 1
            · have hdecLast :
                  ∀ y : T, y ∈ T.G1 u (trans a) →
                    y < trans a ∨
                      ∃ z : new.T lam, z ∈ new.T.Gi u a ∧ y ≤ trans z := by
                simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using
                  hdec (Fin.last (k + 1)) huk
              let M := T.add
                (T.card_times (k + 1) (T.one_del (trans a))) (transAux v).2
              have hMlt : M < T.P (k + 1) M T.Z := by
                exact aux_positive_middle_lt_of_head v a hv haz C hheadC (hlastCoord huk)
              rw [aux_head_snoc v a haz]
              intro x hx
              simp only [T.G1, huk, ite_true, List.append_nil,
                List.mem_append, List.mem_singleton] at hx
              rcases hx with rfl | hx
              · exact Or.inl hMlt
              · dsimp only [M] at hx
                rw [G1_add] at hx
                rcases hx with hx | hx
                · have hdelNF : T.isNF1 (T.one_del (trans a)) := one_del_NF _ ha.1
                  have hdecDel :
                      ∀ y : T, y ∈ T.G1 u (T.one_del (trans a)) →
                        y < trans a ∨ VecWitness u (.snoc (k + 1) v a) y := by
                    intro y hy
                    have hyt := one_del_G1_subset u (trans a) y hy
                    rcases hdecLast y hyt with h | ⟨z, hz, hyz⟩
                    · exact Or.inl h
                    · exact Or.inr
                        (VecWitness_last_support u v a z huk y hz hyz)
                  rcases card_times_support_decomp u (k + 1) huk
                      (VecWitness u (.snoc (k + 1) v a))
                      (fun x y hxy hy => VecWitness_mono u _ x y hxy hy)
                      (T.one_del (trans a)) (trans a) hdelNF
                      (one_del_le _ ha.1) hdecDel x hx with h | h | h
                  · have hxM : x < M := by
                      dsimp only [M]
                      exact lt_of_lt_of_le_thm T _ _ _ h (add_self_le _ _)
                    exact Or.inl (lt_trans_thm _ _ _ hxM hMlt)
                  · exact Or.inr
                      (VecWitness_last u v a huk x (Or.inl h))
                  · exact Or.inr h
                · rcases aux_lower_support_decomp u v hp hdecPrefix x hx with h | h
                  · have hlower := aux_lower_closed v hp
                    have hMNF :
                        T.isNF1 M := by
                      dsimp only [M]
                      exact card_times_append_closed (k + 1)
                        (T.one_del (trans a)) (transAux v).2
                        (one_del_NF _ ha.1) hlower.1 hlower.2.2
                    have hxM : x < M := by
                      dsimp only [M] at hMNF ⊢
                      exact lt_of_lt_of_le_thm T _ _ _ h
                        (add_right_le_of_NF _ _ hMNF)
                    exact Or.inl (lt_trans_thm _ _ _ hxM hMlt)
                  · exact Or.inr (VecWitness_prefix u v a x h)
            · rw [aux_head_snoc v a haz]
              intro x hx
              simp [T.G1, huk] at hx

end LegacyTranslation

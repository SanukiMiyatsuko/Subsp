import Subsp.old.stop_algebra

/-! Legacy normal-form and order-preservation layer for the translation.
The grouping follows the role of `Subsp.new.stop_nf_order`.
-/

-- Merged from Subsp/old/stop_principal.lean
/-! Principal normal forms of the legacy translation and conditional order preservation. -/

namespace LegacyTranslation

open T

theorem add_left_lt (p a b : T) (h : a < b) : T.add p a < T.add p b := by
  induction p with
  | Z => exact h
  | P q c d _ ih =>
      rw [T.P_add_eq, T.P_add_eq]
      exact .p_tail _ _ _ _ ih

theorem card_times_append_lt (n : Nat) (s t l r : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hst : s < t) (hl : l < T.P n T.Z T.Z) :
    T.add (T.card_times n s) l < T.add (T.card_times n t) r := by
  induction hst with
  | Z_lt_P p a b =>
      rw [card_times_P, T.P_add_eq]
      exact lt_of_lt_of_le_thm T _ _ _ hl
        (partial_order.trans _ _ _ (head_base_le n (max p n) _ (Nat.le_max_right p n))
          (head_le_self (T.P (max p n) (cardArg n p a) (T.add (T.card_times n b) r))))
  | p_head p q a c b d hpq =>
      rw [card_times_P, card_times_P, T.P_add_eq, T.P_add_eq]
      obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
      obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
      exact card_heads_lt n p q a c _ _ hpq ha hga hc hgc
  | p_mid p a c b d hac _ =>
      rw [card_times_P, card_times_P, T.P_add_eq, T.P_add_eq]
      obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
      obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
      exact .p_mid _ _ _ _ _ (cardArg_lt_same n p a c ha hga hc hgc hac)
  | p_tail p a b d _ ih =>
      rw [card_times_P, card_times_P, T.P_add_eq, T.P_add_eq]
      exact .p_tail _ _ _ _ (ih (T.isNF1_P_inv _ _ _ hs).2.1 (T.isNF1_P_inv _ _ _ ht).2.1)

theorem one_del_le (s : T) (hs : T.isNF1 s) : T.one_del s ≤ s := by
  match s, hs with
  | .P 0 .Z b, hs => exact T.isNF1_tail_le _ hs _ _ _ rfl
  | .Z, _ | .P (_ + 1) _ _, _ | .P 0 (.P _ _ _) _, _ => exact Or.inr rfl

theorem one_del_lt (s t : T) (hs : T.isNF1 s) (hne : s ≠ T.Z) (h : s < t) :
    T.one_del s < T.one_del t := by
  cases h with
  | Z_lt_P => exact False.elim (hne rfl)
  | p_head p q a c b d hpq =>
      cases q with
      | zero => exact False.elim (Nat.not_lt_zero _ hpq)
      | succ q => exact lt_of_le_of_lt_thm T _ _ _ (one_del_le _ hs) (.p_head _ _ _ _ _ _ hpq)
  | p_mid p a c b d hac =>
      cases p with
      | zero =>
          cases c with
          | Z => exact False.elim (lt_Z_inv hac)
          | P q e f => exact lt_of_le_of_lt_thm T _ _ _ (one_del_le _ hs) (.p_mid _ _ _ _ _ hac)
      | succ p => exact .p_mid _ _ _ _ _ hac
  | p_tail p a b d hbd =>
      cases p with
      | zero =>
          cases a with
          | Z => exact hbd
          | P _ _ _ => exact .p_tail _ _ _ _ hbd
      | succ _ => exact .p_tail _ _ _ _ hbd

def VecGood {lam k : Nat} (v : new.Vec (new.T lam) k) : Prop :=
  ∀ i : Fin k, T.isNF1 (trans (v.idx i)) ∧ ∀ x ∈ T.G1 i.val (trans (v.idx i)), x < trans (v.idx i)

theorem VecGood_prefix {lam k : Nat} (v : new.Vec (new.T lam) k) (a : new.T lam)
    (h : VecGood (.snoc k v a)) : VecGood v := fun i => by
  simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using h i.castSucc

theorem VecGood_last {lam k : Nat} (v : new.Vec (new.T lam) k) (a : new.T lam)
    (h : VecGood (.snoc k v a)) : T.isNF1 (trans a) ∧ ∀ x ∈ T.G1 k (trans a), x < trans a := by
  simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using h (Fin.last k)

theorem aux_single {lam : Nat} (a : new.T lam) :
    transAux (.snoc 0 .nil a) = (T.P 0 (trans a) T.Z, T.early_collapse 0 (trans a)) := by
  cases a <;> rfl

theorem aux_lower_snoc {lam k : Nat} (v : new.Vec (new.T lam) (k + 1)) (a : new.T lam) :
    (transAux (.snoc (k + 1) v a)).2 =
      T.add (T.card_times (k + 1) (T.early_collapse (k + 1) (trans a))) (transAux v).2 := by
  cases a <;> rfl

theorem aux_head_snoc {lam k : Nat} (v : new.Vec (new.T lam) (k + 1)) (a : new.T lam)
    (ha : a ≠ new.T.Z) : (transAux (.snoc (k + 1) v a)).1 =
      T.P (k + 1) (T.add (T.card_times (k + 1) (T.one_del (trans a))) (transAux v).2) T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P _ _ => rfl

theorem aux_lower_closed {lam k : Nat} (v : new.Vec (new.T lam) k) (hv : VecGood v) :
    T.isNF1 (transAux v).2 ∧ T.index_Prop1 (k - 1) (transAux v).2 ∧
      (transAux v).2 < T.P k T.Z T.Z := by
  induction v with
  | nil => exact ⟨.z, .z, .Z_lt_P _ _ _⟩
  | snoc k v a ih =>
      have ha := VecGood_last v a hv
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          obtain ⟨hnf, hi⟩ := early_collapse_closed 0 (trans a) ha.1 ha.2
          exact ⟨hnf, hi, index_Prop1_lt_succ 0 _ hi⟩
      | succ k =>
          obtain ⟨hvNF, hvIdx, hvBound⟩ := ih (VecGood_prefix v a hv)
          obtain ⟨heNF, heIdx⟩ := early_collapse_closed (k + 1) (trans a) ha.1 ha.2
          rw [aux_lower_snoc]
          have hidx : T.index_Prop1 (k + 1)
              (T.add (T.card_times (k + 1) (T.early_collapse (k + 1) (trans a))) (transAux v).2) :=
            Rank1Termination.index_add _ _ _
              (by simpa only [Nat.max_self] using card_times_index (k + 1) (k + 1) _ heIdx)
              (Rank1Termination.index_mono (by omega) _ hvIdx)
          exact ⟨card_times_append_closed (k + 1) _ _ heNF hvNF hvBound,
            hidx, index_Prop1_lt_succ (k + 1) _ hidx⟩

theorem aux_head_closed {lam k : Nat} (v : new.Vec (new.T lam) k) (hv : VecGood v) :
    T.isNF1 (transAux v).1 := by
  induction v with
  | nil => exact .p 0 T.Z T.Z .z .z (fun x hx => by cases hx) (T.Z_le _)
  | snoc k v a ih =>
      have ha := VecGood_last v a hv
      have hp := VecGood_prefix v a hv
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          exact .p 0 (trans a) T.Z ha.1 .z ha.2 (T.Z_le _)
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            rw [aux_zero_tail]
            exact ih hp
          · rw [aux_head_snoc v a haz]
            obtain ⟨hlNF, hlIdx, hlBound⟩ := aux_lower_closed v hp
            have haNF := one_del_NF _ ha.1
            have haGood := one_del_good_pos (k + 1) (Nat.zero_lt_succ k) _ ha.1 ha.2
            exact .p (k + 1) _ T.Z (card_times_append_closed _ _ _ haNF hlNF hlBound) .z
              (card_times_append_good (k + 1) k (Nat.lt_succ_self k) _ _ haNF haGood hlIdx)
              (T.Z_le _)

/-! Lexicographic comparison of the two components of `transAux`. -/

theorem aux_lt {lam k : Nat} (v w : new.Vec (new.T lam) k)
    (hv : VecGood v) (hw : VecGood w)
    (hm : ∀ i : Fin k, v.idx i < w.idx i → trans (v.idx i) < trans (w.idx i))
    (hlt : new.compareVec v w = .lt) :
    (transAux v).2 < (transAux w).2 ∧ (transAux v).1 < (transAux w).1 := by
  induction v with
  | nil => cases w; cases hlt
  | snoc k v a ih =>
      cases w with
      | snoc _ w b =>
          have ha := VecGood_last v a hv
          have hb := VecGood_last w b hw
          have hvp := VecGood_prefix v a hv
          have hmab : a < b → trans a < trans b := by
            simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using hm (Fin.last k)
          have hcmp : a < b ∨ (a = b ∧ new.compareVec v w = .lt) := by
            simp only [new.compareVec] at hlt
            cases hab : new.compareT a b with
            | lt => exact Or.inl hab
            | eq => exact Or.inr ⟨new.T_eq_sound a b hab, by simpa only [hab] using hlt⟩
            | gt => simp [hab] at hlt
          rcases hcmp with hab | ⟨rfl, hrest⟩
          · have he := early_collapse_lt k _ _ ha.1 ha.2 hb.1 (hmab hab)
            cases k with
            | zero =>
                cases v; cases w
                rw [aux_single, aux_single]
                exact ⟨he, .p_mid _ _ _ _ _ (hmab hab)⟩
            | succ k =>
                have hbn : b ≠ new.T.Z := by intro he; subst b; cases a <;> cases hab
                rw [aux_lower_snoc, aux_lower_snoc, aux_head_snoc w b hbn]
                refine ⟨card_times_append_lt (k + 1) _ _ _ _
                  (early_collapse_closed (k + 1) _ ha.1 ha.2).1
                  (early_collapse_closed (k + 1) _ hb.1 hb.2).1 he (aux_lower_closed v hvp).2.2, ?_⟩
                by_cases haz : a = new.T.Z
                · subst a
                  rw [aux_zero_tail]
                  obtain ⟨p, c, he, hp⟩ := aux_principal v
                  rw [he]
                  exact .p_head _ _ _ _ _ _ (by omega)
                · rw [aux_head_snoc v a haz]
                  exact .p_mid _ _ _ _ _ (card_times_append_lt (k + 1) _ _ _ _
                    (one_del_NF _ ha.1) (one_del_NF _ hb.1)
                    (one_del_lt _ _ ha.1 (trans_ne_zero_of_ne_zero a haz) (hmab hab))
                    (aux_lower_closed v hvp).2.2)
          · cases k with
            | zero => cases v; cases w; cases hrest
            | succ k =>
                obtain ⟨ih2, ih1⟩ := ih w hvp (VecGood_prefix w a hw) (fun i => by
                  simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
                    hm i.castSucc) hrest
                rw [aux_lower_snoc, aux_lower_snoc]
                refine ⟨add_left_lt _ _ _ ih2, ?_⟩
                by_cases haz : a = new.T.Z
                · subst a
                  rw [aux_zero_tail, aux_zero_tail]
                  exact ih1
                · rw [aux_head_snoc v a haz, aux_head_snoc w a haz]
                  exact .p_mid _ _ _ _ _ (add_left_lt _ _ _ ih2)

theorem trans_P_head {lam : Nat} (v : new.Vec (new.T lam) lam) (b : new.T lam) :
    T.head (trans (new.T.P v b)) = (transAux v).1 := by
  obtain ⟨p, a, he, _⟩ := aux_principal v
  rw [trans_as_add, he, p_zero_add]
  rfl

/-! Order and normal-form preservation from smaller indexed components. -/

def GoodAt {lam : Nat} (u : Nat) (s : new.T lam) : Prop :=
  T.isNF1 (trans s) ∧ ∀ x ∈ T.G1 u (trans s), x < trans s

theorem good_index_lt_wrap (k : Nat) (a b : T) (hi : T.index_Prop1 k a)
    (hg : ∀ x : T, x ∈ T.G1 k a → x < a) : a < T.P k a b := by
  cases hi with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p c d hp _ =>
      rcases Nat.eq_or_lt_of_le hp with rfl | hp
      · exact T.Lt.p_mid _ _ _ _ _ (hg c (by simp [T.G1]))
      · exact T.Lt.p_head _ _ _ _ _ _ hp

theorem order_preserve_bounded {lam : Nat} (N : Nat)
    (hgood : ∀ (s : new.T lam), new.T.size s < N → ∀ u, new.T.isNFComp u s → GoodAt u s)
    (s t : new.T lam) (hsz : new.T.size s ≤ N) (htz : new.T.size t ≤ N)
    (hs : new.T.isNF s) (ht : new.T.isNF t) (hlt : s < t) : trans s < trans t := by
  induction s using (measure new.T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z =>
          cases t with
          | Z => cases hlt
          | P w b =>
              obtain ⟨p, a, he, _⟩ := aux_principal w
              rw [trans_as_add, he, p_zero_add]
              exact .Z_lt_P _ _ _
      | P v a =>
          cases t with
          | Z => cases hlt
          | P w b =>
              obtain ⟨hv, ha, _⟩ := new.T.isNF_P_inv v a hs
              obtain ⟨hw, hb, _⟩ := new.T.isNF_P_inv w b ht
              change (match new.compareVec v w with
                | .eq => new.compareT a b | ord => ord) = .lt at hlt
              cases hc : new.compareVec v w with
              | lt =>
                  apply lt_of_head_lt
                  rw [trans_P_head, trans_P_head]
                  exact (aux_lt v w
                    (fun i => hgood _ (Nat.lt_of_lt_of_le (new.T.idx_size_lt_P v a i) hsz) i.val (hv i))
                    (fun i => hgood _ (Nat.lt_of_lt_of_le (new.T.idx_size_lt_P w b i) htz) i.val (hw i))
                    (fun i hi => ih _ (new.T.idx_size_lt_P v a i) _
                      (Nat.le_trans (Nat.le_of_lt (new.T.idx_size_lt_P v a i)) hsz)
                      (Nat.le_trans (Nat.le_of_lt (new.T.idx_size_lt_P w b i)) htz)
                      (hv i).1 (hw i).1 hi) hc).2
              | eq =>
                  obtain rfl := new.Vec_eq_sound v w hc
                  rw [new.Vec_refl] at hlt
                  rw [trans_as_add, trans_as_add]
                  exact add_left_lt _ _ _ (ih a (new.T.add_size_lt_P v a) b
                    (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P v a)) hsz)
                    (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P v b)) htz) ha hb hlt)
              | gt => simp [hc] at hlt

theorem NF_step {lam : Nat} (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hs : new.T.isNF (new.T.P v a))
    (hnf : ∀ s : new.T lam, new.T.size s < new.T.size (new.T.P v a) →
      new.T.isNF s → T.isNF1 (trans s))
    (hgood : ∀ s : new.T lam, new.T.size s < new.T.size (new.T.P v a) →
      ∀ u, new.T.isNFComp u s → GoodAt u s) :
    T.isNF1 (trans (new.T.P v a)) := by
  obtain ⟨hv, ha, hh⟩ := new.T.isNF_P_inv v a hs
  have hvg : VecGood v := fun i => hgood _ (new.T.idx_size_lt_P v a i) i.val (hv i)
  have hhead : T.head (trans a) ≤ (transAux v).1 := by
    cases a with
    | Z => exact T.Z_le _
    | P w b =>
        rw [trans_P_head]
        obtain ⟨hw, _, _⟩ := new.T.isNF_P_inv w b ha
        rcases hh with hh | hh
        · have hcmp : new.compareVec w v = .lt := by
            change (match new.compareVec w v with | .eq => Ordering.eq | ord => ord) = .lt at hh
            cases he : new.compareVec w v <;> simp_all
          refine Or.inl (aux_lt w v (fun i => hgood _ (Nat.lt_trans (new.T.idx_size_lt_P w b i)
            (new.T.add_size_lt_P v _)) i.val (hw i)) hvg (fun i hi => ?_) hcmp).2
          exact order_preserve_bounded (new.T.size (new.T.P v (new.T.P w b))) hgood _ _
            (Nat.le_of_lt (Nat.lt_trans (new.T.idx_size_lt_P w b i) (new.T.add_size_lt_P v _)))
            (Nat.le_of_lt (new.T.idx_size_lt_P v _ i)) (hw i).1 (hv i).1 hi
        · cases (new.T_eq_sound _ _ hh : new.T.P w new.T.Z = new.T.P v new.T.Z)
          exact Or.inr rfl
  have hprincipal := aux_head_closed v hvg
  obtain ⟨p, b, he, _⟩ := aux_principal v
  rw [he] at hprincipal hhead
  rw [trans_as_add, he, p_zero_add]
  obtain ⟨hb, _, hg, _⟩ := T.isNF1_P_inv _ _ _ hprincipal
  exact .p p b (trans a) hb (hnf a (new.T.add_size_lt_P v a) ha) hg hhead

theorem source_coord_mem_Gi {lam : Nat} (u : Nat) (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val) : v.idx i ∈ new.T.Gi u (new.T.P v a) :=
  (new.T.mem_Gi_P u v a (v.idx i)).2 (Or.inl ⟨i, hui, Or.inl rfl⟩)

theorem source_coord_support_mem_Gi {lam : Nat} (u : Nat) (v : new.Vec (new.T lam) lam)
    (a z : new.T lam) (i : Fin lam) (hui : u ≤ i.val) (hz : z ∈ new.T.Gi u (v.idx i)) :
    z ∈ new.T.Gi u (new.T.P v a) :=
  (new.T.mem_Gi_P u v a z).2 (Or.inl ⟨i, hui, Or.inr hz⟩)

theorem source_tail_support_mem_Gi {lam : Nat} (u : Nat) (v : new.Vec (new.T lam) lam)
    (a z : new.T lam) (hz : z ∈ new.T.Gi u a) : z ∈ new.T.Gi u (new.T.P v a) :=
  (new.T.mem_Gi_P u v a z).2 (Or.inr hz)

end LegacyTranslation

-- Merged from Subsp/old/stop_good_target.lean
/-! Target-side support bounds for cardinal multiplication and early collapse. -/

namespace LegacyTranslation

open T

/-- Every summand `P p c _` of a target term satisfies `Pr p c`. -/
def SumAll (Pr : Nat → T → Prop) : T → Prop
  | .Z => True
  | .P p c r => Pr p c ∧ SumAll Pr r

/-- `P p c _` occurs as a summand of a target term. -/
def IsSummand (p : Nat) (c : T) : T → Prop
  | .Z => False
  | .P q a r => (q = p ∧ a = c) ∨ IsSummand p c r

theorem SumAll_mono (Pr Qr : Nat → T → Prop) (h : ∀ p c, Pr p c → Qr p c) :
    ∀ t, SumAll Pr t → SumAll Qr t
  | .Z, _ => trivial
  | .P p c r, ⟨hpc, hr⟩ => ⟨h p c hpc, SumAll_mono Pr Qr h r hr⟩

theorem SumAll_of_summand (Pr : Nat → T → Prop) :
    ∀ t, (∀ p c, IsSummand p c t → Pr p c) → SumAll Pr t
  | .Z, _ => trivial
  | .P q a r, h => ⟨h q a (Or.inl ⟨rfl, rfl⟩),
      SumAll_of_summand Pr r (fun p c hs => h p c (Or.inr hs))⟩

theorem SumAll_part (Pr : Nat → T → Prop) (n : Nat) : ∀ t, SumAll Pr t →
    SumAll (fun p c => n < p ∧ Pr p c) (T.part n t).1 ∧
      SumAll (fun p c => p ≤ n ∧ Pr p c) (T.part n t).2
  | .Z, _ => ⟨trivial, trivial⟩
  | .P p c r, ⟨hpc, hr⟩ => by
      have ih := SumAll_part Pr n r hr
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true]
        exact ⟨ih.1, ⟨hp, hpc⟩, ih.2⟩
      · simp only [T.part, hp, ite_false]
        exact ⟨⟨⟨by omega, hpc⟩, ih.1⟩, ih.2⟩

theorem SumAll_one_del (Pr : Nat → T → Prop) (t : T) (h : SumAll Pr t) :
    SumAll Pr (T.one_del t) := by
  match t, h with
  | .P 0 .Z _, h => exact h.2
  | .Z, h | .P (_ + 1) _ _, h | .P 0 (.P _ _ _) _, h => exact h

theorem SumAll_G1_self (n : Nat) : ∀ t : T, SumAll (fun p c => n ≤ p → c ∈ T.G1 n t) t
  | .Z => trivial
  | .P p c r => by
      refine ⟨fun hnp => by simp [T.G1, hnp], ?_⟩
      apply SumAll_mono _ _ _ r (SumAll_G1_self n r)
      intro q d h hnq
      have hd := h hnq
      by_cases hnp : n ≤ p <;> simp [T.G1, hnp, hd]

theorem G1_of_SumAll (u : Nat) (R : T → Prop) : ∀ t : T,
    SumAll (fun p c => u ≤ p → R c ∧ ∀ y ∈ T.G1 u c, R y) t → ∀ y ∈ T.G1 u t, R y
  | .Z, _, y, hy => by cases hy
  | .P p c r, ⟨hpc, hr⟩, y, hy => by
      by_cases hup : u ≤ p
      · simp only [T.G1, hup, ite_true, List.mem_append, List.mem_singleton] at hy
        rcases hy with (rfl | hy) | hy
        · exact (hpc hup).1
        · exact (hpc hup).2 y hy
        · exact G1_of_SumAll u R r hr y hy
      · simp only [T.G1, hup, ite_false] at hy
        exact G1_of_SumAll u R r hr y hy

theorem summand_le_head (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    T.P K X T.Z ≤ T.head t
  | .Z, _, h => h.elim
  | .P p a r, ht, h => by
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inr rfl
      · have hr := (T.isNF1_P_inv p a r ht).2.1
        have hhd := (T.isNF1_P_inv p a r ht).2.2.2
        exact partial_order.trans _ _ _ (summand_le_head K X r hr h) hhd

theorem summand_head_part2 (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    T.P K X T.Z ≤ T.head (T.part K t).2
  | .Z, _, h => h.elim
  | .P p a r, ht, h => by
      have hr := (T.isNF1_P_inv p a r ht).2.1
      have hhd := (T.isNF1_P_inv p a r ht).2.2.2
      by_cases hp : p ≤ K
      · simp only [T.part, hp, ite_true, T.head]
        rcases h with ⟨rfl, rfl⟩ | h
        · exact Or.inr rfl
        · exact partial_order.trans _ _ _ (summand_le_head K X r hr h) hhd
      · simp only [T.part, hp, ite_false]
        rcases h with ⟨rfl, _⟩ | h
        · exact False.elim (hp (Nat.le_refl _))
        · exact summand_head_part2 K X r hr h

/-- A principal argument is below the ambient term once its high part is controlled. -/
theorem summand_arg_lt (K : Nat) (X tv TS : T) (hTS : T.isNF1 TS) (hX : T.isNF1 X)
    (htv : T.isNF1 tv) (hsum : IsSummand K X TS) (hlt : tv < TS)
    (hhigh : (T.part K tv).1 = (T.part K X).1)
    (hlow : (T.part K X).2 < T.P K X T.Z) : X < TS := by
  rcases part_lt_cases K tv TS htv hTS hlt with h | ⟨he, _⟩
  · rw [hhigh] at h
    exact lt_of_part_lt_cases K X TS hX hTS (Or.inl h)
  · apply lt_of_part_lt_cases K X TS hX hTS (Or.inr ⟨hhigh ▸ he, ?_⟩)
    exact lt_of_lt_of_le_thm T _ _ _ hlow
      (partial_order.trans _ _ _ (summand_head_part2 K X TS hTS hsum) (head_le_self _))

theorem stand_G1_subset (u : Nat) : ∀ s x : T, x ∈ T.G1 u (T.stand s) → x ∈ T.G1 u s
  | .Z, x, hx => hx
  | .P a b c, x, hx => by
      rw [T.stand] at hx
      split at hx
      · by_cases hu : u ≤ a
        · simp only [T.G1, hu, ite_true, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (stand_G1_subset u c x hx)
        · simp only [T.G1, hu, ite_false] at hx ⊢
          exact stand_G1_subset u c x hx
      · have h := stand_G1_subset u c x hx
        by_cases hu : u ≤ a <;> simp [T.G1, hu, h]

theorem card_stand_G1_subset (n u : Nat) : ∀ s x : T,
    x ∈ T.G1 u (T.card_times n (T.stand s)) → x ∈ T.G1 u (T.card_times n s)
  | .Z, x, hx => hx
  | .P a b c, x, hx => by
      rw [T.stand] at hx
      split at hx
      · rw [card_times_P] at hx ⊢
        by_cases hu : u ≤ max a n
        · simp only [T.G1, hu, ite_true, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (card_stand_G1_subset n u c x hx)
        · simp only [T.G1, hu, ite_false] at hx ⊢
          exact card_stand_G1_subset n u c x hx
      · have h := card_stand_G1_subset n u c x hx
        rw [card_times_P]
        by_cases hu : u ≤ max a n <;> simp [T.G1, hu, h]

theorem early_collapse_support_exact (u n : Nat) (s : T)
    (hun : u ≤ n) (hs : T.isNF1 s) :
    ∀ x : T, x ∈ T.G1 u (T.early_collapse n s) →
      x = (T.part n s).1 ∨ x ∈ T.G1 u s := by
  intro x hx
  rcases hp : T.part n s with ⟨a, b⟩
  have hb : T.isNF1 b := by
    simpa [hp] using (part_NF n s hs).2
  have hmem : ∀ y : T, y ∈ T.G1 u a ++ T.G1 u b → y ∈ T.G1 u s := by
    intro y hy
    rw [← part_add n s hs, hp, G1_add]
    exact hy
  simp only [T.early_collapse, hp] at hx
  split at hx
  · exact Or.inr (hmem x (List.mem_append_right _ hx))
  · rw [T.stand, stand_eq_self b hb] at hx
    split at hx
    · simp only [T.G1, hun, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · exact Or.inl rfl
      · exact Or.inr (hmem x (List.mem_append_left _ hx))
      · exact Or.inr (hmem x (List.mem_append_right _ hx))
    · exact Or.inr (hmem x (List.mem_append_right _ hx))

theorem early_collapse_le_wrap (n : Nat) (a : T) (ha : T.isNF1 a)
    (hg : ∀ x ∈ T.G1 n a, x < a) :
    T.early_collapse n a ≤ T.P n a T.Z := by
  have hlow := part_snd_lt_wrap n a T.Z ha hg
  dsimp only [T.early_collapse]
  split
  · exact Or.inl hlow
  · rw [T.stand, stand_eq_self _ (part_NF n a ha).2]
    split
    · have he := part_add n a ha
      cases hb : (T.part n a).2 with
      | Z => rw [hb, T.add_Z] at he; rw [he]; exact Or.inr rfl
      | P q d e =>
          refine Or.inl (T.Lt.p_mid _ _ _ _ _ ?_)
          have hlt := add_lt_add_of_ne_Z (T.part n a).1 (T.part n a).2 (by rw [hb]; intro h; cases h)
          rwa [he] at hlt
    · exact Or.inl hlow

theorem cardArg_le_head (n p : Nat) (a b : T) (hs : T.isNF1 (T.P p a b))
    (hcase : p < n ∨ (p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z)) :
    cardArg n p a ≤ T.P p a T.Z := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  rcases hcase with hpn | ⟨rfl, hlt⟩
  · by_cases hp : p = 0
    · subst p
      simp only [cardArg, hpn, ite_true]
      exact early_collapse_le_wrap 0 a ha hga
    · simp only [cardArg, hpn, hp, ite_true, ite_false]
      have he := early_collapse_closed p a ha hga
      rw [T.stand, stand_eq_self _ he.1]
      split
      · cases a with
        | Z => exact Or.inr (by simp [T.early_collapse, T.part])
        | P q d e => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))
      · exact early_collapse_le_wrap p a ha hga
  · simp only [cardArg, Nat.lt_irrefl, hlt, and_self, ite_true, ite_false]
    cases a with
    | Z => exact Or.inr rfl
    | P q d e => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))

/-- Hypotheses on a summand `P p c _` used to bound the supports of cardinal products. -/
def CardCond (n u : Nat) (R : T → Prop) (p : Nat) (c : T) : Prop :=
  (n ≤ p → R c) ∧ (u ≤ p → ∀ y ∈ T.G1 u c, R y) ∧ (u ≤ p → p < n → R (T.part p c).1)

theorem card_times_support_bounded (n u : Nat) (hun : u ≤ n) (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) :
    ∀ s : T, T.isNF1 s → R s → SumAll (CardCond n u R) s →
      ∀ y ∈ T.G1 u (T.card_times n s), R y := by
  intro s hs
  induction hs with
  | z => intro _ _ y hy; cases hy
  | p p a b ha hb hga hh _ ihb =>
      intro hRs hsum y hy
      have hsfull : T.isNF1 (T.P p a b) := .p p a b ha hb hga hh
      obtain ⟨⟨hc1, hc2, hc3⟩, hsb⟩ := hsum
      have hRZ : R T.Z := hR _ _ (T.Z_le _) hRs
      have hRhead : R (T.P p a T.Z) := hR _ _ (head_le_self (T.P p a b)) hRs
      have hRb : R b := hR _ _ (T.isNF1_tail_le _ hsfull p a b rfl) hRs
      rw [card_times_P] at hy
      have hum : u ≤ max p n := Nat.le_trans hun (Nat.le_max_right p n)
      simp only [T.G1, hum, ite_true, List.mem_append, List.mem_singleton] at hy
      rcases hy with (rfl | hy) | hy
      · by_cases hcase : p < n ∨ (p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z)
        · exact hR _ _ (cardArg_le_head n p a b hsfull hcase) hRhead
        · rw [show cardArg n p a = a by
            unfold cardArg
            rw [ite_eq_right (fun h => hcase (Or.inl h)), ite_eq_right (fun h => hcase (Or.inr h))]]
          exact hc1 (Nat.le_of_not_gt fun h => hcase (Or.inl h))
      · by_cases hpn : p < n
        · by_cases hp : p = 0
          · subst p
            simp only [cardArg, hpn, ite_true] at hy
            by_cases hu0 : u = 0
            · subst u
              rcases early_collapse_support_exact 0 0 a (Nat.le_refl 0) ha y hy with h | h
              · rw [h]; exact hc3 (Nat.le_refl 0) hpn
              · exact hc2 (Nat.le_refl 0) y h
            · have hi := (early_collapse_closed 0 a ha hga).2
              rw [index_Prop1_G1_empty 0 _ hi u (Nat.pos_of_ne_zero hu0)] at hy
              cases hy
          · simp only [cardArg, hpn, hp, ite_true, ite_false] at hy
            have hy' := stand_G1_subset u _ y hy
            by_cases hup : u ≤ p
            · simp only [T.G1, hup, ite_true, List.mem_append, List.mem_singleton,
                List.not_mem_nil, or_false] at hy'
              rcases hy' with rfl | hy'
              · exact hRZ
              · rcases early_collapse_support_exact u p a hup ha y hy' with h | h
                · rw [h]; exact hc3 hup hpn
                · exact hc2 hup y h
            · simp only [T.G1, hup, ite_false] at hy'
              have hi := (early_collapse_closed p a ha hga).2
              rw [index_Prop1_G1_empty p _ hi u (by omega)] at hy'
              cases hy'
        · by_cases hcase : p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z
          · obtain ⟨rfl, hlt⟩ := hcase
            simp only [cardArg, Nat.lt_irrefl, hlt, and_self, ite_true, ite_false] at hy
            simp only [T.G1, hun, ite_true, List.mem_append, List.mem_singleton,
              List.not_mem_nil, or_false] at hy
            rcases hy with rfl | hy
            · exact hRZ
            · exact hc2 hun y hy
          · rw [show cardArg n p a = a by unfold cardArg; rw [ite_eq_right hpn, ite_eq_right hcase]]
              at hy
            exact hc2 (Nat.le_trans hun (Nat.le_of_not_gt hpn)) y hy
      · exact ihb hRb hsb y hy

theorem early_card_support_bounded (n u : Nat) (hun : u ≤ n) (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) (t : T) (ht : T.isNF1 t) (hRt : R t)
    (hsum : SumAll (CardCond n u R) t) :
    ∀ y ∈ T.G1 u (T.card_times n (T.early_collapse n t)), R y := by
  have hpart := SumAll_part _ n t hsum
  have hLNF := (part_NF n t ht).2
  have hHNF := (part_NF n t ht).1
  have hRL : R (T.part n t).2 := by
    apply hR _ _ _ hRt
    have h := add_right_le_of_NF (T.part n t).1 (T.part n t).2 (by rw [part_add n t ht]; exact ht)
    rwa [part_add n t ht] at h
  have hLsum : SumAll (CardCond n u R) (T.part n t).2 :=
    SumAll_mono _ _ (fun _ _ h => h.2) _ hpart.2
  have hLsup := card_times_support_bounded n u hun R hR _ hLNF hRL hLsum
  dsimp only [T.early_collapse]
  split
  · exact hLsup
  · rename_i hne
    intro y hy
    have hy' := card_stand_G1_subset n u _ y hy
    rw [card_times_P, Nat.max_self] at hy'
    have hca : cardArg n n (T.part n t).1 = (T.part n t).1 := by
      cases hH : (T.part n t).1 with
      | Z => exact False.elim (hne hH)
      | P q d e =>
          unfold cardArg
          rw [ite_eq_right (Nat.lt_irrefl n), ite_eq_right fun ⟨_, hlt⟩ =>
            lt_asymm_thm hlt (T.Lt.p_head _ _ _ _ _ _ (part_first_head_gt n q t d e hH))]
    rw [hca] at hy'
    simp only [T.G1, hun, ite_true, List.mem_append, List.mem_singleton] at hy'
    rcases hy' with (rfl | hy') | hy'
    · exact hR _ _ (part_first_le n t ht) hRt
    · apply G1_of_SumAll u R _ _ y hy'
      apply SumAll_mono _ _ _ _ hpart.1
      intro p c ⟨hnp, hc1, hc2, _⟩ hup
      exact ⟨hc1 (Nat.le_of_lt hnp), hc2 hup⟩
    · exact hLsup y hy'

end LegacyTranslation

-- Merged from Subsp/old/stop_good.lean
/-! Normal forms and order preservation of the legacy translation on indexed normal forms. -/

namespace LegacyTranslation

open T

theorem SumAll_and3 (P1 P2 P3 : Nat → T → Prop) :
    ∀ t, SumAll P1 t → SumAll P2 t → SumAll P3 t →
      SumAll (fun p c => P1 p c ∧ P2 p c ∧ P3 p c) t
  | .Z, _, _, _ => trivial
  | .P _ _ r, ⟨h1, r1⟩, ⟨h2, r2⟩, ⟨h3, r3⟩ => ⟨⟨h1, h2, h3⟩, SumAll_and3 P1 P2 P3 r r1 r2 r3⟩

theorem part_add_distrib (n : Nat) : ∀ a b : T,
    T.part n (T.add a b) =
      (T.add (T.part n a).1 (T.part n b).1, T.add (T.part n a).2 (T.part n b).2)
  | .Z, b => by simp only [T.part, zero_add]
  | .P p c r, b => by
      rw [T.P_add_eq]
      have ih := part_add_distrib n r b
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true, ih, T.P_add_eq]
      · simp only [T.part, hp, ite_false, ih, T.P_add_eq]

theorem part_card_times (n : Nat) : ∀ s : T,
    (T.part n (T.card_times n s)).1 = (T.part n s).1 ∧
      (T.part n (T.card_times n s)).2 = T.card_times n (T.part n s).2
  | .Z => ⟨rfl, rfl⟩
  | .P p a r => by
      have ih := part_card_times n r
      rw [card_times_P]
      by_cases hp : p ≤ n
      · have hm : max p n = n := Nat.max_eq_right hp
        simp only [T.part, hm, Nat.le_refl, hp, ite_true, ih, card_times_P]
        exact ⟨trivial, trivial⟩
      · have hm : max p n = p := Nat.max_eq_left (by omega)
        have hca : cardArg n p a = a := by
          unfold cardArg
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [T.part, hm, hp, ite_false, ih, hca]
        exact ⟨trivial, trivial⟩

theorem part_one_del_fst (n : Nat) (t : T) : (T.part n (T.one_del t)).1 = (T.part n t).1 := by
  match t with
  | .P 0 .Z b => simp [T.one_del, T.part]
  | .Z | .P (_ + 1) _ _ | .P 0 (.P _ _ _) _ => rfl

/-! Bounds for the auxiliary vector translation. -/

def CoordHyp {lam : Nat} (u : Nat) (C : T) (i : Nat) (x : new.T lam) : Prop :=
  (∀ y ∈ T.G1 u (T.card_times i (T.early_collapse i (trans x))), y < C) ∧
  (u ≤ i → ∀ y ∈ T.G1 u (T.card_times i (T.one_del (trans x))), y < C) ∧
  (i = 0 → ∀ y ∈ T.G1 u (T.early_collapse 0 (trans x)), y < C) ∧
  (i = 0 → u = 0 → ∀ y ∈ T.G1 u (trans x), y < C)

theorem aux_support_bounded {lam : Nat} (u : Nat) (C : T) : ∀ {k : Nat}
    (v : new.Vec (new.T lam) k),
    (∀ i : Fin k, CoordHyp u C i.val (v.idx i)) →
    (∀ y ∈ T.G1 u (transAux v).2, y < C) ∧
      ∀ p a, (transAux v).1 = T.P p a T.Z → u ≤ p → ∀ y ∈ T.G1 u a, y < C
  | _, .nil, _ => by
      refine ⟨fun y hy => by simp [transAux, T.G1] at hy, ?_⟩
      intro p a he _ y hy
      change T.P 0 T.Z T.Z = T.P p a T.Z at he
      cases he
      cases hy
  | _, .snoc k v a, hv => by
      have hlast : CoordHyp u C k a := by
        simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using hv (Fin.last k)
      have hpre : ∀ i : Fin k, CoordHyp u C i.val (v.idx i) := by
        intro i
        simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using hv i.castSucc
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          refine ⟨hlast.2.2.1 rfl, ?_⟩
          intro p b he hup y hy
          cases he
          exact hlast.2.2.2 rfl (Nat.eq_zero_of_le_zero hup) y hy
      | succ k =>
          have ih := aux_support_bounded u C v hpre
          refine ⟨?_, ?_⟩
          · rw [aux_lower_snoc]
            intro y hy
            rw [G1_add, List.mem_append] at hy
            rcases hy with hy | hy
            · exact hlast.1 y hy
            · exact ih.1 y hy
          · intro p b he hup y hy
            by_cases haz : a = new.T.Z
            · subst a
              rw [aux_zero_tail] at he
              exact ih.2 p b he hup y hy
            · rw [aux_head_snoc v a haz] at he
              cases he
              rw [G1_add, List.mem_append] at hy
              rcases hy with hy | hy
              · exact hlast.2.1 hup y hy
              · exact ih.1 y hy

theorem coord_hyp_of {lam : Nat} (u : Nat) (C : T) (i : Nat) (x : new.T lam)
    (hx : GoodAt i x)
    (hxC : u ≤ i → trans x < C)
    (hsum : u ≤ i → SumAll (CardCond i u (· < C)) (trans x)) :
    CoordHyp u C i x := by
  have hR : ∀ a b : T, a ≤ b → b < C → a < C := fun a b h1 h2 => lt_of_le_of_lt_thm T _ _ _ h1 h2
  have hec := early_collapse_closed i (trans x) hx.1 hx.2
  by_cases hui : u ≤ i
  · refine ⟨early_card_support_bounded i u hui (· < C) hR (trans x) hx.1 (hxC hui) (hsum hui),
      fun _ => card_times_support_bounded i u hui (· < C) hR _ (one_del_NF _ hx.1)
        (hR _ _ (one_del_le _ hx.1) (hxC hui)) (SumAll_one_del _ _ (hsum hui)), ?_, ?_⟩
    · intro hi0 y hy
      subst i
      have hu0 : u = 0 := Nat.eq_zero_of_le_zero hui
      subst u
      rcases early_collapse_support_exact 0 0 (trans x) (Nat.le_refl 0) hx.1 y hy with h | h
      · rw [h]
        exact hR _ _ (part_first_le 0 _ hx.1) (hxC hui)
      · exact lt_trans_thm _ _ _ (hx.2 y h) (hxC hui)
    · intro hi0 hu0 y hy
      subst i
      subst hu0
      exact lt_trans_thm _ _ _ (hx.2 y hy) (hxC hui)
  · have hui' : i < u := Nat.lt_of_not_le hui
    refine ⟨?_, fun h => absurd h hui, ?_, fun hi0 hu0 => absurd (hu0 ▸ hi0 ▸ Nat.le_refl 0) hui⟩
    · have hidx := card_times_index i i _ hec.2
      rw [Nat.max_self] at hidx
      rw [index_Prop1_G1_empty i _ hidx u hui']
      intro y hy
      cases hy
    · intro hi0
      subst i
      rw [index_Prop1_G1_empty 0 _ hec.2 u hui']
      intro y hy
      cases hy

theorem aux_top_le {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    ∀ p a, (transAux v).1 = T.P p a T.Z → p ≤ k - 1 := by
  intro k v p a he
  obtain ⟨p', a', he', hp'⟩ := aux_principal v
  rw [he] at he'
  cases he'
  exact hp'

/-- The high part of a principal argument is the high part of its top coordinate. -/
theorem aux_head_high_eq {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    VecGood v →
    ∀ p a, (transAux v).1 = T.P p a T.Z →
      ∀ i : Fin k, i.val = p → (T.part p a).1 = (T.part p (trans (v.idx i))).1
  | _, .nil, _, _, _, _, i, _ => i.elim0
  | _, .snoc k v a, hv, p, b, he, i, hi => by
      have hpre := VecGood_prefix v a hv
      cases k with
      | zero =>
          cases v
          rw [aux_single] at he
          cases he
          have : i = Fin.last 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
          subst this
          simp [new.Vec.idx]
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            rw [aux_zero_tail] at he
            have hp := aux_top_le v p b he
            have hik : i.val < k + 1 := by omega
            simp only [new.Vec.idx, hik, dite_true]
            exact aux_head_high_eq v hpre p b he ⟨i.val, hik⟩ hi
          · rw [aux_head_snoc v a haz] at he
            cases he
            have hil : i = Fin.last (k + 1) := Fin.eq_of_val_eq (by simp; omega)
            subst hil
            have hlow := aux_lower_closed v hpre
            rw [part_add_distrib, part_of_index (k + 1) _
              (Rank1Termination.index_mono (by omega) _ hlow.2.1), T.add_Z,
              (part_card_times (k + 1) _).1, part_one_del_fst]
            simp [new.Vec.idx]

theorem aux_head_high {lam k : Nat} (v : new.Vec (new.T lam) k) (hv : VecGood v) (p : Nat) (a : T)
    (he : (transAux v).1 = T.P p a T.Z) : (T.part p a).1 = T.Z ∨
      ∃ i : Fin k, i.val = p ∧ (T.part p a).1 = (T.part p (trans (v.idx i))).1 := by
  cases k with
  | zero => cases v; cases he; exact Or.inl rfl
  | succ k =>
      have hp := aux_top_le v p a he
      exact Or.inr ⟨⟨p, by omega⟩, rfl, aux_head_high_eq v hv p a he ⟨p, by omega⟩ rfl⟩

/-! Bounds for supports of principal arguments. -/

theorem deep_bound {lam : Nat} (N : Nat)
    (hgood : ∀ s : new.T lam, new.T.size s < N → ∀ u, new.T.isNFComp u s → GoodAt u s)
    (u : Nat) (C : T) :
    ∀ x : new.T lam, new.T.size x ≤ N → new.T.isNF x →
      (∀ z ∈ new.T.Gi u x, trans z < C) →
      SumAll (fun p c => u ≤ p → ∀ y ∈ T.G1 u c, y < C) (trans x) ∧
        SumAll (fun p c => u ≤ p → (T.part p c).1 = T.Z ∨ (T.part p c).1 < C) (trans x) := by
  intro x
  induction x using (measure new.T.size).wf.induction with
  | h x ih =>
      intro hsz hx hsupp
      cases x with
      | Z => exact ⟨trivial, trivial⟩
      | P w b =>
          obtain ⟨hw, hb, _⟩ := new.T.isNF_P_inv w b hx
          have hcoordSz (i : Fin lam) : new.T.size (w.idx i) < N :=
            Nat.lt_of_lt_of_le (new.T.idx_size_lt_P w b i) hsz
          have hgw (i : Fin lam) : GoodAt i.val (w.idx i) := hgood _ (hcoordSz i) i.val (hw i)
          have hvg : VecGood w := hgw
          obtain ⟨K, X, he, _⟩ := aux_principal w
          have htr : trans (new.T.P w b) = T.P K X (trans b) := by
            rw [trans_as_add, he, p_zero_add]
          have ihb := ih b (new.T.add_size_lt_P w b)
            (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P w b)) hsz) hb
            (fun z hz => hsupp z (source_tail_support_mem_Gi u w b z hz))
          rw [htr]
          -- coordinate hypotheses
          have hcoord (i : Fin lam) : CoordHyp u C i.val (w.idx i) := by
            apply coord_hyp_of u C i.val (w.idx i) (hgw i)
            · intro hui
              exact hsupp _ (source_coord_mem_Gi u w b i hui)
            · intro hui
              have ihi := ih (w.idx i) (new.T.idx_size_lt_P w b i)
                (Nat.le_of_lt (hcoordSz i)) (hw i).1
                (fun z hz => hsupp z (source_coord_support_mem_Gi u w b z i hui hz))
              have hself := SumAll_G1_self i.val (trans (w.idx i))
              have h1 : SumAll (fun p c => i.val ≤ p → c < C) (trans (w.idx i)) := by
                apply SumAll_mono _ _ _ _ hself
                intro p c h hip
                exact lt_trans_thm _ _ _ ((hgw i).2 c (h hip))
                  (hsupp _ (source_coord_mem_Gi u w b i hui))
              apply SumAll_mono _ _ _ _ (SumAll_and3 _ _ _ _ h1 ihi.1 ihi.2)
              intro p c ⟨h1, h2, h3⟩
              refine ⟨h1, h2, fun hup _ => ?_⟩
              rcases h3 hup with h | h
              · rw [h]
                exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le _)
                  (hsupp _ (source_coord_mem_Gi u w b i hui))
              · exact h
          have hvb := aux_support_bounded u C w hcoord
          refine ⟨⟨hvb.2 K X he, ihb.1⟩, ⟨?_, ihb.2⟩⟩
          intro hup
          rcases aux_head_high w hvg K X he with h | ⟨i, hi, h⟩
          · exact Or.inl h
          · apply Or.inr
            rw [h]
            subst hi
            exact lt_of_le_of_lt_thm T _ _ _ (part_first_le _ _ (hgw i).1)
              (hsupp _ (source_coord_mem_Gi u w b i hup))

/-! Arguments of principal summands. -/

theorem summand_args_lt {lam : Nat} (N : Nat)
    (hgood : ∀ s : new.T lam, new.T.size s < N → ∀ u, new.T.isNFComp u s → GoodAt u s)
    (u : Nat) (TS : T) (hTS : T.isNF1 TS) (hTSne : T.Z < TS) :
    ∀ b : new.T lam, new.T.size b ≤ N → new.T.isNF b →
      (∀ z ∈ new.T.Gi u b, trans z < TS) →
      (∀ p c, IsSummand p c (trans b) → IsSummand p c TS) →
      SumAll (fun p c => u ≤ p → c < TS) (trans b) := by
  intro b
  induction b using (measure new.T.size).wf.induction with
  | h b ih =>
      intro hsz hb hsupp hsumm
      cases b with
      | Z => exact trivial
      | P w b =>
          obtain ⟨hw, hb', _⟩ := new.T.isNF_P_inv w b hb
          have hgw (i : Fin lam) : GoodAt i.val (w.idx i) :=
            hgood _ (Nat.lt_of_lt_of_le (new.T.idx_size_lt_P w b i) hsz) i.val (hw i)
          have hvg : VecGood w := hgw
          obtain ⟨K, X, he, _⟩ := aux_principal w
          have htr : trans (new.T.P w b) = T.P K X (trans b) := by
            rw [trans_as_add, he, p_zero_add]
          have hhead := aux_head_closed w hvg
          rw [he] at hhead
          obtain ⟨hX, _, hgX, _⟩ := T.isNF1_P_inv K X T.Z hhead
          rw [htr] at hsumm ⊢
          refine ⟨fun hup => ?_, ih b (new.T.add_size_lt_P w b)
            (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P w b)) hsz) hb'
            (fun z hz => hsupp z (source_tail_support_mem_Gi u w b z hz))
            (fun p c hs => hsumm p c (Or.inr hs))⟩
          have hsum : IsSummand K X TS := hsumm K X (Or.inl ⟨rfl, rfl⟩)
          have hlow := part_snd_lt_wrap K X T.Z hX hgX
          rcases aux_head_high w hvg K X he with h | ⟨i, hi, h⟩
          · exact summand_arg_lt K X T.Z TS hTS hX .z hsum hTSne (by rw [h]; rfl) hlow
          · subst hi
            exact summand_arg_lt _ X (trans (w.idx i)) TS hTS hX (hgw i).1 hsum
              (hsupp _ (source_coord_mem_Gi u w b i hup)) h.symm hlow

/-! The main simultaneous induction. -/

theorem good_all {lam : Nat} : ∀ s : new.T lam,
    (new.T.isNF s → T.isNF1 (trans s)) ∧ (∀ u, new.T.isNFComp u s → GoodAt u s) := by
  intro s
  induction s using (measure new.T.size).wf.induction with
  | h s ih =>
      have hgood : ∀ z : new.T lam, new.T.size z < new.T.size s →
          ∀ u, new.T.isNFComp u z → GoodAt u z := fun z hz => (ih z hz).2
      have hNF : new.T.isNF s → T.isNF1 (trans s) := by
        intro hs
        cases s with
        | Z => exact T.isNF1.z
        | P v a => exact NF_step v a hs (fun z hz => (ih z hz).1) hgood
      refine ⟨hNF, fun u hs => ⟨hNF hs.1, ?_⟩⟩
      have hsupp : ∀ z ∈ new.T.Gi u s, trans z < trans s := by
        intro z hz
        exact order_preserve_bounded (new.T.size s) hgood z s
          (Nat.le_of_lt (new.T.Gi_size_lt u s z hz)) (Nat.le_refl _)
          (new.T.isNF_Gi s hs.1 u z hz) hs.1 (hs.2 z hz)
      cases s with
      | Z => intro y hy; cases hy
      | P v a =>
          have hne : T.Z < trans (new.T.P v a) := by
            obtain ⟨K, X, he, _⟩ := aux_principal v
            rw [trans_as_add, he, p_zero_add]
            exact T.Lt.Z_lt_P _ _ _
          have h1 := summand_args_lt (new.T.size (new.T.P v a)) hgood u _ (hNF hs.1) hne
            (new.T.P v a) (Nat.le_refl _) hs.1 hsupp (fun _ _ h => h)
          have h2 := (deep_bound (new.T.size (new.T.P v a)) hgood u _ (new.T.P v a)
            (Nat.le_refl _) hs.1 hsupp).1
          apply G1_of_SumAll u (· < trans (new.T.P v a))
          apply SumAll_mono _ _ _ _ (SumAll_and3 _ _ _ _ h1 h2 h2)
          intro p c ⟨h1, h2, _⟩ hup
          exact ⟨h1 hup, h2 hup⟩

theorem trans_isNF1 {lam : Nat} (s : new.T lam) (hs : new.T.isNF s) : T.isNF1 (trans s) :=
  (good_all s).1 hs

theorem trans_good {lam : Nat} (u : Nat) (s : new.T lam) (hs : new.T.isNFComp u s) :
    GoodAt u s :=
  (good_all s).2 u hs

theorem trans_lt_of_lt {lam : Nat} (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t)
    (h : s < t) : trans s < trans t :=
  order_preserve_bounded (max (new.T.size s) (new.T.size t))
    (fun z _ u hz => trans_good u z hz) s t (Nat.le_max_left _ _) (Nat.le_max_right _ _) hs ht h

theorem trans_lt_iff {lam : Nat} (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  refine ⟨trans_lt_of_lt s t hs ht, fun h => ?_⟩
  rcases new.T_total s t with h' | h' | rfl
  · exact h'
  · exact absurd (trans_lt_of_lt t s ht hs h') (lt_asymm_thm h)
  · exact absurd h (lt_irrefl_thm _)

theorem trans_injective_NF {lam : Nat} (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t)
    (h : trans s = trans t) : s = t := by
  rcases new.T_total s t with h' | h' | h'
  · exact absurd (h ▸ trans_lt_of_lt s t hs ht h') (lt_irrefl_thm _)
  · exact absurd (h ▸ trans_lt_of_lt t s ht hs h') (lt_irrefl_thm _)
  · exact h'

end LegacyTranslation

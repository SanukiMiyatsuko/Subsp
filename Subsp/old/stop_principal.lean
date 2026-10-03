import Subsp.old.stop_cardinal
import Subsp.old.stop_source_fund_nf

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

import Subsp.old.stop_card_support
import Subsp.old.stop_outer
import Subsp.old.stop_indexed_nf

/-! Principal normal forms of the legacy translation. -/

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
  cases s with
  | Z => exact Or.inr rfl
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z => exact T.isNF1_tail_le _ hs _ _ _ rfl
          | P _ _ _ => exact Or.inr rfl
      | succ _ => exact Or.inr rfl

theorem one_del_lt (s t : T) (hs : T.isNF1 s) (hne : s ≠ T.Z) (h : s < t) :
    T.one_del s < T.one_del t := by
  cases h with
  | Z_lt_P => exact False.elim (hne rfl)
  | p_head p q a c b d hpq =>
      cases q with
      | zero => exact False.elim (Nat.not_lt_zero _ hpq)
      | succ q =>
          exact lt_of_le_of_lt_thm T _ _ _ (one_del_le _ hs) (.p_head _ _ _ _ _ _ hpq)
  | p_mid p a c b d hac =>
      cases p with
      | zero =>
          cases c with
          | Z => exact False.elim (lt_Z_inv hac)
          | P q e f =>
              exact lt_of_le_of_lt_thm T _ _ _ (one_del_le _ hs) (.p_mid _ _ _ _ _ hac)
      | succ p => exact .p_mid _ _ _ _ _ hac
  | p_tail p a b d hbd =>
      cases p with
      | zero =>
          cases a with
          | Z => exact hbd
          | P _ _ _ => exact .p_tail _ _ _ _ hbd
      | succ _ => exact .p_tail _ _ _ _ hbd

def VecGood {lam k : Nat} (v : new.Vec (new.T lam) k) : Prop :=
  ∀ i : Fin k, T.isNF1 (trans (v.idx i)) ∧
    ∀ x ∈ T.G1 i.val (trans (v.idx i)), x < trans (v.idx i)

theorem VecGood_prefix {lam k : Nat} (v : new.Vec (new.T lam) k) (a : new.T lam)
    (h : VecGood (.snoc k v a)) : VecGood v := by
  intro i
  simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using h i.castSucc

theorem VecGood_last {lam k : Nat} (v : new.Vec (new.T lam) k) (a : new.T lam)
    (h : VecGood (.snoc k v a)) : T.isNF1 (trans a) ∧
      ∀ x ∈ T.G1 k (trans a), x < trans a := by
  simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using h (Fin.last k)

theorem aux_single {lam : Nat} (a : new.T lam) :
    transAux (.snoc 0 .nil a) = (T.P 0 (trans a) T.Z, T.early_collapse 0 (trans a)) := by
  cases a <;> rfl

theorem aux_lower_snoc {lam k : Nat} (v : new.Vec (new.T lam) (k + 1)) (a : new.T lam) :
    (transAux (.snoc (k + 1) v a)).2 =
      T.add (T.card_times (k + 1) (T.early_collapse (k + 1) (trans a))) (transAux v).2 := by
  cases a <;> rfl

theorem aux_head_snoc {lam k : Nat} (v : new.Vec (new.T lam) (k + 1)) (a : new.T lam)
    (ha : a ≠ new.T.Z) :
    (transAux (.snoc (k + 1) v a)).1 =
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
      have hp := VecGood_prefix v a hv
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          obtain ⟨hnf, hi⟩ := early_collapse_closed 0 (trans a) ha.1 ha.2
          exact ⟨hnf, hi, index_Prop1_lt_succ 0 _ hi⟩
      | succ k =>
          obtain ⟨hvNF, hvIdx, hvBound⟩ := ih hp
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
            exact .p (k + 1) _ T.Z
              (card_times_append_closed _ _ _ haNF hlNF hlBound) .z
              (card_times_append_good (k + 1) k (Nat.lt_succ_self k) _ _ haNF haGood hlIdx)
              (T.Z_le _)

end LegacyTranslation

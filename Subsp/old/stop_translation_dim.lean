import Subsp.old.stop_low_dims
import Subsp.old.stop_source_dim
import Subsp.old.stop_translation_support

/-! Dimension bounds for the legacy translation. -/

namespace LegacyTranslation

theorem trans_index_dim_pred {lam : Nat} (s : new.T lam) :
    T.index_Prop1 (lam - 1) (trans s) := by
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => exact .z
  | P v a _ ih =>
      obtain ⟨p, b, he, hp⟩ := aux_principal v
      rw [trans_as_add, he, p_zero_add]
      exact .p p b (trans a) hp ih
  | nil => trivial
  | snoc => trivial

theorem trans_G1_dim_empty {lam : Nat} (s : new.T lam) (hlam : 0 < lam) :
    T.G1 lam (trans s) = [] := by
  exact index_Prop1_G1_empty (lam - 1) (trans s)
    (trans_index_dim_pred s) lam (by omega)

theorem GoodAt_dim_of_NF {lam : Nat} (s : new.T lam) (hlam : 0 < lam)
    (hs : T.isNF1 (trans s)) :
    GoodAt lam s := by
  refine ⟨hs, ?_⟩
  intro x hx
  rw [trans_G1_dim_empty s hlam] at hx
  cases hx

theorem trans_zero_isNF (s : new.T 0) :
    T.isNF1 (trans s) := by
  rw [LegacyZero.eq_ofNat s, trans_ofNat]
  exact IsN_isNF1 _ (ofNat_IsN _)

theorem GoodAt_zero (s : new.T 0) :
    GoodAt 0 s := by
  refine ⟨trans_zero_isNF s, ?_⟩
  intro x hx
  have hN : T.IsN (trans s) := by
    rw [LegacyZero.eq_ofNat s, trans_ofNat]
    exact ofNat_IsN _
  have hxz := IsN_G1_eq_Z (trans s) hN 0 x hx
  subst x
  cases htr : trans s with
  | Z =>
      rw [htr] at hx
      cases hx
  | P p a b =>
      exact T.Lt.Z_lt_P p a b

end LegacyTranslation

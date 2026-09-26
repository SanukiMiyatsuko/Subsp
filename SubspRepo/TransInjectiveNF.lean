import Subsp.new.stop

open T

theorem trans_injective_NF_work {lam : Nat} (s t : new.T lam)
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

theorem reflect_le_NF_work {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t)
    (hle : trans s ≤ trans t) : s ≤ t := by
  cases hle with
  | inl hlt =>
      exact Or.inl ((gnf_order_embedding s t hs ht).mpr hlt)
  | inr heq =>
      have hst : s = t := trans_injective_NF_work s t hs ht heq
      rw [hst]
      exact Or.inr (new.T_refl t)

#print axioms trans_injective_NF_work
#print axioms reflect_le_NF_work

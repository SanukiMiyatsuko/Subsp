import Subsp.old.stop_source_fund_nf

/-! Supports above the source dimension are empty. -/

namespace new

theorem Vec.Gi_eq_nil_of_length_le {lam k : Nat}
    (u : Nat) (hku : k ≤ u) (v : Vec (T lam) k) :
    Vec.Gi u v = [] := by
  induction v with
  | nil => rfl
  | snoc k v a ih =>
      have hk : k ≤ u := by omega
      have hnot : ¬ u ≤ k := by omega
      simp only [Vec.Gi, hnot, ite_false, List.append_nil]
      exact ih hk

theorem T.Gi_eq_nil_of_dim_le {lam : Nat}
    (u : Nat) (hlu : lam ≤ u) (s : T lam) :
    T.Gi u s = [] := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v b _ ih =>
      rw [T.Gi, Vec.Gi_eq_nil_of_length_le u hlu v, ih]
      rfl
  | nil => trivial
  | snoc => trivial

theorem T.isNFComp_dim {lam : Nat} (s : T lam)
    (hs : T.isNF s) : T.isNFComp lam s := by
  refine ⟨hs, ?_⟩
  intro x hx
  rw [T.Gi_eq_nil_of_dim_le lam (Nat.le_refl lam) s] at hx
  cases hx

theorem T.isNFComp_above_dim {lam : Nat} (u : Nat)
    (hlu : lam ≤ u) (s : T lam) (hs : T.isNF s) :
    T.isNFComp u s := by
  exact T.isNFComp_mono lam u hlu s (T.isNFComp_dim s hs)

end new

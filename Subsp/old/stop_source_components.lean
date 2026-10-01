import Subsp.old.stop_source_comp0

/-! Component extraction lemmas for indexed source normal forms. -/

namespace new

theorem T.isNFComp_tail {lam : Nat} (u : Nat)
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNFComp u (T.P ls add)) :
    T.isNFComp u add := by
  refine ⟨(T.isNF_P_inv ls add hs.1).2.1, ?_⟩
  intro x hx
  exact hs.2 x ((T.mem_Gi_P u ls add x).mpr (Or.inr hx))

theorem T.isNFComp_coord_of_parent {lam : Nat} (u : Nat)
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNFComp u (T.P ls add))
    (i : Fin lam) (hui : u ≤ i.val) :
    T.isNFComp u (ls.idx i) := by
  refine ⟨(T.isNF_P_inv ls add hs.1).1 i |>.1, ?_⟩
  intro x hx
  exact hs.2 x ((T.mem_Gi_P u ls add x).mpr
    (Or.inl ⟨i, hui, Or.inr hx⟩))

theorem T.isNFComp_coord_at_index {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNF (T.P ls add)) (i : Fin lam) :
    T.isNFComp i.val (ls.idx i) :=
  (T.isNF_P_inv ls add hs).1 i

theorem T.isNFComp_coord_mono_from_parent {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNFComp u (T.P ls add))
    (i : Fin lam) (hui : u ≤ i.val) (v : Nat) (hiv : i.val ≤ v) :
    T.isNFComp v (ls.idx i) :=
  T.isNFComp_mono u v (Nat.le_trans hui hiv) _ (T.isNFComp_coord_of_parent u ls add hs i hui)

end new

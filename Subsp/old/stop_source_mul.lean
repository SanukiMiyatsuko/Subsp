import Subsp.old.stop_source_vector

/-! Indexed normal forms for multiplication by a principal source term. -/

namespace new

theorem T.mul_PZ_lt_next {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.mul (T.P ls T.Z) t <
        T.P ls (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P us add _ ih => exact T.P_tail_lt ls _ _ ih
  | nil => trivial
  | snoc => trivial

theorem T.head_mul_PZ_le {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.head (T.mul (T.P ls T.Z) t) ≤ T.P ls T.Z := by
  intro t
  cases t with
  | Z => exact T.Z_le _
  | P us add => exact T.le_refl _

theorem T.mul_PZ_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam)
    (hbase : T.isNF (T.P ls T.Z)) :
    ∀ t : T lam, T.isNF (T.mul (T.P ls T.Z) t) := by
  intro t
  obtain ⟨hcoords, _, _⟩ := T.isNF_P_inv ls T.Z hbase
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact T.isNF.z
  | P us add _ ih =>
      rw [T.mul]
      exact T.isNF.p ls _ (fun i => (hcoords i).1) ih
        (fun i => (hcoords i).2) (T.head_mul_PZ_le ls add)
  | nil => trivial
  | snoc => trivial

theorem T.Gi_mul_PZ_subset {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam) :
    ∀ t x : T lam,
      x ∈ T.Gi u (T.mul (T.P ls T.Z) t) →
        x ∈ T.Gi u (T.P ls T.Z) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => intro x hx; cases hx
  | P us add _ ih =>
      intro x hx
      rw [T.mul] at hx
      rcases (T.mem_Gi_P u ls (T.mul (T.P ls T.Z) add) x).mp hx with hv | ht
      · exact (T.mem_Gi_P u ls T.Z x).mpr (Or.inl hv)
      · exact ih x ht
  | nil => trivial
  | snoc => trivial

theorem T.mul_PZ_NFComp_closed {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam)
    (hbase : T.isNFComp u (T.P ls T.Z)) :
    ∀ t : T lam, T.isNFComp u (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact T.isNFComp_Z u
  | P us add _ ih =>
      refine ⟨T.mul_PZ_NF_closed ls hbase.1 (T.P us add), ?_⟩
      intro y hy
      rw [T.mul] at hy ⊢
      rcases (T.mem_Gi_P u ls (T.mul (T.P ls T.Z) add) y).mp hy with hv | ht
      · exact T.lt_of_lt_of_le _ _ _
          (hbase.2 y ((T.mem_Gi_P u ls T.Z y).mpr (Or.inl hv)))
          (T.P_le_P_same ls T.Z _ (T.Z_le _))
      · exact T_trans _ _ _ (ih.2 y ht) (T.mul_PZ_lt_next ls add)
  | nil => trivial
  | snoc => trivial


theorem T.mul_PZ_lt_of_compareVec_lt {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (hvec : compareVec u v = Ordering.lt) :
    T.mul (T.P u T.Z) t < T.P v T.Z := by
  cases t with
  | Z =>
      rw [T.mul]
      rfl
  | P ts add =>
      rw [T.mul]
      change T.P u (T.mul (T.P u T.Z) add) < T.P v T.Z
      exact T.P_lt_P_of_compareVec_lt _ _ _ _ hvec

end new

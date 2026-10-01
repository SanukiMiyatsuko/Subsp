import Subsp.old.stop_basic

/-! A weak source normal form tailored to the legacy translation. -/

namespace new

inductive T.isWNF {lam : Nat} : T lam → Prop where
  | z : T.isWNF T.Z
  | p (ls : Vec (T lam) lam) (add : T lam)
      (hcoords : ∀ i : Fin lam, T.isWNF (ls.idx i))
      (hadd : T.isWNF add)
      (hhead : T.head add ≤ T.P ls T.Z) :
      T.isWNF (T.P ls add)

theorem T.isWNF_P_inv {lam : Nat} (ls : Vec (T lam) lam) (add : T lam)
    (h : T.isWNF (T.P ls add)) :
    (∀ i : Fin lam, T.isWNF (ls.idx i)) ∧
      T.isWNF add ∧ T.head add ≤ T.P ls T.Z := by
  cases h
  exact ⟨‹_›, ‹_›, ‹_›⟩

theorem T.Z_le {lam : Nat} (s : T lam) : T.Z ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P ls add => exact Or.inl rfl

theorem T.head_mono {lam : Nat}
    (a b : T lam) (h : a < b) :
    T.head a ≤ T.head b := by
  cases a with
  | Z => exact T.Z_le _
  | P als aadd =>
      cases b with
      | Z => cases h
      | P bls badd =>
          change (match compareVec als bls with
            | .eq => compareT aadd badd | ord => ord) = .lt at h
          cases hc : compareVec als bls with
          | lt => exact Or.inl (T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
          | eq => rw [Vec_eq_sound _ _ hc]; exact Or.inr (T_refl _)
          | gt => simp [hc] at h

theorem T.head_mono_le {lam : Nat}
    (a b : T lam) (h : a ≤ b) :
    T.head a ≤ T.head b := by
  rcases h with h | h
  · exact T.head_mono a b h
  · rw [T_eq_sound _ _ h]
    exact Or.inr (T_refl _)

theorem T.isWNF_PZ_of_coords {lam : Nat}
    (ls : Vec (T lam) lam)
    (h : ∀ i : Fin lam, T.isWNF (ls.idx i)) :
    T.isWNF (T.P ls T.Z) := by
  exact .p ls T.Z h .z (T.Z_le _)

theorem T.isWNF_rplc {lam : Nat}
    (ls : Vec (T lam) lam) (i : Fin lam) (a : T lam)
    (hls : ∀ j : Fin lam, T.isWNF (ls.idx j))
    (ha : T.isWNF a) :
    ∀ j : Fin lam, T.isWNF ((ls.rplc i a).idx j) := by
  intro j
  by_cases hji : j.val = i.val
  · rw [Fin.eq_of_val_eq hji, Vec.rplc_idx_same]
    exact ha
  · rw [Vec.rplc_idx_of_ne _ _ _ _ hji]
    exact hls j

theorem T.ofNat_isWNF {lam : Nat} (n : Nat) :
    T.isWNF (T.ofNat (lam := lam) n) := by
  induction n with
  | zero => exact .z
  | succ n ih =>
      rw [T.ofNat]
      refine .p _ _ (fun i => ?_) ih ?_
      · rw [Vec.ofFn_idx]
        exact .z
      · cases n with
        | zero => exact T.Z_le _
        | succ n =>
            exact Or.inr (T_refl _)

theorem T.principal_mul_isWNF {lam : Nat}
    (ls : Vec (T lam) lam)
    (hls : ∀ i : Fin lam, T.isWNF (ls.idx i))
    (t : T lam) :
    T.isWNF (T.mul (T.P ls T.Z) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact .z
  | P tls add _ ih =>
      rw [T.mul]
      change T.isWNF (T.P ls (T.mul (T.P ls T.Z) add))
      refine .p ls _ hls ih ?_
      cases add with
      | Z => exact T.Z_le _
      | P _ _ => exact Or.inr (T_refl _)
  | nil => trivial
  | snoc => trivial

end new

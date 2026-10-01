import Subsp.old.stop_source_support

/-! Normal-form closure under coordinate replacement for the legacy source syntax. -/

namespace new

theorem T.rplc_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i : Fin lam) (a : T lam)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp i.val a) :
    T.isNF (T.P (ls.rplc i a) T.Z) := by
  obtain ⟨hcoords, _, _⟩ := T.isNF_P_inv ls T.Z hs
  refine .p _ T.Z ?_ .z ?_ (T.Z_le _)
  · intro q
    by_cases hqi : q.val = i.val
    · rw [Fin.eq_of_val_eq hqi, Vec.rplc_idx_same]
      exact ha.1
    · rw [Vec.rplc_idx_of_ne _ _ _ _ hqi]
      exact (hcoords q).1
  · intro q x hx
    by_cases hqi : q.val = i.val
    · rw [Fin.eq_of_val_eq hqi, Vec.rplc_idx_same] at hx ⊢
      exact ha.2 x hx
    · rw [Vec.rplc_idx_of_ne _ _ _ _ hqi] at hx ⊢
      exact (hcoords q).2 x hx

theorem T.rplc_two_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i j : Fin lam)
    (a b : T lam)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp i.val a)
    (hb : T.isNFComp j.val b) :
    T.isNF (T.P ((ls.rplc i a).rplc j b) T.Z) := by
  exact T.rplc_NF_closed _ j b (T.rplc_NF_closed ls i a hs ha) hb

end new

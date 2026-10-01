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

theorem T.P_same_le_iff {lam : Nat}
    (ls : Vec (T lam) lam) (a b : T lam) :
    T.P ls a ≤ T.P ls b ↔ a ≤ b := by
  simp only [LE.le, T.le, compareT, Vec_refl]

theorem T.sandwich_same_vector {lam : Nat}
    (ls : Vec (T lam) lam) (a b c : T lam)
    (hl : T.P ls a ≤ c) (hu : c ≤ T.P ls b) :
    ∃ d, c = T.P ls d ∧ a ≤ d ∧ d ≤ b := by
  have hh := T.le_antisymm _ _
    (T.head_mono_le c (T.P ls b) hu)
    (T.head_mono_le (T.P ls a) c hl)
  cases c with
  | Z => cases hh
  | P cs d =>
      change T.P cs T.Z = T.P ls T.Z at hh
      cases hh
      exact ⟨d, rfl, (T.P_same_le_iff _ _ _).mp hl,
        (T.P_same_le_iff _ _ _).mp hu⟩

theorem T.SDom_tail {lam : Nat}
    (z b a : T lam) (ls : Vec (T lam) lam)
    (hs : T.SDom z b a) :
    T.SDom z (T.P ls b) (T.P ls a) := by
  refine ⟨T.P_tail_lt ls b a hs.1, ?_⟩
  intro u c hbc hca x hx
  obtain ⟨d, rfl, hbd, hda⟩ := T.sandwich_same_vector ls b a c hbc hca
  rcases (T.mem_Gi_P u ls b x).mp hx with hv | ht
  · refine ⟨x, List.mem_append_left _ ((T.mem_Gi_P u ls d x).mpr (Or.inl hv)),
      T.le_refl _⟩
  · obtain ⟨y, hy, hxy⟩ := hs.2 u d hbd hda x ht
    refine ⟨y, ?_, hxy⟩
    rcases List.mem_append.mp hy with hy | hy
    · exact List.mem_append_left _ ((T.mem_Gi_P u ls d y).mpr (Or.inr hy))
    · exact List.mem_append_right _ hy

end new

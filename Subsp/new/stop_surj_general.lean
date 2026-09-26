import Subsp.new.stop_surj_support

open T StopSurjMeasure StopSurjCard StopSurjVector StopSurjPrincipal StopSurjSupport

namespace StopSurjGeneral

theorem index1_of_lt_principal (a c : T) (hnf : T.isNF1 a)
    (ha : a < T.P 1 c T.Z) : T.index_Prop1 1 a := by
  cases a with
  | Z => exact T.index_Prop1.z
  | P p u v =>
      apply isNF1_index 1 p u v hnf
      cases lt_inv p u v 1 c T.Z ha with
      | inl hp => exact Nat.le_of_lt hp
      | inr hr =>
          cases hr with
          | inl hm => rw [hm.1]; exact Nat.le_refl 1
          | inr ht => exact False.elim (lt_Z_inv ht.2.2)

/-- Induct on exponent depth, then on the tail. The inverse collapse and inverse
cardinal operations preserve depth, so all coordinates use the outer hypothesis.
The support invariant recovers `isNFComp` when the input has bounded support. -/
theorem exists_preimage (k : Nat) (t : T) (hnf : T.isNF1 t)
    (hsmall : Small (ot_trans_bound (k + 2)) t) :
    ∃ s : new.T (k + 2), Preimage t s := by
  let C := ot_trans_bound (k + 2)
  have hC : T.part C = (C, T.Z) := rfl
  let motive : Nat → Prop := fun n =>
    ∀ t : T, degree t ≤ n → T.isNF1 t → Small C t →
      ∃ s : new.T (k + 2), Preimage t s
  have main : ∀ n, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro t
      induction t with
      | Z =>
          intro hd hn hS
          refine ⟨new.T.Z, new.T.isNF.z, rfl, ?_⟩
          intro y hy
          cases hy
      | P p a b iha ihb =>
          intro hd hn hS
          have hparts := T.isNF1_P_inv p a b hn
          have hPS := small_inv C p a b hn hS
          have hda : degree a < n := Nat.lt_of_lt_of_le (degree_middle_lt p a b) hd
          have pre : ∀ x : T, T.isNF1 x → StopUncollapse.Good x → degree x ≤ degree a → Small C x →
              ∃ sx : new.T (k + 2), new.T.isNFComp sx ∧ trans sx = x := by
            intro x hx hg hdx hxc
            cases ih (degree x) (Nat.lt_of_le_of_lt hdx hda) x (Nat.le_refl _) hx hxc with
            | intro sx hsx => exact ⟨sx, comp_of_preimage x sx hsx hg, hsx.2.1⟩
          cases ihb (Nat.le_trans (degree_tail_le p a b) hd) hparts.2.1 hPS.2 with
          | intro sb hsb =>
              cases p with
              | zero =>
                  cases pre a hparts.1 hparts.2.2.1 (Nat.le_refl _) hPS.1 with
                  | intro sa hsa =>
                      let v := ot_v0 (k + 1) sa
                      have hvi : ∀ i : Fin (k + 2), new.T.isNFComp (v.idx i) ∧
                          Supported (T.P 0 a b) (trans (v.idx i)) := by
                        intro i
                        unfold v ot_v0
                        rw [new.Vec.ofFn_idx]
                        apply Decidable.byCases (p := i.val = 0)
                        · intro hi
                          rw [ite_eq_left hi]
                          refine ⟨hsa.1, ?_⟩
                          rw [hsa.2]
                          exact supported_middle 0 a b a (Or.inr rfl)
                        · intro hi
                          rw [ite_eq_right hi]
                          exact ⟨new.T.isNFComp_Z, supported_middle 0 a b T.Z (T.Z_le a)⟩
                      have hv : ∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x ∧
                          Supported (T.P 0 a b) (trans x) := by
                        intro x hx
                        cases new.Vec.mem_toList_exists_idx v x hx with
                        | intro i he => rw [← he]; exact hvi i
                      have htrans : trans (new.T.P v new.T.Z) = T.P 0 a T.Z := by
                        rw [ot_trans_v0, hsa.2]
                        rfl
                      exact ⟨new.T.P v sb, assemble 0 a b hn v sb
                        (fun x hx => (hv x hx).1) htrans hsb (fun x hx => (hv x hx).2)⟩
              | succ p =>
                  have hp1 : p + 1 = 1 := by
                    change Small (T.P 1 (level (k + 2)) T.Z) (T.P (p + 1) a b) at hS
                    cases lt_inv (p + 1) a b 1 (level (k + 2)) T.Z hS.1 with
                    | inl hp => exact False.elim (Nat.not_lt_zero p (Nat.lt_of_succ_lt_succ hp))
                    | inr hr =>
                        cases hr with
                        | inl hm => exact hm.1
                        | inr ht => exact False.elim (lt_Z_inv ht.2.2)
                  have hp0 : p = 0 := Nat.succ.inj hp1
                  cases hp0
                  have hab : a < level (k + 2) := by
                    change Small (T.P 1 (level (k + 2)) T.Z) (T.P 1 a b) at hS
                    cases lt_inv 1 a b 1 (level (k + 2)) T.Z hS.1 with
                    | inl hp => exact False.elim (Nat.lt_irrefl 1 hp)
                    | inr hr =>
                        cases hr with
                        | inl hm => exact hm.2
                        | inr ht => exact False.elim (lt_Z_inv ht.2.2)
                  have hai := index1_of_lt_principal a _ hparts.1 hab
                  cases higher_preimage k C hC a hparts.1 hai hab hPS.1 pre with
                  | intro v hv =>
                      refine ⟨new.T.P v sb, assemble 1 a b hn v sb hv.1 hv.2.1 hsb ?_⟩
                      intro x hx
                      exact supported_higher a b (trans x) (fun B hB hSm => hv.2.2 B hB hSm x hx))
  exact main (degree t) t (Nat.le_refl _) hnf hsmall

#print axioms exists_preimage

end StopSurjGeneral

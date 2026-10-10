import Subsp.multi.Base

/-! Choice-free reasoning helpers for the `multi` kumakuma proofs.

* `omega_c` closes a goal by `omega`, first trying `exfalso; omega` so that a non-arithmetic goal
  with contradictory arithmetic hypotheses does not go through `Classical.byContradiction`.
* `exists_ne_or_forall` decides whether some coordinate of a vector satisfying a decidable
  predicate is nonzero (coordinates beyond the length are zero). -/

macro "omega_c" : tactic => `(tactic| first | (exfalso; omega) | omega)

namespace kumakuma.Decide

open multi

theorem exists_ne_or_forall (xs : V T) (p : Nat → Prop) [DecidablePred p] :
    (∃ j, p j ∧ V.get0 xs j ≠ .Z) ∨ (∀ j, p j → V.get0 xs j = .Z) := by
  cases Nat.decidableExistsLT (p := fun j => p j ∧ V.get0 xs j ≠ .Z) xs.length with
  | isTrue h =>
    obtain ⟨j, _, h⟩ := h
    exact Or.inl ⟨j, h⟩
  | isFalse h =>
    refine Or.inr (fun j hj => ?_)
    by_cases hl : j < xs.length
    · exact Decidable.byContradiction (fun hne => h ⟨j, hl, hj, hne⟩)
    · exact V.get0_ge xs j (Nat.le_of_not_lt hl)

theorem exists_ne_or_all (xs : V T) :
    (∃ j, V.get0 xs j ≠ .Z) ∨ (∀ j, V.get0 xs j = .Z) := by
  rcases exists_ne_or_forall xs (fun _ => True) with ⟨j, _, h⟩ | h
  · exact Or.inl ⟨j, h⟩
  · exact Or.inr (fun j => h j trivial)

/-- Whether some coordinate satisfying a decidable predicate is nonzero is decidable. -/
instance decExistsNe (xs : V T) (p : Nat → Prop) [DecidablePred p] :
    Decidable (∃ j, p j ∧ V.get0 xs j ≠ .Z) :=
  match Nat.decidableExistsLT (p := fun j => p j ∧ V.get0 xs j ≠ .Z) xs.length with
  | isTrue h => isTrue (by obtain ⟨j, _, h⟩ := h; exact ⟨j, h⟩)
  | isFalse h => isFalse (by
      intro hex
      obtain ⟨j, hj, hne⟩ := hex
      by_cases hl : j < xs.length
      · exact h ⟨j, hl, hj, hne⟩
      · exact hne (V.get0_ge xs j (Nat.le_of_not_lt hl)))

/-- Agreement of two vectors above an index is decidable. -/
instance decForallGtEq (xs q : V T) (r : Nat) :
    Decidable (∀ l, r < l → V.get0 xs l = V.get0 q l) :=
  match Nat.decidableBallLT (max xs.length q.length)
      (fun l _ => r < l → V.get0 xs l = V.get0 q l) with
  | isTrue h => isTrue (by
      intro l hl
      by_cases hn : l < max xs.length q.length
      · exact h l hn hl
      · have hge := Nat.le_of_not_lt hn
        rw [V.get0_ge xs l (Nat.le_trans (Nat.le_max_left _ _) hge),
          V.get0_ge q l (Nat.le_trans (Nat.le_max_right _ _) hge)])
  | isFalse h => isFalse (fun hall => h (fun l _ hl => hall l hl))

end kumakuma.Decide

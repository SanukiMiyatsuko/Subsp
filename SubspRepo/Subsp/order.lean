class strict_partial_order (A : Type u) [LT A] where
  irrefl : ∀ a : A, ¬ a < a
  trans : ∀ a b c : A, a < b → b < c → a < c

open strict_partial_order

variable (A : Type u) [LT A] [strict_partial_order A]

theorem lt_neq (a b : A) (h_lt : a < b) : a ≠ b := by
  intro h_eq
  cases h_eq
  exact irrefl a h_lt

instance : LE A where
  le a b := a < b ∨ a = b

instance (a b : A) [DecidableEq A] [Decidable (a < b)] : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a < b ∨ a = b))

class partial_order where
  refl : ∀ a : A, a ≤ a
  trans : ∀ a b c : A, a ≤ b → b ≤ c → a ≤ c
  antisymm : ∀ a b : A, a ≤ b → b ≤ a → a = b

instance : partial_order A where
  refl a := by
    exact Or.inr rfl

  trans a b c h0 h1 := by
    cases h0 with
    | inl h0_lt =>
      cases h1 with
      | inl h1_lt =>
        have h_lt : a < c := trans a b c h0_lt h1_lt
        exact Or.inl h_lt
      | inr h1_eq =>
        cases h1_eq
        exact Or.inl h0_lt
    | inr h0_eq =>
      cases h0_eq
      exact h1

  antisymm a b h0 h1 := by
    cases h0 with
    | inl h0_lt =>
      cases h1 with
      | inl h1_lt =>
        have h_lt_a : a < a := trans a b a h0_lt h1_lt
        exact False.elim (irrefl a h_lt_a)
      | inr h1_eq =>
        exact h1_eq.symm
    | inr h0_eq =>
      exact h0_eq

open partial_order

theorem lt_of_le_of_lt_thm (a b c : A) (h1 : a ≤ b) (h2 : b < c) : a < c := by
  cases h1 with
  | inl hlt => exact trans a b c hlt h2
  | inr heq => rw [heq]; exact h2

theorem lt_of_lt_of_le_thm (a b c : A) (h1 : a < b) (h2 : b ≤ c) : a < c := by
  cases h2 with
  | inl hlt => exact trans a b c h1 hlt
  | inr heq => rw [<- heq]; exact h1

class strict_linear_order extends strict_partial_order A where
  total : ∀ a b : A, a < b ∨ b < a ∨ a = b

open strict_linear_order

variable (A : Type u) [LT A] [strict_linear_order A]

instance : LE A where
  le a b := a < b ∨ a = b

class linear_order extends partial_order A where
  total : ∀ a b : A, a ≤ b ∨ b ≤ a

instance : linear_order A where
  total a b := by
    have h_tot := total a b
    cases h_tot with
    | inl h_lt_ab =>
      exact Or.inl (Or.inl h_lt_ab)
    | inr h_or =>
      cases h_or with
      | inl h_lt_ba =>
        exact Or.inr (Or.inl h_lt_ba)
      | inr h_eq =>
        exact Or.inl (Or.inr h_eq)

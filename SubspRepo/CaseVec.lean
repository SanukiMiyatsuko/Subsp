import Subsp.new.Base
example {A : Type} : ∀ (v : new.Vec A (0+1)), True := by
  intro v
  cases v with
  | snoc k xs a =>
    trace_state
    trivial
example {A : Type} (k : Nat) : ∀ (v : new.Vec A ((k+1)+1)), True := by
  intro v
  cases v with
  | snoc n xs a =>
    trace_state
    trivial

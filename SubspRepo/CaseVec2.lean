import Subsp.new.Base
example {A : Type} : ∀ (v : new.Vec A 1), True := by
 intro v
 cases v with
 | @snoc n xs a =>
   trace_state
   have _ : new.Vec A n := xs
   have _ : A := a
   exact True.intro

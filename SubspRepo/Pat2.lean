import Subsp.new.Base

theorem pat2 {A : Type} (m:Nat) (v:new.Vec A ((m+1)+1)) : True := by
  cases v with
  | snoc xs a =>
    trace_state
    exact True.intro

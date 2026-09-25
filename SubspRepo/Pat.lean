import Subsp.new.Base
set_option pp.universes false
#check new.Vec.snoc

theorem pat {A : Type} (m:Nat) (v:new.Vec A ((m+1)+1)) : True := by
  cases v with
  | snoc n xs a =>
    trace_state
    exact True.intro

import Subsp.new.trans
open T
example : T.one_del T.Z = T.Z := by rfl
example (q:Nat) (d e b:T) : T.one_del (T.P 0 (T.P q d e) b) = T.P 0 (T.P q d e) b := by rfl
example (b:T) : T.one_del (T.P 0 T.Z b) = b := by rfl

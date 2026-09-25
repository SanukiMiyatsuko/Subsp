import Subsp.new.stop_principal

open T

theorem nfaux_part_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part s).1 ∧ T.isNF1 (T.part s).2 := by
  exact bridge_part_NF1 s hs

#print axioms nfaux_part_NF1

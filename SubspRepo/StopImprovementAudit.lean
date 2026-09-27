import Subsp.new.stop

/-! Checked generalizations used in the main library's structural consolidation. -/

namespace StopImprovementAudit

/-- The removed `ec_good0_mono` follows from the retained monotonicity theorem. -/
theorem collapse_mono (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hgs : ∀ x : T, x ∈ T.G1 0 s → x < s) (hst : s < t) :
    T.early_collapse s < T.early_collapse t := by
  exact bridge_early_collapse_lt s t hs hgs ht hst

/-- The index-zero and index-one wrapping arguments are instances of one lemma.
Normal form is not required. -/
theorem good_index_lt_wrap (k : Nat) (a b : T) (hi : T.index_Prop1 k a)
    (hg : ∀ x : T, x ∈ T.G1 k a → x < a) : a < T.P k a b := by
  exact bridge_good_index_lt_wrap k a b hi hg

example (a b : T) (hi : T.index_Prop1 0 a) (hg : StopUncollapse.Good a) :
    a < T.P 0 a b := good_index_lt_wrap 0 a b hi hg

example (a b : T) (hi : T.index_Prop1 1 a) (hg : StopSurjCard.Good1 a) :
    a < T.P 1 a b := good_index_lt_wrap 1 a b hi hg

example (c : T) (hi : T.index_Prop1 1 c) (hg : ∀ x, x ∈ T.G1 1 c → x < c) :
    c < T.P 1 c T.Z := good_index_lt_wrap 1 c T.Z hi hg

#print axioms collapse_mono
#print axioms good_index_lt_wrap

end StopImprovementAudit

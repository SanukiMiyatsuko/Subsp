import Subsp.new.stop_ot_downward

open T

def cv2s (a b : new.T 2) : new.Vec (new.T 2) 2 :=
  new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def czs : new.T 2 := new.T.Z
def cones : new.T 2 := new.T.P (cv2s czs czs) czs
def ccs : new.T 2 := new.T.P (cv2s czs cones) czs
def css : new.T 2 := new.T.P (cv2s ccs czs) czs
def couts : new.T 2 := new.T.P (cv2s css cones) czs
def cps : new.T 2 := new.T.P (cv2s couts czs) czs

def subBound2s : T :=
  T.P 0
    (T.P 1
      (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) T.Z)
      T.Z)
    T.Z

def isSubNF2s (x : T) : Prop := T.isNF1 x ∧ x < subBound2s

theorem counter_rhs : isSubNF2s (trans cps) := by
  constructor
  · exact of_decide_eq_true rfl
  · exact of_decide_eq_true rfl

theorem counter_not_ot : ¬ new.T.isOT 2 cps := by
  intro h
  have hs := ot_new_isOT_sound 2 cps h
  have hn : ¬ new.T.isNF cps := of_decide_eq_false rfl
  exact hn hs.1

theorem counter_not_iff :
    ¬ (new.T.isOT 2 cps ↔ isSubNF2s (trans cps)) := by
  intro h
  have hot : new.T.isOT 2 cps := h.mpr counter_rhs
  exact counter_not_ot hot

#print axioms counter_rhs
#print axioms counter_not_ot
#print axioms counter_not_iff

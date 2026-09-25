import Bridge
import TestStop

open T

theorem tc_trans_P_add {lam : Nat} (ls : new.Vec (new.T lam) lam) (a : new.T lam) :
    trans (new.T.P ls a) = T.add (trans (new.T.P ls new.T.Z)) (trans a) := by
  rw [_root_.trans.eq_2 ls a, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1]
  cases haux : transAux ls with
  | mk found rest =>
    cases rest with
    | mk sum a0 =>
      change
        (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
         else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a)) =
        T.add
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
           else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z)
          (trans a)
      by_cases hf : found = true
      · rw [ite_eq_left hf, ite_eq_left hf, T.P_add_eq, T.add]
      · rw [ite_eq_right hf, ite_eq_right hf]
        by_cases ha0 : a0 = T.Z
        · rw [ite_eq_left ha0, ite_eq_left ha0, T.P_add_eq, T.add]
        · rw [ite_eq_right ha0, ite_eq_right ha0, T.P_add_eq, T.add]

theorem tc_trans_head {lam : Nat} (s : new.T lam) :
    trans (new.T.head s) = T.head (trans s) := by
  cases s with
  | Z => rfl
  | P ls a =>
    rw [new.T.head, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1,
      _root_.trans.eq_2 ls a]
    cases haux : transAux ls with
    | mk found rest =>
      cases rest with
      | mk sum a0 =>
        change
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
           else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z) =
          T.head
            (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
             else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a))
        by_cases hf : found = true
        · rw [ite_eq_left hf, ite_eq_left hf]
          rfl
        · rw [ite_eq_right hf, ite_eq_right hf]
          by_cases ha0 : a0 = T.Z
          · rw [ite_eq_left ha0, ite_eq_left ha0]
            rfl
          · rw [ite_eq_right ha0, ite_eq_right ha0]
            rfl

#print axioms tc_trans_P_add
#print axioms tc_trans_head

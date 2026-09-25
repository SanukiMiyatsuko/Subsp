import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

theorem tb_trans_ofNat {lam : Nat} (n : Nat) :
  _root_.trans (new.T.ofNat (lam := lam) n) = T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [new.T.ofNat, T.ofNat]
      change T.P 0 T.Z (_root_.trans (new.T.ofNat n)) = T.P 0 T.Z (T.ofNat n)
      rw [ih]

theorem tb_trans_add {lam : Nat} (a b : new.T lam) :
  _root_.trans (a + b) = T.add (_root_.trans a) (_root_.trans b) := by
  induction a with
  | Z => rfl
  | P ls add ihls ihadd =>
      rw [HAdd.hAdd, Add.add, new.T.oplus]
      change _root_.trans (new.T.P ls (new.T.oplus add b)) = T.add (_root_.trans (new.T.P ls add)) (_root_.trans b)
      rw [_root_.trans, _root_.trans]
      cases haux : transAux ls with
      | mk found pair =>
        cases pair with
        | mk sum a0 =>
          change (if found then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (_root_.trans (new.T.oplus add b))
            else if a0 = T.Z then T.P 0 T.Z (_root_.trans (new.T.oplus add b)) else T.P 0 a0 (_root_.trans (new.T.oplus add b))) =
            T.add (if found then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (_root_.trans add)
            else if a0 = T.Z then T.P 0 T.Z (_root_.trans add) else T.P 0 a0 (_root_.trans add)) (_root_.trans b)
          rw [ihadd]
          by_cases hf : found
          · rw [ite_eq_left hf, ite_eq_left hf, T.P_add_eq]
          · rw [ite_eq_right hf, ite_eq_right hf]
            by_cases ha0 : a0 = T.Z
            · rw [ite_eq_left ha0, ite_eq_left ha0, T.P_add_eq]
            · rw [ite_eq_right ha0, ite_eq_right ha0, T.P_add_eq]

theorem tb_trans_head {lam : Nat} (s : new.T lam) :
    T.head (_root_.trans s) = _root_.trans (new.T.head s) := by
  cases s with
  | Z => rfl
  | P ls add =>
      rw [new.T.head]
      rw [_root_.trans, _root_.trans]
      cases haux : transAux ls with
      | mk found pair =>
        cases pair with
        | mk sum a0 =>
          change T.head (if found then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (_root_.trans add)
            else if a0 = T.Z then T.P 0 T.Z (_root_.trans add) else T.P 0 a0 (_root_.trans add)) =
            (if found then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
            else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z)
          by_cases hf : found
          · rw [ite_eq_left hf, ite_eq_left hf]
            rfl
          · rw [ite_eq_right hf, ite_eq_right hf]
            by_cases ha0 : a0 = T.Z
            · rw [ite_eq_left ha0, ite_eq_left ha0]
              rfl
            · rw [ite_eq_right ha0, ite_eq_right ha0]
              rfl

#print axioms tb_trans_ofNat
#print axioms tb_trans_add
#print axioms tb_trans_head

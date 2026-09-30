import Subsp.old.outer_shape
import Subsp.old.trans

theorem T.P_Z_add (s0 : Nat) (s1 y : T) :
    T.P s0 s1 T.Z + y = T.P s0 s1 y := by
  cases y <;> rfl

namespace new

theorem transAux_snoc_zero {lam m : Nat}
    (v : Vec (T lam) (m + 1)) :
    transAux (Vec.snoc (m + 1) v T.Z) = transAux v := by
  simp only [transAux, _root_.trans, T.early_collapse, T.part]
  change ((transAux v).1, (transAux v).2) = transAux v
  exact Prod.eta _

end new

namespace new

theorem transAux_outer0_succ {lam k : Nat}
    (v : Vec (T lam) (k + 1))
    (hv : ∀ i : Fin (k + 1), i.val ≠ 0 → v.idx i = T.Z) :
    transAux v =
      transAux (Vec.snoc 0 Vec.nil (v.idx ⟨0, Nat.zero_lt_succ k⟩)) := by
  induction k with
  | zero =>
      cases v with
      | snoc _ xs a =>
          cases xs
          rfl
  | succ k ih =>
      cases v with
      | snoc _ xs a =>
          have ha : a = T.Z := by
            have h := hv (Fin.last (k + 1)) (by simp)
            simpa [Vec.idx] using h
          subst a
          rw [transAux_snoc_zero]
          have hxs : ∀ i : Fin (k + 1), i.val ≠ 0 → xs.idx i = T.Z := by
            intro i hi
            have h := hv i.castSucc hi
            simpa [Vec.idx, i.isLt] using h
          simpa [Vec.idx] using ih xs hxs

end new

namespace new

theorem trans_outer0_P {lam : Nat}
    (ls : Vec (T (lam + 1)) (lam + 1)) (add : T (lam + 1))
    (hls : Vec.outer0 ls) :
    _root_.trans (T.P ls add) =
      match ls.idx ⟨0, Nat.zero_lt_succ lam⟩ with
      | T.Z => _root_.T.P 0 _root_.T.Z (_root_.trans add)
      | T.P _ _ =>
          _root_.T.P 0 (_root_.trans (ls.idx ⟨0, Nat.zero_lt_succ lam⟩))
            (_root_.trans add) := by
  rw [_root_.trans]
  rw [transAux_outer0_succ ls hls]
  cases h0 : ls.idx ⟨0, Nat.zero_lt_succ lam⟩ with
  | Z =>
      simp [transAux, _root_.trans]
      exact _root_.T.P_Z_add 0 _root_.T.Z (_root_.trans add)
  | P v a =>
      simp [transAux, _root_.trans]
      exact _root_.T.P_Z_add 0 ((transAux v).1 + _root_.trans a) (_root_.trans add)

end new

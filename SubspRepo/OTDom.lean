import Subsp.new.stop_ot_cofinal

open T

def ot_unit (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z


theorem ot_vec_all_Z_eq {lam m : Nat} (v : new.Vec (new.T lam) m)
    (hz : ∀ i : Fin m, v.idx i = new.T.Z) :
    v = new.Vec.ofFn m (fun _ => new.T.Z) := by
  induction v with
  | nil => rfl
  | snoc k xs x ih =>
      have hx : x = new.T.Z := by
        have h := hz (Fin.last k)
        change (if hlt : k < k then xs.idx ⟨k, hlt⟩ else x) = new.T.Z at h
        rw [dite_eq_right (Nat.lt_irrefl k)] at h
        exact h
      have hxs : ∀ i : Fin k, xs.idx i = new.T.Z := by
        intro i
        have h := hz i.castSucc
        change (if hlt : i.val < k then xs.idx ⟨i.val, hlt⟩ else x) = new.T.Z at h
        rw [dite_eq_left i.isLt] at h
        exact h
      rw [ih hxs, hx]
      rfl


theorem ot_dom_one_eq_unit {lam : Nat} (s : new.T lam)
    (hd : new.T.dom s = .one) : s = ot_unit lam := by
  cases s with
  | Z =>
      change new.Dom.zero = new.Dom.one at hd
      cases hd
  | P ls add =>
      by_cases hadd : add = new.T.Z
      · subst add
        cases hmin : new.T.domVecMinIdx ls with
        | none =>
            have hzeroDom := new.T.domVecMinIdx_none_all_zero ls hmin
            have hz : ∀ i : Fin lam, ls.idx i = new.T.Z := by
              intro i
              exact new.T.dom_zero_eq_Z (ls.idx i) (hzeroDom i)
            have hv := ot_vec_all_Z_eq ls hz
            rw [hv]
            rfl
        | some md =>
            obtain ⟨m,d⟩ := md
            rw [new.T.dom, ite_eq_left rfl, hmin] at hd
            by_cases hd1 : d = new.Dom.one
            · rw [ite_eq_left hd1] at hd
              by_cases hm : m.val = 0
              · rw [ite_eq_left hm] at hd
                cases hd
              · rw [ite_eq_right hm] at hd
                cases hd
            · rw [ite_eq_right hd1] at hd
              cases hd
      · rw [new.T.dom, ite_eq_right hadd] at hd
        have ha := ot_dom_one_eq_unit add hd
        -- impossible because then add is nonzero, but dom of parent follows tail; parent can still dom one!
        -- indeed P ls add with add dom one also has dom one; so shape theorem was too strong.
        sorry

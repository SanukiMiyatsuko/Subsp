import Subsp.new.stop_ot_base

open T

theorem ot_lt_Z_inv {lam : Nat} (x : new.T lam) (h : x < new.T.Z) : False := by
  cases x with
  | Z =>
      change Ordering.eq = Ordering.lt at h
      cases h
  | P ls add =>
      change Ordering.gt = Ordering.lt at h
      cases h

theorem ot_fund_one_upper {lam : Nat} :
    ∀ a : new.T lam, new.T.dom a = .one →
      ∀ b : new.T lam, b < a → b ≤ new.T.fund a new.T.Z := by
  let motive : Nat → Prop := fun n =>
    ∀ a : new.T lam, new.T.size a = n → new.T.dom a = .one →
      ∀ b : new.T lam, b < a → b ≤ new.T.fund a new.T.Z
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a hsize hdom b hba
      cases a with
      | Z =>
          change new.Dom.zero = new.Dom.one at hdom
          cases hdom
      | P ls add =>
          by_cases hadd : add = new.T.Z
          · subst add
            have hnone : new.T.domVecMinIdx ls = none := by
              cases hmin : new.T.domVecMinIdx ls with
              | none => exact rfl
              | some md =>
                  obtain ⟨i, d⟩ := md
                  have hd := hdom
                  conv at hd =>
                    lhs
                    rw [new.T.dom, ite_eq_left rfl, hmin]
                  change
                    (if d = new.Dom.one then
                      if i.val = 0 then new.Dom.omega else new.Dom.Omega
                    else new.Dom.omega) = new.Dom.one at hd
                  by_cases hd1 : d = new.Dom.one
                  · rw [ite_eq_left hd1] at hd
                    by_cases hi0 : i.val = 0
                    · rw [ite_eq_left hi0] at hd
                      cases hd
                    · rw [ite_eq_right hi0] at hd
                      cases hd
                  · rw [ite_eq_right hd1] at hd
                    cases hd
            rw [new.T.fund_PZ_none ls new.T.Z hnone]
            cases b with
            | Z => exact Or.inr rfl
            | P ws tail =>
                change
                  (match new.compareVec ws ls with
                  | Ordering.eq => new.compareT tail new.T.Z
                  | ord => ord) = Ordering.lt at hba
                cases hc : new.compareVec ws ls with
                | lt =>
                    obtain ⟨i, hiAbove, hiLt⟩ :=
                      new.Vec.compare_lt_has_pivot ws ls hc
                    have hdz : new.T.dom (ls.idx i) = new.Dom.zero :=
                      new.T.domVecMinIdx_none_all_zero ls hnone i
                    have hiz : ls.idx i = new.T.Z :=
                      new.T.dom_zero_eq_Z (ls.idx i) hdz
                    rw [hiz] at hiLt
                    exact False.elim (ot_lt_Z_inv (ws.idx i) hiLt)
                | eq =>
                    rw [hc] at hba
                    exact False.elim (ot_lt_Z_inv tail hba)
                | gt =>
                    rw [hc] at hba
                    cases hba
          · have hdadd : new.T.dom add = .one := by
              conv at hdom =>
                lhs
                rw [new.T.dom, ite_eq_right hadd]
              exact hdom
            have haddSize : new.T.size add < n := by
              have hlt := new.T.add_size_lt_P ls add
              rw [hsize] at hlt
              exact hlt
            have hrec := ih (new.T.size add) haddSize add rfl hdadd
            rw [new.T.fund_P_tail_eq ls add new.T.Z hadd]
            cases b with
            | Z => exact new.T.Z_le _
            | P ws tail =>
                change
                  (match new.compareVec ws ls with
                  | Ordering.eq => new.compareT tail add
                  | ord => ord) = Ordering.lt at hba
                cases hc : new.compareVec ws ls with
                | lt =>
                    apply Or.inl
                    change
                      (match new.compareVec ws ls with
                      | Ordering.eq => new.compareT tail (new.T.fund add new.T.Z)
                      | ord => ord) = Ordering.lt
                    rw [hc]
                | eq =>
                    rw [hc] at hba
                    have hvec : ws = ls := new.Vec_eq_sound ws ls hc
                    subst ws
                    exact (new.T.P_same_le_iff ls tail (new.T.fund add new.T.Z)).mpr
                      (hrec tail hba)
                | gt =>
                    rw [hc] at hba
                    cases hba)
  intro a hdom b hba
  exact main (new.T.size a) a rfl hdom b hba

#print axioms ot_fund_one_upper

theorem ot_mul_cofinal {lam : Nat}
    (ls : new.Vec (new.T lam) lam) :
    ∀ b : new.T lam, new.T.isNF b →
      new.T.head b ≤ new.T.P ls new.T.Z →
      ∃ n : Nat, b < new.T.mul (new.T.P ls new.T.Z) (new.T.ofNat n) := by
  intro b
  let motive : Nat → Prop := fun n =>
    ∀ a : new.T lam, new.T.size a = n → new.T.isNF a →
      new.T.head a ≤ new.T.P ls new.T.Z →
      ∃ k : Nat, a < new.T.mul (new.T.P ls new.T.Z) (new.T.ofNat k)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a hsize hnf hhead
      cases a with
      | Z =>
          refine ⟨1, ?_⟩
          rw [new.T.ofNat, new.T.mul]
          rfl
      | P ws tail =>
          cases hnf with
          | p _ _ hcoords htail hG htailHead =>
              have hvecRel :=
                new.T.vector_rel_of_P_le_P ws ls new.T.Z new.T.Z hhead
              cases hvecRel with
              | inl hvecLt =>
                  refine ⟨1, ?_⟩
                  rw [new.T.ofNat, new.T.mul]
                  exact new.T.P_lt_P_of_compareVec_lt ws ls tail new.T.Z hvecLt
              | inr hvecEq =>
                  subst ws
                  have htailSize : new.T.size tail < n := by
                    have hh := new.T.add_size_lt_P ls tail
                    rw [hsize] at hh
                    exact hh
                  obtain ⟨k, hk⟩ :=
                    ih (new.T.size tail) htailSize tail rfl htail htailHead
                  refine ⟨k + 1, ?_⟩
                  rw [new.T.ofNat, new.T.mul]
                  exact new.T.P_tail_lt ls tail
                    (new.T.mul (new.T.P ls new.T.Z) (new.T.ofNat k)) hk)
  exact main (new.T.size b) b rfl

#print axioms ot_mul_cofinal

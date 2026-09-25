import Subsp.new.stop_ot_cofinal

open T

theorem oti_zeroVec_not_gt {lam : Nat} (v : new.Vec (new.T lam) lam) :
    new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) v ≠ Ordering.gt := by
  intro hgt
  have htot := new.Vec_total (new.Vec.ofFn lam (fun _ => new.T.Z)) v
  cases htot with
  | inl hlt =>
      rw [hgt] at hlt
      cases hlt
  | inr hr =>
      cases hr with
      | inl hvlt =>
          obtain ⟨i, _, hi⟩ := new.Vec.compare_lt_has_pivot v
            (new.Vec.ofFn lam (fun _ => new.T.Z)) hvlt
          rw [new.Vec.ofFn_idx] at hi
          exact ot_lt_Z_inv (v.idx i) hi
      | inr heq =>
          rw [← heq] at hgt
          have href := new.Vec_refl (n := lam) (new.Vec.ofFn lam (fun _ => new.T.Z))
          rw [href] at hgt
          cases hgt

#print axioms oti_zeroVec_not_gt

theorem oti_ofNat_succ_le_of_lt {lam : Nat} :
    ∀ n : Nat, ∀ x : new.T lam,
      new.T.ofNat n < x → new.T.ofNat (n + 1) ≤ x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      cases x with
      | Z =>
          change Ordering.eq = Ordering.lt at hx
          cases hx
      | P ls add =>
          change
            new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z ≤
              new.T.P ls add
          change
            (match new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
            | Ordering.eq => new.compareT new.T.Z add
            | ord => ord) = Ordering.lt ∨
            (match new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
            | Ordering.eq => new.compareT new.T.Z add
            | ord => ord) = Ordering.eq
          cases hc : new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
          | lt => exact Or.inl rfl
          | eq =>
              cases new.T.Z_le add with
              | inl hz => exact Or.inl hz
              | inr hz => exact Or.inr hz
          | gt =>
              exact False.elim ((oti_zeroVec_not_gt ls) hc)
  | succ n ih =>
      intro x hx
      cases x with
      | Z =>
          exact False.elim (ot_lt_Z_inv (new.T.ofNat (n + 1)) hx)
      | P ls add =>
          change
            (match new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
            | Ordering.eq => new.compareT (new.T.ofNat n) add
            | ord => ord) = Ordering.lt at hx
          change
            new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) (new.T.ofNat (n + 1)) ≤
              new.T.P ls add
          change
            (match new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
            | Ordering.eq => new.compareT (new.T.ofNat (n + 1)) add
            | ord => ord) = Ordering.lt ∨
            (match new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
            | Ordering.eq => new.compareT (new.T.ofNat (n + 1)) add
            | ord => ord) = Ordering.eq
          cases hc : new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
          | lt => exact Or.inl rfl
          | eq =>
              rw [hc] at hx
              have htail := ih add hx
              cases htail with
              | inl hlt => exact Or.inl hlt
              | inr heq => exact Or.inr heq
          | gt =>
              rw [hc] at hx
              cases hx

#print axioms oti_ofNat_succ_le_of_lt

theorem oti_ofNat_le_iter_fund {lam : Nat} (s : new.T lam)
    (hd : new.T.dom s = .Omega) :
    ∀ n : Nat, new.T.ofNat n ≤
      new.T.iter (fun x => new.T.fund s x) (new.T.ofNat n) := by
  intro n
  induction n with
  | zero =>
      rw [new.T.ofNat, new.T.iter]
      exact new.T.le_refl new.T.Z
  | succ n ih =>
      rw [new.T.ofNat, new.T.iter]
      have hstep := new.T.iter_fund_lt_next s (new.T.ofNat n) hd
      have hnatlt : new.T.ofNat n <
          new.T.fund s (new.T.iter (fun x => new.T.fund s x) (new.T.ofNat n)) :=
        new.T.lt_of_le_of_lt (new.T.ofNat n)
          (new.T.iter (fun x => new.T.fund s x) (new.T.ofNat n))
          (new.T.fund s (new.T.iter (fun x => new.T.fund s x) (new.T.ofNat n)))
          ih hstep
      exact oti_ofNat_succ_le_of_lt n _ hnatlt

#print axioms oti_ofNat_le_iter_fund

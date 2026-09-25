import Subsp.new.stop_nf_core

open T

theorem bo_order_preserve_bounded {lam : Nat} (N : Nat)
    (hgood : ∀ x : new.T lam, new.T.size x < N → new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.size s ≤ N → new.T.size t ≤ N →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.size s ≤ N → new.T.size t ≤ N →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s t hsize hsN htN hs ht hst
      cases s with
      | Z =>
        cases t with
        | Z => exact False.elim (strict_partial_order.irrefl new.T.Z hst)
        | P w b =>
          rw [_root_.trans.eq_1]
          have hne : trans (new.T.P w b) ≠ T.Z :=
            tc_trans_ne_Z_of_ne_Z (new.T.P w b) (by intro h; cases h)
          exact tc_Z_lt_of_ne (trans (new.T.P w b)) hne
      | P v a =>
        cases t with
        | Z => exact False.elim (by
            change new.compareT (new.T.P v a) new.T.Z = Ordering.lt at hst
            cases hst)
        | P w b =>
          cases hs with
          | p _ _ hvNF haNF hvG hheadA =>
            cases ht with
            | p _ _ hwNF hbNF hwG hheadB =>
              change
                (match new.compareVec v w with
                | Ordering.eq => new.compareT a b
                | ord => ord) = Ordering.lt at hst
              cases hcmp : new.compareVec v w with
              | lt =>
                have hvGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList v →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have hsx : new.T.size x < new.T.size (new.T.P v a) :=
                    oc_mem_size_lt_P v a x hx
                  have hxN : new.T.size x < N :=
                    Nat.lt_of_lt_of_le hsx hsN
                  exact hgood x hxN ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have htx : new.T.size x < new.T.size (new.T.P w b) :=
                    oc_mem_size_lt_P w b x hx
                  have hxN : new.T.size x < N :=
                    Nat.lt_of_lt_of_le htx htN
                  exact hgood x hxN ⟨hwNF x hx, hwG x hx⟩
                have hmono :
                    ∀ x y : new.T lam,
                      x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
                      x < y → trans x < trans y := by
                  intro x y hx hy hxy
                  have hsx : new.T.size x < new.T.size (new.T.P v a) :=
                    oc_mem_size_lt_P v a x hx
                  have hty : new.T.size y < new.T.size (new.T.P w b) :=
                    oc_mem_size_lt_P w b y hy
                  have hsum :
                      new.T.size x + new.T.size y <
                        new.T.size (new.T.P v a) + new.T.size (new.T.P w b) :=
                    Nat.add_lt_add hsx hty
                  have hsum' : new.T.size x + new.T.size y < n := by
                    rw [hsize] at hsum
                    exact hsum
                  have hxN : new.T.size x ≤ N :=
                    Nat.le_trans (Nat.le_of_lt hsx) hsN
                  have hyN : new.T.size y ≤ N :=
                    Nat.le_trans (Nat.le_of_lt hty) htN
                  exact ih (new.T.size x + new.T.size y) hsum'
                    x y rfl hxN hyN (hvNF x hx) (hwNF y hy) hxy
                exact oc_full_lt_of_compareVec_general v w a b hvGood hwGood hmono hcmp
              | eq =>
                rw [hcmp] at hst
                have hvw : v = w := new.Vec_eq_sound v w hcmp
                subst w
                have hsa : new.T.size a < new.T.size (new.T.P v a) :=
                  new.T.add_size_lt_P v a
                have htb : new.T.size b < new.T.size (new.T.P v b) :=
                  new.T.add_size_lt_P v b
                have hsum :
                    new.T.size a + new.T.size b <
                      new.T.size (new.T.P v a) + new.T.size (new.T.P v b) :=
                  Nat.add_lt_add hsa htb
                have hsum' : new.T.size a + new.T.size b < n := by
                  rw [hsize] at hsum
                  exact hsum
                have haN : new.T.size a ≤ N :=
                  Nat.le_trans (Nat.le_of_lt hsa) hsN
                have hbN : new.T.size b ≤ N :=
                  Nat.le_trans (Nat.le_of_lt htb) htN
                have htail := ih (new.T.size a + new.T.size b) hsum'
                  a b rfl haN hbN haNF hbNF hst
                calc
                  trans (new.T.P v a) =
                      T.add (trans (new.T.P v new.T.Z)) (trans a) :=
                    tc_trans_P_add v a
                  _ < T.add (trans (new.T.P v new.T.Z)) (trans b) :=
                    bridge_add_left_lt (trans (new.T.P v new.T.Z))
                      (trans a) (trans b) htail
                  _ = trans (new.T.P v b) := (tc_trans_P_add v b).symm
              | gt =>
                rw [hcmp] at hst
                cases hst)
  intro s t hsN htN hs ht hst
  exact main (new.T.size s + new.T.size t) s t rfl hsN htN hs ht hst

#print axioms bo_order_preserve_bounded

theorem bo_transAux_a0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (transAux v).2.2 = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  intro k
  induction k with
  | zero =>
      intro v
      cases v with
      | @snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2]
              rfl
  | succ m ih =>
      intro v
      cases v with
      | @snoc n xs a =>
          rw [transAux.eq_3]
          cases haux : transAux xs with
          | mk found rest =>
              cases rest with
              | mk sum a0 =>
                  change a0 = trans (new.Vec.idx (new.Vec.snoc (m + 1) xs a)
                    ⟨0, Nat.zero_lt_succ (m + 1)⟩)
                  change a0 = trans (new.Vec.idx xs ⟨0, Nat.zero_lt_succ m⟩)
                  have h := ih xs
                  rw [haux] at h
                  exact h

#print axioms bo_transAux_a0

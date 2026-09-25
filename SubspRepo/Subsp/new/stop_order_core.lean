import Subsp.new.stop_order_cases

open T

theorem oc_mem_size_lt_P {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a x : new.T lam)
    (hx : x ∈ new.Vec.toList v) :
    new.T.size x < new.T.size (new.T.P v a) := by
  obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx v x hx
  rw [← hi]
  exact new.T.idx_size_lt_P v a i

#print axioms oc_mem_size_lt_P

theorem oc_order_preserve_core {lam : Nat}
    (hgood : ∀ x : new.T lam, new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s t hsize hs ht hst
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
                  exact hgood x ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  exact hgood x ⟨hwNF x hx, hwG x hx⟩
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
                  exact ih (new.T.size x + new.T.size y) hsum'
                    x y rfl (hvNF x hx) (hwNF y hy) hxy
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
                have htail := ih (new.T.size a + new.T.size b) hsum'
                  a b rfl haNF hbNF hst
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
  intro s t hs ht hst
  exact main (new.T.size s + new.T.size t) s t rfl hs ht hst

#print axioms oc_order_preserve_core

theorem oc_order_embedding_core {lam : Nat}
    (hgood : ∀ x : new.T lam, new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  constructor
  · exact oc_order_preserve_core hgood s t hs ht
  · intro htrans
    cases strict_linear_order.total s t with
    | inl hst => exact hst
    | inr hor =>
      cases hor with
      | inl hts =>
        have hrev := oc_order_preserve_core hgood t s ht hs hts
        have hloop : trans s < trans s :=
          strict_partial_order.trans (trans s) (trans t) (trans s) htrans hrev
        exact False.elim (strict_partial_order.irrefl (trans s) hloop)
      | inr heq =>
        rw [heq] at htrans
        exact False.elim (strict_partial_order.irrefl (trans t) htrans)

#print axioms oc_order_embedding_core


theorem oc_order_preserve_with_smaller_good {lam : Nat}
    (hgood : ∀ x u : new.T lam, new.T.size x < new.T.size u →
      new.T.isNFComp x →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s t hsize hs ht hst
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
                  have hsx := oc_mem_size_lt_P v a x hx
                  exact hgood x (new.T.P v a) hsx ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have htx := oc_mem_size_lt_P w b x hx
                  exact hgood x (new.T.P w b) htx ⟨hwNF x hx, hwG x hx⟩
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
                  exact ih (new.T.size x + new.T.size y) hsum'
                    x y rfl (hvNF x hx) (hwNF y hy) hxy
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
                have htail := ih (new.T.size a + new.T.size b) hsum'
                  a b rfl haNF hbNF hst
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
  intro s t hs ht hst
  exact main (new.T.size s + new.T.size t) s t rfl hs ht hst

#print axioms oc_order_preserve_with_smaller_good

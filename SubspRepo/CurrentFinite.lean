import Subsp.new.stop_nf_core

open T

theorem current_order_preserve_below {lam : Nat} (N : Nat)
    (hgood : ∀ x : new.T lam, new.T.size x < N → new.T.isNFComp x →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) :
    ∀ s t : new.T lam,
      new.T.size s < N → new.T.size t < N →
      new.T.isNF s → new.T.isNF t → s < t → trans s < trans t := by
  let motive : Nat → Prop := fun n =>
    ∀ s t : new.T lam,
      new.T.size s + new.T.size t = n →
      new.T.size s < N → new.T.size t < N →
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
                  have hsx := oc_mem_size_lt_P v a x hx
                  have hxN := Nat.lt_trans hsx hsN
                  exact hgood x hxN ⟨hvNF x hx, hvG x hx⟩
                have hwGood :
                    ∀ x : new.T lam, x ∈ new.Vec.toList w →
                      T.isNF1 (trans x) ∧
                        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
                  intro x hx
                  have htx := oc_mem_size_lt_P w b x hx
                  have hxN := Nat.lt_trans htx htN
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
                  have hxN := Nat.lt_trans hsx hsN
                  have hyN := Nat.lt_trans hty htN
                  have hsum :
                      new.T.size x + new.T.size y <
                        new.T.size (new.T.P v a) + new.T.size (new.T.P w b) :=
                    Nat.add_lt_add hsx hty
                  have hsum' : new.T.size x + new.T.size y < n := by
                    rw [hsize] at hsum
                    exact hsum
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
                have haN := Nat.lt_trans hsa hsN
                have hbN := Nat.lt_trans htb htN
                have hsum :
                    new.T.size a + new.T.size b <
                      new.T.size (new.T.P v a) + new.T.size (new.T.P v b) :=
                  Nat.add_lt_add hsa htb
                have hsum' : new.T.size a + new.T.size b < n := by
                  rw [hsize] at hsum
                  exact hsum
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

#print axioms current_order_preserve_below

theorem current_transAux_a0 {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        a0 = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  intro k
  induction k with
  | zero =>
      intro v found sum a0 haux
      cases v with
      | snoc n xs a =>
          cases xs with
          | nil =>
              rw [transAux.eq_2] at haux
              have ha0 : a0 = trans a :=
                congrArg (fun q : Bool × T × T => q.2.2) haux.symm
              change a0 = trans (if h : 0 < 0 then new.Vec.idx new.Vec.nil ⟨0, h⟩ else a)
              rw [dite_eq_right (Nat.lt_irrefl 0)]
              exact ha0
  | succ m ih =>
      intro v found sum a0 haux
      cases v with
      | @snoc n xs a =>
          cases hrest : transAux xs with
          | mk foundRest rest =>
              cases rest with
              | mk sumRest a0Rest =>
                  rw [transAux.eq_3, hrest] at haux
                  have ha0eq : a0 = a0Rest :=
                    congrArg (fun q : Bool × T × T => q.2.2) haux.symm
                  have hrec := ih xs foundRest sumRest a0Rest hrest
                  rw [ha0eq, hrec]
                  change trans (new.Vec.idx xs ⟨0, Nat.zero_lt_succ m⟩) =
                    trans (if h : 0 < m + 1 then new.Vec.idx xs ⟨0, h⟩ else a)
                  rw [dite_eq_left (Nat.zero_lt_succ m)]

#print axioms current_transAux_a0

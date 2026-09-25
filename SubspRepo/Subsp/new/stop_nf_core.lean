import Subsp.new.stop_nf_aux
import Subsp.new.stop_order_core

open T

theorem nfcore_head_NF {lam : Nat} (s : new.T lam)
    (hs : new.T.isNF s) :
    new.T.isNF (new.T.head s) := by
  cases s with
  | Z =>
      exact new.T.isNF.z
  | P ls add =>
      cases hs with
      | p _ _ h0 h1 h2 h3 =>
          rw [new.T.head]
          exact new.T.isNF.p ls new.T.Z h0 new.T.isNF.z h2 (Or.inl rfl)

#print axioms nfcore_head_NF

theorem nfcore_trans_PZ_shape {lam : Nat}
    (v : new.Vec (new.T lam) lam) :
    ∃ i : Nat, ∃ m : T,
      trans (new.T.P v new.T.Z) = T.P i m T.Z := by
  rw [_root_.trans.eq_2]
  cases haux : transAux v with
  | mk found rest =>
      cases rest with
      | mk sum a0 =>
          change
            ∃ i : Nat, ∃ m : T,
              (if found = true then
                T.P 1
                  (T.add (T.card_times 1 (T.one_del sum))
                    (T.early_collapse a0)) T.Z
              else if a0 = T.Z then T.P 0 T.Z T.Z
              else T.P 0 a0 T.Z) = T.P i m T.Z
          by_cases hf : found = true
          · rw [ite_eq_left hf]
            exact ⟨1,
              T.add (T.card_times 1 (T.one_del sum))
                (T.early_collapse a0), rfl⟩
          · rw [ite_eq_right hf]
            by_cases ha0 : a0 = T.Z
            · rw [ite_eq_left ha0]
              exact ⟨0, T.Z, rfl⟩
            · rw [ite_eq_right ha0]
              exact ⟨0, a0, rfl⟩

#print axioms nfcore_trans_PZ_shape

theorem nfcore_add_principal (i : Nat) (m b : T)
    (hp : T.isNF1 (T.P i m T.Z))
    (hb : T.isNF1 b)
    (hhead : T.head b ≤ T.P i m T.Z) :
    T.isNF1 (T.add (T.P i m T.Z) b) := by
  obtain ⟨hm, hz, hg, hh⟩ := T.isNF1_P_inv i m T.Z hp
  rw [T.P_add_eq, T.add.eq_1]
  exact T.isNF1.p i m b hm hb hg hhead

#print axioms nfcore_add_principal

theorem nfcore_trans_P_of_components {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (ha : T.isNF1 (trans a))
    (hhead : T.head (trans a) ≤ trans (new.T.P v new.T.Z)) :
    T.isNF1 (trans (new.T.P v a)) := by
  have hp : T.isNF1 (trans (new.T.P v new.T.Z)) :=
    pn_principal_NF v hv
  obtain ⟨i, m, hshape⟩ := nfcore_trans_PZ_shape v
  rw [tc_trans_P_add v a, hshape]
  rw [hshape] at hp hhead
  exact nfcore_add_principal i m (trans a) hp ha hhead

#print axioms nfcore_trans_P_of_components

theorem nfcore_principal_le {lam : Nat}
    (w v : new.Vec (new.T lam) lam)
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList w → y ∈ new.Vec.toList v →
      x < y → trans x < trans y)
    (hle : new.T.P w new.T.Z ≤ new.T.P v new.T.Z) :
    trans (new.T.P w new.T.Z) ≤ trans (new.T.P v new.T.Z) := by
  cases hle with
  | inl hlt =>
      change
        (match new.compareVec w v with
        | Ordering.eq => new.compareT new.T.Z new.T.Z
        | ord => ord) = Ordering.lt at hlt
      cases hcmp : new.compareVec w v with
      | lt =>
          exact Or.inl
            (oc_full_lt_of_compareVec_general w v new.T.Z new.T.Z
              hw hv hmono hcmp)
      | eq =>
          rw [hcmp] at hlt
          change Ordering.eq = Ordering.lt at hlt
          cases hlt
      | gt =>
          rw [hcmp] at hlt
          cases hlt
  | inr heq =>
      have hterm : new.T.P w new.T.Z = new.T.P v new.T.Z :=
        new.T_eq_sound (new.T.P w new.T.Z) (new.T.P v new.T.Z) heq
      rw [hterm]
      exact Or.inr rfl

#print axioms nfcore_principal_le

theorem nfcore_trans_head_le_P {lam : Nat}
    (w v : new.Vec (new.T lam) lam) (b : new.T lam)
    (hw : ∀ x : new.T lam, x ∈ new.Vec.toList w →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v →
      T.isNF1 (trans x) ∧
        (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hmono : ∀ x y : new.T lam,
      x ∈ new.Vec.toList w → y ∈ new.Vec.toList v →
      x < y → trans x < trans y)
    (hle : new.T.head (new.T.P w b) ≤ new.T.P v new.T.Z) :
    T.head (trans (new.T.P w b)) ≤ trans (new.T.P v new.T.Z) := by
  rw [← tc_trans_head (new.T.P w b)]
  change trans (new.T.P w new.T.Z) ≤ trans (new.T.P v new.T.Z)
  exact nfcore_principal_le w v hw hv hmono hle

#print axioms nfcore_trans_head_le_P

theorem nfcore_NF_step {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hs : new.T.isNF (new.T.P v a))
    (hnfSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size (new.T.P v a) →
      new.T.isNF x → T.isNF1 (trans x))
    (hgoodSmall : ∀ x : new.T lam,
      new.T.size x < new.T.size (new.T.P v a) →
      new.T.isNFComp x →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x))
    (hpresSmall : ∀ x y : new.T lam,
      new.T.size x < new.T.size (new.T.P v a) →
      new.T.size y < new.T.size (new.T.P v a) →
      new.T.isNF x → new.T.isNF y →
      x < y → trans x < trans y) :
    T.isNF1 (trans (new.T.P v a)) := by
  cases hs with
  | p _ _ h0 h1 h2 h3 =>
      have hvGood :
          ∀ x : new.T lam, x ∈ new.Vec.toList v →
            T.isNF1 (trans x) ∧
              (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
        intro x hx
        have hsx : new.T.size x < new.T.size (new.T.P v a) :=
          oc_mem_size_lt_P v a x hx
        exact hgoodSmall x hsx ⟨h0 x hx, h2 x hx⟩
      have haNF : T.isNF1 (trans a) :=
        hnfSmall a (new.T.add_size_lt_P v a) h1
      have hhead : T.head (trans a) ≤ trans (new.T.P v new.T.Z) := by
        cases a with
        | Z =>
            rw [_root_.trans.eq_1, T.head]
            exact T.Z_le _
        | P w b =>
            have hwGood :
                ∀ x : new.T lam, x ∈ new.Vec.toList w →
                  T.isNF1 (trans x) ∧
                    (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
              intro x hx
              have hxa : new.T.size x < new.T.size (new.T.P w b) :=
                oc_mem_size_lt_P w b x hx
              have hap : new.T.size (new.T.P w b) <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                new.T.add_size_lt_P v (new.T.P w b)
              have hxp : new.T.size x <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                Nat.lt_trans hxa hap
              have hcomp : new.T.isNFComp x := by
                cases h1 with
                | p _ _ hw0 hb0 hw2 hbhead =>
                    exact ⟨hw0 x hx, hw2 x hx⟩
              exact hgoodSmall x hxp hcomp
            have hmono :
                ∀ x y : new.T lam,
                  x ∈ new.Vec.toList w → y ∈ new.Vec.toList v →
                  x < y → trans x < trans y := by
              intro x y hx hy hxy
              have hxa : new.T.size x < new.T.size (new.T.P w b) :=
                oc_mem_size_lt_P w b x hx
              have hap : new.T.size (new.T.P w b) <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                new.T.add_size_lt_P v (new.T.P w b)
              have hxp : new.T.size x <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                Nat.lt_trans hxa hap
              have hyp : new.T.size y <
                  new.T.size (new.T.P v (new.T.P w b)) :=
                oc_mem_size_lt_P v (new.T.P w b) y hy
              have hxNF : new.T.isNF x := by
                cases h1 with
                | p _ _ hw0 hb0 hw2 hbhead => exact hw0 x hx
              have hyNF : new.T.isNF y := h0 y hy
              exact hpresSmall x y hxp hyp hxNF hyNF hxy
            exact nfcore_trans_head_le_P w v b hwGood hvGood hmono h3
      exact nfcore_trans_P_of_components v a hvGood haNF hhead

#print axioms nfcore_NF_step

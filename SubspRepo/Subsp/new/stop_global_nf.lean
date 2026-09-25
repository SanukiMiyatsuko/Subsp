import Subsp.new.stop_trans_support
import Subsp.new.stop_bound_order

open T

theorem gnf_all {lam : Nat} :
    ∀ s : new.T lam,
      (new.T.isNF s → T.isNF1 (trans s)) ∧
      (new.T.isNF s →
        ∀ y : T, y ∈ T.G1 0 (trans s) →
          y < trans s ∨
            ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z) ∧
      (new.T.isNFComp s →
        T.isNF1 (trans s) ∧
          (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s)) := by
  let motive : Nat → Prop := fun n =>
    ∀ s : new.T lam, new.T.size s = n →
      (new.T.isNF s → T.isNF1 (trans s)) ∧
      (new.T.isNF s →
        ∀ y : T, y ∈ T.G1 0 (trans s) →
          y < trans s ∨
            ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z) ∧
      (new.T.isNFComp s →
        T.isNF1 (trans s) ∧
          (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s))
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s hsize
      have hsmall :
          ∀ x : new.T lam, new.T.size x < new.T.size s →
            (new.T.isNF x → T.isNF1 (trans x)) ∧
            (new.T.isNF x →
              ∀ y : T, y ∈ T.G1 0 (trans x) →
                y < trans x ∨
                  ∃ z : new.T lam, z ∈ new.T.G x ∧ y ≤ trans z) ∧
            (new.T.isNFComp x →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) := by
        intro x hx
        have hxn : new.T.size x < n := by
          rw [← hsize]
          exact hx
        exact ih (new.T.size x) hxn x rfl
      have hgoodSmall :
          ∀ x : new.T lam, new.T.size x < new.T.size s →
            new.T.isNFComp x →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
        intro x hx hcomp
        exact (hsmall x hx).2.2 hcomp
      have hpresBound :
          ∀ x y : new.T lam,
            new.T.size x ≤ new.T.size s →
            new.T.size y ≤ new.T.size s →
            new.T.isNF x → new.T.isNF y →
            x < y → trans x < trans y := by
        exact bo_order_preserve_bounded (new.T.size s) hgoodSmall
      have hNF : new.T.isNF s → T.isNF1 (trans s) := by
        intro hs
        cases s with
        | Z =>
            rw [_root_.trans.eq_1]
            exact T.isNF1.z
        | P v a =>
            exact nfcore_NF_step v a hs
              (fun x hx hnx => (hsmall x hx).1 hnx)
              hgoodSmall
              (fun x y hx hy hnx hny hxy =>
                hpresBound x y (Nat.le_of_lt hx) (Nat.le_of_lt hy)
                  hnx hny hxy)
      have hDecomp :
          new.T.isNF s →
            ∀ y : T, y ∈ T.G1 0 (trans s) →
              y < trans s ∨
                ∃ z : new.T lam, z ∈ new.T.G s ∧ y ≤ trans z := by
        intro hs
        exact ts_support_decomp_step s hs (hNF hs)
          hgoodSmall
          (fun x hx hnx => (hsmall x hx).2.1 hnx)
      have hGood :
          new.T.isNFComp s →
            T.isNF1 (trans s) ∧
              (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s) := by
        intro hscomp
        constructor
        · exact hNF hscomp.1
        · intro y hy
          cases hDecomp hscomp.1 y hy with
          | inl hlt => exact hlt
          | inr hw =>
              obtain ⟨z, hz, hyz⟩ := hw
              have hzComp : new.T.isNFComp z :=
                new.T.isNF_G_isNFComp s hscomp.1 z hz
              have hzsSize : new.T.size z < new.T.size s :=
                new.T.G_size_lt s z hz
              have hzs : z < s := hscomp.2 z hz
              have htrans : trans z < trans s :=
                hpresBound z s (Nat.le_of_lt hzsSize) (Nat.le_refl _) hzComp.1 hscomp.1 hzs
              exact lt_of_le_of_lt_thm T y (trans z) (trans s) hyz htrans
      exact ⟨hNF, hDecomp, hGood⟩)
  intro s
  exact main (new.T.size s) s rfl

#print axioms gnf_all

theorem gnf_NF_is_NF1 {lam : Nat} (s : new.T lam) :
    new.T.isNF s → T.isNF1 (trans s) := by
  exact (gnf_all s).1

#print axioms gnf_NF_is_NF1

theorem gnf_good {lam : Nat} (s : new.T lam) :
    new.T.isNFComp s →
      T.isNF1 (trans s) ∧
        (∀ y : T, y ∈ T.G1 0 (trans s) → y < trans s) := by
  exact (gnf_all s).2.2

#print axioms gnf_good

theorem gnf_order_embedding {lam : Nat} (s t : new.T lam)
    (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  exact oc_order_embedding_core (fun x hx => gnf_good x hx) s t hs ht

#print axioms gnf_order_embedding

import Subsp.new.stop_surj_principal
import Subsp.new.stop_surj_low

open T StopSurjMeasure StopSurjCard StopSurjVector StopSurjPrincipal

namespace StopSurjSupport

/-- A recovered coordinate is controlled either by a target support term or by
every fixed positive-index bound on the support of the target's high part. -/
def Supported (t y : T) : Prop :=
  (∃ z, z ∈ T.G1 0 t ∧ y ≤ z) ∨
  (∀ B, T.part B = (B, T.Z) →
    (∀ z, z ∈ T.G1 0 (T.part t).1 → z < B) → y < B)

def Preimage {lam : Nat} (t : T) (s : new.T lam) : Prop :=
  new.T.isNF s ∧ trans s = t ∧ ∀ y, y ∈ new.T.G s → Supported t (trans y)

theorem supported_le (t x y : T) (hxy : x ≤ y) (hy : Supported t y) : Supported t x := by
  cases hy with
  | inl hw =>
      cases hw with
      | intro z hz =>
          refine Or.inl ⟨z, hz.1, ?_⟩
          cases hxy with
          | inl h => exact Or.inl (lt_of_lt_of_le_thm T _ _ _ h hz.2)
          | inr h => rw [h]; exact hz.2
  | inr h =>
      apply Or.inr
      intro B hB hG
      exact lt_of_le_of_lt_thm T _ _ _ hxy (h B hB hG)

theorem comp_of_preimage {lam : Nat} (t : T) (s : new.T lam)
    (hs : Preimage t s) (hg : StopUncollapse.Good t) : new.T.isNFComp s := by
  refine ⟨hs.1, ?_⟩
  intro y hy
  have hynf := (new.T.isNF_G_isNFComp s hs.1 y hy).1
  apply (gnf_order_embedding y s hynf hs.1).mpr
  rw [hs.2.1]
  cases hs.2.2 y hy with
  | inl hw =>
      cases hw with
      | intro z hz => exact lt_of_le_of_lt_thm T _ _ _ hz.2 (hg z hz.1)
  | inr h =>
      exact lt_of_lt_of_le_thm T _ _ _
        (h (T.part t).1 (ec_part_fst_fixed t) (sg_good0_part_fst t hg))
        (bridge_part_fst_le_self t)

theorem supported_tail (p : Nat) (a b y : T) (hnf : T.isNF1 (T.P p a b))
    (h : Supported b y) : Supported (T.P p a b) y := by
  cases h with
  | inl hw =>
      cases hw with
      | intro z hz =>
          refine Or.inl ⟨z, ?_, hz.2⟩
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
          exact List.mem_append_right _ hz.1
  | inr h =>
      cases p with
      | zero =>
          have hi := isNF1_index 0 0 a b hnf (Nat.le_refl 0)
          have hbidx : T.index_Prop1 0 b := by
            cases hi with
            | p _ _ _ hp hb => exact hb
          have hp := StopUncollapse.part_of_index0 b hbidx
          have hbad : y < T.Z := h T.Z rfl (by
            intro z hz
            rw [hp] at hz
            cases hz)
          exact False.elim (lt_Z_inv hbad)
      | succ p =>
          apply Or.inr
          intro B hB hG
          apply h B hB
          intro z hz
          apply hG z
          rw [T.part, ite_eq_right (Nat.succ_ne_zero p)]
          change z ∈ T.G1 0 (T.P (p + 1) a (T.part b).1)
          rw [T.G1.eq_2, ite_eq_left (Nat.zero_le (p + 1))]
          exact List.mem_append_right _ hz

theorem supported_middle (p : Nat) (a b x : T) (hxa : x ≤ a) : Supported (T.P p a b) x := by
  refine Or.inl ⟨a, ?_, hxa⟩
  rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))

theorem supported_higher (a b x : T)
    (h : ∀ B, T.part B = (B, T.Z) → Small B a → x < B) : Supported (T.P 1 a b) x := by
  apply Or.inr
  intro B hB hG
  apply h B hB
  have hG' : ∀ z, z ∈ T.G1 0 (T.P 1 a (T.part b).1) → z < B := by
    intro z hz
    apply hG z
    rw [T.part, ite_eq_right (by intro h; cases h)]
    exact hz
  constructor
  · apply hG' a
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1)]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))
  · intro z hz
    apply hG' z
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1)]
    exact List.mem_append_left _ (List.mem_append_right _ hz)

theorem assemble {lam : Nat} (p : Nat) (a b : T) (hnf : T.isNF1 (T.P p a b))
    (v : new.Vec (new.T lam) lam) (sb : new.T lam)
    (hv : ∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x)
    (htrans : trans (new.T.P v new.T.Z) = T.P p a T.Z)
    (hsb : Preimage b sb)
    (hcoord : ∀ x, x ∈ new.Vec.toList v → Supported (T.P p a b) (trans x)) :
    Preimage (T.P p a b) (new.T.P v sb) := by
  have hpNF : new.T.isNF (new.T.P v new.T.Z) := by
    apply new.T.isNF_PZ_of_coords
    intro i
    exact hv (v.idx i) (new.Vec.idx_mem_toList v i)
  have hheadT : trans (new.T.head sb) ≤ trans (new.T.P v new.T.Z) := by
    rw [tc_trans_head, hsb.2.1, htrans]
    exact (T.isNF1_P_inv p a b hnf).2.2.2
  have hhead := StopSurjLow.reflect_le_NF (new.T.head sb) (new.T.P v new.T.Z)
    (nfcore_head_NF sb hsb.1) hpNF hheadT
  have hsNF : new.T.isNF (new.T.P v sb) := new.T.isNF.p v sb
    (fun x hx => (hv x hx).1) hsb.1 (fun x hx => (hv x hx).2) hhead
  refine ⟨hsNF, ?_, ?_⟩
  · rw [tc_trans_P_add, htrans, hsb.2.1, T.P_add_eq, T.add.eq_1]
  · intro y hy
    cases (new.T.mem_G_P v sb y).mp hy with
    | inl hc =>
        cases hc with
        | intro i hi =>
            have hmem := new.Vec.idx_mem_toList v i
            cases hi with
            | inl he => rw [he]; exact hcoord (v.idx i) hmem
            | inr hg =>
                have hxi := hv (v.idx i) hmem
                have hyNF := (new.T.isNF_G_isNFComp (v.idx i) hxi.1 y hg).1
                have hlt := (gnf_order_embedding y (v.idx i) hyNF hxi.1).mp (hxi.2 y hg)
                exact supported_le _ _ _ (Or.inl hlt) (hcoord (v.idx i) hmem)
    | inr ht => exact supported_tail p a b (trans y) hnf (hsb.2.2 y ht)

#print axioms assemble
#print axioms comp_of_preimage

end StopSurjSupport

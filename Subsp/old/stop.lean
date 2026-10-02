import Subsp.old.stop_low_dims
import Subsp.old.stop_translation
import Subsp.old.stop_ot_char
import Subsp.old.stop_ot_domain

/-! The order isomorphism between legacy OT terms and Buchholz normal forms below
`ψ_0(Ω_lam)`, given by the legacy translation. -/

namespace LegacyTranslation

open T

theorem index_of_lt_level (l : Nat) (y : T) (hy : T.isNF1 y) (hlt : y < T.P (l + 1) T.Z T.Z) :
    T.index_Prop1 l y := by
  cases y with
  | Z => exact .z
  | P p a b =>
      have hp : p ≤ l := by
        cases hlt with
        | p_head _ _ _ _ _ _ h => omega
        | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => exact absurd h lt_Z_inv
      exact isNF1_index l p a b hy hp

/-- Normal forms whose arguments lie below a level only use indices below it. -/
theorem DeepIdx_of_args (l : Nat) : ∀ x : T, T.isNF1 x →
    (∀ y ∈ T.G1 0 x, y < T.P (l + 1) T.Z T.Z) → T.index_Prop1 l x → DeepIdx l x
  | .Z, _, _, _ => trivial
  | .P p a b, hx, hg, hi => by
      obtain ⟨ha, hb, _, _⟩ := T.isNF1_P_inv p a b hx
      have hp : p ≤ l := by cases hi with | p _ _ _ h _ => exact h
      have hbi : T.index_Prop1 l b := by cases hi with | p _ _ _ _ h => exact h
      have hga : ∀ y ∈ T.G1 0 a, y < T.P (l + 1) T.Z T.Z := fun y hy => hg y (by
        simp only [T.G1, Nat.zero_le, ite_true, List.mem_append]; exact Or.inl (Or.inr hy))
      have hgb : ∀ y ∈ T.G1 0 b, y < T.P (l + 1) T.Z T.Z := fun y hy => hg y (by
        simp only [T.G1, Nat.zero_le, ite_true, List.mem_append]; exact Or.inr hy)
      have hal : a < T.P (l + 1) T.Z T.Z := hg a (by simp [T.G1])
      exact ⟨hp, DeepIdx_of_args l a ha hga (index_of_lt_level l a ha hal),
        DeepIdx_of_args l b hb hgb hbi⟩

theorem SubNF_args (k : Nat) : ∀ t : T, T.isNF1 t → t < T.P 0 (T.P (k + 1) T.Z T.Z) T.Z →
    ∀ y ∈ T.G1 0 t, y < T.P (k + 1) T.Z T.Z
  | .Z, _, _, y, hy => by cases hy
  | .P p x r, ht, hlt, y, hy => by
      obtain ⟨hx, hr, hgx, _⟩ := T.isNF1_P_inv p x r ht
      have hp0 : p = 0 := by
        cases hlt with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
        | p_mid _ _ _ _ _ _ => rfl
        | p_tail _ _ _ _ _ => rfl
      subst hp0
      have hxl : x < T.P (k + 1) T.Z T.Z := by
        cases hlt with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
        | p_mid _ _ _ _ _ h => exact h
        | p_tail _ _ _ _ h => exact absurd h lt_Z_inv
      have hrl : r < T.P 0 (T.P (k + 1) T.Z T.Z) T.Z :=
        lt_of_le_of_lt_thm T _ _ _ (T.isNF1_tail_le _ ht 0 x r rfl) hlt
      simp only [T.G1, Nat.zero_le, ite_true, List.mem_append, List.mem_singleton] at hy
      rcases hy with (rfl | hy) | hy
      · exact hxl
      · exact lt_trans_thm _ _ _ (hgx y hy) hxl
      · exact SubNF_args k r hr hrl y hy

theorem SubNF_DeepIdx (k : Nat) (t : T) (ht : T.isSubNF (k + 1) t) : DeepIdx k t := by
  apply DeepIdx_of_args k t ht.1 (SubNF_args k t ht.1 ht.2)
  apply Rank1Termination.index_mono (Nat.zero_le k)
  apply index_of_lt_level 0 t ht.1
  exact lt_trans_thm _ _ _ ht.2 (T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0))

theorem otBound_isNF (lam : Nat) : new.T.isNF (new.T.otBound lam) := by
  apply new.T.isNF.p _ _ _ new.T.isNF.z _ (new.T.Z_le _)
  · intro i
    rw [new.Vec.ofFn_idx]
    split
    · exact (new.T.ofNat_isNFComp 0 1).1
    · exact new.T.isNF.z
  · intro i
    rw [new.Vec.ofFn_idx]
    split
    · exact (new.T.ofNat_isNFComp i.val 1).2
    · intro x hx; cases hx

theorem OT_isSubNF (lam : Nat) (s : new.T lam) (hs : new.T.isOT lam s) :
    T.isSubNF lam (trans s) :=
  ⟨trans_isNF1 s (new.T.isOT_isNF s hs), OT_bound lam s hs⟩

theorem SubNF_preimage (k : Nat) (t : T) (ht : T.isSubNF (k + 1) t) :
    ∃ s : new.T (k + 1), new.T.isOT (k + 1) s ∧ trans s = t := by
  obtain ⟨s, hs, hts⟩ := trans_surj (Nat.zero_lt_succ k) t ht.1 (SubNF_DeepIdx k t ht)
  refine ⟨s, (OT_iff_NF_src (k + 1) s).mpr ⟨hs, fun hk => ?_⟩, hts⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  apply (trans_lt_iff _ _ hs (otBound_isNF (j + 2))).mpr
  rw [hts, trans_otBound j]
  exact lt_trans_thm _ _ _ ht.2 (T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0))

end LegacyTranslation

theorem OT_SubNF_order_iso (lam : Nat) :
    ∃ f : new.T.OT lam → T.SubNF lam,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  cases lam with
  | zero => exact OT_SubNF_order_iso_zero
  | succ k =>
      refine ⟨fun s => ⟨trans s.val, LegacyTranslation.OT_isSubNF (k + 1) s.val s.property⟩,
        ?_, ?_, ?_⟩
      · intro s t h
        exact Subtype.ext (LegacyTranslation.trans_injective_NF s.val t.val
          (new.T.isOT_isNF _ s.property) (new.T.isOT_isNF _ t.property)
          (congrArg Subtype.val h))
      · intro t
        obtain ⟨s, hs, hts⟩ := LegacyTranslation.SubNF_preimage k t.val t.property
        exact ⟨⟨s, hs⟩, Subtype.ext hts⟩
      · intro s t
        exact LegacyTranslation.trans_lt_iff s.val t.val
          (new.T.isOT_isNF _ s.property) (new.T.isOT_isNF _ t.property)

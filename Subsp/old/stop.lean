import Subsp.old.stop_ot_char

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

theorem otBound_isNF (lam : Nat) : new.T.isNF (new.T.otBound lam) := by
  refine new.T.isNF.p _ _ (fun i => ?_) new.T.isNF.z (fun i => ?_) (new.T.Z_le _) <;>
    rw [new.Vec.ofFn_idx] <;> split
  · exact (new.T.ofNat_isNFComp 0 1).1
  · exact new.T.isNF.z
  · exact (new.T.ofNat_isNFComp i.val 1).2
  · intro x hx; cases hx

theorem trans_otBound (k : Nat) : trans (new.T.otBound (k + 2)) = T.P 1 T.Z T.Z := by
  have haux (j : Nat) (u : new.T (k + 2)) (hu : trans u = T.P 0 T.Z T.Z) :
      transAux (new.Vec.ofFn (j + 2) (fun i => if i.val = 1 then u else new.T.Z)) =
        (T.P 1 T.Z T.Z, T.P 1 T.Z T.Z) := by
    induction j with
    | zero =>
        change transAux (new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil new.T.Z) u) = _
        cases u with
        | Z => cases hu
        | P ls add =>
            simp [transAux, hu, _root_.trans.eq_1, T.early_collapse, T.part, T.card_times,
              T.one_del]
            constructor <;> rfl
    | succ j ih =>
        rw [new.Vec.ofFn]
        simp only [Fin.val_last, Fin.val_castSucc, show j + 2 ≠ 1 by omega, ite_false]
        rw [transAux_snoc_zero]
        exact ih
  rw [new.T.otBound, trans_as_add, haux k _ (by rw [trans_as_add, transAux_zeros]; rfl)]
  rfl

theorem SubNF_preimage (lam : Nat) (t : T) (ht : T.isSubNF lam t) :
    ∃ s : new.T lam, new.T.isOT lam s ∧ trans s = t := by
  cases lam with
  | zero =>
      -- below `ψ_0(Ω_0)` all normal forms are finite
      have hN : T.IsN t := by
        obtain ⟨ht, hlt⟩ := ht
        have hhead : T.head t ≤ T.P 0 T.Z T.Z := by
          cases hlt with
          | Z_lt_P => exact T.Z_le _
          | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
          | p_mid _ a _ _ _ h => rw [lt_one_eq_Z a h]; exact Or.inr rfl
          | p_tail _ _ _ _ h => cases h
        clear hlt
        induction ht with
        | z => exact .zero
        | p p a b _ _ _ hh _ ih =>
            rcases hhead with hh' | hh'
            · cases hh' with
              | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
              | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
            · cases hh'
              exact .succ b (ih hh)
      obtain ⟨n, rfl⟩ := IsN_exists_ofNat hN
      clear hN ht
      have h : trans (new.T.ofNat (lam := 0) n) = T.ofNat n ∧ new.T.LF 0 n = new.T.ofNat n := by
        induction n with
        | zero => exact ⟨rfl, rfl⟩
        | succ n ih =>
            exact ⟨by rw [new.T.ofNat, trans_zeros_P, ih.1]; rfl,
              congrArg (new.T.P new.Vec.nil) ih.2⟩
      exact ⟨new.T.ofNat n, h.2 ▸ new.T.isOT.base_0 n, h.1⟩
  | succ k =>
      have hD : DeepIdx k t := by
        apply DeepIdx_of_args k t ht.1 (SubNF_args k t ht.1 ht.2)
        apply Rank1Termination.index_mono (Nat.zero_le k)
        apply index_of_lt_level 0 t ht.1
        exact lt_trans_thm _ _ _ ht.2 (T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0))
      obtain ⟨s, hs, hts⟩ := trans_surj_aux (Nat.zero_lt_succ k) _ t (Nat.le_refl _) ht.1 hD
      refine ⟨s, (OT_iff_NF_src k s).mpr ⟨hs, fun hk => ?_⟩, hts⟩
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
  refine ⟨fun s => ⟨trans s.val, LegacyTranslation.trans_isNF1 _ (new.T.isOT_isNF _ s.property),
    LegacyTranslation.OT_bound lam _ s.property⟩, ?_, ?_, ?_⟩
  · intro s t h
    exact Subtype.ext (LegacyTranslation.trans_injective_NF s.val t.val
      (new.T.isOT_isNF _ s.property) (new.T.isOT_isNF _ t.property) (congrArg Subtype.val h))
  · intro t
    obtain ⟨s, hs, hts⟩ := LegacyTranslation.SubNF_preimage lam t.val t.property
    exact ⟨⟨s, hs⟩, Subtype.ext hts⟩
  · intro s t
    exact LegacyTranslation.trans_lt_iff s.val t.val
      (new.T.isOT_isNF _ s.property) (new.T.isOT_isNF _ t.property)

theorem wellfounded_OT (lam : Nat) : WellFounded (fun s t : new.T.OT lam => s.val < t.val) :=
  InvImage.wf
    (fun s : new.T.OT lam =>
      (⟨s.val, new.T.isOT_isNF s.val s.property⟩ : LegacyTranslation.NFsrc lam))
    (LegacyTranslation.wf_NFsrc lam)

def new.T.OTStep {lam : Nat} (a b : new.T.OT lam) : Prop :=
  b.val ≠ new.T.Z ∧
    ∃ n : Nat, a.val = new.T.fund b.val (new.T.ofNat n)

abbrev new.T.OTFundLt {lam : Nat} : new.T.OT lam → new.T.OT lam → Prop :=
  FundOrder.TransClosure new.T.OTStep

theorem new.T.OTStep_lt {lam : Nat} {a b : new.T.OT lam}
    (h : new.T.OTStep a b) :
    a.val < b.val := by
  rcases h with ⟨hbne, n, ha⟩
  rw [ha]
  exact new.T.fund_lt_self b.val (new.T.ofNat n) hbne

theorem new.T.OTFundLt_lt {lam : Nat} {a b : new.T.OT lam}
    (h : new.T.OTFundLt a b) :
    a.val < b.val := by
  induction h with
  | single hstep => exact new.T.OTStep_lt hstep
  | tail _ hstep ih =>
      exact strict_partial_order.trans _ _ _ ih (new.T.OTStep_lt hstep)

theorem new.T.OTFundLt_of_lt {lam : Nat} (a b : new.T.OT lam)
    (hab : a.val < b.val) :
    new.T.OTFundLt a b := by
  induction b using (wellfounded_OT lam).induction generalizing a with
  | h b ih =>
      obtain ⟨n, hfall, hupper⟩ :=
        LegacyTranslation.fund_countable_cofinal_src b.val a.val
          (new.T.isOT_isNF b.val b.property) (new.T.isOT_isNF a.val a.property)
          (new.T.isOT_dom_not_Omega lam b.val b.property) hab
      let c : new.T.OT lam :=
        ⟨new.T.fund b.val (new.T.ofNat n),
          new.T.isOT.step lam b.val b.property n⟩
      have hbne : b.val ≠ new.T.Z := by
        intro hbz
        rw [hbz] at hab
        exact new.T.lt_Z_false a.val hab
      have hstep : new.T.OTStep c b := ⟨hbne, n, rfl⟩
      rcases hupper with hlt | heq
      · exact FundOrder.TransClosure.tail (ih c hfall a hlt) hstep
      · have hac : a = c := Subtype.ext (new.T_eq_sound _ _ heq)
        subst a
        exact FundOrder.TransClosure.single hstep

theorem new.T.OTFundLt_iff_lt {lam : Nat} (a b : new.T.OT lam) :
    new.T.OTFundLt a b ↔ a.val < b.val :=
  ⟨new.T.OTFundLt_lt, new.T.OTFundLt_of_lt a b⟩

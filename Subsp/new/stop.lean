import Subsp.new.stop_surjectivity

/-! The order isomorphism between OT and SubNF. Import this module for all stop results. -/

theorem trans_injective_OT (lam : Nat) (s t : new.T lam)
    (hs : new.T.isOT lam s)
    (ht : new.T.isOT lam t)
    (h : trans s = trans t) :
    s = t := by
  exact trans_injective_on_NF s t
    ((new.T.OT_iff_NF lam s).mp hs).1
    ((new.T.OT_iff_NF lam t).mp ht).1 h

/-- The translation restricted to the two systems of ordinal notations. -/
def trans_OT (lam : Nat) (s : new.T.OT lam) : T.SubNF lam :=
  ⟨trans s.val, OT_imp_NF1 lam s.val s.property⟩

theorem trans_OT_injective (lam : Nat) (s t : new.T.OT lam)
    (h : trans_OT lam s = trans_OT lam t) : s = t := by
  exact Subtype.ext (trans_injective_OT lam s.val t.val s.property t.property (congrArg Subtype.val h))

theorem trans_OT_surjective (lam : Nat) (t : T.SubNF lam) :
    ∃ s : new.T.OT lam, trans_OT lam s = t := by
  obtain ⟨s, hs, he⟩ := exists_OT_of_SubNF lam t.val t.property
  exact ⟨⟨s, hs⟩, Subtype.ext he⟩

theorem trans_OT_lt_iff (lam : Nat) (s t : new.T.OT lam) :
    s.val < t.val ↔ (trans_OT lam s).val < (trans_OT lam t).val := by
  exact order_embeding lam s.val t.val
    ((new.T.OT_iff_NF lam s.val).mp s.property).1
    ((new.T.OT_iff_NF lam t.val).mp t.property).1

theorem trans_OT_le_iff (lam : Nat) (s t : new.T.OT lam) :
    s.val ≤ t.val ↔ (trans_OT lam s).val ≤ (trans_OT lam t).val := by
  exact gnf_le_iff s.val t.val
    (ot_new_isOT_sound lam s.val s.property).1
    (ot_new_isOT_sound lam t.val t.property).1

theorem OT_SubNF_order_iso (lam : Nat) :
    ∃ f : new.T.OT lam → T.SubNF lam,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  exact ⟨trans_OT lam, trans_OT_injective lam,
    trans_OT_surjective lam, trans_OT_lt_iff lam⟩

#print axioms OT_SubNF_order_iso

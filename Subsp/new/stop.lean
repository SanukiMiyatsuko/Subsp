import Subsp.new.multivariable
import Subsp.order
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
      have hb := ot_new_isOT_sound lam b.val b.property
      have ha := ot_new_isOT_sound lam a.val a.property
      obtain ⟨n, hfall, hupper⟩ :=
        ot_fund_countable_cofinal b.val a.val hb.1 ha.1 hb.2 hab
      let c : new.T.OT lam :=
        ⟨new.T.fund b.val (new.T.ofNat n),
          new.T.isOT.step lam b.val b.property n⟩
      have hbne : b.val ≠ new.T.Z := by
        intro hbz
        rw [hbz] at hab
        exact ot_lt_Z_inv a.val hab
      have hstep : new.T.OTStep c b := by
        exact ⟨hbne, n, rfl⟩
      rcases hupper with hlt | heq
      · exact FundOrder.TransClosure.tail (ih c hfall a hlt) hstep
      · have hac : a = c := Subtype.ext (new.T_eq_sound _ _ heq)
        subst a
        exact FundOrder.TransClosure.single hstep

theorem new.T.OTFundLt_iff_lt {lam : Nat} (a b : new.T.OT lam) :
    new.T.OTFundLt a b ↔ a.val < b.val := by
  exact ⟨new.T.OTFundLt_lt, new.T.OTFundLt_of_lt a b⟩

import Subsp.multi.kuma.LabelCut

/-! Closed countable diagonals: context bounds, highest/higher diagonals and the diagonal partition
(the `multi` version of `Subsp/Support/Diagonal.lean`). -/

namespace kumakuma.GeneralImageComparableCuts

open OCF.Jaeger kumakuma.TargetArithmetic kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageCoefficients
open kumakuma.GeneralImageWFInvariant

universe u

theorem H_subset_of_comparable_cuts [LargeCardinals.{u}] (w v t : Term)
    (hwR : Term.isRT w = true) (hw : Term.wf w = true)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (ht : Term.wf t = true)
    (hcut : Term.le w v = true) (hpred : Term.le (Term.predR w) (Term.predR v) = true)
    {z : Term} (hz : z ∈ Term.H v t) : z = .zero ∨ z ∈ Term.H w t := by
  have hpw := (sem_of_wf.{u} hw).isR_pred hwR
  have hpv := (sem_of_wf.{u} hv).isR_pred hvR
  induction t with
  | zero => cases hz
  | add a b iha ihb =>
    have hp := (Term.wf_add_iff _ _).mp ht
    rw [Term.H] at hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases iha hp.2.1 hz with he | he
      · exact Or.inl he
      · exact Or.inr (List.mem_append_left _ he)
    · rcases ihb hp.2.2.1 hz with he | he
      · exact Or.inl he
      · exact Or.inr (List.mem_append_right _ he)
  | inacc n a ih =>
    rcases H_inacc_support n a hz with he | he
    · exact Or.inl he
    · rcases ih ((Term.wf_inacc_iff _ _).mp ht).1 he with he | he
      · exact Or.inl he
      · exact Or.inr (List.mem_append_right _ he)
  | psi c a ihc iha =>
    have hp := (Term.wf_psi_iff _ _).mp ht
    by_cases hskip : Term.le (.psi c a) (Term.predR w) = true
    · have hn := target_le_trans ht hpw.1 hpv.1 hskip hpred
      rw [H_eq_nil_of_le_pred v _ hvR hv ht hn] at hz
      cases hz
    · have hskipF : Term.le (.psi c a) (Term.predR w) = false := by
        cases he : Term.le (.psi c a) (Term.predR w) <;> simp_all
      rw [Term.H, hskipF]
      by_cases hcw : Term.lt c w = true
      · have hcv : Term.lt c v = true := by
          rcases (Term.le_iff_eq_or_lt _ _).mp hcut with he | he
          · rw [← he]; exact hcw
          · exact lemma_6_1.{u}.2.1 _ _ _ hp.2.1 hw hv hcw he
        simp only [hcw, ↓reduceIte]
        rw [Term.H] at hz
        split at hz
        · cases hz
        · exact ihc hp.2.1 hz
      · have hcwF : Term.lt c w = false := by
          cases he : Term.lt c w <;> simp_all
        simp only [hcwF, Bool.false_eq_true, ↓reduceIte]
        rcases H_psi_support hz with he | he | he
        · exact Or.inr (List.mem_cons.mpr (Or.inl he))
        · rcases iha hp.2.2.1 he with he | he
          · exact Or.inl he
          · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_left _ he))
        · rcases ihc hp.2.1 he with he | he
          · exact Or.inl he
          · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_right _ he))

theorem H_bound_of_comparable_cuts [LargeCardinals.{u}] (w v t : Term)
    (hwR : Term.isRT w = true) (hw : Term.wf w = true)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (ht : Term.wf t = true)
    (hcut : Term.le w v = true) (hpred : Term.le (Term.predR w) (Term.predR v) = true)
    (hH : Term.allLt (Term.H w t) t = true) : Term.allLt (Term.H v t) t = true := by
  by_cases ht0 : t = .zero
  · simp only [ht0, Term.H, Term.allLt, List.all_nil]
  · apply (Term.allLt_iff _ _).mpr; intro z hz
    rcases H_subset_of_comparable_cuts w v t hwR hw hvR hv ht hcut hpred hz with he | he
    · rw [he]; exact (zero_lt_iff t).mpr ht0
    · exact (Term.allLt_iff _ _).mp hH z he

end kumakuma.GeneralImageComparableCuts

namespace kumakuma.GeneralImageContextBoundDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageLabelCut kumakuma.GeneralImageLabelClosure
open kumakuma.GeneralImageComparableCuts kumakuma.GeneralImageParametricCut
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRegularDiagonal
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageHeadCuts
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLimitBranches
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder

universe u

theorem regular_lower_label_cut_context [LargeCardinals.{u}] (k m : Nat) (hmk : m ≤ k)
    (q : V multi.T) (hqD : Dim (k + 3) (.P q .Z))
    (hfz : V.fnz q = some (m + 1)) (hdOne : domF (V.get0 q (m + 1)) = .one)
    (hr : Recursive (.P q .Z)) (hs : RecursiveWF (k + 3) (.P q .Z)) :
    ∃ a, Above m a ∧ Term.wf a = true ∧
      convert (k + 3) (code (T.fund (.P q .Z) .Z)) = (if a = .zero then Term.one else a) ∧
      CutFund k (.P q .Z) (layerCut m a) ∧ Term.predR (layerCut m a) = a := by
  have hml' : m + 1 < q.length := fnz_lt_length hfz
  have hlow := (V.fnz_some_spec q _ hfz).2
  let p := T.fund (V.get0 q (m + 1)) .Z
  have hpD : Dim (k + 3) p := Dim_fund _ _ (hqD.coord _) (Dim_Z _)
  let base := V.set q (m + 1) p
  have hbaseD : Dim (k + 3) (.P base .Z) := Dim_set hqD (m + 1) hpD _ (Dim_Z _)
  have hzBase : ∀ i, i < m + 1 → V.get0 base i = .Z := by
    intro i hi
    rw [V.get0_set q (m + 1) p i hml', ite_eq_right (by omega)]
    exact hlow i hi
  have hf (t : multi.T) : T.fund (.P q .Z) t = .P (V.set base m t) .Z := fund_one_succ hfz hdOne t
  have hf0 : T.fund (.P q .Z) .Z = .P base .Z := by
    rw [hf]; congr 1
    exact set_eq_self _ _ _ (hzBase m (by omega))
  obtain ⟨a, ha, heBase, heInsert⟩ := principal_insertion_context k m hmk base hbaseD hzBase
  have hBase : RecursiveWF (k + 3) (.P base .Z) := hf0 ▸ (zero_fund_invariant k _ hqD hr hs).1
  have haw : Term.wf a = true := by
    by_cases ha0 : a = .zero
    · rw [ha0]; rfl
    · have := hBase.wf
      rwa [heBase, ite_eq_right ha0] at this
  obtain ⟨cut, hc, _, hPsi, _⟩ := regular_lower_cutFund_image k m hmk q hqD hfz hdOne hr hs
  have hone : ofNatD (k + 3) 1 ≠ .Z := ofNatD_succ_ne _ 0
  obtain ⟨c, hePsi⟩ := hPsi (ofNatD (k + 3) 1) hone
  have heCut : cut = layerCut m a := by
    rw [hf, heInsert _ hone] at hePsi
    have ht0 : convert (k + 3) (code (ofNatD (k + 3) 1)) ≠ .zero :=
      fun he => hone ((convert_eq_zero_iff _ _).1 he)
    by_cases ha0 : a = .zero
    · by_cases hm0 : m = 0
      · simp only [step, ha0, hm0, ↓reduceIte] at hePsi
        exact (Term.psi.inj hePsi).1.symm.trans (by simp [layerCut, ha0, hm0, Term.bigOmega])
      · simp only [step, ha0, hm0, ht0, ↓reduceIte] at hePsi
        exact (Term.psi.inj hePsi).1.symm.trans (by simp [layerCut, ha0])
    · simp only [step, ha0, ht0, ↓reduceIte, regular] at hePsi
      exact (Term.psi.inj hePsi).1.symm.trans (by simp only [layerCut, ha0, ↓reduceIte])
  refine ⟨a, ha, haw, by rw [hf0, heBase], heCut ▸ hc, ?_⟩
  by_cases ha0 : a = .zero
  · simp [layerCut, ha0, Term.predR]
  · simp only [layerCut, ha0, ↓reduceIte, Term.predR, succTerm_ne_zero,
      predT_succTerm haw, show ¬Term.fT a ≤ m from Nat.not_le.mpr (ha.resolve_left ha0)]

theorem principal_Omega_slot_context [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hib : i ≤ k) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ c, Above i c ∧ Term.wf c = true ∧
      RecursiveWF (k + 3) (.P (V.set xs i .Z) .Z) ∧
      convert (k + 3) (code (.P (V.set xs i .Z) .Z)) = (if c = .zero then Term.one else c) ∧
      convert (k + 3) (code (.P xs .Z)) =
        .psi (layerCut i c) (convert (k + 3) (code (V.get0 xs i))) := by
  have hil : i < xs.length := fnz_lt_length hf
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hcw : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hlow := (V.fnz_some_spec xs i hf).2
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hdrop := Omega_image_drop k _ hcD hcr hcw hdq
  have hBase := principal_replace_relative_recursiveWF k xs i (by omega) hsD hlow hs .Z
    (recursive_zero _) hc0 hdrop (by intros; simp [convert_Z, Term.H, Term.allLt])
  have hbD : Dim (k + 3) (.P (V.set xs i .Z) .Z) := Dim_set hsD i (Dim_Z _) _ (Dim_Z _)
  have hzero : ∀ j, j < i + 1 → V.get0 (V.set xs i .Z) j = .Z := by
    intro j hj
    rw [V.get0_set xs i .Z j hil]
    split
    · rfl
    · exact hlow j (by omega)
  obtain ⟨c, hca, heBase, heInsert⟩ := principal_insertion_context k i hib (V.set xs i .Z) hbD hzero
  have heVec : V.set (V.set xs i .Z) i (V.get0 xs i) = xs := by
    rw [set_set]; exact set_eq_self _ _ _ rfl
  have heOld := heInsert (V.get0 xs i) hc0
  rw [heVec] at heOld
  have hcImage0 : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  rw [step_psi_of_drop _ _ _ hcImage0 hdrop] at heOld
  refine ⟨c, hca, ?_, hBase, heBase, heOld⟩
  by_cases hc : c = .zero
  · rw [hc]; rfl
  · have := hBase.wf
    rwa [heBase, ite_eq_right hc] at this


theorem layerCut_le_of_context_le [LargeCardinals.{u}] (i m : Nat) (him : i ≤ m)
    (c a : Term) (hc : Above i c) (ha : Above m a) (ha0 : a ≠ .zero)
    (hcw : Term.wf c = true) (haw : Term.wf a = true) (hca : Term.le c a = true) :
    Term.le (layerCut i c) (layerCut m a) = true ∧
      Term.le (Term.predR (layerCut i c)) (Term.predR (layerCut m a)) = true := by
  have hfa := ha.resolve_left ha0
  have hPredA : Term.predR (layerCut m a) = a := by
    simp only [layerCut, ha0, ↓reduceIte, Term.predR, succTerm_ne_zero,
      predT_succTerm haw, show ¬Term.fT a ≤ m from Nat.not_le.mpr hfa]
  have hcutA := layerCut_wf m a ha haw
  have hcutC := layerCut_wf i c hc hcw
  constructor
  · by_cases hc0 : c = .zero
    · rw [hc0]
      change Term.le (.inacc i .zero) (layerCut m a) = true
      exact kumakuma.GeneralImageEmptyCutDiagonal.empty_le_regular i _ (layerCut_regular m a)
        (by simp only [layerCut, Term.fT]; omega)
    · rcases (Term.le_iff_eq_or_lt _ _).mp hca with he | he
      · subst c
        by_cases himEq : i = m
        · subst i; simp [Term.le]
        · have himLt : i < m := by omega
          have hlt : Term.lt (layerCut i a) (layerCut m a) = true := by
            simp only [layerCut, ha0, ↓reduceIte, Term.lt, himLt, ↓reduceIte]
            rw [succ_principal (above_principal hfa), Term.lt]
            have hself : Term.lt a (regular m a) = true := by
              rw [context_lt_regular hfa (above_principal hfa)]; simp [Term.le]
            simpa only [regular, succ_principal (above_principal hfa)] using hself
          simp [Term.le, hlt]
      · have hregLt : Term.lt (layerCut i c) a = true := by
          simp only [layerCut, hc0, ↓reduceIte]
          change Term.lt (regular i c) a = true
          rwa [regular_lt_context (above_principal (hc.resolve_left hc0)) (show i < Term.fT a by omega)]
        have haLt : Term.lt a (layerCut m a) = true := by
          simp only [layerCut, ha0, ↓reduceIte]
          change Term.lt a (regular m a) = true
          rw [context_lt_regular hfa (above_principal hfa)]
          simp [Term.le]
        have hlt := lemma_6_1.{u}.2.1 _ _ _ hcutC haw hcutA hregLt haLt
        simp [Term.le, hlt]
  · rw [hPredA]
    by_cases hc0 : c = .zero
    · simp only [layerCut, hc0, ↓reduceIte, Term.predR, Term.le]
      simp only [decide_eq_true_eq, Bool.or_eq_true]
      exact Or.inr ((zero_lt_iff _).mpr ha0)
    · have hPredC : Term.predR (layerCut i c) = c := by
        simp only [layerCut, hc0, ↓reduceIte, Term.predR, succTerm_ne_zero,
          predT_succTerm hcw, show ¬Term.fT c ≤ i from Nat.not_le.mpr (hc.resolve_left hc0)]
      rwa [hPredC]

theorem layerCut_comparable_of_erased_le [LargeCardinals.{u}] (i m : Nat) (him : i ≤ m)
    (c a : Term) (hc : Above i c) (ha : Above m a)
    (hcw : Term.wf c = true) (haw : Term.wf a = true)
    (hca : Term.le (if c = .zero then Term.one else c) (if a = .zero then Term.one else a) = true) :
    Term.le (layerCut i c) (layerCut m a) = true ∧
      Term.le (Term.predR (layerCut i c)) (Term.predR (layerCut m a)) = true := by
  by_cases ha0 : a = .zero
  · have hc0 : c = .zero := by
      by_cases hc0 : c = .zero
      · exact hc0
      · have hOne : Term.le c Term.one = true := by simpa only [ha0, ite_eq_right hc0, ↓reduceIte] using hca
        have hEq := (kumakuma.TargetArithmetic.principal_le_one_iff (above_principal (hc.resolve_left hc0)) hcw).mp hOne
        have hfc := hc.resolve_left hc0
        rw [hEq] at hfc
        simp [Term.fT, Term.one, Term.bigOmega] at hfc
    simp only [layerCut, hc0, ha0, ↓reduceIte, Term.predR]
    constructor
    · exact kumakuma.GeneralImageEmptyCutDiagonal.empty_le_regular i _ (by simp [Term.isRT, Term.isLimT])
        (by simpa only [Term.fT] using him)
    · simp [Term.le]
  · apply layerCut_le_of_context_le i m him c a hc ha ha0 hcw haw
    by_cases hc0 : c = .zero
    · rw [hc0]; simp only [Term.le, (zero_lt_iff _).mpr ha0, Bool.or_true]
    · simpa only [ite_eq_right hc0, ite_eq_right ha0] using hca

theorem context_bound_diagonal_source_closed [LargeCardinals.{u}] (k m : Nat) (hmk : m ≤ k)
    (xs q : V multi.T) (i : Nat) (him : i ≤ m) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (hbound : multi.T.P (V.set xs i .Z) .Z ≤ T.fund (.P q .Z) .Z)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true := by
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hcw : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hlD := Dim_Omega_label hcD hdq
  have hlr := Omega_label_recursive _ hcr hdq
  have hlw := Omega_label_recursiveWF k _ hcw hdq
  obtain ⟨a, ha, haw, heA, hc, _⟩ := regular_lower_label_cut_context k m hmk q hlD hqf hqOne hlr hlw
  obtain ⟨c, hca, hcwC, hBase, heBase, heOld⟩ :=
    principal_Omega_slot_context k xs q i (by omega) hsD hf hdq hr hs
  have hA := (zero_fund_invariant k (.P q .Z) hlD hlr hlw).1
  have hBD : Dim (k + 3) (.P (V.set xs i .Z) .Z) := Dim_set hsD i (Dim_Z _) _ (Dim_Z _)
  have hAD : Dim (k + 3) (T.fund (.P q .Z) .Z) := Dim_fund _ _ hlD (Dim_Z _)
  have hle : Term.le (if c = .zero then Term.one else c) (if a = .zero then Term.one else a) = true := by
    rcases hbound with hl | he
    · have hlt := (convert_order k _ _ hBD hAD hBase hA).mp hl
      rw [heBase, heA] at hlt
      simp only [Term.le, hlt, Bool.or_true]
    · have heq : convert (k + 3) (code (.P (V.set xs i .Z) .Z)) =
          convert (k + 3) (code (T.fund (.P q .Z) .Z)) := by rw [code_congr he]
      rw [heBase, heA] at heq
      rw [heq]; simp [Term.le]
  obtain ⟨hCut, hPred⟩ := layerCut_comparable_of_erased_le i m him c a hca ha hcwC haw hle
  have hp := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
  exact ⟨layerCut m a, hc, H_bound_of_comparable_cuts _ _ _ hp.1 hp.2.1 hc.regular hc.cutWf
    hcw.wf hCut hPred hp.2.2.2⟩

theorem le_of_coordinate_predecessor (lam : Nat) (xs ys zs : V multi.T) (j : Nat) (b : multi.T)
    (hy : V.get0 ys j = kumakuma.SourceSuccessor.succ lam b) (hz : V.get0 zs j = b)
    (hsame : ∀ l, l ≠ j → V.get0 zs l = V.get0 ys l)
    (hprefix : ∀ l, l < j → V.get0 xs l = V.get0 ys l)
    (hlt : xs < ys) : xs ≤ zs := by
  obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot xs ys).1 hlt
  have hab (l : Nat) (hl : p < l) (hlj : l ≠ j) : compareT (V.get0 xs l) (V.get0 zs l) = .eq := by
    rw [hsame l hlj]; exact habove l hl
  show compareV xs zs = .lt ∨ compareV xs zs = .eq
  rcases Nat.lt_trichotomy p j with hpj | hpj | hpj
  · rw [hprefix p hpj] at hp
    exact absurd hp (T.lt_irrefl _)
  · subst hpj
    rw [hy] at hp
    rcases (kumakuma.SourceSuccessor.lt_succ_iff_le lam _ b).1 hp with hl | he
    · apply Or.inl
      apply V.lt_of_pivot p
      · intro l hl; exact hab l hl (by omega)
      · rw [hz]; exact hl
    · apply Or.inr
      apply (V.eqv_iff_get0 xs zs).2
      intro l
      rcases Nat.lt_trichotomy l p with hl | hl | hl
      · rw [hprefix l hl, hsame l (by omega)]; exact compareT_self _
      · subst hl; rw [hz]; exact he
      · exact hab l hl (by omega)
  · apply Or.inl
    apply V.lt_of_pivot p
    · intro l hl; exact hab l hl (by omega)
    · rw [hsame p (by omega)]; exact hp

theorem regular_fund_zero_shape (k m : Nat) (q : V multi.T)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (b : multi.T) (hb : V.get0 q (m + 1) = kumakuma.SourceSuccessor.succ (k + 3) b) :
    T.fund (.P q .Z) .Z = .P (V.set q (m + 1) b) .Z := by
  have hql : m + 1 < q.length := fnz_lt_length hqf
  have hqlow := (V.fnz_some_spec q _ hqf).2
  rw [fund_one_succ hqf hqOne, hb, kumakuma.SourceSuccessor.fund_succ]
  congr 1
  apply set_eq_self
  rw [V.get0_set q (m + 1) b m hql, ite_eq_right (by omega)]
  exact hqlow m (by omega)

theorem consecutive_diagonal_context_bound (k m : Nat)
    (xs q : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some m) (hdq : domF (V.get0 xs m) = .Omega q)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one) (hdiag : xs < q) :
    multi.T.P (V.set xs m .Z) .Z ≤ T.fund (.P q .Z) .Z := by
  have hql : m + 1 < q.length := fnz_lt_length hqf
  have hxl : m < xs.length := fnz_lt_length hf
  have hqlow := (V.fnz_some_spec q _ hqf).2
  have hxlow := (V.fnz_some_spec xs _ hf).2
  have hc0 : V.get0 xs m ≠ .Z := (V.fnz_some_spec xs _ hf).1
  have hqD := Dim_Omega_label (hsD.coord m) hdq
  obtain ⟨b, hb⟩ := dom_one_succ (V.get0 q (m + 1)) (hqD.coord _) hqOne
  rw [regular_fund_zero_shape k m q hqf hqOne b hb]
  have hlt : V.set xs m .Z < q := V.lt_trans (set_lt hxl (T.Z_lt_of_ne hc0)) hdiag
  have hvec : V.set xs m .Z ≤ V.set q (m + 1) b := by
    apply le_of_coordinate_predecessor (k + 3) _ q _ (m + 1) b hb (V.get0_set_same q _ b hql)
    · intro l hl; exact V.get0_set_ne q _ b l hl
    · intro l hl
      rw [hqlow l hl, V.get0_set xs m .Z l hxl]
      split
      · rfl
      · exact hxlow l (by omega)
    · exact hlt
  rcases hvec with hl | he
  · exact Or.inl (T.P_lt_P_of_vlt _ _ hl)
  · exact Or.inr ((T.P_eqv_iff _ _ _ _).2 ⟨he, compareT_ZZ⟩)

end kumakuma.GeneralImageContextBoundDiagonal

namespace kumakuma.GeneralImageHighestContextDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageLabelCut kumakuma.GeneralImageLabelClosure
open kumakuma.GeneralImageComparableCuts kumakuma.GeneralImageParametricCut
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRegularDiagonal
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance kumakuma.GeneralImageMiddleRecursion
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageHeadCuts
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageContextBoundDiagonal
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder

universe u

theorem pairCut_image_comparable [LargeCardinals.{u}] (k : Nat) (h b : multi.T)
    (hhD : Dim (k + 3) h) (hbD : Dim (k + 3) b)
    (hh : RecursiveWF (k + 3) h) (hb : RecursiveWF (k + 3) b) (hle : h ≤ b) :
    Term.le (pairCut (k + 1) (convert (k + 3) (code h)))
      (pairCut (k + 1) (convert (k + 3) (code b))) = true ∧
    Term.le (Term.predR (pairCut (k + 1) (convert (k + 3) (code h))))
      (Term.predR (pairCut (k + 1) (convert (k + 3) (code b)))) = true := by
  rcases hle with hlt | he
  · by_cases hh0 : h = .Z
    · subst hh0
      simp only [convert_Z, pairCut, ↓reduceIte, Term.predR]
      exact ⟨inacc_zero_le _ _, kumakuma.OT2.zero_le _⟩
    · have hb0 : b ≠ .Z := T.ne_Z_of_lt hlt
      have hhNZ : convert (k + 3) (code h) ≠ .zero := fun he => hh0 ((convert_eq_zero_iff _ _).1 he)
      have hbNZ : convert (k + 3) (code b) ≠ .zero := fun he => hb0 ((convert_eq_zero_iff _ _).1 he)
      have hImage := (convert_order k h b hhD hbD hh hb).mp hlt
      have hDrop : Term.lt (dropOne (convert (k + 3) (code h)))
          (dropOne (convert (k + 3) (code b))) = true := by
        rwa [dropOne_order hh.wf hb.wf hhNZ hbNZ]
      constructor
      · have hCut : Term.lt (pairCut (k + 1) (convert (k + 3) (code h)))
            (pairCut (k + 1) (convert (k + 3) (code b))) = true := by
          simp only [pairCut, hhNZ, hbNZ, ↓reduceIte, inacc_same_lt]
          rwa [succTerm_order (dropOne_wf hh.wf) (dropOne_wf hb.wf)]
        simp only [Term.le, hCut, Bool.or_true]
      · rw [pairCut_image_pred k h hh0 hh, pairCut_image_pred k b hb0 hb,
          convert_topNode k h hh0, convert_topNode k b hb0]
        simp only [Term.le, inacc_same_lt, hDrop, Bool.or_true]
  · rw [code_congr he]
    exact ⟨by simp [Term.le], by simp [Term.le]⟩

theorem highest_regular_label_shape (k : Nat) (q : V multi.T) (hqD : Dim (k + 3) (.P q .Z))
    (hqf : V.fnz q = some (k + 2)) (hqOne : domF (V.get0 q (k + 2)) = .one) :
    ∃ b, q = lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b) := by
  obtain ⟨b, hb⟩ := dom_one_succ (V.get0 q (k + 2)) (hqD.coord _) hqOne
  refine ⟨b, ?_⟩
  rw [← hb]
  exact lastVec_of_low hqD.length (V.fnz_some_spec q _ hqf).2

theorem highest_consecutive_parent_bound (k : Nat) (xs : V multi.T) (b : multi.T)
    {q : V multi.T} (heQ : q = lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b))
    (hdiag : xs < q) : V.get0 xs (k + 2) ≤ b := by
  subst heQ
  obtain ⟨p, _, hp⟩ := (V.lt_iff_pivot _ _).1 hdiag
  by_cases hpk : p = k + 2
  · subst hpk
    rw [get0_lastVec, ite_eq_left rfl] at hp
    exact (kumakuma.SourceSuccessor.lt_succ_iff_le (k + 3) _ b).1 hp
  · rw [get0_lastVec, ite_eq_right hpk] at hp
    exact absurd hp (T.not_lt_Z _)

theorem principal_middle_Omega_cut [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (k + 1)) (hdq : domF (V.get0 xs (k + 1)) = .Omega q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    convert (k + 3) (code (.P xs .Z)) =
        .psi (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
          (convert (k + 3) (code (V.get0 xs (k + 1)))) ∧
      Term.wf (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))) = true ∧
      Term.allLt (Term.H (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
        (convert (k + 3) (code (V.get0 xs (k + 1))))) (convert (k + 3) (code (V.get0 xs (k + 1)))) =
        true := by
  have hcr : Recursive (V.get0 xs (k + 1)) := (Recursive_P.1 hr).1 _
  have hcw : RecursiveWF (k + 3) (V.get0 xs (k + 1)) := (RecursiveWF_P.1 hs).1 _
  have hcD : Dim (k + 3) (V.get0 xs (k + 1)) := hsD.coord _
  have hc0' : V.get0 xs (k + 1) ≠ .Z := (V.fnz_some_spec xs _ hf).1
  have hc0 : convert (k + 3) (code (V.get0 xs (k + 1))) ≠ .zero :=
    fun he => hc0' ((convert_eq_zero_iff _ _).1 he)
  have heOld : convert (k + 3) (code (.P xs .Z)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
        (convert (k + 3) (code (V.get0 xs (k + 1)))) := by
    let args := arguments (k + 3) (trim (codes xs))
    rw [convert_principal, principal_as_layers]
    change lower (k + 1) args (topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)) = _
    have hnz : topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero) ≠ .zero := by
      rw [converted_coordinate xs (k + 1)]
      simp [topPair, hc0]
    rw [lower_keep (k + 1) args _ hnz (fun l hl => by
      rw [converted_coordinate xs l, (V.fnz_some_spec xs _ hf).2 l hl, convert_Z]),
      converted_coordinate xs (k + 2), converted_coordinate xs (k + 1)]
    simp only [topPair, hc0, ↓reduceIte, pairCut, Omega_image_drop k _ hcD hcr hcw hdq]
  have hp := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
  exact ⟨heOld, hp.2.1, hp.2.2.2⟩

theorem highest_consecutive_source_closed [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (k + 1)) (hdq : domF (V.get0 xs (k + 1)) = .Omega q)
    (hqf : V.fnz q = some (k + 2)) (hqOne : domF (V.get0 q (k + 2)) = .one) (hdiag : xs < q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs (k + 1)))))
        (convert (k + 3) (code (V.get0 xs (k + 1)))) = true := by
  have hcoords : ∀ l, RecursiveWF (k + 3) (V.get0 xs l) := (RecursiveWF_P.1 hs).1
  have hlD := Dim_Omega_label (hsD.coord (k + 1)) hdq
  have hlw := Omega_label_recursiveWF k _ (hcoords (k + 1)) hdq
  obtain ⟨b, heQ⟩ := highest_regular_label_shape k q hlD hqf hqOne
  have heLabel : multi.T.P q .Z = topNode k (kumakuma.SourceSuccessor.succ (k + 3) b) := by
    rw [heQ]; rfl
  have hsLabel : RecursiveWF (k + 3) (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) :=
    heLabel ▸ hlw
  have hb : RecursiveWF (k + 3) b := (recursive_succ_iff _ _ _).mp (kumakuma.GeneralImageHighOmega.high_recursive_image k _ hsLabel)
  have hbD : Dim (k + 3) b := by
    have h := hlD.coord (k + 2)
    rw [heQ, get0_lastVec, ite_eq_left rfl] at h
    exact kumakuma.GeneralImageRelativePredecessor.Dim_of_oplus h
  have hc : CutFund k (.P q .Z) (pairCut (k + 1) (convert (k + 3) (code b))) := by
    rw [heLabel]; exact highest_regular_cutFund_at k b hsLabel
  obtain ⟨hCut, hPred⟩ := pairCut_image_comparable k (V.get0 xs (k + 2)) b (hsD.coord _) hbD
    (hcoords (k + 2)) hb (highest_consecutive_parent_bound k xs b heQ hdiag)
  obtain ⟨_, hw, hH⟩ := principal_middle_Omega_cut k xs q hsD hf hdq hr hs
  exact ⟨_, hc, H_bound_of_comparable_cuts _ _ _ (pairCut_regular _ _) hw hc.regular hc.cutWf
    (hcoords (k + 1)).wf hCut hPred hH⟩

end kumakuma.GeneralImageHighestContextDiagonal

namespace kumakuma.GeneralImageStrictHighestDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageLabelCut kumakuma.GeneralImageLabelClosure
open kumakuma.GeneralImageComparableCuts kumakuma.GeneralImageParametricCut
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRegularDiagonal
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance kumakuma.GeneralImageMiddleRecursion
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageHeadCuts
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageContextBoundDiagonal
open kumakuma.GeneralImageHighestContextDiagonal
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder

universe u

theorem strict_highest_diagonal_branch (k : Nat) (xs q : V multi.T) (b : multi.T)
    (hsD : Dim (k + 3) (.P xs .Z))
    (heQ : q = lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b))
    (hhigh : V.get0 xs (k + 2) < b) : xs < q := by
  subst heQ
  apply V.lt_of_pivot (k + 2)
  · intro j hj
    rw [V.get0_ge xs j (by rw [hsD.length]; omega), get0_lastVec, ite_eq_right (by omega)]
    exact compareT_ZZ
  · rw [get0_lastVec, ite_eq_left rfl]
    exact (kumakuma.SourceSuccessor.lt_succ_iff_le (k + 3) _ b).2 (Or.inl hhigh)

theorem diagonal_selector_below_highest [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) : i ≤ k + 1 := by
  have hik : i < k + 3 := by have := fnz_lt_length hf; rwa [hsD.length] at this
  apply Classical.byContradiction; intro hi
  have heI : i = k + 2 := by omega
  subst heI
  exact no_diagonal_highest k xs hsD hs ((Recursive_P.1 hr).1 _) hf hdq hdiag

theorem strict_highest_parent_index [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hi : i ≤ k) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (b : multi.T) (hbD : Dim (k + 3) b) (hb : RecursiveWF (k + 3) b)
    (hhigh : V.get0 xs (k + 2) < b)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ w, convert (k + 3) (code (.P xs .Z)) = .psi w (convert (k + 3) (code (V.get0 xs i))) ∧
      Term.isRT w = true ∧ Term.wf w = true ∧
      Term.le w (pairCut (k + 1) (convert (k + 3) (code b))) = true ∧
      Term.le (Term.predR w) (Term.predR (pairCut (k + 1) (convert (k + 3) (code b)))) = true ∧
      Term.allLt (Term.H w (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true := by
  have hb0 : b ≠ .Z := T.ne_Z_of_lt hhigh
  have hbNZ : convert (k + 3) (code b) ≠ .zero := fun he => hb0 ((convert_eq_zero_iff _ _).1 he)
  obtain ⟨c, hca, hcw, hBase, heBase, heOld⟩ :=
    principal_Omega_slot_context k xs q i hi hsD hf hdq hr hs
  have hB := topNode_recursiveWF k b hb
  have hBD : Dim (k + 3) (.P (V.set xs i .Z) .Z) := Dim_set hsD i (Dim_Z _) _ (Dim_Z _)
  have hraw : multi.T.P (V.set xs i .Z) .Z < topNode k b := by
    show multi.T.P _ .Z < multi.T.P (lastVec (k + 2) b) .Z
    apply highest_principal_lt (m := k + 2)
    · exact Nat.le_of_eq (by rw [V.length_set, hsD.length])
    · exact Nat.le_of_eq (lastVec_length _ _)
    · rw [V.get0_set_ne xs i .Z (k + 2) (by omega), get0_lastVec, ite_eq_left rfl]
      exact hhigh
  have hBound := (convert_order k _ _ hBD (Dim_topNode hbD) hBase hB).mp hraw
  rw [heBase] at hBound
  have hPred : Term.predR (pairCut (k + 1) (convert (k + 3) (code b))) =
      convert (k + 3) (code (topNode k b)) := pairCut_image_pred k b hb0 hb
  have hBft : Term.fT (convert (k + 3) (code (topNode k b))) = k + 1 := by
    rw [convert_topNode k b hb0]; rfl
  have hBNZ : convert (k + 3) (code (topNode k b)) ≠ .zero := by
    rw [convert_topNode k b hb0]; intro he; cases he
  have hcBound : Term.lt c (convert (k + 3) (code (topNode k b))) = true := by
    by_cases hc0 : c = .zero
    · rw [hc0]; exact (zero_lt_iff _).mpr hBNZ
    · simpa only [ite_eq_right hc0] using hBound
  have hSucc := topNode_recursiveWF k (kumakuma.SourceSuccessor.succ (k + 3) b)
    ((recursive_succ_iff _ _ _).mpr hb)
  have hCutW : Term.wf (pairCut (k + 1) (convert (k + 3) (code b))) = true := by
    rw [← highest_regular_image k b]; exact hSucc.wf
  have hBlt : Term.lt (convert (k + 3) (code (topNode k b)))
      (pairCut (k + 1) (convert (k + 3) (code b))) = true := by
    rw [convert_topNode k b hb0]
    simp only [pairCut, hbNZ, ↓reduceIte, inacc_same_lt]
    rw [lt_succTerm_eq_le (dropOne_wf hb.wf) (dropOne_wf hb.wf)]
    simp [Term.le]
  have hp := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
  refine ⟨layerCut i c, heOld, hp.1, hp.2.1, ?_, ?_, hp.2.2.2⟩
  · by_cases hc0 : c = .zero
    · rw [hc0]
      exact kumakuma.GeneralImageEmptyCutDiagonal.empty_le_regular i _ (pairCut_regular _ _)
        (by simp only [pairCut, Term.fT]; omega)
    · have hwB : Term.lt (layerCut i c) (convert (k + 3) (code (topNode k b))) = true := by
        simp only [layerCut, hc0, ↓reduceIte]
        change Term.lt (regular i c) (convert (k + 3) (code (topNode k b))) = true
        rwa [regular_lt_context (above_principal (hca.resolve_left hc0)) (by rw [hBft]; omega)]
      have hwCut := lemma_6_1.{u}.2.1 _ _ _ hp.2.1 hB.wf hCutW hwB hBlt
      simp only [Term.le, hwCut, Bool.or_true]
  · rw [hPred]
    by_cases hc0 : c = .zero
    · simp only [layerCut, hc0, ↓reduceIte, Term.predR]
      exact kumakuma.OT2.zero_le _
    · have hPredW : Term.predR (layerCut i c) = c := by
        simp only [layerCut, hc0, ↓reduceIte, Term.predR, succTerm_ne_zero,
          predT_succTerm hcw, show ¬Term.fT c ≤ i from Nat.not_le.mpr (hca.resolve_left hc0)]
      rw [hPredW]
      simp only [Term.le, hcBound, Bool.or_true]

theorem strict_highest_diagonal_source_closed [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (b : multi.T)
    (heQ : q = lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b))
    (hhigh : V.get0 xs (k + 2) < b)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true := by
  have hdiag := strict_highest_diagonal_branch k xs q b hsD heQ hhigh
  have hi := diagonal_selector_below_highest k xs q i hsD hf hdq hdiag hr hs
  have hlD := Dim_Omega_label (hsD.coord i) hdq
  have hqf : V.fnz q = some (k + 2) := by
    rw [heQ]; exact fnz_lastVec (k + 2) (kumakuma.SourceSuccessor.succ_ne_zero _ b)
  have hqOne : domF (V.get0 q (k + 2)) = .one := by
    rw [heQ, get0_lastVec, ite_eq_left rfl]; exact kumakuma.SourceSuccessor.dom_succ _ _
  by_cases hil : i ≤ k
  · have hcw : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
    have hlw := Omega_label_recursiveWF k _ hcw hdq
    have heLabel : multi.T.P q .Z = topNode k (kumakuma.SourceSuccessor.succ (k + 3) b) := by
      rw [heQ]; rfl
    have hsLabel : RecursiveWF (k + 3) (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) :=
      heLabel ▸ hlw
    have hb : RecursiveWF (k + 3) b := (recursive_succ_iff _ _ _).mp (kumakuma.GeneralImageHighOmega.high_recursive_image k _ hsLabel)
    have hbD : Dim (k + 3) b := by
      have h := hlD.coord (k + 2)
      rw [heQ, get0_lastVec, ite_eq_left rfl] at h
      exact kumakuma.GeneralImageRelativePredecessor.Dim_of_oplus h
    have hc : CutFund k (.P q .Z) (pairCut (k + 1) (convert (k + 3) (code b))) := by
      rw [heLabel]; exact highest_regular_cutFund_at k b hsLabel
    obtain ⟨w, _, hwR, hw, hCut, hPred, hH⟩ :=
      strict_highest_parent_index k xs q i hil hsD hf hdq b hbD hb hhigh hr hs
    exact ⟨_, hc, H_bound_of_comparable_cuts w _ _ hwR hw hc.regular hc.cutWf hcw.wf hCut hPred hH⟩
  · have heI : i = k + 1 := by omega
    subst heI
    exact highest_consecutive_source_closed k xs q hsD hf hdq hqf hqOne hdiag hr hs

end kumakuma.GeneralImageStrictHighestDiagonal

namespace kumakuma.GeneralImageCutTransport

open OCF.Jaeger OCF.Ordinal
open OCF.Jaeger.Term
open kumakuma.GeneralImageWFInvariant kumakuma.GeneralImageCoefficients

universe u

theorem H_bound_iff_C [LargeCardinals.{u}] (v t a : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (ht : Term.wf t = true) (ha : Term.wf a = true) :
    Term.allLt (Term.H v t) a = true ↔ C (V.{u} v) (V a) (V t) := by
  have sv := sem_of_wf.{u} hv
  have hreg : IsRegBelowΛ₀ (V.{u} v) := ⟨sv.isR_iff.mp hvR, sv.lt_Λ₀⟩
  rw [lemma_5_6 hreg (sem_of_wf.{u} ht).T]
  constructor
  · intro h x hx
    obtain ⟨z, hz, rfl⟩ := (H_iff hvR hv ht x).mp hx
    exact (lt_iff_V (H_wf hvR hv ht hz) ha).mp ((Term.allLt_iff _ _).mp h z hz)
  · intro h
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    exact (lt_iff_V (H_wf hvR hv ht hz) ha).mpr
      (h _ ((H_iff hvR hv ht _).mpr ⟨z, hz, rfl⟩))

end kumakuma.GeneralImageCutTransport

namespace kumakuma.GeneralImageCriticalDiagonal

open multi kumakuma.OTQuotient kumakuma.GeneralImageHighestContextDiagonal

theorem highest_diagonal_parent_bound (k : Nat) (xs q : V multi.T) (b : multi.T)
    (heQ : q = lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b))
    (hdiag : xs < q) : V.get0 xs (k + 2) ≤ b :=
  highest_consecutive_parent_bound k xs b heQ hdiag

end kumakuma.GeneralImageCriticalDiagonal

namespace kumakuma.GeneralImageSharedLowerContext

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRegularLimit kumakuma.GeneralImageRegularDiagonal


theorem above_base_image_injective (m : Nat) (a b : Term)
    (ha : Above m a) (hb : Above m b)
    (he : (if a = .zero then Term.one else a) = (if b = .zero then Term.one else b)) : a = b := by
  by_cases ha0 : a = .zero
  · by_cases hb0 : b = .zero
    · exact ha0.trans hb0.symm
    · rw [ite_eq_left ha0, ite_eq_right hb0] at he
      have hf := hb.resolve_left hb0
      rw [← he] at hf; simp only [Term.one, Term.bigOmega, Term.fT] at hf; omega
  · by_cases hb0 : b = .zero
    · rw [ite_eq_right ha0, ite_eq_left hb0] at he
      have hf := ha.resolve_left ha0
      rw [he] at hf; simp only [Term.one, Term.bigOmega, Term.fT] at hf; omega
    · simpa only [ite_eq_right ha0, ite_eq_right hb0] using he

theorem principal_shared_lower_image (k m : Nat) (hm : m ≤ k)
    (base xs : V multi.T)
    (hzero : ∀ j, j < m + 1 → V.get0 base j = .Z)
    (hsame : ∀ j, m < j → V.get0 xs j = V.get0 base j)
    (a : Term) (ha : Above m a)
    (heBase : convert (k + 3) (code (.P base .Z)) = (if a = .zero then Term.one else a)) :
    convert (k + 3) (code (.P xs .Z)) =
      lower (m + 1) (arguments (k + 3) (trim (codes xs))) a := by
  let args := arguments (k + 3) (trim (codes base))
  let top := topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)
  obtain ⟨b, hb, hformula⟩ := lower_coordinate_context (k + 1) m (by omega) args top
    (topPair_context _ _ _)
  have heB : convert (k + 3) (code (.P base .Z)) = (if b = .zero then Term.one else b) := by
    rw [convert_principal, principal_as_layers]
    change lower (k + 1) args top = _
    rw [hformula args (fun _ _ _ => rfl)]
    exact lower_zero_block (m + 1) (by omega) args b (fun j hj => by
      rw [converted_coordinate base j, hzero j hj, convert_Z])
  have heAB := above_base_image_injective m a b ha (context_above hb) (heBase.symm.trans heB)
  let newArgs := arguments (k + 3) (trim (codes xs))
  have hArgs (j : Nat) (hj : m < j) (_ : j < k + 3) :
      newArgs[j]?.getD .zero = args[j]?.getD .zero := by
    rw [converted_coordinate xs j, converted_coordinate base j, hsame j hj]
  rw [convert_principal, principal_as_layers]
  change lower (k + 1) newArgs
    (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) = _
  rw [hArgs (k + 2) (by omega) (by omega), hArgs (k + 1) (by omega) (by omega)]
  rw [hformula newArgs (fun j hj hjl => hArgs j hj (by omega)), heAB]

end kumakuma.GeneralImageSharedLowerContext

namespace kumakuma.GeneralImageClosedDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageLabelCut kumakuma.GeneralImageLabelClosure
open kumakuma.GeneralImageComparableCuts kumakuma.GeneralImageParametricCut
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRegularDiagonal
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageHeadCuts
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLimitBranches
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder

universe u

theorem closed_diagonal_selector_bound [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hdiag : xs < q) (hr : Recursive (.P xs .Z))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) : i ≤ k + 1 :=
  kumakuma.GeneralImageStrictHighestDiagonal.diagonal_selector_below_highest k xs q i hsD hf hdq
    hdiag hr hs

theorem closed_diagonal_fund_eq (xs q : V multi.T) (i : Nat)
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q) (lam n : Nat) :
    T.fund (.P xs .Z) (ofNatD lam n) =
      .P (V.set xs i (multi.T.iter (T.fund (V.get0 xs i)) (ofNatD lam (n + 1)))) .Z :=
  fund_diag hf hdq hdiag _

theorem closed_diagonal_recursiveWF [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
      (convert (k + 3) (code (V.get0 xs i))) = true)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) :
    RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)) := by
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hcw : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hib := closed_diagonal_selector_bound k xs q i hsD hf hdq hdiag hr hs
  have hIter := Omega_iter_at_label_cut_relative k _ hcD hcr hcw hdq cut hc hSource (n + 1)
  rw [closed_diagonal_fund_eq xs q i hf hdq hdiag (k + 3) n]
  apply principal_replace_relative_recursiveWF k xs i hib hsD (V.fnz_some_spec xs i hf).2 hs _ hIter.1
  · exact (V.fnz_some_spec xs i hf).1
  · exact Omega_image_drop k _ hcD hcr hcw hdq
  · exact hIter.2

theorem closed_diagonal_relative [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
      (convert (k + 3) (code (V.get0 xs i))) = true)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))))
      (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))) = true := by
  cases n with
  | zero => exact (zero_fund_invariant k _ hsD hr hs).2.2 v hvR hv hH
  | succ n =>
    have hn := closed_diagonal_recursiveWF k xs q i hsD hf hdq hdiag cut hc hSource hr hs (n + 1)
    have hd : domF (.P xs .Z) = .omega := domF_diag hf hdq hdiag
    exact omega_relative_allcuts k _ hsD hr hs hd (n + 1) hn
      (fun v hvR hv hOmega hH => diagonal_parent_relative_above k xs i q hsD hf hdq hdiag hr hs
        (n + 1) (by omega) hn v hvR hv hOmega hH) v hvR hv hH

theorem closed_diagonal_dominated_support [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
      (convert (k + 3) (code (V.get0 xs i))) = true)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))) →
      DominatedCoefficient k v (.P xs .Z) z := by
  have hlow := (V.fnz_some_spec xs i hf).2
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hib := closed_diagonal_selector_bound k xs q i hsD hf hdq hdiag hr hs
  let a := multi.T.iter (T.fund (V.get0 xs i)) (ofNatD (k + 3) (n + 1))
  have hIt := Omega_iter_at_label_cut k _ hcD hcr (hcoords i) hdq cut hc hSource (n + 1)
  have haD : Dim (k + 3) a := hIt.1
  have ha : RecursiveWF (k + 3) a := hIt.2.1
  have ha0 : a ≠ .Z := domOmega_fund_ne_zero _ _ hdq
  have haLt : Term.lt (convert (k + 3) (code a)) (convert (k + 3) (code (V.get0 xs i))) = true :=
    (convert_order k _ _ haD hcD ha (hcoords i)).mp (fund_lt _ _ hc0)
  have hf' : T.fund (.P xs .Z) (ofNatD (k + 3) n) = .P (V.set xs i a) .Z :=
    closed_diagonal_fund_eq xs q i hf hdq hdiag (k + 3) n
  have hn := closed_diagonal_recursiveWF k xs q i hsD hf hdq hdiag cut hc hSource hr hs n
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)) := Dim_fund _ _ hsD (Dim_ofNatD _ _)
  have hcNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  have haNZ : convert (k + 3) (code a) ≠ .zero := fun he => ha0 ((convert_eq_zero_iff _ _).1 he)
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff (k + 3) (k + 2) (V.get0 xs i)).mpr
      ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (V.get0 xs i)) .Z)
      hsD (Dim_lowVec hcD (Dim_Z _)) hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    intro z hz
    rw [heSource, fund_low_Omega (k + 2) _ _ q hdq, H_low_empty_above_Omega v hOmega] at hz
    cases hz
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow a hcNZ haNZ
      (Omega_image_drop k _ hcD hcr (hcoords i) hdq) hIsLow
    have heFund := hf' ▸ heNew
    have hlt := (convert_order k _ _ hnD hsD hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
    rw [heOld, heFund] at hlt
    intro z hz; rw [heFund] at hz
    rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz
      with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
    · exact Or.inr (Or.inl (heOld ▸ ho))
    · have lift (ho : DominatedCoefficient k v (V.get0 xs i) z) :
          DominatedCoefficient k v (.P xs .Z) z := by
        rcases ho with he | ho | ⟨c, hcs, hmem, hbound⟩
        · exact Or.inl he
        · exact Or.inr (Or.inl (heOld ▸ hchild _ ho))
        · exact Or.inr (Or.inr ⟨c, Subterm.trans hcs (Subterm.coordinate xs .Z i),
            hmem.elim (fun h => Or.inl (heOld ▸ hchild _ h)) (fun h => Or.inr (heOld ▸ hchild _ h)),
            hbound⟩)
      have rootBound (hl : Term.lt z (convert (k + 3) (code (V.get0 xs i))) = true) :
          DominatedCoefficient k v (.P xs .Z) z :=
        Or.inr (Or.inr ⟨V.get0 xs i, Subterm.coordinate xs .Z i, Or.inl (heOld ▸ hroot),
          by simp [Term.le, hl]⟩)
      rcases he with he | he
      · apply rootBound; rw [he]; exact dropOne_lt_of_lt ha.wf (hcoords i).wf haLt
      · rcases Omega_iter_coefficient_support_at_label_cut k _ hcD hcr (hcoords i) hdq cut hc hSource
            v hvR hv hOmega (n + 1) he with ho | ho
        · exact lift ho
        · exact rootBound ho

end kumakuma.GeneralImageClosedDiagonal

namespace kumakuma.GeneralImageCriticalZeroDiagonal

open OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageWFInvariant kumakuma.GeneralImageRawOrder
open kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageLimitBranches
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageClosedDiagonal
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageRelativePredecessor
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceRecursiveDescending
open kumakuma.SourceFundGap

universe u

theorem psi_wf_of_dropOne (v a : Term) (ha : Term.wf a = true)
    (hw : Term.wf (.psi v (dropOne a)) = true) : Term.wf (.psi v a) = true := by
  by_cases hh : Term.head a = Term.one
  · obtain ⟨n, he⟩ := head_one_nat ha hh
    obtain ⟨hvR, hv, _, _⟩ := (Term.wf_psi_iff _ _).mp hw
    apply (Term.wf_psi_iff _ _).mpr
    refine ⟨hvR, hv, ha, ?_⟩
    rw [he]
    exact H_nat_bound v (n + 1)
  · rwa [dropOne_of_head_ne hh] at hw

end kumakuma.GeneralImageCriticalZeroDiagonal

namespace kumakuma.GeneralImageHigherSparseDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageWFInvariant kumakuma.GeneralImageRawOrder kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageRegularDiagonal kumakuma.GeneralImageContextBoundDiagonal
open kumakuma.GeneralImageHighestContextDiagonal kumakuma.GeneralImageSharedLowerContext
open kumakuma.GeneralImageCofinalityBounds
open kumakuma.GeneralImageLabelCut kumakuma.GeneralImageOmegaSpine
open kumakuma.GeneralImageCoefficients kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageLimitBranches
open kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageOmegaContext
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageComparableCuts kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageClosedDiagonal
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder

universe u

theorem terminal_successor_fund_zero (k m : Nat) (q : V multi.T)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (b : multi.T) (hb : V.get0 q (m + 1) = kumakuma.SourceSuccessor.succ (k + 3) b) :
    T.fund (.P q .Z) .Z = .P (V.set q (m + 1) b) .Z :=
  regular_fund_zero_shape k m q hqf hqOne b hb

theorem principal_higher_Omega_cut_image [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hi : i ≤ k + 1) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ w, convert (k + 3) (code (.P xs .Z)) = .psi w (convert (k + 3) (code (V.get0 xs i))) ∧
      Term.fT w = i := by
  by_cases hib : i ≤ k
  · obtain ⟨c, _, _, _, _, he⟩ := principal_Omega_slot_context k xs q i hib hsD hf hdq hr hs
    exact ⟨layerCut i c, he, by simp only [layerCut, Term.fT]⟩
  · have heI : i = k + 1 := by omega
    subst heI
    obtain ⟨he, _, _⟩ := principal_middle_Omega_cut k xs q hsD hf hdq hr hs
    exact ⟨_, he, by simp only [pairCut, Term.fT]⟩

theorem high_not_below_empty_psi (n : Nat) (p b : Term)
    (hp : Term.wf p = true) (hfn : n < Term.fT p) :
    Term.lt p (.psi (.inacc n .zero) b) = false := by
  cases p with
  | zero | add => simp [Term.fT] at hfn
  | inacc j a =>
    simp only [Term.fT] at hfn
    simp [Term.lt, Term.fT, show ¬j < n by omega, show ¬j = n by omega]
  | psi v a =>
    have hv := ((Term.wf_psi_iff _ _).mp hp).1
    cases v with
    | zero | add | psi => cases hv
    | inacc j c =>
      simp only [Term.fT] at hfn
      simp [Term.lt, Term.fT, hfn, show ¬j < n by omega, show ¬j = n by omega]

theorem H_self_of_cut_below_zero_context [LargeCardinals.{u}] (w v a t : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (ha : Term.wf a = true)
    (hp : Term.wf (.psi w t) = true) (hPred : Term.predR v = a)
    (hWA : Term.le w a = true) (hAV : Term.lt a v = true)
    (hPA : Term.lt (.psi w t) a = true) : Term.allLt (Term.H v t) t = true := by
  have hw := (Term.wf_psi_iff _ _).mp hp
  have hwv : Term.lt w v = true := by
    rcases (Term.le_iff_eq_or_lt _ _).mp hWA with he | he
    · rwa [he]
    · exact lemma_6_1.{u}.2.1 _ _ _ hw.2.1 ha hv he hAV
  have hpred : Term.le (Term.predR w) (Term.predR v) = true := by
    rw [hPred]
    have hlt := lemma_6_1.{u}.2.1 _ _ _ ((sem_of_wf.{u} hw.2.1).isR_pred hw.1).1
      hp ha (psi_above_predR w t hp) hPA
    simp only [Term.le, hlt, Bool.or_true]
  exact H_bound_of_comparable_cuts w v t hw.1 hw.2.1 hvR hv hw.2.2.1
    (by simp only [Term.le, hwv, Bool.or_true]) hpred hw.2.2.2

theorem high_le_step_context [LargeCardinals.{u}] (j : Nat) (a b p : Term)
    (ha : Above j a) (hw : Term.wf (step j a b) = true)
    (hp : Term.wf p = true) (hjp : j < Term.fT p)
    (hle : Term.le p (step j a b) = true) : Term.le p a = true := by
  have reject (n : Nat) (x : Term) (hn : n < Term.fT p)
      (h : Term.le p (.psi (.inacc n .zero) x) = true) : False := by
    rcases (Term.le_iff_eq_or_lt _ _).mp h with he | he
    · have hf := congrArg Term.fT he
      simp only [Term.fT] at hf; omega
    · rw [high_not_below_empty_psi n p x hp hn] at he; cases he
  by_cases ha0 : a = .zero
  · subst a
    by_cases hj0 : j = 0
    · subst j
      change Term.le p (.psi (.inacc 0 .zero) b) = true at hle
      exact False.elim (reject 0 b hjp hle)
    · by_cases hb0 : b = .zero
      · simp only [step, hj0, hb0, ↓reduceIte] at hle
        rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
        · rw [he, Term.fT] at hjp; omega
        · cases p <;> simp only [Term.lt] at he <;> cases he
      · simp only [step, hj0, hb0, ↓reduceIte] at hle
        exact False.elim (reject j (dropOne b) hjp hle)
  · by_cases hb0 : b = .zero
    · simpa only [step, ha0, hb0, ↓reduceIte] using hle
    · have hwa := step_context_wf ha hw
      simp only [step, ha0, hb0, ↓reduceIte] at hw hle
      rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
      · have hf := congrArg Term.fT he
        simp only [Term.fT, regular] at hf; omega
      · rwa [context_lt_psi_regular (dropOne b) hwa (above_principal (ha.resolve_left ha0)) hp hjp hw] at he

theorem step_context_le [LargeCardinals.{u}] (j : Nat) (a b : Term)
    (ha : Above j a) (hw : Term.wf (step j a b) = true) : Term.le a (step j a b) = true := by
  by_cases ha0 : a = .zero
  · rw [ha0]; exact kumakuma.OT2.zero_le _
  · by_cases hb0 : b = .zero
    · simp only [step, ha0, hb0, ↓reduceIte, Term.le, decide_true, Bool.true_or]
    · have hwa := step_context_wf ha hw
      simp only [step, ha0, hb0, ↓reduceIte] at hw ⊢
      have hlt : Term.lt a (.psi (regular j a) (dropOne b)) = true := by
        rw [context_lt_psi_regular _ hwa (above_principal (ha.resolve_left ha0)) hwa (ha.resolve_left ha0) hw]
        simp [Term.le]
      simp only [Term.le, hlt, Bool.or_true]

theorem lower_context_le [LargeCardinals.{u}] (j : Nat) (xs : List Term) (a : Term)
    (ha : Context j a) (hw : Term.wf (lower j xs a) = true) :
    Term.le a (lower j xs a) = true := by
  induction j generalizing a with
  | zero => simp only [lower, Term.le, decide_true, Bool.true_or]
  | succ j ih =>
    rw [lower_succ] at hw ⊢
    have ha' := context_above ha
    have hshape : Context j (step j a (xs[j]?.getD .zero)) := step_shape _ ha'
    have hstep := lower_context_wf j xs _ hshape hw
    exact target_le_trans (step_context_wf ha' hstep) hstep hw
      (step_context_le j a _ ha' hstep) (ih _ hshape hw)

end kumakuma.GeneralImageHigherSparseDiagonal

namespace kumakuma.GeneralImageHigherDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageWFInvariant kumakuma.GeneralImageRawOrder
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageHigherSparseDiagonal kumakuma.GeneralImageSharedLowerContext
open kumakuma.GeneralImageRegularDiagonal kumakuma.GeneralImageCofinalityBounds
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageCofinalityInheritance
open kumakuma.GeneralImageParametricCut kumakuma.GeneralImageLabelCut kumakuma.GeneralImageOmegaSpine
open kumakuma.GeneralImageCutTransport kumakuma.GeneralImageRelativePredecessor
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder
open kumakuma.GeneralImageOmegaCoefficients kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageUpperOmega
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageContextBoundDiagonal
open kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageClosedDiagonal kumakuma.GeneralImageDominatedCoefficients
open kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageHighestContextDiagonal

universe u

theorem Omega_label_relative_bound [LargeCardinals.{u}] (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (v B : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) (hB : Term.wf B = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) B = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (.P q .Z)))) B = true := by
  have hL := (Omega_label_recursiveWF k s hs hd).wf
  have hp := OmegaLabelPath.of_domain s hd
  clear hd
  induction hp with
  | regular _ => exact hH
  | inherit xs i hf hdq hnd hc ih =>
    have hil : i < xs.length := fnz_lt_length hf
    have hik : i < k + 3 := by rw [← hsD.length]; exact hil
    have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
    have hcw : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
    have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
    have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
    have hNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
      fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
    have hdParent : domF (.P xs .Z) = .Omega q := domF_nondiag hf hdq hnd
    by_cases hib : i ≤ k + 1
    · obtain ⟨w, heOld, _⟩ := principal_replacement_psi_images k xs i hib
        (V.fnz_some_spec xs i hf).2 (V.get0 xs i) hNZ hNZ
        (Omega_image_drop k _ hcD hcr hcw hdq) (Omega_principal_image_ne_low k xs i hsD hs hdParent)
      have hwP := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
      by_cases hskip : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = true
      · have hLpred := target_le_trans hL hs.wf ((sem_of_wf.{u} hv).isR_pred hvR).1
          (cofinality_image_le k _ hsD hr hs hdParent) hskip
        rw [H_eq_nil_of_le_pred v _ hvR hv hL hLpred]
        rfl
      have hskipF : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = false := by
        cases he : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) <;> simp_all
      rw [heOld] at hskipF hH
      by_cases hcut : Term.lt w v = true
      · have hWH : Term.allLt (Term.H v w) B = true := by
          simpa only [Term.H, hskipF, hcut, Bool.false_eq_true, ↓reduceIte] using hH
        apply (H_bound_iff_C v _ B hvR hv hL hB).mpr
        have sw := sem_of_wf.{u} hwP.2.1
        have hLw : Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
          cases w with
          | zero | add | psi => cases hwP.1
          | inacc n a =>
            exact le_psi_index_bound n a _ _ hL (heOld ▸ hs.wf)
              (heOld ▸ cofinality_image_le k _ hsD hr hs hdParent)
        exact C_lt_reg ⟨sw.isR_iff.mp hwP.1, sw.lt_Λ₀⟩
          ((lt_iff_V hL hwP.2.1).mp hLw) ((lt_iff_V hwP.2.1 hv).mp hcut)
          ((H_bound_iff_C v w B hvR hv hwP.2.1 hB).mp hWH)
      · have hcutF : Term.lt w v = false := by cases he : Term.lt w v <;> simp_all
        have hChild : Term.allLt (Term.H v (convert (k + 3) (code (V.get0 xs i)))) B = true := by
          apply (Term.allLt_iff _ _).mpr; intro z hz
          apply (Term.allLt_iff _ _).mp hH z
          rw [Term.H, hskipF, hcutF]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
        exact ih hcD hcr hcw hChild
    · have hi : i = k + 2 := by omega
      subst hi
      have heXs : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
        lastVec_of_low hsD.length (V.fnz_some_spec xs _ hf).2
      have heSource : multi.T.P xs .Z = topNode k (V.get0 xs (k + 2)) :=
        congrArg (fun us => multi.T.P us .Z) heXs
      rw [heSource, H_topNode_above_Omega k _ hc0 v hOmega, Omega_image_drop k _ hcD hcr hcw hdq] at hH
      exact ih hcD hcr hcw hH
  | tail xs b hb hc ih =>
    have hbr : Recursive b := (Recursive_P.1 hr).2.1
    have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
    apply ih hsD.tail hbr hbw
    apply (Term.allLt_iff _ _).mpr; intro z hz
    apply (Term.allLt_iff _ _).mp hH z
    rw [convert_P]
    exact H_assemble_right v _ _ hz

theorem regular_le_step_context [LargeCardinals.{u}] (j : Nat) (a b w : Term)
    (ha : Above j a) (hw : Term.wf (step j a b) = true)
    (hwr : Term.isRT w = true) (hww : Term.wf w = true) (hf : j ≤ Term.fT w)
    (hle : Term.le w (step j a b) = true) : Term.le w a = true := by
  by_cases hj : j < Term.fT w
  · exact high_le_step_context j a b w ha hw hww hj hle
  have hfEq : Term.fT w = j := by omega
  cases w with
  | zero | add | psi => cases hwr
  | inacc n u =>
    have hn : n = j := hfEq
    subst n
    have hu := (Term.wf_inacc_iff _ _).mp hww
    by_cases ha0 : a = .zero
    · subst a
      by_cases hj0 : j = 0
      · subst j
        change Term.le (.inacc 0 u) (.psi (.inacc 0 .zero) b) = true at hle
        simp only [Term.le, Term.lt, Term.fT, reduceCtorEq, decide_false,
          Nat.lt_irrefl, Nat.le_refl, decide_true, Bool.false_and, Bool.true_and,
          Bool.false_or, ↓reduceIte] at hle
        cases u <;> simp only [Term.lt] at hle <;> cases hle
      · by_cases hb0 : b = .zero
        · simpa only [step, hj0, hb0, ↓reduceIte] using hle
        · simp only [step, hj0, hb0, ↓reduceIte, Term.le, Term.lt, Term.fT,
            reduceCtorEq, decide_false, Nat.lt_irrefl, Nat.le_refl, decide_true,
            Bool.false_and, Bool.true_and, Bool.false_or] at hle
          cases u <;> simp only [Term.lt] at hle <;> cases hle
    · by_cases hb0 : b = .zero
      · simpa only [step, ha0, hb0, ↓reduceIte] using hle
      · have haw := step_context_wf ha hw
        have hfa := ha.resolve_left ha0
        simp only [step, ha0, hb0, ↓reduceIte, Term.le, Term.lt, Term.fT, regular,
          reduceCtorEq, decide_false, Nat.lt_irrefl, Nat.le_refl, decide_true,
          Bool.false_and, Bool.true_and, Bool.false_or] at hle
        have hua : Term.lt u a = true := by
          rw [lt_succTerm_eq_le hu.1 haw] at hle
          rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
          · have hft := congrArg Term.fT he
            omega
          · exact he
        have hwa : Term.lt (.inacc j u) a = true := by
          cases a with
          | zero | add => simp only [Term.fT] at hfa; omega
          | inacc n c => simpa only [Term.lt, show j < n by simpa only [Term.fT] using hfa, ↓reduceIte] using hua
          | psi v c =>
            simpa only [Term.lt, show j < Term.fT v by simpa only [Term.fT] using hfa,
              show ¬Term.fT v ≤ j by simp only [Term.fT] at hfa; omega,
              decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false] using hua
        simp only [Term.le, hwa, Bool.or_true]

theorem regular_le_lower_context [LargeCardinals.{u}] (j : Nat) (xs : List Term) (a w : Term)
    (ha : Context j a) (hw : Term.wf (lower j xs a) = true)
    (hwr : Term.isRT w = true) (hww : Term.wf w = true) (hj : j ≤ Term.fT w + 1)
    (hle : Term.le w (lower j xs a) = true) : Term.le w a = true := by
  induction j generalizing a with
  | zero => exact hle
  | succ j ih =>
    rw [lower_succ] at hw hle
    have ha' := context_above ha
    have hshape := step_shape (xs[j]?.getD .zero) ha'
    have hstep := lower_context_wf j xs _ hshape hw
    exact regular_le_step_context j a _ w ha' hstep hwr hww (by omega)
      (ih _ hshape hw (by omega) hle)

theorem regular_le_topPair_base [LargeCardinals.{u}] (n : Nat) (h c w : Term)
    (hh : Term.wf h = true) (hc : c ≠ .zero)
    (hwr : Term.isRT w = true) (hww : Term.wf w = true) (hf : Term.fT w = n)
    (hle : Term.le w (topPair n h c) = true) :
    h ≠ .zero ∧ Term.le w (.inacc n (dropOne h)) = true := by
  cases w with
  | zero | add | psi => cases hwr
  | inacc j u =>
    have hj : j = n := hf
    subst j
    have hu := (Term.wf_inacc_iff _ _).mp hww
    by_cases hh0 : h = .zero
    · simp only [topPair, hc, hh0, ↓reduceIte, Term.le, Term.lt, Term.fT,
        reduceCtorEq, decide_false, Nat.lt_irrefl, Nat.le_refl, decide_true,
        Bool.false_and, Bool.true_and, Bool.false_or] at hle
      cases u <;> simp only [Term.lt] at hle <;> cases hle
    · refine ⟨hh0, ?_⟩
      simp only [topPair, hc, hh0, ↓reduceIte, Term.le, Term.lt, Term.fT,
        reduceCtorEq, decide_false, Nat.lt_irrefl, Nat.le_refl, decide_true,
        Bool.false_and, Bool.true_and, Bool.false_or] at hle
      rw [lt_succTerm_eq_le hu.1 (dropOne_wf hh)] at hle
      simpa only [Term.le, Term.lt, Term.inacc.injEq, true_and, Nat.lt_irrefl, ↓reduceIte] using hle


theorem middle_cut_le_zero_of_le_label [LargeCardinals.{u}] (k : Nat)
    (q : V multi.T) (hqD : Dim (k + 3) (.P q .Z))
    (hqf : V.fnz q = some (k + 1)) (hqOne : domF (V.get0 q (k + 1)) = .one)
    (hr : Recursive (.P q .Z)) (hs : RecursiveWF (k + 3) (.P q .Z))
    (w : Term) (hwr : Term.isRT w = true) (hw : Term.wf w = true) (hf : Term.fT w = k + 1)
    (hle : Term.le w (convert (k + 3) (code (.P q .Z))) = true) :
    Term.le w (convert (k + 3) (code (T.fund (.P q .Z) .Z))) = true := by
  have hql : k + 1 < q.length := fnz_lt_length hqf
  have hqlow := (V.fnz_some_spec q _ hqf).2
  obtain ⟨b, hb⟩ := dom_one_succ (V.get0 q (k + 1)) (hqD.coord _) hqOne
  let A := V.set q (k + 1) b
  let h := convert (k + 3) (code (V.get0 q (k + 2)))
  have hhR : RecursiveWF (k + 3) (V.get0 q (k + 2)) := (RecursiveWF_P.1 hs).1 _
  have hhw : Term.wf h = true := hhR.wf
  have hbw : Term.wf (convert (k + 3) (code b)) = true := by
    have hp := (RecursiveWF_P.1 hs).1 (k + 1)
    rw [hb] at hp
    exact ((recursive_succ_iff _ _ _).mp hp).wf
  have hePrincipal (xs : V multi.T) (hz : ∀ j, j < k + 1 → V.get0 xs j = .Z) :
      convert (k + 3) (code (.P xs .Z)) =
        if topPair (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))
            (convert (k + 3) (code (V.get0 xs (k + 1)))) = .zero then Term.one else
          topPair (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))
            (convert (k + 3) (code (V.get0 xs (k + 1)))) := by
    rw [convert_principal, principal_as_layers]
    rw [lower_zero_block (k + 1) (by omega)]
    · rw [converted_coordinate xs (k + 2), converted_coordinate xs (k + 1)]
    · intro j hj
      rw [converted_coordinate xs j, hz j hj, convert_Z]
  have hqNZ : convert (k + 3) (code (V.get0 q (k + 1))) ≠ .zero := by
    rw [hb, convert_succ]; exact succTerm_ne_zero _
  have heQ := hePrincipal q hqlow
  have hTopNZ : topPair (k + 1) h (convert (k + 3) (code (V.get0 q (k + 1)))) ≠ .zero := by
    simp only [topPair, hqNZ, ↓reduceIte]; intro he; cases he
  change _ = if topPair (k + 1) h _ = .zero then _ else _ at heQ
  rw [ite_eq_right hTopNZ] at heQ
  obtain ⟨hh0, hWB⟩ := regular_le_topPair_base (k + 1) h _ w hhw hqNZ hwr hw hf (heQ ▸ hle)
  have hzeroA (j : Nat) (hj : j < k + 1) : V.get0 A j = .Z := by
    show V.get0 (V.set q (k + 1) b) j = .Z
    rw [V.get0_set_ne q _ b j (by omega)]; exact hqlow j hj
  have heA := hePrincipal A hzeroA
  have hA2 : V.get0 A (k + 2) = V.get0 q (k + 2) := V.get0_set_ne q _ b _ (by omega)
  have hA1 : V.get0 A (k + 1) = b := V.get0_set_same q _ b hql
  rw [hA2, hA1] at heA
  have heFund : T.fund (.P q .Z) .Z = .P A .Z := terminal_successor_fund_zero k k q hqf hqOne b hb
  have hNewNZ : topPair (k + 1) h (convert (k + 3) (code b)) ≠ .zero := by
    by_cases hb0 : convert (k + 3) (code b) = .zero <;>
      simp only [topPair, hh0, hb0, ↓reduceIte] <;> intro he <;> cases he
  change _ = if topPair (k + 1) h _ = .zero then _ else _ at heA
  rw [ite_eq_right hNewNZ] at heA
  rw [heFund, heA]
  have hBaseW : Term.wf (.inacc (k + 1) (dropOne h)) = true :=
    kumakuma.GeneralImageRegularLimit.inacc_image_drop_wf k _ hhR
  have hNewW := (zero_fund_invariant k (.P q .Z) hqD hr hs).1.wf
  rw [heFund, heA] at hNewW
  apply target_le_trans hw hBaseW hNewW hWB
  change Term.le (.inacc (k + 1) (dropOne h)) (topPair (k + 1) h (convert (k + 3) (code b))) = true
  by_cases hb0 : convert (k + 3) (code b) = .zero
  · simp only [topPair, hh0, hb0, ↓reduceIte, Term.le, decide_true, Bool.true_or]
  · have hlt := topPair_order (k + 1) hhw Term.wf_zero hhw hbw
    have hZero : Term.lt .zero (convert (k + 3) (code b)) = true := (zero_lt_iff _).mpr hb0
    simp only [lt_self, decide_true, Bool.true_and, Bool.false_or, hZero] at hlt
    have hBaseLt : Term.lt (.inacc (k + 1) (dropOne h))
        (topPair (k + 1) h (convert (k + 3) (code b))) = true := by
      simpa only [topPair, hh0, ↓reduceIte] using hlt
    simp only [Term.le, hBaseLt, Bool.or_true]

theorem higher_cut_le_zero_of_le_label [LargeCardinals.{u}] (k m : Nat) (hmk : m + 1 ≤ k)
    (q : V multi.T) (hqD : Dim (k + 3) (.P q .Z))
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (hr : Recursive (.P q .Z)) (hs : RecursiveWF (k + 3) (.P q .Z))
    (w : Term) (hwr : Term.isRT w = true) (hw : Term.wf w = true) (hf : m + 1 ≤ Term.fT w)
    (hle : Term.le w (convert (k + 3) (code (.P q .Z))) = true) :
    Term.le w (convert (k + 3) (code (T.fund (.P q .Z) .Z))) = true := by
  have hql : m + 1 < q.length := fnz_lt_length hqf
  have hqlow := (V.fnz_some_spec q _ hqf).2
  obtain ⟨b, hb⟩ := dom_one_succ (V.get0 q (m + 1)) (hqD.coord _) hqOne
  let base := V.set q (m + 1) .Z
  let A := V.set q (m + 1) b
  have hz (j : Nat) (hj : j < m + 2) : V.get0 base j = .Z := by
    show V.get0 (V.set q (m + 1) .Z) j = .Z
    rw [V.get0_set q (m + 1) .Z j hql]
    split
    · rfl
    · exact hqlow j (by omega)
  have hsameQ (j : Nat) (hj : m + 1 < j) : V.get0 q j = V.get0 base j := by
    show _ = V.get0 (V.set q (m + 1) .Z) j
    rw [V.get0_set_ne q _ .Z j (by omega)]
  have hsameA (j : Nat) (hj : m + 1 < j) : V.get0 A j = V.get0 base j := by
    show V.get0 (V.set q (m + 1) b) j = V.get0 (V.set q (m + 1) .Z) j
    rw [V.get0_set_ne q _ b j (by omega), V.get0_set_ne q _ .Z j (by omega)]
  have hbaseD : Dim (k + 3) (.P base .Z) := Dim_set hqD (m + 1) (Dim_Z _) _ (Dim_Z _)
  obtain ⟨c, hc, heBase, _⟩ := principal_insertion_context k (m + 1) hmk base hbaseD hz
  have hctx : Context (m + 2) c := by
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr ⟨above_principal hc, by omega⟩
  have heQ := principal_shared_lower_image k (m + 1) hmk base q hz hsameQ c hc heBase
  have heA := principal_shared_lower_image k (m + 1) hmk base A hz hsameA c hc heBase
  have heFund : T.fund (.P q .Z) .Z = .P A .Z := terminal_successor_fund_zero k m q hqf hqOne b hb
  have hAw := (zero_fund_invariant k (.P q .Z) hqD hr hs).1.wf
  rw [heFund] at hAw
  have hcw := lower_context_wf (m + 2) _ c hctx (heA ▸ hAw)
  have hWC := regular_le_lower_context (m + 2) _ c w hctx (heQ ▸ hs.wf) hwr hw (by omega) (heQ ▸ hle)
  rw [heFund, heA]
  exact target_le_trans hw hcw (heA ▸ hAw) hWC (lower_context_le _ _ c hctx (heA ▸ hAw))

theorem higher_source_closed [LargeCardinals.{u}] (k m : Nat)
    (xs q : V multi.T) (i : Nat) (hmi : m < i) (hi : i ≤ k + 1) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (hbound : multi.T.P xs .Z < T.fund (.P q .Z) .Z)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true := by
  classical
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hcw : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hlD := Dim_Omega_label hcD hdq
  have hlr := Omega_label_recursive _ hcr hdq
  have hlw := Omega_label_recursiveWF k _ hcw hdq
  have hA := (zero_fund_invariant k (.P q .Z) hlD hlr hlw).1
  have hAD : Dim (k + 3) (T.fund (.P q .Z) .Z) := Dim_fund _ _ hlD (Dim_Z _)
  obtain ⟨w, heOld, hf'⟩ := principal_higher_Omega_cut_image k xs q i hi hsD hf hdq hr hs
  have hPsi := heOld ▸ hs.wf
  have hp := (Term.wf_psi_iff _ _).mp hPsi
  have hOmega : Term.lt Term.bigOmega w = true := by
    rcases lemma_6_1.{u}.2.2 Term.bigOmega w Term.wf_bigOmega hp.2.1 with he | he | he
    · exact he
    · have hft := congrArg Term.fT he
      simp only [Term.bigOmega, Term.fT, hf'] at hft; omega
    · rw [kumakuma.CountableTarget.regular_not_below_omega hp.1] at he; cases he
  have hLH := Omega_label_relative_bound k _ hcD hcr hcw hdq w _ hp.1 hp.2.1 hOmega hcw.wf hp.2.2.2
  obtain ⟨a, ha, haw, heA, hc, hePred⟩ :=
    regular_lower_label_cut_context k m (by omega) q hlD hqf hqOne hlr hlw
  have hParentLt := (convert_order k _ _ hsD hAD hs hA).mp hbound
  have ha0 : a ≠ .zero := by
    intro he
    rw [heOld, heA, he, ite_eq_left rfl, principal_not_lt_one (by rfl) hPsi] at hParentLt
    cases hParentLt
  rw [ite_eq_right ha0] at heA
  have hPA : Term.lt (.psi w (convert (k + 3) (code (V.get0 xs i)))) a = true := by
    rwa [heOld, heA] at hParentLt
  have hWA : Term.le w a = true := by
    apply Classical.byContradiction; intro hnot
    have hnotLabel : ¬Term.le w (convert (k + 3) (code (.P q .Z))) = true := by
      intro hle
      apply hnot
      rw [← heA]
      by_cases hml : m + 1 ≤ k
      · exact higher_cut_le_zero_of_le_label k m hml q hlD hqf hqOne hlr hlw w hp.1 hp.2.1
          (by rw [hf']; omega) hle
      · have hmEq : m = k := by omega
        subst m
        exact middle_cut_le_zero_of_le_label k q hlD hqf hqOne hlr hlw w hp.1 hp.2.1
          (by rw [hf']; omega) hle
    have hLW : Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
      rcases lemma_6_1.{u}.2.2 _ _ hlw.wf hp.2.1 with he | he | he
      · exact he
      · exact False.elim (hnotLabel (by rw [← he]; simp [Term.le]))
      · exact False.elim (hnotLabel (by simp only [Term.le, he, Bool.or_true]))
    have sw := sem_of_wf.{u} hp.2.1
    have hLP : Term.lt (convert (k + 3) (code (.P q .Z)))
        (.psi w (convert (k + 3) (code (V.get0 xs i)))) = true := by
      apply (lt_iff_V hlw.wf hPsi).mpr
      exact (theorem_4_9 ⟨sw.isR_iff.mp hp.1, sw.lt_Λ₀⟩ _ _).mp
        ⟨(H_bound_iff_C w _ _ hp.1 hp.2.1 hlw.wf hcw.wf).mp hLH,
          (lt_iff_V hlw.wf hp.2.1).mp hLW⟩
    have hPL : Term.lt (.psi w (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (.P q .Z))) = true := by
      rw [← heOld]
      exact (convert_order k _ _ hsD hlD hs hlw).mp
        (T.lt_trans hbound (fund_lt _ .Z (by intro he; cases he)))
    have hbad := lemma_6_1.{u}.2.1 _ _ _ hlw.wf hPsi hlw.wf hLP hPL
    rw [lt_self] at hbad; cases hbad
  have hAV : Term.lt a (layerCut m a) = true := by
    simp only [layerCut, ha0, ↓reduceIte]
    change Term.lt a (regular m a) = true
    rw [context_lt_regular (ha.resolve_left ha0) (above_principal (ha.resolve_left ha0))]
    simp [Term.le]
  exact ⟨_, hc, H_self_of_cut_below_zero_context w _ a _ hc.regular hc.cutWf haw hPsi hePred hWA hAV hPA⟩

end kumakuma.GeneralImageHigherDiagonal

namespace kumakuma.GeneralImageDiagonalPartition

open multi kumakuma.OTQuotient kumakuma.CountableSource
open kumakuma.SourceFundOrder kumakuma.SourceFundGap kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageContextBoundDiagonal kumakuma.GeneralImageStrictHighestDiagonal
open kumakuma.GeneralImageCriticalDiagonal
open kumakuma.GeneralImageHighestDiagonal
open kumakuma.GeneralImageCoefficients
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageLimitBranches
open kumakuma.GeneralImageOmegaSpine
open kumakuma.GeneralImageHighestContextDiagonal
open OCF.Jaeger

universe u

theorem vector_interval_above (xs lo ys : V multi.T) (i : Nat)
    (hz : ∀ j, j < i → V.get0 xs j = .Z)
    (hh : ∀ j, i < j → V.get0 lo j = V.get0 xs j)
    (hlo : lo ≤ ys) (hhi : ys < xs) :
    ∀ j, i < j → compareT (V.get0 ys j) (V.get0 xs j) = .eq := by
  obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot ys xs).1 hhi
  have hpi : i ≤ p := pivot_above_zero hz hp
  have hp_eq : p = i := by
    apply Nat.le_antisymm _ hpi
    apply Nat.le_of_not_lt
    intro hip
    apply vlt_irrefl_of_le_lt hlo
    apply V.lt_of_pivot p
    · intro j hj
      rw [hh j (by omega)]
      exact habove j hj
    · rw [hh p hip]; exact hp
  subst hp_eq
  exact habove

theorem diagonal_zero_label_or_critical (k m : Nat)
    (xs q : V multi.T) (hsD : Dim (k + 3) (.P xs .Z)) (hqD : Dim (k + 3) (.P q .Z))
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (b : multi.T) (hb : V.get0 q (m + 1) = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hdiag : xs < q) :
    multi.T.P xs .Z < T.fund (.P q .Z) .Z ∨
      (V.get0 xs (m + 1) = b ∧ ∀ j, m + 1 < j → V.get0 xs j = V.get0 q j) := by
  have hql : m + 1 < q.length := fnz_lt_length hqf
  have hqlow := (V.fnz_some_spec q _ hqf).2
  rw [regular_fund_zero_shape k m q hqf hqOne b hb]
  have hbD : Dim (k + 3) b := by
    have h := hqD.coord (m + 1)
    rw [hb] at h
    exact kumakuma.GeneralImageRelativePredecessor.Dim_of_oplus h
  have finish (hlo : V.set q (m + 1) b ≤ xs) :
      V.get0 xs (m + 1) = b ∧ ∀ j, m + 1 < j → V.get0 xs j = V.get0 q j := by
    have hh : ∀ j, m + 1 < j → V.get0 (V.set q (m + 1) b) j = V.get0 q j :=
      fun j hj => V.get0_set_ne q _ b j (by omega)
    have hcoord := vector_interval q (V.set q (m + 1) b) xs (m + 1) hqlow hh hlo hdiag
    have hloB : b ≤ V.get0 xs (m + 1) := by
      have := hcoord.1; rwa [V.get0_set_same q _ b hql] at this
    have hhiB : V.get0 xs (m + 1) ≤ b := by
      apply (kumakuma.SourceSuccessor.lt_succ_iff_le (k + 3) _ b).mp
      rw [← hb]; exact hcoord.2.1
    refine ⟨eq_of_norm_eq (hsD.coord _) hbD
      ((compareT_eq_iff _ _).1 (source_le_antisymm hhiB hloB)), ?_⟩
    intro j hj
    exact eq_of_norm_eq (hsD.coord _) (hqD.coord _)
      ((compareT_eq_iff _ _).1 (vector_interval_above q _ xs (m + 1) hqlow hh hlo hdiag j hj))
  rcases V.lt_trichotomy xs (V.set q (m + 1) b) with hl | he | hl
  · exact Or.inl (T.P_lt_P_of_vlt _ _ hl)
  · exact Or.inr (finish (Or.inr (V.eqv_symm ((compareV_eq_iff _ _).2 he))))
  · exact Or.inr (finish (Or.inl hl))

theorem noncritical_diagonal_context_bound (k m : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z)) (hqD : Dim (k + 3) (.P q .Z))
    (hf : V.fnz xs = some i)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (b : multi.T) (hb : V.get0 q (m + 1) = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hdiag : xs < q)
    (hn : ¬(V.get0 xs (m + 1) = b ∧ ∀ j, m + 1 < j → V.get0 xs j = V.get0 q j)) :
    multi.T.P (V.set xs i .Z) .Z ≤ T.fund (.P q .Z) .Z := by
  have hp : multi.T.P xs .Z < T.fund (.P q .Z) .Z := by
    rcases diagonal_zero_label_or_critical k m xs q hsD hqD hqf hqOne b hb hdiag with hp | hp
    · exact hp
    · exact False.elim (hn hp)
  have hil := fnz_lt_length hf
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have herase : multi.T.P (V.set xs i .Z) .Z < .P xs .Z :=
    T.P_lt_P_of_vlt _ _ (set_lt hil (T.Z_lt_of_ne hc0))
  exact Or.inl (T.lt_trans herase hp)

end kumakuma.GeneralImageDiagonalPartition

namespace kumakuma.GeneralImageCountableObstructions

open multi kumakuma.OTQuotient kumakuma.CountableSource
open kumakuma.SourceFundOrder kumakuma.SourceFundGap kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageCoefficients kumakuma.GeneralImageRawOrder
open kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageDiagonalPartition
open kumakuma.GeneralImageLabelClosure kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageCriticalZeroDiagonal
open kumakuma.GeneralImageStrictHighestDiagonal
open kumakuma.GeneralImageHigherSparseDiagonal
open kumakuma.GeneralImageHigherDiagonal
open kumakuma.GeneralImageOmegaCoefficients kumakuma.GeneralImageContextBoundDiagonal
open kumakuma.GeneralImageCofinalityBounds
open OCF.Jaeger

universe u

theorem higher_selector_not_critical (k m : Nat)
    (xs q : V multi.T) (i : Nat) (hmi : m < i)
    (hdq : domF (V.get0 xs i) = .Omega q)
    (b : multi.T) (hb : V.get0 q (m + 1) = kumakuma.SourceSuccessor.succ (k + 3) b) :
    ¬(V.get0 xs (m + 1) = b ∧ ∀ j, m + 1 < j → V.get0 xs j = V.get0 q j) := by
  rintro ⟨hp, hh⟩
  have hmass := Omega_label_mass_le (V.get0 xs i) hdq
  by_cases hi : i = m + 1
  · subst hi
    rw [hp] at hmass
    have hidx := mass_idx_lt q .Z (m + 1)
    rw [hb, mass_succ] at hidx
    omega
  · have he := hh i (by omega)
    rw [he] at hmass
    have hidx := mass_idx_lt q .Z i
    omega

theorem higher_selector_zero_label_bound (k m : Nat)
    (xs q : V multi.T) (i : Nat) (hmi : m < i) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (hd : domF (.P xs .Z) = .omega) :
    multi.T.P xs .Z < T.fund (.P q .Z) .Z ∧
      multi.T.P (V.set xs i .Z) .Z ≤ T.fund (.P q .Z) .Z := by
  have hdiag : xs < q := by
    by_cases hl : xs < q
    · exact hl
    · rw [domF_nondiag hf hdq hl] at hd; cases hd
  have hqD := Dim_Omega_label (hsD.coord i) hdq
  obtain ⟨b, hb⟩ := dom_one_succ (V.get0 q (m + 1)) (hqD.coord _) hqOne
  have hn := higher_selector_not_critical k m xs q i hmi hdq b hb
  constructor
  · rcases diagonal_zero_label_or_critical k m xs q hsD hqD hqf hqOne b hb hdiag with hl | hc
    · exact hl
    · exact False.elim (hn hc)
  · exact noncritical_diagonal_context_bound k m xs q i hsD hqD hf hqf hqOne b hb hdiag hn

end kumakuma.GeneralImageCountableObstructions

import Subsp.Support.LabelCut

/-! Closed countable diagonals: context bounds, highest/higher diagonals and the diagonal partition. -/

namespace Support.GeneralImageComparableCuts

open OCF.Jaeger Support.TargetArithmetic Support.GeneralImageRelativePredecessor
open Support.GeneralImageCoefficients
open Support.GeneralImageWFInvariant

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

end Support.GeneralImageComparableCuts

namespace Support.GeneralImageContextBoundDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageLabelClosure
open Support.GeneralImageComparableCuts Support.GeneralImageParametricCut
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularDiagonal
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance
open Support.GeneralImageRelativePredecessor Support.GeneralImageMiddleSums
open Support.GeneralImageZeroFund Support.GeneralImageHeadCuts
open Support.GeneralImageCountableLayers Support.GeneralImageCountableInheritance
open Support.GeneralImageHighestDiagonal Support.GeneralImageCountableRecursion
open Support.GeneralImageDominatedCoefficients Support.GeneralImageOmegaCoefficients
open Support.GeneralImageLimitSupport
open Support.GeneralImageLimitBranches
open Support.SourceRecursiveDescending Support.SourceFundOrder

universe u

theorem regular_lower_label_cut_context [LargeCardinals.{u}] (k m : Nat) (hmk : m ≤ k)
    (q : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (hr : Recursive (.P q .Z)) (hs : RecursiveWF (k + 3) (.P q .Z)) :
    ∃ a, Above m a ∧ Term.wf a = true ∧
      convert (k + 3) (code (new.T.fund (.P q .Z) .Z)) = (if a = .zero then Term.one else a) ∧
      CutFund k (.P q .Z) (layerCut m a) ∧ Term.predR (layerCut m a) = a := by
  let sel : Fin (k + 3) := ⟨m + 1, by omega⟩
  obtain ⟨b, hb⟩ := dom_one_succ (q.idx sel) ((Support.DimensionCut.minIdx_spec q hm).1.symm)
  let base := q.rplc sel b
  have hzero : ∀ j, j.val < m + 1 → base.idx j = .Z := by
    intro j hj
    simp only [base, vec_rplc_idx, sel, ite_eq_right (by change j.val ≠ m + 1; omega)]
    exact (Support.DimensionCut.minIdx_spec q hm).2.2 j hj
  have hf0 : new.T.fund (.P q .Z) .Z = .P base .Z := by
    rw [fund_regular_bound q (by omega) hm, hb, Support.SourceSuccessor.fund_succ]
    congr 1; apply vec_ext; intro j
    simp only [vec_rplc_idx]
    split
    · exact (hzero j (by omega)).symm
    · simp only [base, sel, vec_rplc_idx]
  obtain ⟨a, ha, heBase, heInsert⟩ := principal_insertion_context k m hmk base hzero
  have hBase : RecursiveWF (k + 3) (.P base .Z) := hf0 ▸ (zero_fund_invariant k (.P q .Z) hr hs).1
  have haw : Term.wf a = true := by
    by_cases ha0 : a = .zero
    · rw [ha0]; rfl
    · simpa only [heBase, ite_eq_right ha0] using hBase.wf
  obtain ⟨cut, hc, _, hPsi, _⟩ := regular_lower_cutFund_image k m hmk q hm hr hs
  have heFund : new.T.fund (.P q .Z) (new.T.ofNat 1) =
      .P (base.rplc ⟨m, by omega⟩ (new.T.ofNat 1)) .Z := by
    rw [fund_regular_bound q (by omega) hm, hb, Support.SourceSuccessor.fund_succ]
  obtain ⟨c, hePsi⟩ := hPsi (new.T.ofNat 1) (by intro he; cases he)
  have heCut : cut = layerCut m a := by
    rw [heFund, heInsert _ (by intro he; cases he)] at hePsi
    have ht0 : convert (k + 3) (code (new.T.ofNat (lam := k + 3) 1)) ≠ .zero := by
      rw [Support.FiniteCorrespondence.code_ofNat]
      change convert (k + 3) Support.UserImage.oneCode ≠ .zero
      rw [DimensionImage.convert_one]; intro he; cases he
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
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hib : i.val ≤ k)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ c, Above i.val c ∧ Term.wf c = true ∧
      RecursiveWF (k + 3) (.P (xs.rplc i .Z) .Z) ∧
      convert (k + 3) (code (.P (xs.rplc i .Z) .Z)) = (if c = .zero then Term.one else c) ∧
      convert (k + 3) (code (.P xs .Z)) =
        .psi (layerCut i.val c) (convert (k + 3) (code (xs.idx i))) := by
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hdrop := Omega_image_drop k _ hcr hcw hd
  have hBase := principal_replace_relative_recursiveWF k xs i (by omega)
    (Support.DimensionCut.minIdx_spec xs hm).2.2 hs .Z (recursive_zero _ _) hc0 hdrop
    (by intros; simp only [code, convert, Term.H, Term.allLt, List.all_nil])
  have hzero : ∀ j, j.val < i.val + 1 → (xs.rplc i .Z).idx j = .Z := by
    intro j hj
    simp only [vec_rplc_idx]
    split
    · rfl
    · exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j (by omega)
  obtain ⟨c, hca, heBase, heInsert⟩ := principal_insertion_context k i.val hib (xs.rplc i .Z) hzero
  have heVec : (xs.rplc i .Z).rplc ⟨i.val, by omega⟩ (xs.idx i) = xs := by
    apply vec_ext; intro j
    simp only [vec_rplc_idx]
    split
    · have heJ : j = i := Fin.ext (by assumption); rw [heJ]
    · simp_all only
  have heOld := heInsert (xs.idx i) hc0
  rw [heVec] at heOld
  have hcImage0 : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  rw [step_psi_of_drop _ _ _ hcImage0 hdrop] at heOld
  refine ⟨c, hca, ?_, hBase, heBase, heOld⟩
  by_cases hc : c = .zero
  · rw [hc]; rfl
  · simpa only [heBase, ite_eq_right hc] using hBase.wf

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
      exact Support.GeneralImageEmptyCutDiagonal.empty_le_regular i _ (layerCut_regular m a)
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
        have hEq := (Support.TargetArithmetic.principal_le_one_iff (above_principal (hc.resolve_left hc0)) hcw).mp hOne
        have hfc := hc.resolve_left hc0
        rw [hEq] at hfc
        simp [Term.fT, Term.one, Term.bigOmega] at hfc
    simp only [layerCut, hc0, ha0, ↓reduceIte, Term.predR]
    constructor
    · exact Support.GeneralImageEmptyCutDiagonal.empty_le_regular i _ (by simp [Term.isRT, Term.isLimT])
        (by simpa only [Term.fT] using him)
    · simp [Term.le]
  · apply layerCut_le_of_context_le i m him c a hc ha ha0 hcw haw
    by_cases hc0 : c = .zero
    · rw [hc0]; simp only [Term.le, (zero_lt_iff _).mpr ha0, Bool.or_true]
    · simpa only [ite_eq_right hc0, ite_eq_right ha0] using hca

theorem context_bound_diagonal_source_closed [LargeCardinals.{u}] (k m : Nat) (hmk : m ≤ k)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (him : i.val ≤ m)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (hbound : new.T.le (.P (xs.rplc i .Z) .Z) (new.T.fund (.P q .Z) .Z))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true := by
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlr := Omega_label_recursive k _ hcr hd
  have hlw := Omega_label_recursiveWF k _ hcw hd
  obtain ⟨a, ha, haw, heA, hc, hePredA⟩ := regular_lower_label_cut_context k m hmk q hq hlr hlw
  obtain ⟨c, hca, hcwC, hBase, heBase, heOld⟩ := principal_Omega_slot_context k xs q i (by omega) hm hr hs
  have hA := (zero_fund_invariant k (.P q .Z) hlr hlw).1
  have hle : Term.le (if c = .zero then Term.one else c) (if a = .zero then Term.one else a) = true := by
    rcases hbound with hl | he
    · have hlt := (convert_order k _ _ hBase hA).mp hl
      rw [heBase, heA] at hlt
      simp only [Term.le, hlt, Bool.or_true]
    · have heq := congrArg (fun s => convert (k + 3) (code s)) (new.T_eq_sound _ _ he)
      rw [heBase, heA] at heq
      rw [heq]; simp [Term.le]
  obtain ⟨hCut, hPred⟩ := layerCut_comparable_of_erased_le i.val m him c a hca ha hcwC haw hle
  have hp := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
  exact ⟨layerCut m a, hc, H_bound_of_comparable_cuts _ _ _ hp.1 hp.2.1 hc.regular hc.cutWf
    hcw.wf hCut hPred hp.2.2.2⟩

theorem compareVec_le_coordinate_predecessor {lam n : Nat}
    (xs ys zs : Vec (new.T lam) n) (j : Fin n) (b : new.T lam)
    (hy : ys.idx j = Support.SourceSuccessor.succ b) (hz : zs.idx j = b)
    (hsame : ∀ l, l.val ≠ j.val → zs.idx l = ys.idx l)
    (hprefix : ∀ l, l.val < j.val → xs.idx l = ys.idx l)
    (hlt : Vec.lt xs ys) : Vec.le xs zs := by
  induction xs with
  | nil => exact j.elim0
  | snoc n xs x ih =>
    cases ys with
    | snoc _ ys y =>
      cases zs with
      | snoc _ zs z =>
        by_cases hjn : j.val < n
        · let jj : Fin n := ⟨j.val, hjn⟩
          have heJ : j = jj.castSucc := Fin.ext rfl
          have hzy : z = y := by
            simpa only [vec_snoc_idx_last] using hsame (Fin.last n) (by simp only [Fin.val_last]; omega)
          cases hc : new.compareT x y with
          | lt => simpa only [Vec.le, new.compareVec, hzy, hc] using (Or.inl rfl : Ordering.lt = .lt ∨ Ordering.lt = .eq)
          | gt => simp only [Vec.lt, new.compareVec, hc] at hlt; cases hlt
          | eq =>
            have hlow : Vec.lt xs ys := by simpa only [Vec.lt, new.compareVec, hc] using hlt
            have hyn : ys.idx jj = Support.SourceSuccessor.succ b := by simpa only [heJ, vec_snoc_idx_cast] using hy
            have hzn : zs.idx jj = b := by simpa only [heJ, vec_snoc_idx_cast] using hz
            have hlowBound := ih ys zs jj hyn hzn
              (fun l hl => by
                have hl' : l.castSucc.val ≠ j.val := hl
                simpa only [vec_snoc_idx_cast] using hsame l.castSucc hl')
              (fun l hl => by simpa only [vec_snoc_idx_cast] using hprefix l.castSucc hl) hlow
            simpa only [Vec.le, new.compareVec, hzy, hc] using hlowBound
        · have heJ : j = Fin.last n := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
          have hxys : xs = ys := by
            apply vec_ext; intro l
            simpa only [vec_snoc_idx_cast] using hprefix l.castSucc (by rw [heJ]; simp only [Fin.val_last]; exact l.isLt)
          have hzys : zs = ys := by
            apply vec_ext; intro l
            simpa only [vec_snoc_idx_cast] using hsame l.castSucc (by rw [heJ]; change l.val ≠ n; have := l.isLt; omega)
          have hyLast : y = Support.SourceSuccessor.succ b := by simpa only [heJ, vec_snoc_idx_last] using hy
          have hzLast : z = b := by simpa only [heJ, vec_snoc_idx_last] using hz
          have hxb : new.T.lt x (Support.SourceSuccessor.succ b) := by
            cases he : new.compareT x (Support.SourceSuccessor.succ b) <;>
              simp_all only [new.T.lt, Vec.lt, new.compareVec, new.Vec_refl]
          have hBound := (Support.SourceSuccessor.lt_succ_iff_le x b).mp hxb
          unfold new.T.le at hBound
          cases he : new.compareT x b <;>
            simp_all only [Vec.le, new.compareVec, new.Vec_refl]

theorem consecutive_diagonal_context_bound (k m : Nat) (hmk : m ≤ k + 1)
    (xs q : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨m, by omega⟩, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one)) (hdiag : Vec.lt xs q) :
    new.T.le (.P (xs.rplc ⟨m, by omega⟩ .Z) .Z) (new.T.fund (.P q .Z) .Z) := by
  let i : Fin (k + 3) := ⟨m, by omega⟩
  let j : Fin (k + 3) := ⟨m + 1, by omega⟩
  obtain ⟨b, hb⟩ := dom_one_succ (q.idx j) ((Support.DimensionCut.minIdx_spec q hq).1.symm)
  let base := q.rplc j b
  have hzero : ∀ l, l.val < m + 1 → base.idx l = .Z := by
    intro l hl
    simp only [base, vec_rplc_idx, j, ite_eq_right (by change l.val ≠ m + 1; omega)]
    exact (Support.DimensionCut.minIdx_spec q hq).2.2 l (by change l.val < m + 1; exact hl)
  have hf0 : new.T.fund (.P q .Z) .Z = .P base .Z := by
    rw [fund_regular_bound q (by omega) hq, hb, Support.SourceSuccessor.fund_succ]
    congr 1; apply vec_ext; intro l
    simp only [vec_rplc_idx]
    split
    · exact (hzero l (by omega)).symm
    · simp only [base, j, vec_rplc_idx]
  have hc0 : xs.idx i ≠ .Z := by
    have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
    intro he; rw [he, new.T.dom] at hd; cases hd
  have hZlt : new.compareT .Z (xs.idx i) = .lt := by
    cases he : xs.idx i with
    | Z => exact False.elim (hc0 he)
    | P => rfl
  have hlt : Vec.lt (xs.rplc i .Z) q :=
    new.Vec_trans _ _ _ (compareVec_rplc_lt xs i .Z hZlt) hdiag
  have hp : ∀ l, l.val < j.val → (xs.rplc i .Z).idx l = q.idx l := by
    intro l hl
    rw [(Support.DimensionCut.minIdx_spec q hq).2.2 l hl, vec_rplc_idx]
    split
    · rfl
    · rename_i hne
      have hn : l.val ≠ m := hne
      exact (Support.DimensionCut.minIdx_spec xs hm).2.2 l (by change l.val < m; change l.val < m + 1 at hl; omega)
  have hvec : Vec.le (xs.rplc i .Z) base := compareVec_le_coordinate_predecessor _ q base j b hb
    (by simp only [base, vec_rplc_idx, ↓reduceIte])
    (fun l hl => by simp only [base, vec_rplc_idx, ite_eq_right hl]) hp hlt
  rw [hf0]
  rcases hvec with hl | he
  · apply Or.inl
    change new.compareT (.P (xs.rplc i .Z) .Z) (.P base .Z) = .lt
    simp only [new.compareT, hl]
  · apply Or.inr
    change new.compareT (.P (xs.rplc i .Z) .Z) (.P base .Z) = .eq
    simp only [new.compareT, he]

end Support.GeneralImageContextBoundDiagonal

namespace Support.GeneralImageHighestContextDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageLabelClosure
open Support.GeneralImageComparableCuts Support.GeneralImageParametricCut
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularDiagonal
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance Support.GeneralImageMiddleRecursion
open Support.GeneralImageRelativePredecessor Support.GeneralImageMiddleSums
open Support.GeneralImageZeroFund Support.GeneralImageHeadCuts
open Support.GeneralImageCountableLayers Support.GeneralImageCountableInheritance
open Support.GeneralImageHighestDiagonal Support.GeneralImageCountableRecursion
open Support.GeneralImageDominatedCoefficients Support.GeneralImageOmegaCoefficients
open Support.GeneralImageLimitSupport
open Support.GeneralImageLimitBranches Support.GeneralImageContextBoundDiagonal
open Support.SourceRecursiveDescending Support.SourceFundOrder

universe u

theorem pairCut_image_comparable [LargeCardinals.{u}] (k : Nat) (h b : new.T (k + 3))
    (hh : RecursiveWF (k + 3) h) (hb : RecursiveWF (k + 3) b) (hle : new.T.le h b) :
    Term.le (pairCut (k + 1) (convert (k + 3) (code h)))
      (pairCut (k + 1) (convert (k + 3) (code b))) = true ∧
    Term.le (Term.predR (pairCut (k + 1) (convert (k + 3) (code h))))
      (Term.predR (pairCut (k + 1) (convert (k + 3) (code b)))) = true := by
  rcases hle with hlt | he
  · by_cases hh0 : h = .Z
    · simp only [hh0, code, convert, pairCut, ↓reduceIte, Term.predR]
      exact ⟨inacc_zero_le _ _, Support.OT2.zero_le _⟩
    · have hb0 : b ≠ .Z := by
        intro he
        rw [he] at hlt
        cases h <;> cases hlt
      have hhNZ : convert (k + 3) (code h) ≠ .zero := by
        intro he; exact hh0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
      have hbNZ : convert (k + 3) (code b) ≠ .zero := by
        intro he; exact hb0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
      have hImage := (convert_order k h b hh hb).mp hlt
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
  · rw [new.T_eq_sound _ _ he]
    exact ⟨by simp [Term.le], by simp [Term.le]⟩

theorem highest_regular_label_shape (k : Nat) (q : Vec (new.T (k + 3)) (k + 3))
    (hq : new.T.domVecMinIdx q = some (⟨k + 2, by omega⟩, .one)) :
    ∃ b, q = lastVec (k + 2) (Support.SourceSuccessor.succ b) := by
  obtain ⟨b, hb⟩ := dom_one_succ (q.idx ⟨k + 2, by omega⟩)
    ((Support.DimensionCut.minIdx_spec q hq).1.symm)
  refine ⟨b, ?_⟩
  apply vec_ext; intro j
  rw [lastVec_idx]
  by_cases hj : j.val = k + 2
  · rw [ite_eq_left hj]
    have heJ : j = ⟨k + 2, by omega⟩ := Fin.ext hj
    rwa [heJ]
  · rw [ite_eq_right hj]
    exact (Support.DimensionCut.minIdx_spec q hq).2.2 j
      (by change j.val < k + 2; have := j.isLt; omega)

theorem highest_consecutive_parent_bound (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨k + 1, by omega⟩, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨k + 2, by omega⟩, .one))
    (b : new.T (k + 3)) (heQ : q = lastVec (k + 2) (Support.SourceSuccessor.succ b))
    (hdiag : Vec.lt xs q) : new.T.le (xs.idx ⟨k + 2, by omega⟩) b := by
  have heXs : xs.rplc ⟨k + 1, by omega⟩ .Z = lastVec (k + 2) (xs.idx ⟨k + 2, by omega⟩) := by
    apply vec_ext; intro j
    simp only [vec_rplc_idx, lastVec_idx]
    by_cases hj : j.val = k + 2
    · rw [ite_eq_left hj, ite_eq_right (by change j.val ≠ k + 1; omega)]
      have heJ : j = ⟨k + 2, by omega⟩ := Fin.ext hj
      rw [heJ]
    · rw [ite_eq_right hj]
      split
      · rfl
      · rename_i hne
        exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j
          (by change j.val < k + 1; change j.val ≠ k + 1 at hne; have := j.isLt; omega)
  have hbound := consecutive_diagonal_context_bound k (k + 1) (Nat.le_refl _) xs q hm hq hdiag
  rw [congrArg (fun v => new.T.P v new.T.Z) heXs, heQ] at hbound
  change new.T.le (topNode k (xs.idx ⟨k + 2, by omega⟩))
    (new.T.fund (topNode k (Support.SourceSuccessor.succ b)) .Z) at hbound
  rw [highest_regular_fund_zero] at hbound
  simp only [new.T.le, topNode, new.compareT, lastVec, new.compareVec, new.Vec_refl] at hbound
  cases he : new.compareT (xs.idx ⟨k + 2, by omega⟩) b <;>
    simp_all only [new.T.le]

theorem principal_middle_Omega_cut [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨k + 1, by omega⟩, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    let w := pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))
    let c := convert (k + 3) (code (xs.idx ⟨k + 1, by omega⟩))
    convert (k + 3) (code (.P xs .Z)) = .psi w c ∧ Term.wf w = true ∧
      Term.allLt (Term.H w c) c = true := by
  let i : Fin (k + 3) := ⟨k + 1, by omega⟩
  let j : Fin (k + 3) := ⟨k + 2, by omega⟩
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hc0 : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he
    have hcZ : xs.idx i = .Z := code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
    rw [hcZ, new.T.dom] at hd; cases hd
  have heOld : convert (k + 3) (code (.P xs .Z)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code (xs.idx j)))) (convert (k + 3) (code (xs.idx i))) := by
    let args := arguments (k + 3) (trim (codes xs))
    rw [convert_principal, principal_as_layers]
    change lower (k + 1) args (topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)) = _
    have hnz : topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero) ≠ .zero := by
      rw [converted_coordinate xs i]
      simp [topPair, hc0]
    rw [lower_keep (k + 1) args _ hnz (fun l hl => by
      rw [converted_coordinate xs ⟨l, by omega⟩, (Support.DimensionCut.minIdx_spec xs hm).2.2 ⟨l, by omega⟩ hl,
        code, convert]), converted_coordinate xs j, converted_coordinate xs i]
    simp only [topPair, hc0, ↓reduceIte, pairCut, Omega_image_drop k _ hcr hcw hd]
  have hp := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
  exact ⟨heOld, hp.2.1, hp.2.2.2⟩

theorem highest_consecutive_source_closed [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨k + 1, by omega⟩, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨k + 2, by omega⟩, .one)) (hdiag : Vec.lt xs q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx ⟨k + 1, by omega⟩))))
        (convert (k + 3) (code (xs.idx ⟨k + 1, by omega⟩))) = true := by
  let i : Fin (k + 3) := ⟨k + 1, by omega⟩
  let j : Fin (k + 3) := ⟨k + 2, by omega⟩
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcoords : ∀ l, RecursiveWF (k + 3) (xs.idx l) := by rw [RecursiveWF] at hs; exact hs.1
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlw := Omega_label_recursiveWF k _ (hcoords i) hd
  obtain ⟨b, heQ⟩ := highest_regular_label_shape k q hq
  have heLabel : (.P q .Z : new.T (k + 3)) = topNode k (Support.SourceSuccessor.succ b) := by rw [heQ]; rfl
  have hsLabel := heLabel ▸ hlw
  have hb : RecursiveWF (k + 3) b := by
    have hbs : RecursiveWF (k + 3) (Support.SourceSuccessor.succ b) := by
      have hsTop : RecursiveWF (k + 3) (.P (lastVec (k + 2) (Support.SourceSuccessor.succ b)) .Z) := hsLabel
      rw [RecursiveWF] at hsTop
      simpa only [lastVec_idx, j, ↓reduceIte] using hsTop.1 j
    exact (recursive_succ_iff _ _).mp hbs
  let cut := pairCut (k + 1) (convert (k + 3) (code b))
  have hc : CutFund k (.P q .Z) cut := by rw [heLabel]; exact highest_regular_cutFund_at k b hsLabel
  obtain ⟨hCut, hPred⟩ := pairCut_image_comparable k (xs.idx j) b (hcoords j) hb
    (highest_consecutive_parent_bound k xs q hm hq b heQ hdiag)
  obtain ⟨_, hw, hH⟩ := principal_middle_Omega_cut k xs q hm hr hs
  exact ⟨cut, hc, H_bound_of_comparable_cuts _ _ _ (pairCut_regular _ _) hw hc.regular hc.cutWf
    (hcoords i).wf hCut hPred hH⟩

end Support.GeneralImageHighestContextDiagonal

namespace Support.GeneralImageStrictHighestDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageLabelClosure
open Support.GeneralImageComparableCuts Support.GeneralImageParametricCut
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularDiagonal
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance Support.GeneralImageMiddleRecursion
open Support.GeneralImageRelativePredecessor Support.GeneralImageMiddleSums
open Support.GeneralImageZeroFund Support.GeneralImageHeadCuts
open Support.GeneralImageCountableLayers Support.GeneralImageCountableInheritance
open Support.GeneralImageHighestDiagonal Support.GeneralImageCountableRecursion
open Support.GeneralImageDominatedCoefficients Support.GeneralImageOmegaCoefficients
open Support.GeneralImageLimitSupport
open Support.GeneralImageLimitBranches Support.GeneralImageContextBoundDiagonal
open Support.GeneralImageHighestContextDiagonal
open Support.SourceRecursiveDescending Support.SourceFundOrder

universe u

theorem strict_highest_diagonal_branch (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
    (heQ : q = lastVec (k + 2) (Support.SourceSuccessor.succ b))
    (hhigh : new.T.lt (xs.idx ⟨k + 2, by omega⟩) b) : Vec.lt xs q := by
  apply compareVec_of_lt_at xs q ⟨k + 2, by omega⟩
  · rw [heQ, lastVec_idx, ite_eq_left rfl]
    exact (Support.SourceSuccessor.lt_succ_iff_le _ b).mpr (Or.inl hhigh)
  · intro j hj
    have := j.isLt
    change k + 2 < j.val at hj
    omega

theorem diagonal_selector_below_highest (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (hr : Recursive (.P xs .Z)) : i.val ≤ k + 1 := by
  by_cases hi : i.val ≤ k + 1
  · exact hi
  apply False.elim
  have heI : i = Fin.last (k + 2) := Fin.ext (by simp only [Fin.val_last]; have := i.isLt; omega)
  have heXs : xs = lastVec (k + 2) (xs.idx i) := by
    apply vec_ext; intro j; rw [lastVec_idx]
    by_cases hj : j.val = k + 2
    · rw [ite_eq_left hj]
      have heJ : j = i := Fin.ext (by rw [heI]; simpa only [Fin.val_last] using hj)
      rw [heJ]
    · rw [ite_eq_right hj]
      exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j
        (by rw [heI]; simp only [Fin.val_last]; have := j.isLt; omega)
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  exact Support.SourceOmegaHighest.highest_not_diagonal (k + 2) _ hcr
    (Support.DimensionCut.minIdx_spec xs hm).1.symm (heXs ▸ hdiag)

theorem strict_highest_parent_index [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hi : i.val ≤ k)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (b : new.T (k + 3)) (hb : RecursiveWF (k + 3) b)
    (hhigh : new.T.lt (xs.idx ⟨k + 2, by omega⟩) b)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ w, convert (k + 3) (code (.P xs .Z)) = .psi w (convert (k + 3) (code (xs.idx i))) ∧
      Term.isRT w = true ∧ Term.wf w = true ∧
      Term.le w (pairCut (k + 1) (convert (k + 3) (code b))) = true ∧
      Term.le (Term.predR w) (Term.predR (pairCut (k + 1) (convert (k + 3) (code b)))) = true ∧
      Term.allLt (Term.H w (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true := by
  have hb0 : b ≠ .Z := by
    intro he; rw [he] at hhigh
    cases heH : xs.idx ⟨k + 2, by omega⟩ <;> rw [heH] at hhigh <;> cases hhigh
  have hbNZ : convert (k + 3) (code b) ≠ .zero := by
    intro he; exact hb0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  obtain ⟨c, hca, hcw, hBase, heBase, heOld⟩ := principal_Omega_slot_context k xs q i hi hm hr hs
  have hB := topNode_recursiveWF k b hb
  have hraw : new.T.lt (.P (xs.rplc i .Z) .Z) (topNode k b) := by
    apply highest_principal_lt
    rw [vec_rplc_idx, Fin.val_last, ite_eq_right (by change k + 2 ≠ i.val; omega), lastVec_idx,
      Fin.val_last, ite_eq_left rfl]
    exact hhigh
  have hBound := (convert_order k _ _ hBase hB).mp hraw
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
  have hSucc := topNode_recursiveWF k (Support.SourceSuccessor.succ b) ((recursive_succ_iff _ _).mpr hb)
  have hCutW : Term.wf (pairCut (k + 1) (convert (k + 3) (code b))) = true := by
    rw [← highest_regular_image k b]; exact hSucc.wf
  have hBlt : Term.lt (convert (k + 3) (code (topNode k b)))
      (pairCut (k + 1) (convert (k + 3) (code b))) = true := by
    rw [convert_topNode k b hb0]
    simp only [pairCut, hbNZ, ↓reduceIte, inacc_same_lt]
    rw [lt_succTerm_eq_le (dropOne_wf hb.wf) (dropOne_wf hb.wf)]
    simp [Term.le]
  have hp := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
  refine ⟨layerCut i.val c, heOld, hp.1, hp.2.1, ?_, ?_, hp.2.2.2⟩
  · by_cases hc0 : c = .zero
    · rw [hc0]
      exact Support.GeneralImageEmptyCutDiagonal.empty_le_regular i.val _ (pairCut_regular _ _)
        (by simp only [pairCut, Term.fT]; omega)
    · have hwB : Term.lt (layerCut i.val c) (convert (k + 3) (code (topNode k b))) = true := by
        simp only [layerCut, hc0, ↓reduceIte]
        change Term.lt (regular i.val c) (convert (k + 3) (code (topNode k b))) = true
        rwa [regular_lt_context (above_principal (hca.resolve_left hc0)) (by rw [hBft]; omega)]
      have hwCut := lemma_6_1.{u}.2.1 _ _ _ hp.2.1 hB.wf hCutW hwB hBlt
      simp only [Term.le, hwCut, Bool.or_true]
  · rw [hPred]
    by_cases hc0 : c = .zero
    · simp only [layerCut, hc0, ↓reduceIte, Term.predR]
      exact Support.OT2.zero_le _
    · have hPredW : Term.predR (layerCut i.val c) = c := by
        simp only [layerCut, hc0, ↓reduceIte, Term.predR, succTerm_ne_zero,
          predT_succTerm hcw, show ¬Term.fT c ≤ i.val from Nat.not_le.mpr (hca.resolve_left hc0)]
      rw [hPredW]
      simp only [Term.le, hcBound, Bool.or_true]

theorem strict_highest_diagonal_source_closed [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (b : new.T (k + 3))
    (heQ : q = lastVec (k + 2) (Support.SourceSuccessor.succ b))
    (hhigh : new.T.lt (xs.idx ⟨k + 2, by omega⟩) b)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true := by
  have hi := diagonal_selector_below_highest k xs q i hm (strict_highest_diagonal_branch k xs q b heQ hhigh) hr
  have hq : new.T.domVecMinIdx q = some (⟨k + 2, by omega⟩, .one) := by
    rw [heQ]
    simp only [minIdx_lastVec, Support.SourceSuccessor.dom_succ, reduceCtorEq, ↓reduceIte]
    rfl
  by_cases hil : i.val ≤ k
  · have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
    have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
    have hlw := Omega_label_recursiveWF k _ hcw hd
    have heLabel : (.P q .Z : new.T (k + 3)) = topNode k (Support.SourceSuccessor.succ b) := by rw [heQ]; rfl
    have hsLabel := heLabel ▸ hlw
    have hb : RecursiveWF (k + 3) b := by
      have hsTop : RecursiveWF (k + 3) (.P (lastVec (k + 2) (Support.SourceSuccessor.succ b)) .Z) := hsLabel
      rw [RecursiveWF] at hsTop
      have hbs : RecursiveWF (k + 3) (Support.SourceSuccessor.succ b) := by
        simpa only [lastVec_idx, ↓reduceIte] using hsTop.1 ⟨k + 2, by omega⟩
      exact (recursive_succ_iff _ _).mp hbs
    let cut := pairCut (k + 1) (convert (k + 3) (code b))
    have hc : CutFund k (.P q .Z) cut := by rw [heLabel]; exact highest_regular_cutFund_at k b hsLabel
    obtain ⟨w, _, hwR, hw, hCut, hPred, hH⟩ := strict_highest_parent_index k xs q i hil hm b hb hhigh hr hs
    exact ⟨cut, hc, H_bound_of_comparable_cuts w _ _ hwR hw hc.regular hc.cutWf hcw.wf hCut hPred hH⟩
  · have heI : i = ⟨k + 1, by omega⟩ := Fin.ext (by change i.val = k + 1; omega)
    rw [heI] at hm ⊢
    exact highest_consecutive_source_closed k xs q hm hq (strict_highest_diagonal_branch k xs q b heQ hhigh) hr hs

end Support.GeneralImageStrictHighestDiagonal

namespace Support.GeneralImageCutTransport

open OCF.Jaeger OCF.Ordinal
open OCF.Jaeger.Term
open Support.GeneralImageWFInvariant Support.GeneralImageCoefficients

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

end Support.GeneralImageCutTransport

namespace Support.GeneralImageCriticalDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageLabelClosure
open Support.GeneralImageComparableCuts Support.GeneralImageParametricCut
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularDiagonal
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance Support.GeneralImageMiddleRecursion
open Support.GeneralImageRelativePredecessor Support.GeneralImageMiddleSums
open Support.GeneralImageZeroFund Support.GeneralImageHeadCuts
open Support.GeneralImageCountableLayers Support.GeneralImageCountableInheritance
open Support.GeneralImageHighestDiagonal Support.GeneralImageCountableRecursion
open Support.GeneralImageDominatedCoefficients Support.GeneralImageOmegaCoefficients
open Support.GeneralImageLimitSupport
open Support.GeneralImageLimitBranches Support.GeneralImageContextBoundDiagonal
open Support.GeneralImageHighestContextDiagonal
open Support.SourceRecursiveDescending Support.SourceFundOrder
open Support.GeneralImageCutTransport Support.GeneralImageStrictHighestDiagonal

universe u

theorem highest_diagonal_parent_bound (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
    (heQ : q = lastVec (k + 2) (Support.SourceSuccessor.succ b))
    (hdiag : Vec.lt xs q) : new.T.le (xs.idx ⟨k + 2, by omega⟩) b := by
  apply (Support.SourceSuccessor.lt_succ_iff_le _ b).mp
  rw [heQ] at hdiag
  cases xs with
  | snoc _ ys y =>
    rw [show (⟨k + 2, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) from Fin.ext rfl,
      vec_snoc_idx_last]
    change new.compareVec (.snoc (k + 2) ys y)
      (.snoc (k + 2) (zeros (k + 2)) (Support.SourceSuccessor.succ b)) = .lt at hdiag
    cases he : new.compareT y (Support.SourceSuccessor.succ b) with
    | lt => exact he
    | eq =>
      simp only [new.compareVec, he] at hdiag
      exact False.elim (Support.DimensionCut.compareVec_zero_not_lt ys hdiag)
    | gt => simp only [new.compareVec, he] at hdiag; cases hdiag

end Support.GeneralImageCriticalDiagonal

namespace Support.GeneralImageSharedLowerContext

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageLimitSupport
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRegularLimit Support.GeneralImageRegularDiagonal

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
    (base xs : Vec (new.T (k + 3)) (k + 3))
    (hzero : ∀ j, j.val < m + 1 → base.idx j = .Z)
    (hsame : ∀ j, m < j.val → xs.idx j = base.idx j)
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
      rw [converted_coordinate base ⟨j, by omega⟩, hzero ⟨j, by omega⟩ hj, code, convert])
  have heAB := above_base_image_injective m a b ha (context_above hb) (heBase.symm.trans heB)
  let newArgs := arguments (k + 3) (trim (codes xs))
  have hArgs (j : Nat) (hj : m < j) (hjl : j < k + 3) :
      newArgs[j]?.getD .zero = args[j]?.getD .zero := by
    rw [converted_coordinate xs ⟨j, hjl⟩, converted_coordinate base ⟨j, hjl⟩, hsame ⟨j, hjl⟩ hj]
  rw [convert_principal, principal_as_layers]
  change lower (k + 1) newArgs
    (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) = _
  rw [hArgs (k + 2) (by omega) (by omega), hArgs (k + 1) (by omega) (by omega)]
  rw [hformula newArgs (fun j hj hjl => hArgs j hj (by omega)), heAB]

end Support.GeneralImageSharedLowerContext

namespace Support.GeneralImageClosedDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageLabelClosure
open Support.GeneralImageComparableCuts Support.GeneralImageParametricCut
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularDiagonal
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance
open Support.GeneralImageRelativePredecessor Support.GeneralImageMiddleSums
open Support.GeneralImageZeroFund Support.GeneralImageHeadCuts
open Support.GeneralImageCountableLayers Support.GeneralImageCountableInheritance
open Support.GeneralImageHighestDiagonal Support.GeneralImageCountableRecursion
open Support.GeneralImageDominatedCoefficients Support.GeneralImageOmegaCoefficients
open Support.GeneralImageLimitSupport
open Support.GeneralImageLimitBranches
open Support.SourceRecursiveDescending Support.SourceFundOrder

universe u

theorem closed_diagonal_selector_bound [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hdiag : Vec.lt xs q) (hr : Recursive (.P xs .Z))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) : i.val ≤ k + 1 := by
  have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  apply Classical.byContradiction; intro he
  have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
  exact no_diagonal_highest k xs hs (hi ▸ hchildR) (hi ▸ hm) hdiag

theorem closed_diagonal_fund_eq (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q) (n : Nat) :
    new.T.fund (.P xs .Z) (new.T.ofNat n) =
      .P (xs.rplc i (new.T.iter (new.T.fund (xs.idx i)) (new.T.ofNat (n + 1)))) .Z := by
  simp only [new.T.fund, ↓reduceIte, hm, hdiag, GetElem.getElem]
  rw [← iter_ofNat_succ (new.T.fund (xs.idx i)) n]

theorem closed_diagonal_recursiveWF [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
      (convert (k + 3) (code (xs.idx i))) = true)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) :
    RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat n)) := by
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hib := closed_diagonal_selector_bound k xs q i hm hdiag hr hs
  have hIter := Omega_iter_at_label_cut_relative k _ hcr hcw hd cut hc hSource (n + 1)
  rw [closed_diagonal_fund_eq k xs q i hm hdiag n]
  apply principal_replace_relative_recursiveWF k xs i hib
    (Support.DimensionCut.minIdx_spec xs hm).2.2 hs _ hIter.1
  · intro he; rw [he, new.T.dom] at hd; cases hd
  · exact Omega_image_drop k _ hcr hcw hd
  · exact hIter.2

theorem closed_diagonal_relative [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
      (convert (k + 3) (code (xs.idx i))) = true)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))))
      (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))) = true := by
  cases n with
  | zero => exact (zero_fund_invariant k _ hr hs).2.2 v hvR hv hH
  | succ n =>
    have hn := closed_diagonal_recursiveWF k xs q i hm hdiag cut hc hSource hr hs (n + 1)
    have hd : new.T.dom (.P xs .Z) = .omega := by simp only [new.T.dom, ↓reduceIte, hm, hdiag]
    exact omega_relative_allcuts k _ hr hs hd (n + 1) hn
      (fun v hvR hv hOmega hH => diagonal_parent_relative_above k xs i q hm hdiag hr hs
        (n + 1) (by omega) hn v hvR hv hOmega hH) v hvR hv hH

theorem closed_diagonal_dominated_support [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
      (convert (k + 3) (code (xs.idx i))) = true)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))) →
      DominatedCoefficient k v (.P xs .Z) z := by
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hib := closed_diagonal_selector_bound k xs q i hm hdiag hr hs
  let a := new.T.iter (new.T.fund (xs.idx i)) (new.T.ofNat (n + 1))
  have ha : RecursiveWF (k + 3) a := (Omega_iter_at_label_cut k _ hcr (hcoords i) hd cut hc hSource (n + 1)).1
  have ha0 : a ≠ .Z := by dsimp only [a]; rw [iter_ofNat_succ]; exact domOmega_fund_ne_zero _ _ hd
  have haLt : Term.lt (convert (k + 3) (code a)) (convert (k + 3) (code (xs.idx i))) = true := by
    apply (convert_order k _ _ ha (hcoords i)).mp
    dsimp only [a]; rw [iter_ofNat_succ]; exact fund_lt _ _ hc0
  have hf : new.T.fund (.P xs .Z) (new.T.ofNat n) = .P (xs.rplc i a) .Z :=
    closed_diagonal_fund_eq k xs q i hm hdiag n
  have hn := closed_diagonal_recursiveWF k xs q i hm hdiag cut hc hSource hr hs n
  have hcNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have haNZ : convert (k + 3) (code a) ≠ .zero := by
    intro he; exact ha0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) = .psi Term.bigOmega (convert (k + 3) (code (xs.idx i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff _ _ _).mpr ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (xs.idx i)) .Z)
      hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    intro z hz
    rw [heSource, fund_low_Omega (k + 2) _ _ q hd, H_low_empty_above_Omega v hOmega] at hz
    cases hz
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow a hcNZ haNZ
      (Omega_image_drop k _ hcr (hcoords i) hd) hIsLow
    have heFund := hf ▸ heNew
    have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
    rw [heOld, heFund] at hlt
    intro z hz; rw [heFund] at hz
    rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz
      with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
    · exact Or.inr (Or.inl (heOld ▸ ho))
    · have lift (ho : DominatedCoefficient k v (xs.idx i) z) : DominatedCoefficient k v (.P xs .Z) z := by
        rcases ho with he | ho | ⟨c, hcs, hmem, hbound⟩
        · exact Or.inl he
        · exact Or.inr (Or.inl (heOld ▸ hchild _ ho))
        · exact Or.inr (Or.inr ⟨c, Subterm.trans hcs (Subterm.coordinate xs .Z i),
            hmem.elim (fun h => Or.inl (heOld ▸ hchild _ h)) (fun h => Or.inr (heOld ▸ hchild _ h)), hbound⟩)
      have rootBound (hl : Term.lt z (convert (k + 3) (code (xs.idx i))) = true) :
          DominatedCoefficient k v (.P xs .Z) z :=
        Or.inr (Or.inr ⟨xs.idx i, Subterm.coordinate xs .Z i, Or.inl (heOld ▸ hroot), by simp [Term.le, hl]⟩)
      rcases he with he | he
      · apply rootBound; rw [he]; exact dropOne_lt_of_lt ha.wf (hcoords i).wf haLt
      · rcases Omega_iter_coefficient_support_at_label_cut k _ hcr (hcoords i) hd cut hc hSource
            v hvR hv hOmega (n + 1) he with ho | ho
        · exact lift ho
        · exact rootBound ho

end Support.GeneralImageClosedDiagonal

namespace Support.GeneralImageCriticalZeroDiagonal

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageWFInvariant Support.GeneralImageRawOrder
open Support.GeneralImageLimitSupport Support.GeneralImageLimitBranches
open Support.GeneralImageOmegaSpine Support.GeneralImageMiddleSums
open Support.GeneralImageDominatedCoefficients Support.GeneralImageClosedDiagonal
open Support.GeneralImageZeroFund Support.GeneralImageRelativePredecessor
open Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceRecursiveDescending
open Support.SourceFundGap

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

end Support.GeneralImageCriticalZeroDiagonal

namespace Support.GeneralImageHigherSparseDiagonal

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageWFInvariant Support.GeneralImageRawOrder Support.GeneralImageCountableRecursion
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageRegularDiagonal Support.GeneralImageContextBoundDiagonal
open Support.GeneralImageHighestContextDiagonal Support.GeneralImageSharedLowerContext
open Support.GeneralImageCofinalityBounds
open Support.GeneralImageLabelCut Support.GeneralImageOmegaSpine
open Support.GeneralImageCoefficients Support.GeneralImageLimitSupport Support.GeneralImageLimitBranches
open Support.GeneralImageMiddleSums Support.GeneralImageOmegaContext
open Support.GeneralImageZeroFund Support.GeneralImageComparableCuts Support.GeneralImageRelativePredecessor
open Support.GeneralImageDominatedCoefficients Support.GeneralImageClosedDiagonal
open Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceRecursiveDescending Support.SourceFundOrder

universe u

theorem terminal_successor_fund_zero (k m : Nat) (hmk : m ≤ k + 1)
    (q : Vec (new.T (k + 3)) (k + 3))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (b : new.T (k + 3)) (hb : q.idx ⟨m + 1, by omega⟩ = Support.SourceSuccessor.succ b) :
    new.T.fund (.P q .Z) .Z = .P (q.rplc ⟨m + 1, by omega⟩ b) .Z := by
  rw [fund_regular_bound q (by omega) hq, hb, Support.SourceSuccessor.fund_succ]
  congr 1; apply vec_ext; intro j; simp only [vec_rplc_idx]
  split
  · rename_i he
    change j.val = m at he
    simp only [ite_eq_right (by change j.val ≠ m + 1; omega)]
    exact ((Support.DimensionCut.minIdx_spec q hq).2.2 j (by change j.val < m + 1; omega)).symm
  · rfl

theorem principal_higher_Omega_cut_image [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hi : i.val ≤ k + 1)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ w, convert (k + 3) (code (.P xs .Z)) = .psi w (convert (k + 3) (code (xs.idx i))) ∧
      Term.fT w = i.val := by
  by_cases hib : i.val ≤ k
  · obtain ⟨c, _, _, _, _, he⟩ := principal_Omega_slot_context k xs q i hib hm hr hs
    exact ⟨layerCut i.val c, he, by simp only [layerCut, Term.fT]⟩
  · have heI : i = ⟨k + 1, by omega⟩ := Fin.ext (by change i.val = k + 1; omega)
    have hmI := hm; rw [heI] at hmI
    obtain ⟨he, _, _⟩ := principal_middle_Omega_cut k xs q hmI hr hs
    rw [← heI] at he
    refine ⟨_, he, ?_⟩
    simp only [pairCut, Term.fT, heI]

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
  · rw [ha0]; exact Support.OT2.zero_le _
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

end Support.GeneralImageHigherSparseDiagonal

namespace Support.GeneralImageHigherDiagonal

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageWFInvariant Support.GeneralImageRawOrder
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageHigherSparseDiagonal Support.GeneralImageSharedLowerContext
open Support.GeneralImageRegularDiagonal Support.GeneralImageCofinalityBounds
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageCofinalityInheritance
open Support.GeneralImageParametricCut Support.GeneralImageLabelCut Support.GeneralImageOmegaSpine
open Support.GeneralImageCutTransport Support.GeneralImageRelativePredecessor
open Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceRecursiveDescending Support.SourceFundOrder
open Support.GeneralImageOmegaCoefficients Support.GeneralImageMiddleSums
open Support.GeneralImageCountableRecursion
open Support.GeneralImageLimitBranches Support.GeneralImageUpperOmega
open Support.GeneralImageZeroFund Support.GeneralImageContextBoundDiagonal
open Support.GeneralImageSharedContext
open Support.GeneralImageClosedDiagonal Support.GeneralImageDominatedCoefficients
open Support.GeneralImageLimitSupport

universe u

theorem Omega_label_relative_bound [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (v B : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) (hB : Term.wf B = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) B = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (.P q .Z)))) B = true := by
  have hL := (Omega_label_recursiveWF k s hs hd).wf
  have hp := OmegaLabelPath.of_domain s hd
  induction hp with
  | regular _ => exact hH
  | inherit xs i hm hnd hc ih =>
    have hchildD := hc.domain
    have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
    have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
    have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchildD; cases hchildD
    have hNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
      intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
    have hdParent : new.T.dom (.P xs .Z) = .Omega q := by simp only [new.T.dom, ↓reduceIte, hm, hnd]
    by_cases hib : i.val ≤ k + 1
    · obtain ⟨w, heOld, _⟩ := principal_replacement_psi_images k xs i hib
        (Support.DimensionCut.minIdx_spec xs hm).2.2 (xs.idx i) hNZ hNZ
        (Omega_image_drop k _ hcr hcw hchildD) (Omega_principal_image_ne_low k xs i hs hdParent)
      have hwP := (Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)
      by_cases hskip : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = true
      · have hLpred := target_le_trans hL hs.wf ((sem_of_wf.{u} hv).isR_pred hvR).1
          (cofinality_image_le k _ hr hs hdParent) hskip
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
              (heOld ▸ cofinality_image_le k _ hr hs hdParent)
        exact C_lt_reg ⟨sw.isR_iff.mp hwP.1, sw.lt_Λ₀⟩
          ((lt_iff_V hL hwP.2.1).mp hLw) ((lt_iff_V hwP.2.1 hv).mp hcut)
          ((H_bound_iff_C v w B hvR hv hwP.2.1 hB).mp hWH)
      · have hcutF : Term.lt w v = false := by cases he : Term.lt w v <;> simp_all
        have hChild : Term.allLt (Term.H v (convert (k + 3) (code (xs.idx i)))) B = true := by
          apply (Term.allLt_iff _ _).mpr; intro z hz
          apply (Term.allLt_iff _ _).mp hH z
          rw [Term.H, hskipF, hcutF]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
        exact ih hcr hcw hchildD hChild
    · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      have heXs : xs = lastVec (k + 2) (xs.idx i) := by
        apply vec_ext; intro j; rw [lastVec_idx]
        by_cases hj : j.val = k + 2
        · rw [ite_eq_left hj]; have heJ : j = i := Fin.ext (by rw [hi]; simpa using hj); rw [heJ]
        · rw [ite_eq_right hj]
          exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j
            (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
      have heSource : (.P xs .Z : new.T (k + 3)) = topNode k (xs.idx i) :=
        congrArg (fun us => new.T.P us .Z) heXs
      rw [heSource, H_topNode_above_Omega k _ hc0 v hOmega, Omega_image_drop k _ hcr hcw hchildD] at hH
      exact ih hcr hcw hchildD hH
  | tail xs b hb hc ih =>
    have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
    have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
    apply ih hbr hbw hc.domain
    apply (Term.allLt_iff _ _).mpr; intro z hz
    apply (Term.allLt_iff _ _).mp hH z
    simp only [code, convert]
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
    (q : Vec (new.T (k + 3)) (k + 3))
    (hq : new.T.domVecMinIdx q = some (⟨k + 1, by omega⟩, .one))
    (hr : Recursive (.P q .Z)) (hs : RecursiveWF (k + 3) (.P q .Z))
    (w : Term) (hwr : Term.isRT w = true) (hw : Term.wf w = true) (hf : Term.fT w = k + 1)
    (hle : Term.le w (convert (k + 3) (code (.P q .Z))) = true) :
    Term.le w (convert (k + 3) (code (new.T.fund (.P q .Z) .Z))) = true := by
  let sel : Fin (k + 3) := ⟨k + 1, by omega⟩
  obtain ⟨b, hb⟩ := dom_one_succ (q.idx sel) ((Support.DimensionCut.minIdx_spec q hq).1.symm)
  let A := q.rplc sel b
  let h := convert (k + 3) (code (q.idx ⟨k + 2, by omega⟩))
  have hhR : RecursiveWF (k + 3) (q.idx ⟨k + 2, by omega⟩) := by rw [RecursiveWF] at hs; exact hs.1 _
  have hhw : Term.wf h = true := hhR.wf
  have hbw : Term.wf (convert (k + 3) (code b)) = true := by
    rw [RecursiveWF] at hs
    have hp := hs.1 sel
    rw [hb] at hp
    have hd := Support.SourceSuccessor.dom_succ b
    have hf := fund_one_recursiveWF _ .Z hp hd
    rw [Support.SourceSuccessor.fund_succ] at hf
    exact hf.wf
  have hePrincipal (xs : Vec (new.T (k + 3)) (k + 3))
      (hz : ∀ j, j.val < k + 1 → xs.idx j = .Z) :
      convert (k + 3) (code (.P xs .Z)) =
        if topPair (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))
            (convert (k + 3) (code (xs.idx sel))) = .zero then Term.one else
          topPair (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))
            (convert (k + 3) (code (xs.idx sel))) := by
    rw [convert_principal, principal_as_layers]
    rw [lower_zero_block (k + 1) (by omega)]
    · rw [converted_coordinate xs ⟨k + 2, by omega⟩, converted_coordinate xs sel]
    · intro j hj
      rw [converted_coordinate xs ⟨j, by omega⟩, hz ⟨j, by omega⟩ hj, code, convert]
  have hqNZ : convert (k + 3) (code (q.idx sel)) ≠ .zero := by
    rw [hb, convert_succ]; exact succTerm_ne_zero _
  have heQ := hePrincipal q (Support.DimensionCut.minIdx_spec q hq).2.2
  have hTopNZ : topPair (k + 1) h (convert (k + 3) (code (q.idx sel))) ≠ .zero := by
    simp only [topPair, hqNZ, ↓reduceIte]; intro he; cases he
  change _ = if topPair (k + 1) h _ = .zero then _ else _ at heQ
  rw [ite_eq_right hTopNZ] at heQ
  obtain ⟨hh0, hWB⟩ := regular_le_topPair_base (k + 1) h _ w hhw hqNZ hwr hw hf (heQ ▸ hle)
  have hzeroA (j : Fin (k + 3)) (hj : j.val < k + 1) : A.idx j = .Z := by
    simp only [A, vec_rplc_idx, sel, ite_eq_right (by omega : j.val ≠ k + 1)]
    exact (Support.DimensionCut.minIdx_spec q hq).2.2 j hj
  have heA := hePrincipal A hzeroA
  simp only [A, vec_rplc_idx, sel, ite_eq_right (by omega : k + 2 ≠ k + 1), ↓reduceIte] at heA
  have heFund : new.T.fund (.P q .Z) .Z = .P A .Z := terminal_successor_fund_zero k k (by omega) q hq b hb
  have hNewNZ : topPair (k + 1) h (convert (k + 3) (code b)) ≠ .zero := by
    by_cases hb0 : convert (k + 3) (code b) = .zero <;>
      simp only [topPair, hh0, hb0, ↓reduceIte] <;> intro he <;> cases he
  change _ = if topPair (k + 1) h _ = .zero then _ else _ at heA
  rw [ite_eq_right hNewNZ] at heA
  rw [heFund, heA]
  have hBaseW : Term.wf (.inacc (k + 1) (dropOne h)) = true :=
    Support.GeneralImageRegularLimit.inacc_image_drop_wf k _ hhR
  have hNewW := (zero_fund_invariant k (.P q .Z) hr hs).1.wf
  rw [heFund, heA] at hNewW
  apply target_le_trans hw hBaseW hNewW hWB
  change Term.le (.inacc (k + 1) (dropOne h)) (topPair (k + 1) h (convert (k + 3) (code b))) = true
  by_cases hb0 : convert (k + 3) (code b) = .zero
  · simp only [topPair, hh0, hb0, ↓reduceIte, Term.le, decide_true, Bool.true_or]
  · have hlt := topPair_order (k + 1) hhw Term.wf_zero hhw hbw
    have hZero : Term.lt .zero (convert (k + 3) (code b)) = true := (zero_lt_iff _).mpr hb0
    simp only [lt_self, decide_true, Bool.true_and, Bool.false_or, hZero] at hlt
    have hBaseLt : Term.lt (.inacc (k + 1) (dropOne h)) (topPair (k + 1) h (convert (k + 3) (code b))) = true := by
      simpa only [topPair, hh0, ↓reduceIte] using hlt
    simp only [Term.le, hBaseLt, Bool.or_true]

theorem higher_cut_le_zero_of_le_label [LargeCardinals.{u}] (k m : Nat) (hmk : m + 1 ≤ k)
    (q : Vec (new.T (k + 3)) (k + 3))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (hr : Recursive (.P q .Z)) (hs : RecursiveWF (k + 3) (.P q .Z))
    (w : Term) (hwr : Term.isRT w = true) (hw : Term.wf w = true) (hf : m + 1 ≤ Term.fT w)
    (hle : Term.le w (convert (k + 3) (code (.P q .Z))) = true) :
    Term.le w (convert (k + 3) (code (new.T.fund (.P q .Z) .Z))) = true := by
  let sel : Fin (k + 3) := ⟨m + 1, by omega⟩
  obtain ⟨b, hb⟩ := dom_one_succ (q.idx sel) ((Support.DimensionCut.minIdx_spec q hq).1.symm)
  let base := q.rplc sel .Z
  let A := q.rplc sel b
  have hz (j : Fin (k + 3)) (hj : j.val < m + 2) : base.idx j = .Z := by
    simp only [base, vec_rplc_idx]
    split
    · rfl
    · rename_i hne
      exact (Support.DimensionCut.minIdx_spec q hq).2.2 j (by change j.val ≠ m + 1 at hne; change j.val < m + 1; omega)
  have hsameQ (j : Fin (k + 3)) (hj : m + 1 < j.val) : q.idx j = base.idx j := by
    simp only [base, vec_rplc_idx, sel, ite_eq_right (by omega : j.val ≠ m + 1)]
  have hsameA (j : Fin (k + 3)) (hj : m + 1 < j.val) : A.idx j = base.idx j := by
    simp only [A, base, vec_rplc_idx, sel, ite_eq_right (by omega : j.val ≠ m + 1)]
  obtain ⟨c, hc, heBase, _⟩ := principal_insertion_context k (m + 1) hmk base hz
  have hctx : Context (m + 2) c := by
    rcases hc with hc | hc
    · exact Or.inl hc
    · exact Or.inr ⟨above_principal hc, by omega⟩
  have heQ := principal_shared_lower_image k (m + 1) hmk base q hz hsameQ c hc heBase
  have heA := principal_shared_lower_image k (m + 1) hmk base A hz hsameA c hc heBase
  have heFund : new.T.fund (.P q .Z) .Z = .P A .Z := terminal_successor_fund_zero k m (by omega) q hq b hb
  have hAw := (zero_fund_invariant k (.P q .Z) hr hs).1.wf
  rw [heFund] at hAw
  have hcw := lower_context_wf (m + 2) _ c hctx (heA ▸ hAw)
  have hWC := regular_le_lower_context (m + 2) _ c w hctx (heQ ▸ hs.wf) hwr hw (by omega) (heQ ▸ hle)
  rw [heFund, heA]
  exact target_le_trans hw hcw (heA ▸ hAw) hWC (lower_context_le _ _ c hctx (heA ▸ hAw))

theorem higher_source_closed [LargeCardinals.{u}] (k m : Nat) (hmk : m ≤ k + 1)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hmi : m < i.val) (hi : i.val ≤ k + 1)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (hbound : new.T.lt (.P xs .Z) (new.T.fund (.P q .Z) .Z))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true := by
  classical
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlr := Omega_label_recursive k _ hcr hd
  have hlw := Omega_label_recursiveWF k _ hcw hd
  have hA := (Support.GeneralImageZeroFund.zero_fund_invariant k (.P q .Z) hlr hlw).1
  obtain ⟨w, heOld, hf⟩ := principal_higher_Omega_cut_image k xs q i hi hm hr hs
  have hPsi := heOld ▸ hs.wf
  have hp := (Term.wf_psi_iff _ _).mp hPsi
  have hOmega : Term.lt Term.bigOmega w = true := by
    rcases lemma_6_1.{u}.2.2 Term.bigOmega w Term.wf_bigOmega hp.2.1 with he | he | he
    · exact he
    · have hft := congrArg Term.fT he
      simp only [Term.bigOmega, Term.fT, hf] at hft; omega
    · rw [Support.CountableTarget.regular_not_below_omega hp.1] at he; cases he
  have hLH := Omega_label_relative_bound k _ hcr hcw hd w _ hp.1 hp.2.1 hOmega hcw.wf hp.2.2.2
  obtain ⟨a, ha, haw, heA, hc, hePred⟩ := regular_lower_label_cut_context k m (by omega) q hq hlr hlw
  have hParentLt := (convert_order k _ _ hs hA).mp hbound
  have ha0 : a ≠ .zero := by
    intro he
    rw [heOld, heA, he, ite_eq_left rfl, principal_not_lt_one (by rfl) hPsi] at hParentLt
    cases hParentLt
  rw [ite_eq_right ha0] at heA
  have hPA : Term.lt (.psi w (convert (k + 3) (code (xs.idx i)))) a = true := by
    rwa [heOld, heA] at hParentLt
  have hWA : Term.le w a = true := by
    apply Classical.byContradiction; intro hnot
    have hnotLabel : ¬Term.le w (convert (k + 3) (code (.P q .Z))) = true := by
      intro hle
      apply hnot
      rw [← heA]
      by_cases hml : m + 1 ≤ k
      · exact higher_cut_le_zero_of_le_label k m hml q hq hlr hlw w hp.1 hp.2.1 (by rw [hf]; omega) hle
      · have hmEq : m = k := by omega
        subst m
        exact middle_cut_le_zero_of_le_label k q hq hlr hlw w hp.1 hp.2.1 (by rw [hf]; omega) hle
    have hLW : Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
      rcases lemma_6_1.{u}.2.2 _ _ hlw.wf hp.2.1 with he | he | he
      · exact he
      · exact False.elim (hnotLabel (by rw [← he]; simp [Term.le]))
      · exact False.elim (hnotLabel (by simp only [Term.le, he, Bool.or_true]))
    have sw := sem_of_wf.{u} hp.2.1
    have hLP : Term.lt (convert (k + 3) (code (.P q .Z)))
        (.psi w (convert (k + 3) (code (xs.idx i)))) = true := by
      apply (lt_iff_V hlw.wf hPsi).mpr
      exact (theorem_4_9 ⟨sw.isR_iff.mp hp.1, sw.lt_Λ₀⟩ _ _).mp
        ⟨(H_bound_iff_C w _ _ hp.1 hp.2.1 hlw.wf hcw.wf).mp hLH,
          (lt_iff_V hlw.wf hp.2.1).mp hLW⟩
    have hPL : Term.lt (.psi w (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (.P q .Z))) = true := by
      rw [← heOld]
      exact (convert_order k _ _ hs hlw).mp
        (new.T_trans _ _ _ hbound (fund_lt _ .Z (by intro he; cases he)))
    have hbad := lemma_6_1.{u}.2.1 _ _ _ hlw.wf hPsi hlw.wf hLP hPL
    rw [lt_self] at hbad; cases hbad
  have hAV : Term.lt a (layerCut m a) = true := by
    simp only [layerCut, ha0, ↓reduceIte]
    change Term.lt a (regular m a) = true
    rw [context_lt_regular (ha.resolve_left ha0) (above_principal (ha.resolve_left ha0))]
    simp [Term.le]
  exact ⟨_, hc, H_self_of_cut_below_zero_context w _ a _ hc.regular hc.cutWf haw hPsi hePred hWA hAV hPA⟩

end Support.GeneralImageHigherDiagonal

namespace Support.GeneralImageDiagonalPartition

open new Support.OTQuotient Support.CountableSource
open Support.SourceFundOrder Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageWFInvariant
open Support.GeneralImageContextBoundDiagonal Support.GeneralImageStrictHighestDiagonal
open Support.GeneralImageCriticalDiagonal
open Support.GeneralImageHighestDiagonal
open Support.GeneralImageCoefficients
open Support.GeneralImageRawOrder Support.GeneralImageLimitBranches
open Support.GeneralImageOmegaSpine
open Support.GeneralImageHighestContextDiagonal
open OCF.Jaeger

universe u

theorem vector_interval_higher_same {lam n : Nat}
    (xs lo ys : Vec (new.T lam) n) (i : Fin n)
    (hh : ∀ j, i.val < j.val → lo.idx j = xs.idx j)
    (hlo : Vec.le lo ys) (hhi : Vec.le ys xs) :
    ∀ j, i.val < j.val → ys.idx j = xs.idx j := by
  induction xs with
  | nil => exact i.elim0
  | snoc n xs x ih =>
    cases lo with
    | snoc _ lo a =>
      cases ys with
      | snoc _ ys y =>
        by_cases hin : i.val < n
        · let ii : Fin n := ⟨i.val, hin⟩
          have heI : i = ii.castSucc := Fin.ext rfl
          have hax : a = x := by simpa only [vec_snoc_idx_last] using hh (Fin.last n) hin
          have hyx : y = x := source_le_antisymm (vec_le_last ys xs y x hhi)
            (by simpa only [hax] using vec_le_last lo ys a y hlo)
          subst a; subst y
          have hlo' : Vec.le lo ys := (vec_same_last_le lo ys x).mp hlo
          have hhi' : Vec.le ys xs := (vec_same_last_le ys xs x).mp hhi
          have hlow := ih lo ys ii
            (fun j hj => by simpa only [vec_snoc_idx_cast] using hh j.castSucc hj) hlo' hhi'
          intro j hj
          by_cases hjn : j.val < n
          · let jj : Fin n := ⟨j.val, hjn⟩
            have heJ : j = jj.castSucc := Fin.ext rfl
            simpa only [heJ, vec_snoc_idx_cast] using hlow jj hj
          · have heJ : j = Fin.last n := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
            rw [heJ, vec_snoc_idx_last, vec_snoc_idx_last]
        · intro j hj
          have := i.isLt; have := j.isLt; omega

theorem diagonal_zero_label_or_critical (k m : Nat) (hmk : m ≤ k + 1)
    (xs q : Vec (new.T (k + 3)) (k + 3))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (b : new.T (k + 3)) (hb : q.idx ⟨m + 1, by omega⟩ = Support.SourceSuccessor.succ b)
    (hdiag : Vec.lt xs q) :
    new.T.lt (.P xs .Z) (new.T.fund (.P q .Z) .Z) ∨
      (xs.idx ⟨m + 1, by omega⟩ = b ∧ ∀ j, m + 1 < j.val → xs.idx j = q.idx j) := by
  let sel : Fin (k + 3) := ⟨m + 1, by omega⟩
  let base := q.rplc sel b
  have hzero : ∀ j, j.val < m + 1 → base.idx j = .Z := by
    intro j hj
    simp only [base, vec_rplc_idx, sel, ite_eq_right (by change j.val ≠ m + 1; omega)]
    exact (Support.DimensionCut.minIdx_spec q hq).2.2 j hj
  have hf0 : new.T.fund (.P q .Z) .Z = .P base .Z := by
    rw [fund_regular_bound q (by omega) hq, hb,
      Support.SourceSuccessor.fund_succ]
    congr 1; apply vec_ext; intro j
    simp only [vec_rplc_idx]
    split
    · exact (hzero j (by omega)).symm
    · simp only [base, sel, vec_rplc_idx]
  have finish (hlo : Vec.le base xs) :
      xs.idx sel = b ∧ ∀ j, m + 1 < j.val → xs.idx j = q.idx j := by
    have hh : ∀ j, sel.val < j.val → base.idx j = q.idx j := by
      intro j hj; simp only [base, vec_rplc_idx, ite_eq_right (by omega : j.val ≠ sel.val)]
    have hcoord := vector_interval q base xs sel (Support.DimensionCut.minIdx_spec q hq).2.2 hh hlo hdiag
    have hloB : new.T.le b (xs.idx sel) := by simpa only [base, vec_rplc_idx, ↓reduceIte] using hcoord.1
    have hhiB : new.T.le (xs.idx sel) b := by
      apply (Support.SourceSuccessor.lt_succ_iff_le _ b).mp
      simpa only [sel, hb] using hcoord.2.1
    exact ⟨source_le_antisymm hhiB hloB,
      vector_interval_higher_same q base xs sel hh hlo (Or.inl hdiag)⟩
  rcases new.Vec_total xs base with hl | hl | he
  · apply Or.inl; rw [hf0]
    simp only [new.T.lt, new.compareT, hl]
  · exact Or.inr (finish (Or.inl hl))
  · exact Or.inr (finish (Or.inr (by rw [he]; exact new.Vec_refl _)))

theorem noncritical_diagonal_context_bound (k m : Nat) (hmk : m ≤ k + 1)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (b : new.T (k + 3)) (hb : q.idx ⟨m + 1, by omega⟩ = Support.SourceSuccessor.succ b)
    (hdiag : Vec.lt xs q)
    (hn : ¬(xs.idx ⟨m + 1, by omega⟩ = b ∧ ∀ j, m + 1 < j.val → xs.idx j = q.idx j)) :
    new.T.le (.P (xs.rplc i .Z) .Z) (new.T.fund (.P q .Z) .Z) := by
  have hp : new.T.lt (.P xs .Z) (new.T.fund (.P q .Z) .Z) := by
    rcases diagonal_zero_label_or_critical k m hmk xs q hq b hb hdiag with hp | hp
    · exact hp
    · exact False.elim (hn hp)
  have hc0 : xs.idx i ≠ .Z := by
    have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
    intro he; rw [he, new.T.dom] at hd; cases hd
  have hzero : new.compareT (.Z : new.T (k + 3)) (xs.idx i) = .lt := by
    cases he : xs.idx i with
    | Z => exact False.elim (hc0 he)
    | P => rfl
  have herase : new.T.lt (.P (xs.rplc i .Z) .Z) (.P xs .Z) := by
    simp only [new.T.lt, new.compareT, compareVec_rplc_lt xs i .Z hzero]
  exact Or.inl (new.T_trans _ _ _ herase hp)

end Support.GeneralImageDiagonalPartition

namespace Support.GeneralImageCountableObstructions

open new Support.OTQuotient Support.CountableSource
open Support.SourceFundOrder Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageCoefficients Support.GeneralImageRawOrder
open Support.GeneralImageWFInvariant
open Support.GeneralImageDiagonalPartition
open Support.GeneralImageLabelClosure Support.GeneralImageCountableInheritance
open Support.GeneralImageCriticalZeroDiagonal
open Support.GeneralImageStrictHighestDiagonal
open Support.GeneralImageHigherSparseDiagonal
open Support.GeneralImageHigherDiagonal
open Support.GeneralImageOmegaCoefficients Support.GeneralImageContextBoundDiagonal
open OCF.Jaeger

universe u

theorem higher_selector_not_critical (k m : Nat) (hmk : m ≤ k + 1)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hmi : m < i.val)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (b : new.T (k + 3)) (hb : q.idx ⟨m + 1, by omega⟩ = Support.SourceSuccessor.succ b) :
    ¬(xs.idx ⟨m + 1, by omega⟩ = b ∧ ∀ j, m + 1 < j.val → xs.idx j = q.idx j) := by
  rintro ⟨hp, hh⟩
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hmass := Omega_label_mass_le (xs.idx i) hd
  by_cases hi : i.val = m + 1
  · have he : i = ⟨m + 1, by omega⟩ := Fin.ext hi
    rw [he, hp] at hmass
    have hidx := mass_idx_lt q .Z (⟨m + 1, by omega⟩ : Fin (k + 3))
    rw [hb, mass_succ] at hidx
    omega
  · have he := hh i (by omega)
    rw [he] at hmass
    have hidx := mass_idx_lt q .Z i
    omega

theorem higher_selector_zero_label_bound (k m : Nat) (hmk : m ≤ k + 1)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hmi : m < i.val)
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (hd : new.T.dom (.P xs .Z) = .omega) :
    new.T.lt (.P xs .Z) (new.T.fund (.P q .Z) .Z) ∧
      new.T.le (.P (xs.rplc i .Z) .Z) (new.T.fund (.P q .Z) .Z) := by
  have hdiag : Vec.lt xs q := by
    by_cases hl : Vec.lt xs q
    · exact hl
    · simp only [new.T.dom, ↓reduceIte, hm, hl] at hd; cases hd
  obtain ⟨b, hb⟩ := dom_one_succ (q.idx ⟨m + 1, by omega⟩)
    ((Support.DimensionCut.minIdx_spec q hq).1.symm)
  have hn := higher_selector_not_critical k m hmk xs q i hmi hm b hb
  constructor
  · rcases diagonal_zero_label_or_critical k m hmk xs q hq b hb hdiag with hl | hc
    · exact hl
    · exact False.elim (hn hc)
  · exact noncritical_diagonal_context_bound k m hmk xs q i hm hq b hb hdiag hn

end Support.GeneralImageCountableObstructions

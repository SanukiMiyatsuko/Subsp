import Subsp.Support.Cofinality

/-! Omega spines, dominated coefficients, label cuts (`CutFund`) and Omega fund at the label cut. -/

namespace Support.GeneralImageHighestDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion
open Support.GeneralImageCofinalityBounds Support.GeneralImageCofinalityCoefficients
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageZeroFund
open Support.GeneralImageCountableLayers Support.GeneralImageOmegaCoefficients
open Support.GeneralImageCountableInheritance Support.GeneralImageMiddleSums
open Support.GeneralImageOmegaContext

universe u

theorem highest_regular_fund_shape (k : Nat) (b t : new.T (k + 3)) :
    new.T.fund (topNode k (Support.SourceSuccessor.succ b)) t =
      .P ((lastVec (k + 2) b).rplc ⟨k + 1, by omega⟩ t) .Z := by
  have hm : new.T.domVecMinIdx (lastVec (k + 2) (Support.SourceSuccessor.succ b)) =
      some (⟨k + 2, by omega⟩, .one) := by
    simp only [minIdx_lastVec, Support.SourceSuccessor.dom_succ, reduceCtorEq, ↓reduceIte]
    rfl
  rw [topNode, fund_regular_bound _ (by omega : k + 1 + 1 < k + 3) hm t,
    lastVec_idx, ite_eq_left rfl, Support.SourceSuccessor.fund_succ]
  rw [show (⟨k + 1 + 1, by omega⟩ : Fin (k + 3)) = Fin.last (k + 2) from rfl,
    Support.SourceOmegaHighest.lastVec_replace_last]

theorem highest_regular_fund_zero (k : Nat) (b : new.T (k + 3)) :
    new.T.fund (topNode k (Support.SourceSuccessor.succ b)) .Z = topNode k b := by
  rw [highest_regular_fund_shape, topNode]
  congr 1; apply vec_ext; intro j
  simp only [vec_rplc_idx]
  split
  · rw [lastVec_idx, ite_eq_right (by omega)]
  · rfl

theorem highest_regular_image (k : Nat) (b : new.T (k + 3)) :
    convert (k + 3) (code (topNode k (Support.SourceSuccessor.succ b))) =
      pairCut (k + 1) (convert (k + 3) (code b)) := by
  rw [convert_topNode k _ (Support.SourceSuccessor.succ_ne_zero b), convert_succ]
  by_cases hb : convert (k + 3) (code b) = .zero
  · simp [hb, pairCut, succTerm, dropOne, Term.one]
  · simp only [drop_succ _ hb, pairCut, hb, ↓reduceIte]

theorem highest_regular_fund_image (k : Nat) (b t : new.T (k + 3)) (ht : t ≠ .Z) :
    convert (k + 3) (code (new.T.fund (topNode k (Support.SourceSuccessor.succ b)) t)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code b))) (dropOne (convert (k + 3) (code t))) := by
  have htI : convert (k + 3) (code t) ≠ .zero := by
    intro he; exact ht (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  let xs := (lastVec (k + 2) b).rplc ⟨k + 1, by omega⟩ t
  let args := arguments (k + 3) (trim (codes xs))
  have htop : args[k + 2]?.getD .zero = convert (k + 3) (code b) := by
    rw [converted_coordinate xs ⟨k + 2, by omega⟩]
    simp [xs, vec_rplc_idx, lastVec_idx]
  have hmid : args[k + 1]?.getD .zero = convert (k + 3) (code t) := by
    rw [converted_coordinate xs ⟨k + 1, by omega⟩]; simp [xs, vec_rplc_idx]
  have hzero : ∀ j, j < k + 1 → args[j]?.getD .zero = .zero := by
    intro j hj; rw [converted_coordinate xs ⟨j, by omega⟩]
    simp only [xs, vec_rplc_idx, ite_eq_right (by omega : j ≠ k + 1), lastVec_idx,
      ite_eq_right (by omega : j ≠ k + 2), code, convert]
  rw [highest_regular_fund_shape, convert_principal, principal_as_layers]
  change lower (k + 1) args (topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)) = _
  rw [htop, hmid, lower_keep _ _ _ (by simp [topPair, htI]) hzero]
  simp [topPair, pairCut, htI]

theorem highest_regular_fund_at_cut (k : Nat) (b t : new.T (k + 3))
    (hb : RecursiveWF (k + 3) b) (ht : RecursiveWF (k + 3) t) (ht0 : t ≠ .Z)
    (hroot : Term.wf (.psi (pairCut (k + 1) (convert (k + 3) (code b)))
      (dropOne (convert (k + 3) (code t)))) = true) :
    RecursiveWF (k + 3) (new.T.fund (topNode k (Support.SourceSuccessor.succ b)) t) := by
  have hw : Term.wf (convert (k + 3) (code (new.T.fund (topNode k (Support.SourceSuccessor.succ b)) t))) = true := by
    rw [highest_regular_fund_image k b t ht0]; exact hroot
  rw [highest_regular_fund_shape, RecursiveWF]
  refine ⟨?_, recursive_zero _ _, ?_⟩
  · intro i
    simp only [vec_rplc_idx]
    split
    · exact ht
    · rw [lastVec_idx]; split
      · exact hb
      · exact recursive_zero _ _
  · rwa [highest_regular_fund_shape] at hw

theorem highest_base_image (k : Nat) (b : new.T (k + 3)) :
    convert (k + 3) (code (topNode k b)) =
      if convert (k + 3) (code b) = .zero then Term.one
      else topPair (k + 1) (convert (k + 3) (code b)) .zero := by
  by_cases hb : convert (k + 3) (code b) = .zero
  · have hbZ : b = .Z := code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp hb)
    have he : lastVec (k + 2) (.Z : new.T (k + 3)) = lowVec (k + 2) .Z := by
      apply vec_ext; intro j; simp [lastVec_idx, lowVec_idx]
    rw [ite_eq_left hb, hbZ, topNode, he, convert_low_principal, code, convert]
    rfl
  · have hbZ : b ≠ .Z := by intro he; rw [he, code, convert] at hb; exact hb rfl
    rw [ite_eq_right hb, convert_topNode k b hbZ]
    simp [topPair, hb]

theorem highest_cut_base_support (k : Nat) (b : new.T (k + 3)) (v : Term) {z : Term}
    (hz : z ∈ Term.H v (pairCut (k + 1) (convert (k + 3) (code b)))) :
    z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code (topNode k b))) := by
  by_cases hb : convert (k + 3) (code b) = .zero
  · simp only [pairCut, hb, ↓reduceIte] at hz
    rcases H_inacc_support (k + 1) .zero hz with he | he
    · exact Or.inl he
    · cases he
  · simp only [pairCut, hb, ↓reduceIte] at hz
    rcases H_inacc_support (k + 1) _ hz with he | he
    · exact Or.inl he
    · rcases H_succ_support _ he with he | he
      · exact Or.inl he
      · apply Or.inr
        rw [highest_base_image, ite_eq_right hb]
        simp only [topPair, hb, ↓reduceIte, Term.H]
        exact List.mem_append_right _ he

theorem diagonal_parent_relative_above [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (q : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (n : Nat) (hnat : 0 < n)
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat n)))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))))
      (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))) = true := by
  classical
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  let a := new.T.iter (new.T.fund (xs.idx i)) (new.T.ofNat (n + 1))
  have ha0 : a ≠ .Z := by
    dsimp only [a]
    rw [iter_ofNat_succ]
    exact domOmega_fund_ne_zero _ _ hd
  have hf : new.T.fund (.P xs .Z) (new.T.ofNat n) = .P (xs.rplc i a) .Z := by
    simp only [new.T.fund, ↓reduceIte, hm, hdiag, GetElem.getElem]
    rw [← iter_ofNat_succ (new.T.fund (xs.idx i)) n]
  have hib : i.val ≤ k + 1 := by
    apply Classical.byContradiction; intro he
    have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    exact no_diagonal_highest k xs hs (hi ▸ hchildR) (hi ▸ hm) hdiag
  have hcNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have haNZ : convert (k + 3) (code a) ≠ .zero := by
    intro he; exact ha0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (xs.idx i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff _ _ _).mpr ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (xs.idx i)) .Z)
      hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    rw [heSource, fund_low_Omega (k + 2) _ _ q hd, H_low_empty_above_Omega v hOmega]
    rfl
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow a hcNZ haNZ
      (Omega_image_drop k _ hchildR (hcoords i) hd) hIsLow
    have heFund := hf ▸ heNew
    have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
    rw [heOld, heFund] at hlt
    have hparentLtChild := (convert_order k _ _ hs (hcoords i)).mp
      (diagonal_principal_lt_argument xs _ hchildR hd hdiag)
    have ctx (z : Term)
        (hz : z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n))))) :
        z ∈ Term.H v w ∧ z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) := by
      rw [heFund] at hz
      rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz
        with ⟨hw, ho⟩ | ⟨_, hroot, _⟩
      · exact ⟨hw, heOld ▸ ho⟩
      · have hback := (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
        have hfalse := lemma_6_1.{u}.2.1 _ _ _ (hcoords i).wf hs.wf (hcoords i).wf hback hparentLtChild
        rw [lt_self] at hfalse; cases hfalse
    by_cases hex : ∃ j : Fin (k + 3), i ≠ j ∧ xs.idx j ≠ .Z
    · obtain ⟨j, hij, hj⟩ := hex
      have ht : new.T.ofNat (lam := k + 3) n ≠ .Z := by
        cases n with
        | zero => omega
        | succ n => intro he; cases he
      have hdom : new.T.dom (.P xs .Z) = .omega := by
        simp only [new.T.dom, ↓reduceIte, hm, hdiag]
      exact closed_of_updated_coefficients k v _ _ hs hn (omega_image_head_ne_one k _ hs hdom)
        (by rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _)
        (by rw [hf, convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _)
        (fun t htS => positive_principal_subterm_gap xs i j hij hc0 hj _ ht htS)
        (fun z hz => Or.inr (Or.inl (ctx z hz).2)) hH
    · have hother : ∀ j : Fin (k + 3), j.val ≠ i.val → xs.idx j = .Z := by
        intro j hj; apply Classical.byContradiction; intro hz
        exact hex ⟨j, fun he => hj (congrArg Fin.val he.symm), hz⟩
      have hip : 0 < i.val := by
        by_cases hi0 : i.val = 0
        · have he : xs = lowVec (k + 2) (xs.idx i) := by
            apply vec_ext; intro j; rw [lowVec_idx]
            by_cases hj : j.val = 0
            · rw [ite_eq_left hj]
              have hji : j = i := Fin.ext (hj.trans hi0.symm); rw [hji]
            · rw [ite_eq_right hj]; exact hother j (by rw [hi0]; exact hj)
          exact False.elim (hIsLow (by rw [he, convert_low_principal]; simp only [lowVec_idx, hi0, ↓reduceIte]))
        · omega
      have heSingle := convert_positive_single k xs i hip hib hlow
        (fun j hj => hother j (by omega)) hc0
      rw [Omega_image_drop k _ hchildR (hcoords i) hd] at heSingle
      have hNewW : w = .inacc i.val .zero := by
        rw [heOld] at heSingle; exact Term.psi.inj heSingle |>.1
      apply (Term.allLt_iff _ _).mpr; intro z hz
      have hctx := (ctx z hz).1
      rw [hNewW] at hctx
      simp [Term.H, Term.hOne, hOmega] at hctx

end Support.GeneralImageHighestDiagonal

namespace Support.GeneralImageRegularDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion
open Support.GeneralImageRelativePredecessor Support.GeneralImageCofinalityCoefficients
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageZeroFund
open Support.GeneralImageHighestDiagonal Support.GeneralImageOmegaContext
open Support.GeneralImageCountableRecursion
open Support.GeneralImageCountableLayers Support.GeneralImageCountableInheritance

universe u

theorem lower_coordinate_context (j m : Nat) (hm : m < j)
    (xs : List Term) (a : Term) (hctx : Context j a) :
    ∃ c, Context (m + 1) c ∧ ∀ ys : List Term,
      (∀ i, m < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero) →
      lower j ys a = lower (m + 1) ys c := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    by_cases he : m = j
    · subst m; exact ⟨a, hctx, fun _ _ => rfl⟩
    · obtain ⟨c, hc, hformula⟩ := ih (by omega) _ (step_shape _ (context_above hctx))
      refine ⟨c, hc, ?_⟩
      intro ys hsame
      rw [lower_succ, hsame j (by omega) (by omega)]
      exact hformula ys (fun i him hij => hsame i him (by omega))

theorem lower_zero_block (j : Nat) (hj : 0 < j) (xs : List Term) (a : Term)
    (hzero : ∀ i, i < j → xs[i]?.getD .zero = .zero) :
    lower j xs a = if a = .zero then Term.one else a := by
  by_cases ha : a = .zero
  · rw [ite_eq_left ha, ha]
    rw [Support.DimensionImage.lower_zero_context j xs hj (fun i _ hi => hzero i hi), hzero 0 hj]
    rfl
  · rw [ite_eq_right ha]
    exact lower_keep j xs a ha hzero

theorem principal_insertion_context (k m : Nat) (hm : m ≤ k)
    (xs : Vec (new.T (k + 3)) (k + 3))
    (hzero : ∀ i, i.val < m + 1 → xs.idx i = .Z) :
    ∃ a, Above m a ∧
      convert (k + 3) (code (.P xs .Z)) = (if a = .zero then Term.one else a) ∧
      ∀ t : new.T (k + 3), t ≠ .Z →
        convert (k + 3) (code (.P (xs.rplc ⟨m, by omega⟩ t) .Z)) =
          step m a (convert (k + 3) (code t)) := by
  let args := arguments (k + 3) (trim (codes xs))
  let top := topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)
  obtain ⟨a, ha, hformula⟩ := lower_coordinate_context (k + 1) m (by omega) args top
    (topPair_context _ _ _)
  refine ⟨a, context_above ha, ?_, ?_⟩
  · rw [convert_principal, principal_as_layers]
    change lower (k + 1) args top = _
    rw [hformula args (fun _ _ _ => rfl)]
    exact lower_zero_block (m + 1) (by omega) args a (fun i hi => by
      rw [converted_coordinate xs ⟨i, by omega⟩, hzero ⟨i, by omega⟩ hi, code, convert])
  · intro t ht
    let ys := xs.rplc ⟨m, by omega⟩ t
    let newArgs := arguments (k + 3) (trim (codes ys))
    have hs (i : Nat) (hi : m < i) (hij : i < k + 3) :
        newArgs[i]?.getD .zero = args[i]?.getD .zero := by
      rw [converted_coordinate ys ⟨i, hij⟩, converted_coordinate xs ⟨i, hij⟩]
      simp only [ys, vec_rplc_idx, ite_eq_right (by omega : i ≠ m)]
    have hnz : convert (k + 3) (code t) ≠ .zero := by
      intro he; exact ht (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
    rw [convert_principal, principal_as_layers]
    change lower (k + 1) newArgs
      (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) = _
    rw [hs (k + 2) (by omega) (by omega), hs (k + 1) (by omega) (by omega)]
    rw [hformula newArgs (fun i hi hij => hs i hi (by omega)), lower_succ]
    rw [converted_coordinate ys ⟨m, by omega⟩]
    simp only [ys, vec_rplc_idx, ↓reduceIte]
    rw [lower_keep m newArgs _ (step_ne_zero_of_argument m _ _ hnz) (fun i hi => by
      rw [converted_coordinate ys ⟨i, by omega⟩]
      simp only [ys, vec_rplc_idx, ite_eq_right (by omega : i ≠ m)]
      rw [hzero ⟨i, by omega⟩ (by change i < m + 1; omega), code, convert])]

theorem layerCut_base_support (m : Nat) (a v : Term) {z : Term}
    (hz : z ∈ Term.H v (layerCut m a)) :
    z = .zero ∨ z ∈ Term.H v (if a = .zero then Term.one else a) := by
  by_cases ha : a = .zero
  · simp only [layerCut, ha, ↓reduceIte] at hz
    rcases H_inacc_support m .zero hz with he | he
    · exact Or.inl he
    · cases he
  · simp only [layerCut, ha, ↓reduceIte] at hz
    rcases H_inacc_support m _ hz with he | he
    · exact Or.inl he
    · rcases H_succ_support _ he with he | he
      · exact Or.inl he
      · exact Or.inr (by simpa only [ha, ↓reduceIte] using he)

end Support.GeneralImageRegularDiagonal

namespace Support.GeneralImageOmegaSpine

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageRegularDiagonal Support.GeneralImageHighestDiagonal
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageZeroFund
open Support.GeneralImageCountableRecursion Support.GeneralImageCountableLayers
open Support.GeneralImageOmegaCoefficients
open Support.GeneralImageUpperOmega Support.GeneralImageHighOmega Support.SourceOmegaHighest
open Support.GeneralImageMiddleSums Support.GeneralImageCountableInheritance
open Support.GeneralImageRelativePredecessor

universe u

def InsertedCoefficient (v cut a z : Term) : Prop :=
  z = .zero ∨ z = a ∨ z = dropOne a ∨ z ∈ Term.H v a ∨ z ∈ Term.H v cut

structure CutFund (k : Nat) (s : new.T (k + 3)) (cut : Term) : Prop where
  regular : Term.isRT cut = true
  cutWf : Term.wf cut = true
  selfEmpty : Term.H cut cut = []
  fundWf : ∀ t, RecursiveWF (k + 3) t →
    Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true →
    RecursiveWF (k + 3) (new.T.fund s t)
  zeroSupport : ∀ z, z ∈ Term.H cut (convert (k + 3) (code (new.T.fund s .Z))) → z = .zero
  cutSupport : ∀ v, Term.lt Term.bigOmega v = true → ∀ z, z ∈ Term.H v cut →
    z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code (new.T.fund s .Z)))
  fundSupport : ∀ t, t ≠ .Z → ∀ v z,
    z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) →
    InsertedCoefficient v cut (convert (k + 3) (code t)) z
  baseSupport : ∀ v z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s .Z))) →
    z = .zero ∨ z ∈ Term.H v cut

theorem inserted_psi_support (v cut a z : Term)
    (hz : z ∈ Term.H v (.psi cut a)) :
    z = a ∨ z ∈ Term.H v a ∨ z ∈ Term.H v cut := H_psi_support hz

theorem layerCut_contains_base (m : Nat) (a v : Term) {z : Term}
    (hz : z ∈ Term.H v (if a = .zero then Term.one else a)) :
    z = .zero ∨ z ∈ Term.H v (layerCut m a) := by
  by_cases ha : a = .zero
  · rw [ite_eq_left ha] at hz; exact Or.inl (H_one_mem hz)
  · rw [ite_eq_right ha] at hz
    apply Or.inr
    simp only [layerCut, ha, ↓reduceIte, Term.H, Support.OT2.H_succTerm]
    exact List.mem_append_right _ (List.mem_append_left _ hz)

theorem regular_lower_cutFund_image [LargeCardinals.{u}] (k m : Nat)
    (hmk : m ≤ k) (xs : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, by omega⟩, .one))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P xs .Z) cut ∧ Term.fT cut = m ∧
      (∀ t, t ≠ .Z → ∃ a, convert (k + 3) (code (new.T.fund (.P xs .Z) t)) = .psi cut a) ∧
      ∀ j, m < j → Term.lt (convert (k + 3) (code (new.T.fund (.P xs .Z) .Z))) (.inacc j .zero) = true →
        Term.lt cut (.inacc j .zero) = true := by
  let sel : Fin (k + 3) := ⟨m + 1, by omega⟩
  let ins : Fin (k + 3) := ⟨m, by omega⟩
  let s := new.T.P xs .Z
  have hdOne := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ i, RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1
  let p := new.T.fund (xs.idx sel) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hcoords sel) hdOne
  let base := xs.rplc sel p
  have hzBase : ∀ i : Fin (k + 3), i.val < m + 1 → base.idx i = .Z := by
    intro i hi
    simp only [base, vec_rplc_idx, sel, ite_eq_right (by change i.val ≠ m + 1; omega)]
    exact hlow i hi
  have hf (t : new.T (k + 3)) : new.T.fund s t = .P (base.rplc ins t) .Z := by
    dsimp only [s]; rw [fund_regular_bound xs (by omega) hm t]
  have hfZero : new.T.fund s .Z = .P base .Z := by
    rw [hf]; congr 1; apply vec_ext; intro i
    simp only [vec_rplc_idx, ins]
    split
    · exact (hzBase i (by change i.val < m + 1; omega)).symm
    · rfl
  obtain ⟨a, ha, heBase, heInsert⟩ := principal_insertion_context k m hmk base hzBase
  have hB : RecursiveWF (k + 3) (.P base .Z) := hfZero ▸ (zero_fund_invariant k s hr hs).1
  have hwA : Term.wf a = true := by
    by_cases ha0 : a = .zero
    · simp [ha0, Term.wf]
    · simpa only [heBase, ha0, ↓reduceIte] using hB.wf
  let cut := layerCut m a
  have hCutW : Term.wf cut = true := layerCut_wf m a ha hwA
  have hCutR : Term.isRT cut = true := layerCut_regular m a
  have hCutH : Term.H cut cut = [] := by
    by_cases ha0 : a = .zero
    · by_cases hm0 : m = 0
      · simp [cut, layerCut, ha0, hm0, Term.H]
      · exact layerCut_H_self_empty m (by omega) a ha hwA
    · simpa only [cut, layerCut, ha0, ↓reduceIte, regular] using regular_H_self_empty m a ha hwA
  let arg (t : new.T (k + 3)) := if m = 0 ∧ a = .zero then convert (k + 3) (code t)
    else dropOne (convert (k + 3) (code t))
  have hNew (t : new.T (k + 3)) (ht0 : t ≠ .Z) :
      convert (k + 3) (code (new.T.fund s t)) = .psi cut (arg t) := by
    rw [hf, heInsert t ht0]
    have htNZ : convert (k + 3) (code t) ≠ .zero := by
      intro he; exact ht0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
    by_cases ha0 : a = .zero <;> by_cases hm0 : m = 0 <;>
      simp [step, cut, layerCut, regular, arg, ha0, hm0, htNZ, Term.bigOmega]
  refine ⟨cut, ⟨hCutR, hCutW, hCutH, ?_, ?_, ?_, ?_, ?_⟩,
    (by simp only [cut, layerCut, Term.fT]), ?_, ?_⟩
  · intro t ht hHt
    by_cases ht0 : t = .Z
    · rw [ht0, hfZero]; exact hB
    · have hArg : Term.wf (arg t) = true ∧ Term.allLt (Term.H cut (arg t)) (arg t) = true := by
        dsimp only [arg]; split
        · exact ⟨ht.wf, hHt⟩
        · exact ⟨dropOne_wf ht.wf, H_drop_bound cut _ ht.wf hHt⟩
      have hw := (Term.wf_psi_iff _ _).mpr ⟨hCutR, hCutW, hArg.1, hArg.2⟩
      have hwFull := hNew t ht0 ▸ hw
      rw [hf, RecursiveWF]
      refine ⟨?_, recursive_zero _ _, ?_⟩
      · intro i; simp only [vec_rplc_idx]; split
        · exact ht
        · simp only [base, vec_rplc_idx]; split
          · exact hp
          · exact hcoords i
      · rwa [hf] at hwFull
  · intro z hz
    rw [hfZero, heBase] at hz
    by_cases ha0 : a = .zero
    · rw [ite_eq_left ha0] at hz; exact H_one_mem hz
    · rw [ite_eq_right ha0, layerCut_H_context_empty m a ha hwA] at hz; cases hz
  · intro v _ z hz
    rcases layerCut_base_support m a v hz with he | he
    · exact Or.inl he
    · exact Or.inr (by rw [hfZero, heBase]; exact he)
  · intro t ht0 v z hz
    rw [hNew t ht0] at hz
    rcases inserted_psi_support v cut _ z hz with he | he | he
    · dsimp only [arg] at he; split at he
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl he))
    · have hzT : z ∈ Term.H v (convert (k + 3) (code t)) := by
        dsimp only [arg] at he; split at he
        · exact he
        · exact Support.OT2.mem_H_dropOne he
      exact Or.inr (Or.inr (Or.inr (Or.inl hzT)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
  · intro v z hz
    rw [hfZero, heBase] at hz
    exact layerCut_contains_base m a v hz
  · intro t ht0
    exact ⟨arg t, hNew t ht0⟩
  · intro j hj hBase
    by_cases ha0 : a = .zero
    · simp [cut, layerCut, ha0, Term.lt, hj]
    · rw [hfZero, heBase, ite_eq_right ha0] at hBase
      have hp := above_principal (ha.resolve_left ha0)
      simpa only [cut, layerCut, ha0, ↓reduceIte, Term.lt, hj,
        succ_principal hp] using hBase

theorem regular_lower_cutFund [LargeCardinals.{u}] (k m : Nat)
    (hmk : m ≤ k) (xs : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, by omega⟩, .one))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P xs .Z) cut := by
  obtain ⟨cut, hc, _, _, _⟩ := regular_lower_cutFund_image k m hmk xs hm hr hs
  exact ⟨cut, hc⟩

theorem highest_regular_cutFund_at [LargeCardinals.{u}] (k : Nat) (b : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (topNode k (Support.SourceSuccessor.succ b))) :
    CutFund k (topNode k (Support.SourceSuccessor.succ b)) (pairCut (k + 1) (convert (k + 3) (code b))) := by
  have hb : RecursiveWF (k + 3) b := (recursive_succ_iff _ _).mp (high_recursive_image k _ hs)
  let cut := pairCut (k + 1) (convert (k + 3) (code b))
  have hCutW : Term.wf cut = true := by
    change Term.wf (pairCut (k + 1) (convert (k + 3) (code b))) = true
    rw [← highest_regular_image k b]; exact hs.wf
  have hCutR : Term.isRT cut = true := pairCut_regular _ _
  have hB := topNode_recursiveWF k b hb
  have hCutH : Term.H cut cut = [] := pairCut_H_self_empty (k + 1) (by omega) _ hb.wf hCutW
  refine ⟨hCutR, hCutW, hCutH, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hHt
    by_cases ht0 : t = .Z
    · rw [ht0, highest_regular_fund_zero]; exact hB
    · exact highest_regular_fund_at_cut k b t hb ht ht0
        ((Term.wf_psi_iff _ _).mpr ⟨hCutR, hCutW, dropOne_wf ht.wf, H_drop_bound cut _ ht.wf hHt⟩)
  · intro z hz
    rw [highest_regular_fund_zero, highest_base_image] at hz
    split at hz
    · exact H_one_mem hz
    · rw [(topPair_zero_bound (k + 1) (by omega) _ hb.wf hCutW).2] at hz
      cases hz
  · intro v _ z hz
    rw [highest_regular_fund_zero]
    exact highest_cut_base_support k b v hz
  · intro t ht0 v z hz
    rw [highest_regular_fund_image k b t ht0] at hz
    rcases H_psi_support hz with he | he | he
    · exact Or.inr (Or.inr (Or.inl he))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Support.OT2.mem_H_dropOne he))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
  · intro v z hz
    rw [highest_regular_fund_zero] at hz
    by_cases hb0 : b = .Z
    · rw [highest_base_image] at hz
      simp only [hb0, code, convert, ↓reduceIte] at hz
      exact Or.inl (H_one_mem hz)
    · rw [convert_topNode k b hb0] at hz
      rcases H_inacc_support (k + 1) _ hz with he | he
      · exact Or.inl he
      · apply Or.inr
        change z ∈ Term.H v (pairCut (k + 1) (convert (k + 3) (code b)))
        have hbNZ : convert (k + 3) (code b) ≠ .zero := by
          intro he; exact hb0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
        simp only [pairCut, hbNZ, ↓reduceIte, Term.H, Support.OT2.H_succTerm]
        exact List.mem_append_right _ (List.mem_append_left _ he)

theorem highest_regular_cutFund [LargeCardinals.{u}] (k : Nat) (b : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (topNode k (Support.SourceSuccessor.succ b))) :
    ∃ cut, CutFund k (topNode k (Support.SourceSuccessor.succ b)) cut :=
  ⟨pairCut (k + 1) (convert (k + 3) (code b)), highest_regular_cutFund_at k b hs⟩

theorem regular_cutFund [LargeCardinals.{u}] (k m : Nat) (hml : m + 1 < k + 3)
    (xs : Vec (new.T (k + 3)) (k + 3))
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P xs .Z) cut := by
  by_cases hmk : m ≤ k
  · exact regular_lower_cutFund k m hmk xs hm hr hs
  · have heM : m = k + 1 := by omega
    subst m
    have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
    obtain ⟨b, hb⟩ := dom_one_succ (xs.idx (Fin.last (k + 2))) hd
    have heXs : xs = lastVec (k + 2) (xs.idx (Fin.last (k + 2))) := by
      apply vec_ext; intro j; rw [lastVec_idx]
      by_cases hj : j.val = k + 2
      · rw [ite_eq_left hj]
        have heJ : j = Fin.last (k + 2) := Fin.ext hj; rw [heJ]
      · rw [ite_eq_right hj]
        exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j
          (by change j.val < k + 1 + 1; have := j.isLt; omega)
    have heSource : (.P xs .Z : new.T (k + 3)) = topNode k (Support.SourceSuccessor.succ b) := by
      rw [heXs, hb]; rfl
    rw [heSource] at hs ⊢
    exact highest_regular_cutFund k b hs

end Support.GeneralImageOmegaSpine

namespace Support.GeneralImageDominatedCoefficients

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageLimitSupport Support.GeneralImageMiddleCofinality Support.GeneralImageMiddleSums
open Support.GeneralImageZeroFund Support.GeneralImageOmegaSpine Support.SourceFundOrder
open Support.SourceFundGap Support.GeneralImageCofinalityCoefficients
open Support.GeneralImageUpperOmega Support.GeneralImageHighestDiagonal
open Support.GeneralImageCountableRecursion Support.SourceRecursiveDescending
open Support.GeneralImageCountableInheritance Support.GeneralImageCountableLayers
open Support.GeneralImageLimitBranches Support.GeneralImageOmegaContext

universe u

def DominatedCoefficient (k : Nat) (v : Term) (s : new.T (k + 3)) (z : Term) : Prop :=
  z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code s)) ∨
    ∃ a, Subterm a s ∧
      (convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) ∧
      Term.le z (convert (k + 3) (code a)) = true

theorem UpdatedCoefficient.dominated [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : new.T (k + 3)) (hs : RecursiveWF (k + 3) s) {z : Term}
    (hc : UpdatedCoefficient k v s t z) : DominatedCoefficient k v s z := by
  rcases hc with he | he | ⟨a, ha, hw, hm, he⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · refine Or.inr (Or.inr ⟨a, ha, hm, ?_⟩)
    have haW := ha.recursiveWF hs
    by_cases ha0 : a = .Z
    · subst a
      rcases he with rfl | rfl <;> simp [new.T.fund, code, convert, dropOne, Term.le]
    · have hl := (convert_order k _ _ hw haW).mp (fund_lt a t ha0)
      rcases he with rfl | rfl
      · simp [Term.le, hl]
      · simp [Term.le, dropOne_lt_of_lt hw.wf haW.wf hl]

theorem closed_of_dominated_coefficients [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (new.T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hs0 : convert (k + 3) (code s) ≠ .zero)
    (hn0 : convert (k + 3) (code (new.T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) → DominatedCoefficient k v s z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s t))))
      (convert (k + 3) (code (new.T.fund s t))) = true := by
  have oldBound (a : new.T (k + 3)) (ha : Subterm a s)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) : new.T.lt a s := by
    have haW := ha.recursiveWF hs
    apply (convert_order k _ _ haW hs).mpr
    rcases hm with hm | hm
    · exact (Term.allLt_iff _ _).mp hH _ hm
    · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hs0 hhead ((Term.allLt_iff _ _).mp hH _ hm)
  have bound (a : new.T (k + 3)) (ha : Subterm a s)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) :
      Term.lt (convert (k + 3) (code a)) (convert (k + 3) (code (new.T.fund s t))) = true :=
    (convert_order k _ _ (ha.recursiveWF hs) hn).mp (small_lt_fund_all s t a (oldBound a ha hm) (hgap a ha))
  apply (Term.allLt_iff _ _).mpr; intro z hz
  rcases hcoef z hz with he | ho | ⟨a, ha, hm, he⟩
  · rw [he]; exact (zero_lt_iff _).mpr hn0
  · rcases H_convert_source k v s ho with rfl | ⟨a, ha, he⟩
    · exact (zero_lt_iff _).mpr hn0
    · have hm := he.elim (fun h => Or.inl (h ▸ ho)) (fun h => Or.inr (h ▸ ho))
      rcases he with rfl | rfl
      · exact bound a ha hm
      · exact dropOne_lt_of_lt (ha.recursiveWF hs).wf hn.wf (bound a ha hm)
  · rcases (Term.le_iff_eq_or_lt _ _).mp he with he | he
    · rw [he]; exact bound a ha hm
    · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf v _ hn.wf hz) (ha.recursiveWF hs).wf hn.wf
        he (bound a ha hm)

theorem dominated_child_coefficients_below_parent [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (t a : new.T (k + 3))
    (ht : t ≠ .Z) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t)) (ha : RecursiveWF (k + 3) a)
    (hhead : Term.head (convert (k + 3) (code (.P xs .Z))) ≠ Term.one)
    (hn0 : convert (k + 3) (code (new.T.fund (.P xs .Z) t)) ≠ .zero) (v : Term)
    (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (xs.idx i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))))
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code a)) → DominatedCoefficient k v (xs.idx i) z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code a)) →
      Term.lt z (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true := by
  have hc : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hs0 : convert (k + 3) (code (.P xs .Z)) ≠ .zero := by
    rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
  have bound (b : new.T (k + 3)) (hb : Subterm b (xs.idx i))
      (hm : convert (k + 3) (code b) ∈ Term.H v (convert (k + 3) (code (xs.idx i))) ∨
        dropOne (convert (k + 3) (code b)) ∈ Term.H v (convert (k + 3) (code (xs.idx i)))) :
      Term.lt (convert (k + 3) (code b)) (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true := by
    have hbW := hb.recursiveWF hc
    have hbOld : new.T.lt b (.P xs .Z) := by
      apply (convert_order k _ _ hbW hs).mpr
      rcases hm with hm | hm
      · exact (Term.allLt_iff _ _).mp hH _ (embed _ hm)
      · exact undrop_lt_head_ne_one _ _ hbW.wf hs.wf hs0 hhead ((Term.allLt_iff _ _).mp hH _ (embed _ hm))
    have hgap : mass b < gap (.P xs .Z) t := by
      have hmass := Support.SourceCoefficientGap.mass_lt_of_subterm hb
      have hi := vectorMass_idx_le xs i
      simp only [gap, ite_eq_right ht, mass, Nat.add_zero, Nat.add_sub_cancel_left]; omega
    exact (convert_order k _ _ hbW hn).mp (small_lt_fund_all (.P xs .Z) t b hbOld hgap)
  intro z hz
  rcases hcoef z hz with he | ho | ⟨b, hb, hm, he⟩
  · rw [he]; exact (zero_lt_iff _).mpr hn0
  · rcases H_convert_source k v (xs.idx i) ho with rfl | ⟨b, hb, he⟩
    · exact (zero_lt_iff _).mpr hn0
    · have hm := he.elim (fun h => Or.inl (h ▸ ho)) (fun h => Or.inr (h ▸ ho))
      rcases he with rfl | rfl
      · exact bound b hb hm
      · exact dropOne_lt_of_lt (hb.recursiveWF hc).wf hn.wf (bound b hb hm)
  · rcases (Term.le_iff_eq_or_lt _ _).mp he with he | he
    · rw [he]; exact bound b hb hm
    · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf v _ ha.wf hz) (hb.recursiveWF hc).wf hn.wf
        he (bound b hb hm)

theorem inherited_omega_dominated_support [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .omega))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) (hnat : 0 < n)
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat n)))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) (new.T.ofNat n)))) →
      DominatedCoefficient k v (xs.idx i) z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))) →
      DominatedCoefficient k v (.P xs .Z) z := by
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hdrop := drop_image_of_omega k _ (hcoords i) hd
  have hnChild0 := omega_fund_nat_ne_zero k _ hd n hnat
  have hf : new.T.fund (.P xs .Z) (new.T.ofNat n) =
      .P (xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n))) .Z := by
    simp only [new.T.fund, ↓reduceIte, hm, GetElem.getElem]
  have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) (new.T.ofNat n)) := by
    have hw := hn; rw [hf, RecursiveWF] at hw
    simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
  have hcNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have hnNZ : convert (k + 3) (code (new.T.fund (xs.idx i) (new.T.ofNat n))) ≠ .zero := by
    intro he; exact hnChild0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (xs.idx i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term}
      (hc : DominatedCoefficient k v (xs.idx i) z) : DominatedCoefficient k v (.P xs .Z) z := by
    rcases hc with he | ho | ⟨a, ha, hmA, hle⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl (embed _ ho))
    · exact Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i),
        hmA.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), hle⟩)
  intro z hz
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (xs.idx i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff _ _ _).mpr ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (xs.idx i)) .Z)
      hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    rw [heSource, fund_low_omega (k + 2) _ _ hd, H_low_empty_above_Omega v hOmega] at hz; cases hz
  · by_cases hib : i.val ≤ k + 1
    · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow _ hcNZ hnNZ hdrop hIsLow
      have heFund := hf ▸ heNew
      have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
      rw [heOld, heFund] at hlt
      rw [heFund] at hz
      rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz
        with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
      · exact Or.inr (Or.inl (heOld ▸ ho))
      · rcases he with he | hzChild
        · refine Or.inr (Or.inr ⟨xs.idx i, Subterm.coordinate xs .Z i, Or.inl (heOld ▸ hroot), ?_⟩)
          rw [he]
          have hl := (convert_order k _ _ hnChild (hcoords i)).mp (fund_lt _ _ hc0)
          simp [Term.le, dropOne_lt_of_lt hnChild.wf (hcoords i).wf hl]
        · exact lift (fun z hz => heOld ▸ hchild z hz) (hcoef z hzChild)
    · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      have he : xs = lastVec (k + 2) (xs.idx i) := by
        apply vec_ext; intro j; rw [lastVec_idx]
        by_cases hj : j.val = k + 2
        · rw [ite_eq_left hj]
          have hji : j = i := Fin.ext (by rw [hi]; simpa using hj); rw [hji]
        · rw [ite_eq_right hj]
          exact hlow j (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
      have heOld : (.P xs .Z : new.T (k + 3)) = topNode k (xs.idx i) := congrArg (fun us => new.T.P us .Z) he
      have heR := congrArg (fun us => us.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n))) he
      rw [hi, Support.SourceOmegaHighest.lastVec_replace_last] at heR
      have heR' : xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n)) =
          lastVec (k + 2) (new.T.fund (xs.idx i) (new.T.ofNat n)) := by simpa only [hi] using heR
      have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) = Term.H v (convert (k + 3) (code (xs.idx i))) := by
        rw [heOld, H_topNode_above_Omega k _ hc0 v hOmega, hdrop]
      rw [hf, heR', ← topNode, H_topNode_above_Omega k _ hnChild0 v hOmega] at hz
      exact lift (fun z hz => heH ▸ hz) (hcoef z (Support.OT2.mem_H_dropOne hz))

theorem inherited_omega_dominated_relative_above [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .omega))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) (hnat : 0 < n)
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat n)))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) (new.T.ofNat n)))) →
      DominatedCoefficient k v (xs.idx i) z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))))
      (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))) = true := by
  classical
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hdrop := drop_image_of_omega k _ (hcoords i) hd
  have hnChild0 := omega_fund_nat_ne_zero k _ hd n hnat
  have ht : new.T.ofNat (lam := k + 3) n ≠ .Z := by cases n with
    | zero => omega
    | succ n => intro he; cases he
  have hdom : new.T.dom (.P xs .Z) = .omega := by simp only [new.T.dom, ↓reduceIte, hm]
  have hhead := omega_image_head_ne_one k _ hs hdom
  have hf : new.T.fund (.P xs .Z) (new.T.ofNat n) =
      .P (xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n))) .Z := by
    simp only [new.T.fund, ↓reduceIte, hm, GetElem.getElem]
  have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) (new.T.ofNat n)) := by
    have hw := hn; rw [hf, RecursiveWF] at hw
    simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := by
    rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
  have hnZ : convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n))) ≠ .zero := by
    rw [hf, convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
  by_cases hex : ∃ j : Fin (k + 3), i ≠ j ∧ xs.idx j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact closed_of_dominated_coefficients k v _ _ hs hn hhead hsZ hnZ
      (fun a ha => positive_principal_subterm_gap xs i j hij hc0 hj _ ht ha)
      (inherited_omega_dominated_support k xs i hm hs n hnat hn v hvR hv hOmega hcoef) hH
  · have hother : ∀ j : Fin (k + 3), j.val ≠ i.val → xs.idx j = .Z := by
      intro j hj
      apply Classical.byContradiction; intro hz
      exact hex ⟨j, fun he => hj (congrArg Fin.val he.symm), hz⟩
    by_cases hi0 : i.val = 0
    · have he : xs = lowVec (k + 2) (xs.idx i) := by
        apply vec_ext; intro j; rw [lowVec_idx]
        by_cases hj : j.val = 0
        · rw [ite_eq_left hj]
          have hji : j = i := Fin.ext (hj.trans hi0.symm); rw [hji]
        · rw [ite_eq_right hj]; exact hother j (by rw [hi0]; exact hj)
      rw [he, fund_low_omega (k + 2) _ _ hd, H_low_empty_above_Omega v hOmega]
      rfl
    · by_cases hib : i.val ≤ k + 1
      · have hip : 0 < i.val := by omega
        have hhigh (j : Fin (k + 3)) (hj : i.val < j.val) : xs.idx j = .Z := hother j (by omega)
        have heOld := convert_positive_single k xs i hip hib hlow hhigh hc0
        rw [hdrop] at heOld
        let ys := xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n))
        have hnewLow (j : Fin (k + 3)) (hj : j.val < i.val) : ys.idx j = .Z := by
          simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j.val ≠ i.val)]; exact hlow j hj
        have hnewHigh (j : Fin (k + 3)) (hj : i.val < j.val) : ys.idx j = .Z := by
          simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j.val ≠ i.val)]; exact hhigh j hj
        have hnewIdx : ys.idx i = new.T.fund (xs.idx i) (new.T.ofNat n) := by simp [ys, vec_rplc_idx]
        have heNew := convert_positive_single k ys i hip hib hnewLow hnewHigh (hnewIdx ▸ hnChild0)
        rw [hnewIdx] at heNew
        have heFund := hf ▸ heNew
        have hwOld := heOld ▸ hs.wf
        have hwNew := heFund ▸ hn.wf
        have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
        rw [heOld, heFund] at hlt
        apply (Term.allLt_iff _ _).mpr
        intro z hz; rw [heFund] at hz
        rcases H_psi_replacement_support v _ _ _ hvR hv hwOld hwNew hlt hz with ⟨hctx, _⟩ | ⟨he, hroot, hchild⟩
        · simp [Term.H, Term.hOne, hOmega] at hctx
        · rcases he with he | hzChild
          · rw [he]
            have hOldArg : Term.lt (convert (k + 3) (code (xs.idx i)))
                (.psi (.inacc i.val .zero) (convert (k + 3) (code (xs.idx i)))) = true := by
              rw [← heOld]; exact (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
            have hOwn := (psi_argument_lt_iff _ _ hwOld).mp hOldArg
            have hChildLt := (convert_order k _ _ hnChild (hcoords i)).mp (fund_lt (xs.idx i) _ hc0)
            have hOwnW := ((Term.wf_psi_iff _ _).mp hwOld).2.1
            have hNewOwn := lemma_6_1.{u}.2.1 _ _ _ hnChild.wf (hcoords i).wf hOwnW hChildLt hOwn
            rw [heFund]
            exact (psi_argument_lt_iff _ _ hwNew).mpr (dropOne_lt_of_lt hnChild.wf hOwnW hNewOwn)
          · exact dominated_child_coefficients_below_parent k xs i _ _ ht hs hn hnChild hhead hnZ v
              (fun z hz => heOld ▸ hchild z hz) hcoef hH z hzChild
      · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
        have he : xs = lastVec (k + 2) (xs.idx i) := by
          apply vec_ext; intro j; rw [lastVec_idx]
          by_cases hj : j.val = k + 2
          · rw [ite_eq_left hj]
            have hji : j = i := Fin.ext (by rw [hi]; simpa using hj); rw [hji]
          · rw [ite_eq_right hj]; exact hother j (by rw [hi]; simpa only [Fin.val_last] using hj)
        have heOld : (.P xs .Z : new.T (k + 3)) = topNode k (xs.idx i) := congrArg (fun us => new.T.P us .Z) he
        have heR := congrArg (fun us => us.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n))) he
        rw [hi, Support.SourceOmegaHighest.lastVec_replace_last] at heR
        have heR' : xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat n)) =
            lastVec (k + 2) (new.T.fund (xs.idx i) (new.T.ofNat n)) := by simpa only [hi] using heR
        have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) = Term.H v (convert (k + 3) (code (xs.idx i))) := by
          rw [heOld, H_topNode_above_Omega k _ hc0 v hOmega, hdrop]
        apply (Term.allLt_iff _ _).mpr
        intro z hz
        rw [hf, heR', ← topNode, H_topNode_above_Omega k _ hnChild0 v hOmega] at hz
        exact dominated_child_coefficients_below_parent k xs i _ _ ht hs hn hnChild hhead hnZ v
          (fun z hz => heH ▸ hz) hcoef hH z (Support.OT2.mem_H_dropOne hz)

end Support.GeneralImageDominatedCoefficients

namespace Support.GeneralImageLabelCut

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageMiddleSums Support.GeneralImageMiddleCofinality
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance Support.GeneralImageCofinalityCoefficients
open Support.GeneralImageUpperOmega Support.GeneralImageHighOmega
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant
open Support.SourceOmegaTail

open Support.GeneralImageOmegaSpine

universe u

theorem Omega_fund_at_label_cut_invariant [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (κ : Term) (hc : CutFund k (.P q .Z) κ)
    (t : new.T (k + 3)) (ht : RecursiveWF (k + 3) t)
    (hHt : Term.allLt (Term.H κ (convert (k + 3) (code t)))
      (convert (k + 3) (code t)) = true) :
    RecursiveWF (k + 3) (new.T.fund s t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P q .Z))) v = true →
        (∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) → UpdatedCoefficient k v s t z) ∧
        (Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
          Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s t))))
            (convert (k + 3) (code (new.T.fund s t))) = true) := by
  cases heS : s with
  | Z => rw [heS, new.T.dom] at hd; cases hd
  | P xs b =>
    rw [heS] at hr hs hd
    by_cases hb : b = .Z
    · subst b
      have hdom := hd
      rw [new.T.dom] at hdom
      simp only [↓reduceIte] at hdom
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [hm] at hdom; cases hdom
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchildD := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        cases d with
        | zero | omega => simp only [hm] at hdom; cases hdom
        | one =>
          obtain ⟨n, hin⟩ := i
          cases n with
          | zero => simp only [hm, ↓reduceIte] at hdom; cases hdom
          | succ m =>
            simp only [hm, show m + 1 ≠ 0 by omega, ↓reduceIte] at hdom
            have he := new.Dom.Omega.inj hdom
            subst q
            have hn := hc.fundWf t ht hHt
            have hrelative := fund_regular_cofinal_relative_all_of_wf k m xs hin hm hr hs t hn
            refine ⟨hn, ?_⟩
            intro v hvR hv hOmega hcut
            exact ⟨fun z hz => H_fund_regular_cofinal_support k m xs hin hm hs t v hvR hv hOmega hcut hz,
              hrelative v hvR hv hOmega hcut⟩
        | Omega ys =>
          simp only [hm] at hdom
          by_cases hlt : Vec.lt xs ys
          · simp only [hlt, ↓reduceIte] at hdom; cases hdom
          · simp only [hlt, ↓reduceIte] at hdom
            have he := new.Dom.Omega.inj hdom
            subst q
            have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
            have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
            obtain ⟨hnChild, hchildInv⟩ := Omega_fund_at_label_cut_invariant k (xs.idx i) hchildR (hcoords i) hchildD κ hc t ht hHt
            have hf : new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
              simp only [new.T.fund, ↓reduceIte, hm, hlt, GetElem.getElem]
            have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchildD; cases hchildD
            have hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t) := by
              rw [hf]
              by_cases hib : i.val ≤ k + 1
              · apply principal_replace_cofinal_recursiveWF k xs i hib
                  (Support.DimensionCut.minIdx_spec xs hm).2.2 hs _ hnChild hc0
                  (Omega_image_drop k _ hchildR (hcoords i) hchildD)
                  (convert (k + 3) (code (.P ys .Z))) (Omega_label_recursiveWF k _ hs hd).wf
                  (cofinality_image_le k _ hr hs hd) (Omega_principal_image_ne_low k xs i hs hd)
                intro v hvR hv hOmega hcut hH
                exact (hchildInv v hvR hv hOmega hcut).2 hH
              · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
                let c := xs.idx i
                have he : xs = lastVec (k + 2) c := by
                  apply vec_ext
                  intro j
                  rw [lastVec_idx]
                  by_cases hj : j.val = k + 2
                  · rw [ite_eq_left hj]
                    have hji : j = i := Fin.ext (by rw [hi]; simpa using hj)
                    rw [hji]
                  · rw [ite_eq_right hj]
                    exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j
                      (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
                have hrplc : xs.rplc i (new.T.fund c t) = lastVec (k + 2) (new.T.fund c t) := by
                  have heR := congrArg (fun us => us.rplc i (new.T.fund c t)) he
                  rw [hi, Support.SourceOmegaHighest.lastVec_replace_last] at heR
                  simpa only [hi] using heR
                have heP : (.P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z : new.T (k + 3)) =
                    topNode k (new.T.fund c t) := congrArg (fun us => new.T.P us .Z) hrplc
                rw [heP]
                exact topNode_recursiveWF k _ hnChild
            refine ⟨hn, ?_⟩
            intro v hvR hv hOmega hcut
            have hc := (hchildInv v hvR hv hOmega hcut).1
            exact ⟨parent_Omega_updated_support k xs ys i hm hr hs hd t hn v hvR hv hOmega hc,
              parent_Omega_relative_of_child_support k xs ys i hm hr hs hd t hn v hvR hv hOmega hc⟩
    · have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      have hdb : new.T.dom b = .Omega q := by simpa only [new.T.dom, ite_eq_right hb] using hd
      obtain ⟨hnB, htailInv⟩ := Omega_fund_at_label_cut_invariant k b hbr hbw hdb κ hc t ht hHt
      have hn := fund_nonzero_tail_recursiveWF k xs b t hs hb hnB
      refine ⟨hn, ?_⟩
      intro v hvR hv hOmega hcut
      have hcoef (z : Term) (hz : z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs b) t)))) :
          UpdatedCoefficient k v (.P xs b) t z := by
        rw [new.T.fund, ite_eq_right hb, code, convert] at hz
        rcases H_assemble_support v _ _ hz with hz | hz
        · exact Or.inr (Or.inl (by
            simp only [code, convert]
            exact H_assemble_left v _ _ hz))
        · rcases (htailInv v hvR hv hOmega hcut).1 z hz with he | ho | ⟨a, ha, hw, hmA, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl
            simp only [code, convert]
            exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
            simp only [code, convert]
            exact hmA.elim (fun h => Or.inl (H_assemble_right v _ _ h))
              (fun h => Or.inr (H_assemble_right v _ _ h))
      refine ⟨hcoef, ?_⟩
      intro hH
      have hsZ : convert (k + 3) (code (.P xs b)) ≠ .zero := by
        intro he
        have heS : (.P xs b : new.T (k + 3)) = .Z :=
          code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
        cases heS
      have hnZ : convert (k + 3) (code (new.T.fund (.P xs b) t)) ≠ .zero := by
        intro he
        exact domOmega_fund_ne_zero _ t hd
          (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
      exact closed_of_updated_coefficients k v _ t hs hn (Omega_image_head_ne_one k _ hr hs hd) hsZ hnZ
        (fun a ha => sum_subterm_gap xs b t hb (Omega_head_mass_pos xs b hr hd) hd ha) hcoef hH
termination_by new.T.size s
decreasing_by
  all_goals rw [heS]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem Omega_label_recursive (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) {q : Vec (new.T (k + 3)) (k + 3)}
    (hd : new.T.dom s = .Omega q) : Recursive (.P q .Z) := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [new.T.dom] at hd
      simp only [↓reduceIte] at hd
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchild := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          simp only [hm] at hd
          by_cases hz : i.val = 0
          · simp only [hz, ↓reduceIte] at hd; cases hd
          · simp only [hz, ↓reduceIte] at hd
            have he := new.Dom.Omega.inj hd
            rw [← he]; exact hr
        | Omega ys =>
          simp only [hm] at hd
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte] at hd; cases hd
          · simp only [hv, ↓reduceIte] at hd
            have he := new.Dom.Omega.inj hd
            have hc : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
            rw [← he]
            exact Omega_label_recursive k (xs.idx i) hc hchild
    · rw [new.T.dom, ite_eq_right hb] at hd
      have hc : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      exact Omega_label_recursive k b hc hd
termination_by new.T.size s
decreasing_by
  all_goals simp_all only [new.T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

theorem Omega_label_cutFund [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q) :
    ∃ κ, CutFund k (.P q .Z) κ := by
  obtain ⟨⟨i, hil⟩, hi, hm⟩ := domOmega_regular s hd
  cases i with
  | zero => change 0 < 0 at hi; omega
  | succ m =>
    exact regular_cutFund k m hil q hm (Omega_label_recursive k s hr hd)
      (Omega_label_recursiveWF k s hs hd)

end Support.GeneralImageLabelCut

namespace Support.GeneralImageParametricCut

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageMiddleSums Support.GeneralImageMiddleCofinality
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance Support.GeneralImageCofinalityCoefficients
open Support.GeneralImageUpperOmega Support.GeneralImageHighOmega
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant
open Support.SourceOmegaTail

open Support.GeneralImageOmegaSpine

open Support.GeneralImageLabelCut Support.GeneralImageOmegaCofinality
open Support.SourceFundGap Support.SourceOmegaHighest
open Support.GeneralImageZeroFund
open Support.GeneralImageDominatedCoefficients

universe u

theorem closed_of_updated_or_bounded [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (new.T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hnewZero : convert (k + 3) (code (new.T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (extra : Term → Prop)
    (hBound : ∀ z, extra z → Term.lt z (convert (k + 3) (code (new.T.fund s t))) = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) →
      UpdatedCoefficient k v s t z ∨ extra z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s t))))
      (convert (k + 3) (code (new.T.fund s t))) = true := by
  have hzlt := (zero_lt_iff _).mpr hnewZero
  have oldBound (a : new.T (k + 3)) (ha : Subterm a s)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) : new.T.lt a s := by
    have hw := ha.recursiveWF hs
    apply (convert_order k _ _ hw hs).mpr
    rcases hm with hm | hm
    · exact (Term.allLt_iff _ _).mp hH _ hm
    · exact undrop_lt_head_ne_one _ _ hw.wf hs.wf hzero hhead ((Term.allLt_iff _ _).mp hH _ hm)
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  rcases hcoef z hz with hc | hex
  · rcases hc with he | ho | ⟨a, ha, hw, hm, he⟩
    · rw [he]; exact hzlt
    · rcases H_convert_source k v s ho with rfl | ⟨a, ha, he⟩
      · exact hzlt
      · have hw := ha.recursiveWF hs
        have hal := oldBound a ha (he.elim (fun he => Or.inl (he ▸ ho)) (fun he => Or.inr (he ▸ ho)))
        have hl := (convert_order k _ _ hw hn).mp (small_lt_fund_all s t a hal (hgap a ha))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
    · by_cases ha0 : a = .Z
      · subst a
        rcases he with rfl | rfl <;> simpa only [new.T.fund, code, convert, dropOne] using hzlt
      · have hal := oldBound a ha hm
        have hl := (convert_order k _ _ hw hn).mp
          (T_trans _ _ _ (fund_lt a t ha0) (small_lt_fund_all s t a hal (hgap a ha)))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
  · exact hBound z hex

theorem parent_Omega_updated_or_support [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hd : new.T.dom (.P xs .Z) = .Omega q) (t : new.T (k + 3))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (extra : Term → Prop)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) t))) →
      UpdatedCoefficient k v (xs.idx i) t z ∨ extra z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) →
      UpdatedCoefficient k v (.P xs .Z) t z ∨ extra z := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hchildD := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchildD; cases hchildD
  have hcNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have haNZ : convert (k + 3) (code (new.T.fund (xs.idx i) t)) ≠ .zero := by
    intro he
    exact domOmega_fund_ne_zero _ t hchildD
      (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have hnd : ¬ Vec.lt xs q := by
    intro he; simp only [new.T.dom, ↓reduceIte, hm, he] at hd; cases hd
  have hf : new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
    simp only [new.T.fund, ↓reduceIte, hm, hnd, GetElem.getElem]
  have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) t) := by
    have hw := hn
    rw [hf, RecursiveWF] at hw
    simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (xs.idx i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term}
      (hc : UpdatedCoefficient k v (xs.idx i) t z) : UpdatedCoefficient k v (.P xs .Z) t z := by
    rcases hc with he | ho | ⟨a, ha, hw, ho, he⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl (embed _ ho))
    · exact Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i), hw,
        ho.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), he⟩)
  intro z hz
  by_cases hib : i.val ≤ k + 1
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib
      (Support.DimensionCut.minIdx_spec xs hm).2.2 _ hcNZ haNZ
      (Omega_image_drop k _ hchildR (hcoords i) hchildD) (Omega_principal_image_ne_low k xs i hs hd)
    have heFund := hf ▸ heNew
    have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) t (by intro he; cases he))
    have hwOld := heOld ▸ hs.wf
    have hwNew := heFund ▸ hn.wf
    rw [heOld, heFund] at hlt
    rw [heFund] at hz
    rcases H_psi_replacement_support v w _ _ hvR hv hwOld hwNew hlt hz with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
    · exact Or.inl (Or.inr (Or.inl (heOld ▸ ho)))
    · rcases he with he | hzChild
      · exact Or.inl (Or.inr (Or.inr ⟨xs.idx i, Subterm.coordinate xs .Z i, hnChild,
          Or.inl (heOld ▸ hroot), Or.inr he⟩))
      · rcases hcoef z hzChild with hu | hex
        · exact Or.inl (lift (fun z hz => heOld ▸ hchild z hz) hu)
        · exact Or.inr hex
  · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    have he : xs = lastVec (k + 2) (xs.idx i) := by
      apply vec_ext
      intro j
      rw [lastVec_idx]
      by_cases hj : j.val = k + 2
      · rw [ite_eq_left hj]
        have hji : j = i := Fin.ext (by rw [hi]; simpa using hj)
        rw [hji]
      · rw [ite_eq_right hj]
        exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j
          (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
    have heOld : (.P xs .Z : new.T (k + 3)) = topNode k (xs.idx i) :=
      congrArg (fun us => new.T.P us .Z) he
    have heNew : new.T.fund (.P xs .Z) t = topNode k (new.T.fund (xs.idx i) t) := by
      rw [hf]
      have hrplc : (lastVec (k + 2) (xs.idx i)).rplc i (new.T.fund (xs.idx i) t) =
          lastVec (k + 2) (new.T.fund (xs.idx i) t) := by
        rw [hi, Support.SourceOmegaHighest.lastVec_replace_last]
      exact congrArg (fun us => new.T.P us .Z)
        ((congrArg (fun us => us.rplc i (new.T.fund (xs.idx i) t)) he).trans hrplc)
    have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) =
        Term.H v (convert (k + 3) (code (xs.idx i))) := by
      rw [heOld]; exact H_topNode_Omega k _ hchildR (hcoords i) hchildD v hOmega
    rw [heNew, H_topNode_above_Omega k _ (domOmega_fund_ne_zero _ t hchildD) v hOmega] at hz
    rcases hcoef z (Support.OT2.mem_H_dropOne hz) with hu | hex
    · exact Or.inl (lift (fun z hz => heH ▸ hz) hu)
    · exact Or.inr hex

theorem topNode_relative_of_updated_or_bounded [LargeCardinals.{u}] (k : Nat)
    (a t : new.T (k + 3)) (hr : Recursive a) (ha : RecursiveWF (k + 3) a)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom a = .Omega q)
    (hs : RecursiveWF (k + 3) (topNode k a))
    (hnChild : RecursiveWF (k + 3) (new.T.fund a t)) (v : Term)
    (hv : Term.lt Term.bigOmega v = true)
    (extra : Term → Prop)
    (hBound : ∀ z, extra z → Term.lt z (convert (k + 3) (code (new.T.fund (topNode k a) t))) = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund a t))) → UpdatedCoefficient k v a t z ∨ extra z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (topNode k a))))
      (convert (k + 3) (code (topNode k a))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (topNode k a) t))))
      (convert (k + 3) (code (new.T.fund (topNode k a) t))) = true := by
  have hza : a ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hzn := domOmega_fund_ne_zero a t hd
  have hf : new.T.fund (topNode k a) t = topNode k (new.T.fund a t) :=
    highest_Omega_fund (k + 2) a t hr hd
  have hn : RecursiveWF (k + 3) (new.T.fund (topNode k a) t) := hf ▸ topNode_recursiveWF k _ hnChild
  have hhead : Term.head (convert (k + 3) (code (topNode k a))) ≠ Term.one := by
    rw [convert_topNode k a hza]
    simp only [Term.head, Term.one]
    intro he; cases he
  have hsZ : convert (k + 3) (code (topNode k a)) ≠ .zero := by rw [convert_topNode k a hza]; intro he; cases he
  have hnZ : convert (k + 3) (code (new.T.fund (topNode k a) t)) ≠ .zero := by
    rw [hf, convert_topNode k _ hzn]; intro he; cases he
  have heH := H_topNode_Omega k a hr ha hd v hv
  have oldBound (b : new.T (k + 3)) (hb : Subterm b a)
      (hm : convert (k + 3) (code b) ∈ Term.H v (convert (k + 3) (code a)) ∨
        dropOne (convert (k + 3) (code b)) ∈ Term.H v (convert (k + 3) (code a))) :
      new.T.lt b (topNode k a) := by
    have hw := hb.recursiveWF ha
    have oldMem : convert (k + 3) (code b) ∈ Term.H v (convert (k + 3) (code (topNode k a))) ∨
        dropOne (convert (k + 3) (code b)) ∈ Term.H v (convert (k + 3) (code (topNode k a))) := by
      rw [heH]; exact hm
    apply (convert_order k _ _ hw hs).mpr
    rcases oldMem with hm | hm
    · exact (Term.allLt_iff _ _).mp hH _ hm
    · exact undrop_lt_head_ne_one _ _ hw.wf hs.wf hsZ hhead ((Term.allLt_iff _ _).mp hH _ hm)
  have hzlt := (zero_lt_iff _).mpr hnZ
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  rw [hf, H_topNode_above_Omega k _ hzn v hv] at hz
  have hzChild := Support.OT2.mem_H_dropOne hz
  rcases hcoef z hzChild with hc | hex
  · rcases hc with he | ho | ⟨b, hb, hw, hm, he⟩
    · rw [he]; exact hzlt
    · rcases H_convert_source k v a ho with rfl | ⟨b, hb, he⟩
      · exact hzlt
      · have hw := hb.recursiveWF ha
        have hal := oldBound b hb (he.elim (fun he => Or.inl (he ▸ ho)) (fun he => Or.inr (he ▸ ho)))
        have hl := (convert_order k _ _ hw hn).mp
          (small_lt_fund_all _ t b hal (topNode_child_subterm_gap k a t hr hd hb))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
    · by_cases hb0 : b = .Z
      · subst b
        rcases he with rfl | rfl <;> simpa only [new.T.fund, code, convert, dropOne] using hzlt
      · have hal := oldBound b hb hm
        have hl := (convert_order k _ _ hw hn).mp
          (T_trans _ _ _ (fund_lt b t hb0)
            (small_lt_fund_all _ t b hal (topNode_child_subterm_gap k a t hr hd hb)))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
  · exact hBound z hex

theorem parent_Omega_relative_of_updated_or_bounded [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hd : new.T.dom (.P xs .Z) = .Omega q) (t : new.T (k + 3))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (extra : Term → Prop)
    (hBound : ∀ z, extra z → Term.lt z (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) t))) →
      UpdatedCoefficient k v (xs.idx i) t z ∨ extra z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t))))
      (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true := by
  classical
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hchildD := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchildD; cases hchildD
  have hnd : ¬ Vec.lt xs q := by intro he; simp only [new.T.dom, ↓reduceIte, hm, he] at hd; cases hd
  have hf : new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
    simp only [new.T.fund, ↓reduceIte, hm, hnd, GetElem.getElem]
  have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) t) := by
    have hw := hn
    rw [hf, RecursiveWF] at hw
    simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := by
    rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
  have hnZ : convert (k + 3) (code (new.T.fund (.P xs .Z) t)) ≠ .zero := by
    intro he
    exact domOmega_fund_ne_zero _ t hd
      (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have hhead := Omega_image_head_ne_one k _ hr hs hd
  by_cases hex : ∃ j : Fin (k + 3), i ≠ j ∧ xs.idx j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact closed_of_updated_or_bounded k v _ t hs hn hhead hsZ hnZ
      (fun a ha => principal_subterm_gap xs i j hij hc0 hj hd t ha)
      extra hBound (parent_Omega_updated_or_support k xs q i hm hr hs hd t hn v hvR hv hOmega extra hcoef) hH
  · have hother : ∀ j : Fin (k + 3), j.val ≠ i.val → xs.idx j = .Z := by
      intro j hj
      apply Classical.byContradiction
      intro hz
      apply hex
      exact ⟨j, fun he => hj (congrArg Fin.val he.symm), hz⟩
    by_cases hib : i.val ≤ k + 1
    · have hip : 0 < i.val := by
        by_cases hi0 : i.val = 0
        · have he : xs = lowVec (k + 2) (xs.idx i) := by
            apply vec_ext
            intro j
            rw [lowVec_idx]
            by_cases hj : j.val = 0
            · rw [ite_eq_left hj]
              have hji : j = i := Fin.ext (hj.trans hi0.symm)
              rw [hji]
            · rw [ite_eq_right hj]
              exact hother j (by rw [hi0]; exact hj)
          have hsource : (.P xs .Z : new.T (k + 3)) = .P (lowVec (k + 2) (xs.idx i)) .Z :=
            congrArg (fun us => new.T.P us .Z) he
          have ho : Outer (.P (lowVec (k + 2) (xs.idx i)) .Z) := .cons _ _ .zero
          have hdom := hd
          rw [hsource] at hdom
          exact False.elim (outer_not_Omega ho q hdom)
        · omega
      have hhigh (j : Fin (k + 3)) (hj : i.val < j.val) : xs.idx j = .Z := hother j (by omega)
      have hdrop := Omega_image_drop k _ hchildR (hcoords i) hchildD
      have heOld := convert_positive_single k xs i hip hib (Support.DimensionCut.minIdx_spec xs hm).2.2 hhigh hc0
      rw [hdrop] at heOld
      let ys := xs.rplc i (new.T.fund (xs.idx i) t)
      have hnewLow (j : Fin (k + 3)) (hj : j.val < i.val) : ys.idx j = .Z := by
        simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j.val ≠ i.val)]
        exact (Support.DimensionCut.minIdx_spec xs hm).2.2 j hj
      have hnewHigh (j : Fin (k + 3)) (hj : i.val < j.val) : ys.idx j = .Z := by
        simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j.val ≠ i.val)]
        exact hhigh j hj
      have hnewIdx : ys.idx i = new.T.fund (xs.idx i) t := by simp only [ys, vec_rplc_idx, ↓reduceIte]
      have hnewNZ : ys.idx i ≠ .Z := hnewIdx ▸ domOmega_fund_ne_zero _ t hchildD
      have heNew := convert_positive_single k ys i hip hib hnewLow hnewHigh hnewNZ
      rw [hnewIdx] at heNew
      have heFund : convert (k + 3) (code (new.T.fund (.P xs .Z) t)) =
          .psi (.inacc i.val .zero) (dropOne (convert (k + 3) (code (new.T.fund (xs.idx i) t)))) := hf ▸ heNew
      have hwOld := heOld ▸ hs.wf
      have hwNew := heFund ▸ hn.wf
      have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) t (by intro he; cases he))
      rw [heOld, heFund] at hlt
      have hgapChild (a : new.T (k + 3)) (ha : Subterm a (xs.idx i)) : mass a < gap (.P xs .Z) t := by
        have hmA := Support.SourceCoefficientGap.mass_lt_of_subterm ha
        have hmI := vectorMass_idx_le xs i
        rw [gap_Omega _ _ _ hd, mass, mass]
        omega
      have oldBound (a : new.T (k + 3)) (ha : Subterm a (xs.idx i))
          (hmA : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
            dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) :
          new.T.lt a (.P xs .Z) := by
        have haW := ha.recursiveWF (hcoords i)
        apply (convert_order k _ _ haW hs).mpr
        rcases hmA with hmA | hmA
        · exact (Term.allLt_iff _ _).mp hH _ hmA
        · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hsZ hhead ((Term.allLt_iff _ _).mp hH _ hmA)
      apply (Term.allLt_iff _ _).mpr
      intro z hz
      rw [heFund] at hz
      rcases H_psi_replacement_support v _ _ _ hvR hv hwOld hwNew hlt hz with ⟨hctx, _⟩ | ⟨he, hroot, hchild⟩
      · simp [Term.H, Term.hOne, hOmega] at hctx
      · rcases he with he | hzChild
        · rw [he]
          have hOldArg : Term.lt (convert (k + 3) (code (xs.idx i)))
              (.psi (.inacc i.val .zero) (convert (k + 3) (code (xs.idx i)))) = true := by
            rw [← heOld]; exact (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
          have hOwn := (psi_argument_lt_iff _ _ hwOld).mp hOldArg
          have hChildLt := (convert_order k _ _ hnChild (hcoords i)).mp (fund_lt (xs.idx i) t hc0)
          have hOwnW := ((Term.wf_psi_iff _ _).mp hwOld).2.1
          have hNewOwn := lemma_6_1.{u}.2.1 _ _ _ hnChild.wf (hcoords i).wf hOwnW hChildLt hOwn
          have hDropOwn := dropOne_lt_of_lt hnChild.wf hOwnW hNewOwn
          rw [heFund]
          exact (psi_argument_lt_iff _ _ hwNew).mpr hDropOwn
        · have embed (a : Term) (ha : a ∈ Term.H v (convert (k + 3) (code (xs.idx i)))) :
              a ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) := heOld ▸ hchild a ha
          rcases hcoef z hzChild with hu | hex
          · rcases hu with he | ho | ⟨a, ha, haW, hmA, he⟩
            · rw [he]; exact (zero_lt_iff _).mpr hnZ
            · rcases H_convert_source k v (xs.idx i) ho with rfl | ⟨a, ha, he⟩
              · exact (zero_lt_iff _).mpr hnZ
              · have haW := ha.recursiveWF (hcoords i)
                have hOld := oldBound a ha (he.elim (fun he => Or.inl (he ▸ embed _ ho)) (fun he => Or.inr (he ▸ embed _ ho)))
                have hNew := (convert_order k _ _ haW hn).mp
                  (small_lt_fund_all (.P xs .Z) t a hOld (hgapChild a ha))
                rcases he with rfl | rfl
                · exact hNew
                · exact dropOne_lt_of_lt haW.wf hn.wf hNew
            · by_cases ha0 : a = .Z
              · subst a
                rcases he with rfl | rfl <;> simpa only [new.T.fund, code, convert, dropOne] using (zero_lt_iff _).mpr hnZ
              · have hOld := oldBound a ha (hmA.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)))
                have hSmall := small_lt_fund_all (.P xs .Z) t a hOld (hgapChild a ha)
                have hNew := (convert_order k _ _ haW hn).mp (T_trans _ _ _ (fund_lt a t ha0) hSmall)
                rcases he with rfl | rfl
                · exact hNew
                · exact dropOne_lt_of_lt haW.wf hn.wf hNew
          · exact hBound z hex
    · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      have he : xs = lastVec (k + 2) (xs.idx i) := by
        apply vec_ext
        intro j
        rw [lastVec_idx]
        by_cases hj : j.val = k + 2
        · rw [ite_eq_left hj]
          have hji : j = i := Fin.ext (by rw [hi]; simpa using hj)
          rw [hji]
        · rw [ite_eq_right hj]
          exact hother j (by rw [hi]; simpa only [Fin.val_last] using hj)
      have hsource : (.P xs .Z : new.T (k + 3)) = topNode k (xs.idx i) := congrArg (fun us => new.T.P us .Z) he
      have htop := topNode_relative_of_updated_or_bounded k (xs.idx i) t hchildR (hcoords i) hchildD
        (hsource ▸ hs) hnChild v hOmega extra
        (fun z hz => (congrArg (fun s => new.T.fund s t) hsource) ▸ hBound z hz) hcoef (hsource ▸ hH)
      exact (congrArg (fun s => new.T.fund s t) hsource) ▸ htop

theorem inserted_coefficient_bound_at_self [LargeCardinals.{u}]
    (cut a b : Term) (ha : Term.wf a = true) (hb : Term.wf b = true)
    (hb0 : b ≠ .zero) (hSelf : Term.H cut cut = [])
    (hH : Term.allLt (Term.H cut a) a = true) (hNext : Term.lt a b = true)
    {z : Term} (hz : InsertedCoefficient cut cut a z) : Term.lt z b = true := by
  rcases hz with he | he | he | he | he
  · rw [he]; exact (zero_lt_iff _).mpr hb0
  · rw [he]; exact hNext
  · rw [he]; exact dropOne_lt_of_lt ha hb hNext
  · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf cut _ ha he) ha hb
      ((Term.allLt_iff _ _).mp hH z he) hNext
  · rw [hSelf] at he; cases he

theorem Omega_fund_parametric_support [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (t : new.T (k + 3)) (ht0 : t ≠ .Z)
    (hn : RecursiveWF (k + 3) (new.T.fund s t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) →
      UpdatedCoefficient k v s t z ∨ InsertedCoefficient v cut (convert (k + 3) (code t)) z := by
  cases heS : s with
  | Z => rw [heS, new.T.dom] at hd; cases hd
  | P xs b =>
    rw [heS] at hr hs hd hn
    by_cases hb : b = .Z
    · subst b
      have hdom := hd
      rw [new.T.dom] at hdom
      simp only [↓reduceIte] at hdom
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [hm] at hdom; cases hdom
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchildD := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        cases d with
        | zero | omega => simp only [hm] at hdom; cases hdom
        | one =>
          obtain ⟨n, hin⟩ := i
          cases n with
          | zero => simp only [hm, ↓reduceIte] at hdom; cases hdom
          | succ m =>
            simp only [hm, show m + 1 ≠ 0 by omega, ↓reduceIte] at hdom
            have he := new.Dom.Omega.inj hdom
            subst q
            intro z hz
            exact Or.inr (hc.fundSupport t ht0 v z hz)
        | Omega ys =>
          simp only [hm] at hdom
          by_cases hlt : Vec.lt xs ys
          · simp only [hlt, ↓reduceIte] at hdom; cases hdom
          · simp only [hlt, ↓reduceIte] at hdom
            have he := new.Dom.Omega.inj hdom
            subst q
            have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
            have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
            have hf : new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
              simp only [new.T.fund, ↓reduceIte, hm, hlt, GetElem.getElem]
            have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) t) := by
              have hw := hn
              rw [hf, RecursiveWF] at hw
              simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
            have hchildCoef := Omega_fund_parametric_support k (xs.idx i) hchildR (hcoords i)
              hchildD cut hc t ht0 hnChild v hvR hv hOmega
            exact parent_Omega_updated_or_support k xs ys i hm hr hs hd t hn v hvR hv hOmega
              (InsertedCoefficient v cut (convert (k + 3) (code t))) hchildCoef
    · have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      have hdb : new.T.dom b = .Omega q := by simpa only [new.T.dom, ite_eq_right hb] using hd
      have hnB : RecursiveWF (k + 3) (new.T.fund b t) := by
        have hw := hn
        rw [new.T.fund, ite_eq_right hb, RecursiveWF] at hw
        exact hw.2.1
      have htailCoef := Omega_fund_parametric_support k b hbr hbw hdb cut hc t ht0 hnB v hvR hv hOmega
      intro z hz
      rw [new.T.fund, ite_eq_right hb, code, convert] at hz
      rcases H_assemble_support v _ _ hz with hz | hz
      · exact Or.inl (Or.inr (Or.inl (by
          simp only [code, convert]
          exact H_assemble_left v _ _ hz)))
      · rcases htailCoef z hz with hu | he
        · apply Or.inl
          rcases hu with he | ho | ⟨a, ha, hw, hmA, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl
            simp only [code, convert]
            exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
            simp only [code, convert]
            exact hmA.elim (fun h => Or.inl (H_assemble_right v _ _ h))
              (fun h => Or.inr (H_assemble_right v _ _ h))
        · exact Or.inr he
termination_by new.T.size s
decreasing_by
  all_goals rw [heS]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem Omega_fund_relative_of_bounded_parameter [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hSource : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : new.T (k + 3)) (ht0 : t ≠ .Z)
    (hn : RecursiveWF (k + 3) (new.T.fund s t))
    (hBound : ∀ z, InsertedCoefficient v cut (convert (k + 3) (code t)) z →
      Term.lt z (convert (k + 3) (code (new.T.fund s t))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s t))))
      (convert (k + 3) (code (new.T.fund s t))) = true := by
  have hn0 : convert (k + 3) (code (new.T.fund s t)) ≠ .zero := by
    intro he
    exact domOmega_fund_ne_zero _ _ hd
      (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  cases heS : s with
  | Z => rw [heS, new.T.dom] at hd; cases hd
  | P xs b =>
    rw [heS] at hr hs hd hn hSource hBound hn0
    by_cases hb : b = .Z
    · subst b
      have hdom := hd
      rw [new.T.dom] at hdom
      simp only [↓reduceIte] at hdom
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [hm] at hdom; cases hdom
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchildD := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        cases d with
        | zero | omega => simp only [hm] at hdom; cases hdom
        | one =>
          obtain ⟨n, hin⟩ := i
          cases n with
          | zero => simp only [hm, ↓reduceIte] at hdom; cases hdom
          | succ m =>
            simp only [hm, show m + 1 ≠ 0 by omega, ↓reduceIte] at hdom
            have he := new.Dom.Omega.inj hdom
            subst q
            apply (Term.allLt_iff _ _).mpr
            intro z hz
            exact hBound z (hc.fundSupport t ht0 v z hz)
        | Omega ys =>
          simp only [hm] at hdom
          by_cases hlt : Vec.lt xs ys
          · simp only [hlt, ↓reduceIte] at hdom; cases hdom
          · simp only [hlt, ↓reduceIte] at hdom
            have he := new.Dom.Omega.inj hdom
            subst q
            have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
            have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
            have hf : new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
              simp only [new.T.fund, ↓reduceIte, hm, hlt, GetElem.getElem]
            have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) t) := by
              have hw := hn
              rw [hf, RecursiveWF] at hw
              simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
            have hchildCoef := Omega_fund_parametric_support k (xs.idx i) hchildR (hcoords i)
              hchildD cut hc t ht0 hnChild v hvR hv hOmega
            exact parent_Omega_relative_of_updated_or_bounded k xs ys i hm hr hs hd t hn
              v hvR hv hOmega (InsertedCoefficient v cut (convert (k + 3) (code t)))
              hBound hchildCoef hSource
    · have hs0 : convert (k + 3) (code (.P xs b)) ≠ .zero := by
        intro he
        have heP : (.P xs b : new.T (k + 3)) = .Z :=
          code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
        cases heP
      have hcoef := Omega_fund_parametric_support k (.P xs b) hr hs hd cut hc t ht0 hn
        v hvR hv hOmega
      exact closed_of_updated_or_bounded k v _ t hs hn (Omega_image_head_ne_one k _ hr hs hd)
        hs0 hn0 (fun a ha => sum_subterm_gap xs b t hb (Omega_head_mass_pos xs b hr hd) hd ha)
        (InsertedCoefficient v cut (convert (k + 3) (code t))) hBound hcoef hSource

theorem Omega_fund_closed_at_cut_of_wf [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (hCut : Term.lt Term.bigOmega cut = true)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : new.T (k + 3)) (ht : RecursiveWF (k + 3) t)
    (hT : Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (hn : RecursiveWF (k + 3) (new.T.fund s t))
    (hNext : Term.lt (convert (k + 3) (code t)) (convert (k + 3) (code (new.T.fund s t))) = true) :
    Term.allLt (Term.H cut (convert (k + 3) (code (new.T.fund s t))))
      (convert (k + 3) (code (new.T.fund s t))) = true := by
  by_cases ht0 : t = .Z
  · subst t
    exact (zero_fund_invariant k s hr hs).2.2 cut hc.regular hc.cutWf hSource
  have hn0 : convert (k + 3) (code (new.T.fund s t)) ≠ .zero := by
    intro he
    exact domOmega_fund_ne_zero _ _ hd
      (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  apply Omega_fund_relative_of_bounded_parameter k s hr hs hd cut hc cut hc.regular hc.cutWf hCut hSource t ht0 hn
  intro z hz
  exact inserted_coefficient_bound_at_self cut _ _ ht.wf hn.wf hn0 hc.selfEmpty hT hNext hz

theorem Omega_fund_at_label_cut_closed [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (hCut : Term.lt Term.bigOmega cut = true)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : new.T (k + 3)) (ht : RecursiveWF (k + 3) t)
    (hT : Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (hNext : new.T.lt t (new.T.fund s t)) :
    RecursiveWF (k + 3) (new.T.fund s t) ∧
    Term.allLt (Term.H cut (convert (k + 3) (code (new.T.fund s t))))
      (convert (k + 3) (code (new.T.fund s t))) = true := by
  have hn := (Omega_fund_at_label_cut_invariant k s hr hs hd cut hc t ht hT).1
  exact ⟨hn, Omega_fund_closed_at_cut_of_wf k s hr hs hd cut hc hCut hSource t ht hT hn
    ((convert_order k _ _ ht hn).mp hNext)⟩

theorem Omega_iter_at_label_cut [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (n : Nat) :
    RecursiveWF (k + 3) (new.T.iter (new.T.fund s) (new.T.ofNat n)) ∧
    Term.allLt (Term.H cut (convert (k + 3) (code (new.T.iter (new.T.fund s) (new.T.ofNat n)))))
      (convert (k + 3) (code (new.T.iter (new.T.fund s) (new.T.ofNat n)))) = true := by
  by_cases he : cut = Term.bigOmega
  · subst cut
    exact all_Omega_iter_closed k s hr hs hd ((H_omega_bound_iff_subterms k s hs hr).mp hSource) n
  have hCut : Term.lt Term.bigOmega cut = true := by
    rcases lemma_6_1.{u}.2.2 Term.bigOmega cut Term.wf_bigOmega hc.cutWf with h | h | h
    · exact h
    · exact False.elim (he h.symm)
    · rw [Support.CountableTarget.regular_not_below_omega hc.regular] at h; cases h
  induction n with
  | zero =>
    simp only [new.T.ofNat, new.T.iter]
    exact ⟨Support.GeneralImageWFInvariant.recursive_zero _ _, by simp [code, convert, Term.H, Term.allLt]⟩
  | succ n ih =>
    rw [iter_ofNat_succ]
    apply Omega_fund_at_label_cut_closed k s hr hs hd cut hc hCut hSource _ ih.1 ih.2
    exact (iter_ofNat_succ (new.T.fund s) n) ▸ domOmega_iter_lt_next s hd n

inductive OmegaLabelPath {lam : Nat} (q : Vec (new.T lam) lam) : new.T lam → Prop
  | regular (hq : RegularVector q) : OmegaLabelPath q (.P q .Z)
  | inherit (xs : Vec (new.T lam) lam) (i : Fin lam)
      (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hnd : ¬Vec.lt xs q)
      (hc : OmegaLabelPath q (xs.idx i)) : OmegaLabelPath q (.P xs .Z)
  | tail (xs : Vec (new.T lam) lam) (b : new.T lam) (hb : b ≠ .Z)
      (hc : OmegaLabelPath q b) : OmegaLabelPath q (.P xs b)

theorem OmegaLabelPath.domain {lam : Nat} {q : Vec (new.T lam) lam} {s : new.T lam}
    (hp : OmegaLabelPath q s) : new.T.dom s = .Omega q := by
  induction hp with
  | regular hq => exact regularVector_dom hq
  | inherit xs i hm hnd hc ih => simp only [new.T.dom, ↓reduceIte, hm, hnd]
  | tail xs b hb hc ih => simpa only [new.T.dom, ite_eq_right hb] using ih

theorem OmegaLabelPath.of_domain {lam : Nat} (s : new.T lam)
    {q : Vec (new.T lam) lam} (hd : new.T.dom s = .Omega q) : OmegaLabelPath q s := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [new.T.dom] at hd
      simp only [↓reduceIte] at hd
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          simp only [hm] at hd
          by_cases hi : i.val = 0
          · simp only [hi, ↓reduceIte] at hd; cases hd
          · simp only [hi, ↓reduceIte] at hd
            have he := new.Dom.Omega.inj hd
            subst q
            exact .regular ⟨i, by omega, hm⟩
        | Omega ys =>
          simp only [hm] at hd
          by_cases hnd : Vec.lt xs ys
          · simp only [hnd, ↓reduceIte] at hd; cases hd
          · simp only [hnd, ↓reduceIte] at hd
            have he := new.Dom.Omega.inj hd
            subst q
            exact .inherit xs i hm hnd
              (OmegaLabelPath.of_domain (xs.idx i) (Support.DimensionCut.minIdx_spec xs hm).1.symm)
    · apply OmegaLabelPath.tail xs b hb
      exact OmegaLabelPath.of_domain b (by simpa only [new.T.dom, ite_eq_right hb] using hd)
termination_by new.T.size s
decreasing_by
  all_goals simp_all only [new.T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

theorem Omega_label_subterm_lift {lam : Nat} (s : new.T lam)
    {q : Vec (new.T lam) lam} (hd : new.T.dom s = .Omega q)
    {a : new.T lam} (ha : Subterm a (.P q .Z)) : Subterm a s := by
  have hp := OmegaLabelPath.of_domain s hd
  induction hp with
  | regular _ => exact ha
  | inherit xs i _ _ hc ih => exact Subterm.trans (ih hc.domain) (Subterm.coordinate xs .Z i)
  | tail xs b _ hc ih => exact Subterm.trans (ih hc.domain) (Subterm.tail xs b)

theorem Omega_label_coefficient_lift [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (.P q .Z))) →
      z ∈ Term.H v (convert (k + 3) (code s)) := by
  have hL := (Omega_label_recursiveWF k s hs hd).wf
  have hp := OmegaLabelPath.of_domain s hd
  induction hp with
  | regular _ => exact fun _ hz => hz
  | inherit xs i hm hnd hc ih =>
    have hchildD := hc.domain
    have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
    have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
    have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchildD; cases hchildD
    have hNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
      intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
    have hdParent : new.T.dom (.P xs .Z) = .Omega q := by simp only [new.T.dom, ↓reduceIte, hm, hnd]
    have hCoef := ih hcr hcw hchildD
    intro z hz
    have hChildCoef := hCoef z hz
    by_cases hib : i.val ≤ k + 1
    · obtain ⟨w, heOld, _⟩ := principal_replacement_psi_images k xs i hib
        (Support.DimensionCut.minIdx_spec xs hm).2.2 (xs.idx i) hNZ hNZ
        (Omega_image_drop k _ hcr hcw hchildD) (Omega_principal_image_ne_low k xs i hs hdParent)
      have hw := ((Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)).2.1
      have hwR := ((Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)).1
      have hLw : Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
        cases w with
        | zero | add | psi => cases hwR
        | inacc n a =>
          exact le_psi_index_bound n a _ _ hL (heOld ▸ hs.wf)
            (heOld ▸ cofinality_image_le k _ hr hs hdParent)
      have hVw : Term.lt v w = true := by
        rcases (Term.le_iff_eq_or_lt _ _).mp hVL with he | he
        · simpa only [← he] using hLw
        · exact lemma_6_1.{u}.2.1 _ _ _ hv hL hw he hLw
      have hwV : Term.lt w v = false := by
        cases he : Term.lt w v with
        | false => rfl
        | true =>
          have hh := lemma_6_1.{u}.2.1 _ _ _ hw hv hw he hVw
          rw [lt_self] at hh; cases hh
      by_cases hskip : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = true
      · have hLpred := target_le_trans hL hs.wf ((sem_of_wf.{u} hv).isR_pred hvR).1
          (cofinality_image_le k _ hr hs hdParent) hskip
        rw [H_eq_nil_of_le_pred v _ hvR hv hL hLpred] at hz; cases hz
      have hskipF : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = false := by
        cases he : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) <;> simp_all
      rw [heOld] at hskipF
      rw [heOld, Term.H, hskipF, hwV]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hChildCoef)
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
      rw [heSource, H_topNode_above_Omega k _ hc0 v hOmega, Omega_image_drop k _ hcr hcw hchildD]
      exact hChildCoef
  | tail xs b hb hc ih =>
    have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
    have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
    intro z hz
    simp only [code, convert]
    exact H_assemble_right v _ _ (ih hbr hbw hc.domain z hz)

theorem Omega_cut_dominated_below_label [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true) :
    ∀ z, z ∈ Term.H v cut → DominatedCoefficient k v s z := by
  have hlr := Omega_label_recursive k s hr hd
  have hlw := Omega_label_recursiveWF k s hs hd
  have embed := Omega_label_coefficient_lift k s hr hs hd v hvR hv hOmega hVL
  intro z hz
  rcases hc.cutSupport v hOmega z hz with he | he
  · exact Or.inl he
  have hCoeff := UpdatedCoefficient.dominated k v (.P q .Z) .Z hlw
    ((zero_fund_invariant k (.P q .Z) hlr hlw).2.1 v hvR hv hOmega z he)
  rcases hCoeff with he | he | ⟨a, ha, hmem, hbound⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl (embed z he))
  · exact Or.inr (Or.inr ⟨a, Omega_label_subterm_lift s hd ha,
      hmem.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), hbound⟩)

theorem Omega_iter_coefficient_support_at_label_cut [LargeCardinals.{u}]
    (k : Nat) (s : new.T (k + 3)) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) (n : Nat) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (new.T.iter (new.T.fund s) (new.T.ofNat n))))) :
    DominatedCoefficient k v s z ∨ Term.lt z (convert (k + 3) (code s)) = true := by
  have hs0 : s ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hL := (Omega_label_recursiveWF k s hs hd).wf
  induction n with
  | zero => simp only [new.T.ofNat, new.T.iter, code, convert, Term.H] at hz; cases hz
  | succ n ih =>
    rw [iter_ofNat_succ] at hz
    let t := new.T.iter (new.T.fund s) (new.T.ofNat n)
    by_cases ht0 : t = .Z
    · change z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) at hz
      rw [ht0] at hz
      exact Or.inl (UpdatedCoefficient.dominated k v s .Z hs
        ((zero_fund_invariant k s hr hs).2.1 v hvR hv hOmega z hz))
    have hInv := Omega_iter_at_label_cut k s hr hs hd cut hc hSource n
    have hn := (Omega_fund_at_label_cut_invariant k s hr hs hd cut hc t hInv.1 hInv.2).1
    by_cases hAbove : Term.lt (convert (k + 3) (code (.P q .Z))) v = true
    · exact Or.inl (UpdatedCoefficient.dominated k v s t hs
        (((Omega_fund_at_label_cut_invariant k s hr hs hd cut hc t hInv.1 hInv.2).2 v hvR hv hOmega hAbove).1 z hz))
    have hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true := by
      rcases lemma_6_1.{u}.2.2 v _ hv hL with he | he | he
      · simp [Term.le, he]
      · simp [Term.le, he]
      · exact False.elim (hAbove he)
    have htLt : Term.lt (convert (k + 3) (code t)) (convert (k + 3) (code s)) = true := by
      apply (convert_order k _ _ hInv.1 hs).mp
      cases n with
      | zero => exact False.elim (ht0 (by simp only [t, new.T.ofNat, new.T.iter]))
      | succ n =>
        change new.T.lt (new.T.iter (new.T.fund s) (new.T.ofNat (n + 1))) s
        rw [iter_ofNat_succ]; exact fund_lt s _ hs0
    rcases Omega_fund_parametric_support k s hr hs hd cut hc t ht0 hn v hvR hv hOmega z hz with ho | ho
    · exact Or.inl (UpdatedCoefficient.dominated k v s t hs ho)
    · rcases ho with he | he | he | he | he
      · exact Or.inl (Or.inl he)
      · rw [he]; exact Or.inr htLt
      · rw [he]; exact Or.inr (dropOne_lt_of_lt hInv.1.wf hs.wf htLt)
      · exact ih he
      · exact Or.inl (Omega_cut_dominated_below_label k s hr hs hd cut hc v hvR hv hOmega hVL z he)

end Support.GeneralImageParametricCut

namespace Support.GeneralImageEmptyCutDiagonal

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageCofinalityBounds Support.GeneralImageCofinalityCoefficients
open Support.GeneralImageOmegaSpine Support.GeneralImageParametricCut
open Support.GeneralImageSharedTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageOmegaContext
open Support.GeneralImageMiddleCofinality Support.GeneralImageCofinalityInheritance
open Support.GeneralImageMiddleSums
open Support.GeneralImageDominatedCoefficients Support.GeneralImageHeadCuts
open Support.GeneralImageHighestDiagonal Support.GeneralImageCountableInheritance
open Support.GeneralImageCountableLayers Support.GeneralImageCountableRecursion
open Support.GeneralImageOmegaCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageZeroFund
open Support.SourceOmegaHighest Support.GeneralImageHighOmega

universe u

theorem empty_le_regular (i : Nat) (cut : Term) (hc : Term.isRT cut = true)
    (hi : i ≤ Term.fT cut) : Term.le (.inacc i .zero) cut = true := by
  cases cut with
  | zero | add | psi => cases hc
  | inacc j a =>
    by_cases hij : i < j
    · simp [Term.le, Term.lt, hij]
    · have he : i = j := by simp only [Term.fT] at hi; omega
      subst j
      cases a <;> simp [Term.le, Term.lt]

end Support.GeneralImageEmptyCutDiagonal

namespace Support.GeneralImageLabelClosure

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageParametricCut Support.GeneralImageOmegaSpine
open Support.GeneralImageLabelCut Support.GeneralImageCofinalityBounds
open Support.GeneralImageMiddleSums Support.GeneralImageZeroFund
open Support.GeneralImageOmegaCoefficients Support.GeneralImageOmegaCofinality
open Support.GeneralImageDominatedCoefficients Support.GeneralImageRelativePredecessor
open Support.SourceRecursiveDescending Support.SourceFundOrder Support.SourceFundGap
open Support.SourceSubtermBounds Support.GeneralImageLimitSupport
open Support.SourceOmegaInvariant

universe u

theorem Omega_label_mass_le {lam : Nat} (s : new.T lam)
    {q : Vec (new.T lam) lam} (hd : new.T.dom s = .Omega q) :
    mass (.P q .Z) ≤ mass s := by
  have hp := OmegaLabelPath.of_domain s hd
  induction hp with
  | regular _ => exact Nat.le_refl _
  | inherit xs i _ _ hc ih =>
    have hi := ih hc.domain
    have hm := vectorMass_idx_le xs i
    simp only [mass, Nat.add_zero] at hi ⊢
    omega
  | tail xs b _ hc ih =>
    have hi := ih hc.domain
    simp only [mass, Nat.add_zero] at hi ⊢
    omega

theorem Omega_cut_bound_after_update [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true)
    (hSource : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : new.T (k + 3)) (ht0 : t ≠ .Z)
    (hn : RecursiveWF (k + 3) (new.T.fund s t)) :
    ∀ z, z ∈ Term.H v cut → Term.lt z (convert (k + 3) (code (new.T.fund s t))) = true := by
  have hlr := Omega_label_recursive k s hr hd
  have hlw := Omega_label_recursiveWF k s hs hd
  have hb := (zero_fund_invariant k (.P q .Z) hlr hlw).1
  have hn0 : convert (k + 3) (code (new.T.fund s t)) ≠ .zero := by
    intro he; exact domOmega_fund_ne_zero _ _ hd
      (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have hs0 : convert (k + 3) (code s) ≠ .zero := by
    intro he
    have heS : s = .Z := code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
    rw [heS, new.T.dom] at hd; cases hd
  have hhead := Omega_image_head_ne_one k s hr hs hd
  have oldBound (a : new.T (k + 3)) (ha : Subterm a s)
      (hmem : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) :
      Term.lt (convert (k + 3) (code a)) (convert (k + 3) (code s)) = true := by
    rcases hmem with he | he
    · exact (Term.allLt_iff _ _).mp hSource _ he
    · exact undrop_lt_head_ne_one _ _ (ha.recursiveWF hs).wf hs.wf hs0 hhead
        ((Term.allLt_iff _ _).mp hSource _ he)
  intro z hz
  rcases hc.cutSupport v hOmega z hz with he | hBase
  · rw [he]; exact (zero_lt_iff _).mpr hn0
  have hDom := Omega_cut_dominated_below_label k s hr hs hd cut hc v hvR hv hOmega hVL z hz
  have hOld : Term.lt z (convert (k + 3) (code s)) = true := by
    rcases hDom with he | he | ⟨a, ha, hmem, hle⟩
    · rw [he]; exact (zero_lt_iff _).mpr hs0
    · exact (Term.allLt_iff _ _).mp hSource _ he
    · rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
      · rw [he]; exact oldBound a ha hmem
      · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf v cut hc.cutWf hz)
          (ha.recursiveWF hs).wf hs.wf he (oldBound a ha hmem)
  rcases H_convert_source k v (new.T.fund (.P q .Z) .Z) hBase with he | ⟨a, ha, he⟩
  · rw [he]; exact (zero_lt_iff _).mpr hn0
  · have haw := ha.recursiveWF hb
    have haOld : new.T.lt a s := by
      apply (convert_order k _ _ haw hs).mpr
      rcases he with he | he
      · simpa only [← he] using hOld
      · exact undrop_lt_head_ne_one _ _ haw.wf hs.wf hs0 hhead (he ▸ hOld)
    have hmass := Support.SourceCoefficientGap.mass_lt_of_subterm ha
    have hbMass := mass_fund_zero_le (.P q .Z : new.T (k + 3))
    have hgMass := zeroGap_le_mass (.P q .Z : new.T (k + 3))
    have hlMass := Omega_label_mass_le s hd
    have haGap : mass a < gap s t := by rw [gap_nonzero _ _ ht0]; omega
    have hNew := (convert_order k _ _ haw hn).mp (small_lt_fund_all s t a haOld haGap)
    rcases he with rfl | rfl
    · exact hNew
    · exact dropOne_lt_of_lt haw.wf hn.wf hNew

theorem Omega_fund_at_label_cut_relative [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (t : new.T (k + 3)) (htr : Recursive t) (ht : RecursiveWF (k + 3) t)
    (hTC : Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (hNext : new.T.lt t (new.T.fund s t)) :
    RecursiveWF (k + 3) (new.T.fund s t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s t))))
          (convert (k + 3) (code (new.T.fund s t))) = true := by
  have hInv := Omega_fund_at_label_cut_invariant k s hr hs hd cut hc t ht hTC
  have hn := hInv.1
  refine ⟨hn, ?_⟩
  intro v hvR hv hSource hT
  by_cases ht0 : t = .Z
  · subst t; exact (zero_fund_invariant k s hr hs).2.2 v hvR hv hSource
  rcases lemma_6_1.{u}.2.2 Term.bigOmega v Term.wf_bigOmega hv with hOmega | he | hOmega
  · by_cases hAbove : Term.lt (convert (k + 3) (code (.P q .Z))) v = true
    · exact (hInv.2 v hvR hv hOmega hAbove).2 hSource
    have hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true := by
      rcases lemma_6_1.{u}.2.2 v _ hv (Omega_label_recursiveWF k s hs hd).wf with he | he | he
      · simp [Term.le, he]
      · simp [Term.le, he]
      · exact False.elim (hAbove he)
    have hn0 : convert (k + 3) (code (new.T.fund s t)) ≠ .zero := by
      intro he; exact domOmega_fund_ne_zero _ _ hd
        (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
    have hNextImage := (convert_order k _ _ ht hn).mp hNext
    apply Omega_fund_relative_of_bounded_parameter k s hr hs hd cut hc v hvR hv hOmega hSource t ht0 hn
    intro z hz
    rcases hz with he | he | he | he | he
    · rw [he]; exact (zero_lt_iff _).mpr hn0
    · rw [he]; exact hNextImage
    · rw [he]; exact dropOne_lt_of_lt ht.wf hn.wf hNextImage
    · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf v _ ht.wf he) ht.wf hn.wf
        ((Term.allLt_iff _ _).mp hT _ he) hNextImage
    · exact Omega_cut_bound_after_update k s hr hs hd cut hc v hvR hv hOmega hVL hSource t ht0 hn z he
  · subst v
    exact H_convert_bound_of_subterms k Term.bigOmega _ hn
      (fund_Omega_subterms s t hr hd ((H_omega_bound_iff_subterms k s hs hr).mp hSource)
        ((H_omega_bound_iff_subterms k t ht htr).mp hT) hNext)
  · rw [Support.CountableTarget.regular_not_below_omega hvR] at hOmega; cases hOmega

theorem Omega_iter_at_label_cut_relative [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (n : Nat) :
    RecursiveWF (k + 3) (new.T.iter (new.T.fund s) (new.T.ofNat n)) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.iter (new.T.fund s) (new.T.ofNat n)))))
          (convert (k + 3) (code (new.T.iter (new.T.fund s) (new.T.ofNat n)))) = true := by
  induction n with
  | zero =>
    simp only [new.T.ofNat, new.T.iter]
    exact ⟨recursive_zero _ _, by intros; simp only [code, convert, Term.H, Term.allLt, List.all_nil]⟩
  | succ n ih =>
    have hInv := Omega_iter_at_label_cut k s hr hs hd cut hc hSource n
    have htr := iter_recursive (new.T.fund s) (fun a ha => fund_recursive s a hr ha)
      (new.T.ofNat n) (ofNat_recursive (k + 3) n)
    have hNew := Omega_fund_at_label_cut_relative k s hr hs hd cut hc _ htr hInv.1 hInv.2
      ((iter_ofNat_succ (new.T.fund s) n) ▸ domOmega_iter_lt_next s hd n)
    rw [iter_ofNat_succ]
    exact ⟨hNew.1, fun v hvR hv hV => hNew.2 v hvR hv hV (ih.2 v hvR hv hV)⟩

end Support.GeneralImageLabelClosure

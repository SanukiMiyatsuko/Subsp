import Subsp.multi.kuma.Cofinality

/-! Omega spines, dominated coefficients, label cuts (`CutFund`) and Omega fund at the label cut
(the `multi` version of `Subsp/Support/LabelCut.lean`). -/

namespace kumakuma.GeneralImageHighestDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageCountableInheritance kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageOmegaContext

universe u

theorem highest_regular_fund_shape (k : Nat) (b t : multi.T) :
    T.fund (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) t =
      .P (V.set (lastVec (k + 2) b) (k + 1) t) .Z := by
  have hg : V.get0 (lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b)) (k + 1 + 1) =
      kumakuma.SourceSuccessor.succ (k + 3) b := by rw [get0_lastVec, ite_eq_left rfl]
  have hf : V.fnz (lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b)) = some (k + 1 + 1) :=
    fnz_lastVec (k + 2) (kumakuma.SourceSuccessor.succ_ne_zero _ b)
  rw [topNode, fund_one_succ hf (by rw [hg]; exact kumakuma.SourceSuccessor.dom_succ _ _) t, hg,
    kumakuma.SourceSuccessor.fund_succ]
  rw [show k + 1 + 1 = k + 2 from rfl, kumakuma.SourceOmegaHighest.lastVec_replace_last]

theorem highest_regular_fund_zero (k : Nat) (b : multi.T) :
    T.fund (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) .Z = topNode k b := by
  rw [highest_regular_fund_shape, topNode]
  congr 1
  apply set_eq_self
  rw [get0_lastVec, ite_eq_right (by omega)]

theorem highest_regular_image (k : Nat) (b : multi.T) :
    convert (k + 3) (code (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b))) =
      pairCut (k + 1) (convert (k + 3) (code b)) := by
  rw [convert_topNode k _ (kumakuma.SourceSuccessor.succ_ne_zero _ b), convert_succ]
  by_cases hb : convert (k + 3) (code b) = .zero
  · simp [hb, pairCut, succTerm, dropOne, Term.one]
  · simp only [drop_succ _ hb, pairCut, hb, ↓reduceIte]

theorem get0_highest_set (k : Nat) (b t : multi.T) (j : Nat) :
    V.get0 (V.set (lastVec (k + 2) b) (k + 1) t) j =
      if j = k + 1 then t else if j = k + 2 then b else .Z := by
  rw [V.get0_set _ (k + 1) t j (by rw [lastVec_length]; omega), get0_lastVec]

theorem highest_regular_fund_image (k : Nat) (b t : multi.T) (ht : t ≠ .Z) :
    convert (k + 3) (code (T.fund (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) t)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code b))) (dropOne (convert (k + 3) (code t))) := by
  have htI : convert (k + 3) (code t) ≠ .zero :=
    fun he => ht ((convert_eq_zero_iff _ _).1 he)
  let xs := V.set (lastVec (k + 2) b) (k + 1) t
  let args := arguments (k + 3) (trim (codes xs))
  have htop : args[k + 2]?.getD .zero = convert (k + 3) (code b) := by
    rw [converted_coordinate xs (k + 2), get0_highest_set, ite_eq_right (by omega), ite_eq_left rfl]
  have hmid : args[k + 1]?.getD .zero = convert (k + 3) (code t) := by
    rw [converted_coordinate xs (k + 1), get0_highest_set, ite_eq_left rfl]
  have hzero : ∀ j, j < k + 1 → args[j]?.getD .zero = .zero := by
    intro j hj
    rw [converted_coordinate xs j, get0_highest_set, ite_eq_right (by omega), ite_eq_right (by omega),
      convert_Z]
  rw [highest_regular_fund_shape, convert_principal, principal_as_layers]
  change lower (k + 1) args (topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)) = _
  rw [htop, hmid, lower_keep _ _ _ (by simp [topPair, htI]) hzero]
  simp [topPair, pairCut, htI]

theorem highest_regular_fund_at_cut (k : Nat) (b t : multi.T)
    (hb : RecursiveWF (k + 3) b) (ht : RecursiveWF (k + 3) t) (ht0 : t ≠ .Z)
    (hroot : Term.wf (.psi (pairCut (k + 1) (convert (k + 3) (code b)))
      (dropOne (convert (k + 3) (code t)))) = true) :
    RecursiveWF (k + 3) (T.fund (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) t) := by
  have hw : Term.wf (convert (k + 3)
      (code (T.fund (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) t))) = true := by
    rw [highest_regular_fund_image k b t ht0]; exact hroot
  rw [highest_regular_fund_shape] at hw ⊢
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, hw⟩
  intro i
  rw [get0_highest_set]
  split
  · exact ht
  · split
    · exact hb
    · exact recursive_zero _

theorem highest_base_image (k : Nat) (b : multi.T) :
    convert (k + 3) (code (topNode k b)) =
      if convert (k + 3) (code b) = .zero then Term.one
      else topPair (k + 1) (convert (k + 3) (code b)) .zero := by
  by_cases hb : convert (k + 3) (code b) = .zero
  · have hbZ : b = .Z := (convert_eq_zero_iff _ _).1 hb
    have he : lastVec (k + 2) .Z = lowVec (k + 2) .Z := by rw [lowVec_Z]; rfl
    rw [ite_eq_left hb, hbZ, topNode, he, convert_low_principal, convert_Z]
    rfl
  · have hbZ : b ≠ .Z := fun he => hb ((convert_eq_zero_iff _ _).2 he)
    rw [ite_eq_right hb, convert_topNode k b hbZ]
    simp [topPair, hb]

theorem highest_cut_base_support (k : Nat) (b : multi.T) (v : Term) {z : Term}
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

theorem diagonal_parent_relative_above (k : Nat)
    (xs : V multi.T) (i : Nat) (q : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hd : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (n : Nat) (hnat : 0 < n)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))))
      (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))) = true := by
  classical
  have hil : i < xs.length := fnz_lt_length hf
  have hik : i < k + 3 := by rw [← hsD.length]; exact hil
  have hlow := (V.fnz_some_spec xs i hf).2
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)) := Dim_fund _ _ hsD (Dim_ofNatD _ _)
  let a := multi.T.iter (T.fund (V.get0 xs i)) (ofNatD (k + 3) (n + 1))
  have ha0 : a ≠ .Z := domOmega_fund_ne_zero _ _ hd
  have hfund : T.fund (.P xs .Z) (ofNatD (k + 3) n) = .P (V.set xs i a) .Z := fund_diag hf hd hdiag _
  have hib : i ≤ k + 1 := by
    apply Classical.byContradiction; intro he
    have hi : i = k + 2 := by omega
    subst hi
    exact no_diagonal_highest k xs hsD hs hchildR hf hd hdiag
  have hcNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  have haNZ : convert (k + 3) (code a) ≠ .zero := fun he => ha0 ((convert_eq_zero_iff _ _).1 he)
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff (k + 3) (k + 2) (V.get0 xs i)).mpr
      ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (V.get0 xs i)) .Z)
      hsD (Dim_lowVec hchildDim (Dim_Z _)) hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    rw [heSource, fund_low_Omega (k + 2) _ _ q hd, H_low_empty_above_Omega v hOmega]
    rfl
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow a hcNZ haNZ
      (Omega_image_drop k _ hchildDim hchildR (hcoords i) hd) hIsLow
    have heFund := hfund ▸ heNew
    have hlt := (convert_order k _ _ hnD hsD hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
    rw [heOld, heFund] at hlt
    have hparentLtChild := (convert_order k _ _ hsD hchildDim hs (hcoords i)).mp
      (diagonal_principal_lt_argument xs _ hchildR hd hdiag)
    have ctx (z : Term)
        (hz : z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n))))) :
        z ∈ Term.H v w ∧ z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) := by
      rw [heFund] at hz
      rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz
        with ⟨hw, ho⟩ | ⟨_, hroot, _⟩
      · exact ⟨hw, heOld ▸ ho⟩
      · have hback := (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
        have hfalse := kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ (hcoords i).wf hs.wf (hcoords i).wf hback hparentLtChild
        rw [lt_self] at hfalse; cases hfalse
    by_cases hex : ∃ j, i ≠ j ∧ V.get0 xs j ≠ .Z
    · obtain ⟨j, hij, hj⟩ := hex
      have ht : ofNatD (k + 3) n ≠ .Z := by
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact ofNatD_succ_ne _ _
      have hdom : domF (.P xs .Z) = .omega := domF_diag hf hd hdiag
      exact closed_of_updated_coefficients k v _ _ hsD (Dim_ofNatD _ _) hs hn
        (omega_image_head_ne_one k _ hsD hs hdom) (convert_ne_zero xs .Z)
        (by rw [hfund]; exact convert_ne_zero _ _)
        (fun t htS => positive_principal_subterm_gap xs i j hij hc0 hj _ ht htS)
        (fun z hz => Or.inr (Or.inl (ctx z hz).2)) hH
    · have hother : ∀ j, j ≠ i → V.get0 xs j = .Z := by
        intro j hj; apply Classical.byContradiction; intro hz
        exact hex ⟨j, fun he => hj he.symm, hz⟩
      have hip : 0 < i := by
        apply Nat.pos_of_ne_zero
        intro hi0
        subst hi0
        have he : xs = lowVec (k + 2) (V.get0 xs 0) := by
          apply V.eq_of_get0 _ _ (by rw [hsD.length, lowVec_length])
          intro j
          rw [get0_lowVec]
          by_cases hj : j = 0
          · rw [ite_eq_left hj, hj]
          · rw [ite_eq_right hj]; exact hother j hj
        apply hIsLow
        conv => lhs; rw [he]
        rw [convert_low_principal]
      have heSingle := convert_positive_single k xs i hip hib hlow
        (fun j hj => hother j (by omega)) hc0
      rw [Omega_image_drop k _ hchildDim hchildR (hcoords i) hd] at heSingle
      have hNewW : w = .inacc i .zero := by
        rw [heOld] at heSingle; exact (Term.psi.inj heSingle).1
      apply (Term.allLt_iff _ _).mpr; intro z hz
      have hctx := (ctx z hz).1
      rw [hNewW] at hctx
      simp [Term.H, Term.hOne, hOmega] at hctx

end kumakuma.GeneralImageHighestDiagonal

namespace kumakuma.GeneralImageRegularDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageOmegaContext
open kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableInheritance

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
    rw [kumakuma.DimensionImage.lower_zero_context j xs hj (fun i _ hi => hzero i hi), hzero 0 hj]
    rfl
  · rw [ite_eq_right ha]
    exact lower_keep j xs a ha hzero


theorem principal_insertion_context (k m : Nat) (hm : m ≤ k)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hzero : ∀ i, i < m + 1 → V.get0 xs i = .Z) :
    ∃ a, Above m a ∧
      convert (k + 3) (code (.P xs .Z)) = (if a = .zero then Term.one else a) ∧
      ∀ t : multi.T, t ≠ .Z →
        convert (k + 3) (code (.P (V.set xs m t) .Z)) =
          step m a (convert (k + 3) (code t)) := by
  have hml : m < xs.length := by rw [hsD.length]; omega
  let args := arguments (k + 3) (trim (codes xs))
  let top := topPair (k + 1) (args[k + 2]?.getD .zero) (args[k + 1]?.getD .zero)
  obtain ⟨a, ha, hformula⟩ := lower_coordinate_context (k + 1) m (by omega) args top
    (topPair_context _ _ _)
  refine ⟨a, context_above ha, ?_, ?_⟩
  · rw [convert_principal, principal_as_layers]
    change lower (k + 1) args top = _
    rw [hformula args (fun _ _ _ => rfl)]
    exact lower_zero_block (m + 1) (by omega) args a (fun i hi => by
      rw [converted_coordinate xs i, hzero i hi, convert_Z])
  · intro t ht
    let ys := V.set xs m t
    let newArgs := arguments (k + 3) (trim (codes ys))
    have hs (i : Nat) (hi : m < i) (_ : i < k + 3) :
        newArgs[i]?.getD .zero = args[i]?.getD .zero := by
      rw [converted_coordinate ys i, converted_coordinate xs i]
      show convert (k + 3) (code (V.get0 (V.set xs m t) i)) = _
      rw [V.get0_set_ne xs m t i (by omega)]
    have hnz : convert (k + 3) (code t) ≠ .zero :=
      fun he => ht ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 he)
    rw [convert_principal, principal_as_layers]
    change lower (k + 1) newArgs
      (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) = _
    rw [hs (k + 2) (by omega) (by omega), hs (k + 1) (by omega) (by omega)]
    rw [hformula newArgs (fun i hi hij => hs i hi (by omega)), lower_succ]
    rw [converted_coordinate ys m]
    show lower m newArgs (step m a (convert (k + 3) (code (V.get0 (V.set xs m t) m)))) = _
    rw [V.get0_set_same xs m t hml]
    rw [lower_keep m newArgs _ (step_ne_zero_of_argument m _ _ hnz) (fun i hi => by
      rw [converted_coordinate ys i]
      show convert (k + 3) (code (V.get0 (V.set xs m t) i)) = _
      rw [V.get0_set_ne xs m t i (by omega), hzero i (by omega), convert_Z])]

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

end kumakuma.GeneralImageRegularDiagonal

namespace kumakuma.GeneralImageOmegaSpine

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageRegularDiagonal kumakuma.GeneralImageHighestDiagonal
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageCountableRecursion kumakuma.GeneralImageCountableLayers
open kumakuma.GeneralImageOmegaCoefficients kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageUpperOmega kumakuma.GeneralImageHighOmega kumakuma.SourceOmegaHighest
open kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageRelativePredecessor

universe u

def InsertedCoefficient (v cut a z : Term) : Prop :=
  z = .zero ∨ z = a ∨ z = dropOne a ∨ z ∈ Term.H v a ∨ z ∈ Term.H v cut

structure CutFund (k : Nat) (s : multi.T) (cut : Term) : Prop where
  regular : Term.isRT cut = true
  cutWf : Term.wf cut = true
  selfEmpty : Term.H cut cut = []
  fundWf : ∀ t, RecursiveWF (k + 3) t →
    Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true →
    RecursiveWF (k + 3) (T.fund s t)
  zeroSupport : ∀ z, z ∈ Term.H cut (convert (k + 3) (code (T.fund s .Z))) → z = .zero
  cutSupport : ∀ v, Term.lt Term.bigOmega v = true → ∀ z, z ∈ Term.H v cut →
    z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code (T.fund s .Z)))
  fundSupport : ∀ t, t ≠ .Z → ∀ v z,
    z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) →
    InsertedCoefficient v cut (convert (k + 3) (code t)) z
  baseSupport : ∀ v z, z ∈ Term.H v (convert (k + 3) (code (T.fund s .Z))) →
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
    simp only [layerCut, ha, ↓reduceIte, Term.H, kumakuma.OT2.H_succTerm]
    exact List.mem_append_right _ (List.mem_append_left _ hz)

theorem regular_lower_cutFund_image (k m : Nat)
    (hmk : m ≤ k) (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hfz : V.fnz xs = some (m + 1)) (hdOne : domF (V.get0 xs (m + 1)) = .one)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P xs .Z) cut ∧ Term.fT cut = m ∧
      (∀ t, t ≠ .Z → ∃ a, convert (k + 3) (code (T.fund (.P xs .Z) t)) = .psi cut a) ∧
      ∀ j, m < j → Term.lt (convert (k + 3) (code (T.fund (.P xs .Z) .Z))) (.inacc j .zero) = true →
        Term.lt cut (.inacc j .zero) = true := by
  have hml' : m + 1 < xs.length := fnz_lt_length hfz
  let s := multi.T.P xs .Z
  have hlow := (V.fnz_some_spec xs _ hfz).2
  have hcoords : ∀ i, RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1
  let p := T.fund (V.get0 xs (m + 1)) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hsD.coord _) (hcoords _) hdOne
  have hpD : Dim (k + 3) p := Dim_fund _ _ (hsD.coord _) (Dim_Z _)
  let base := V.set xs (m + 1) p
  have hbaseD : Dim (k + 3) (.P base .Z) := Dim_set hsD (m + 1) hpD _ (Dim_Z _)
  have hbidx (i : Nat) : V.get0 base i = if i = m + 1 then p else V.get0 xs i :=
    V.get0_set xs (m + 1) p i hml'
  have hzBase : ∀ i, i < m + 1 → V.get0 base i = .Z := by
    intro i hi
    rw [hbidx, ite_eq_right (by omega)]
    exact hlow i hi
  have hf (t : multi.T) : T.fund s t = .P (V.set base m t) .Z := fund_one_succ hfz hdOne t
  have hfZero : T.fund s .Z = .P base .Z := by
    rw [hf]; congr 1
    exact set_eq_self _ _ _ (hzBase m (by omega))
  obtain ⟨a, ha, heBase, heInsert⟩ := principal_insertion_context k m hmk base hbaseD hzBase
  have hB : RecursiveWF (k + 3) (.P base .Z) := hfZero ▸ (zero_fund_invariant k s hsD hr hs).1
  have hwA : Term.wf a = true := by
    by_cases ha0 : a = .zero
    · simp [ha0, Term.wf]
    · have := hB.wf
      rwa [heBase, ite_eq_right ha0] at this
  let cut := layerCut m a
  have hCutW : Term.wf cut = true := layerCut_wf m a ha hwA
  have hCutR : Term.isRT cut = true := layerCut_regular m a
  have hCutH : Term.H cut cut = [] := by
    by_cases ha0 : a = .zero
    · by_cases hm0 : m = 0
      · simp [cut, layerCut, ha0, hm0, Term.H]
      · exact layerCut_H_self_empty m (by omega) a ha hwA
    · simpa only [cut, layerCut, ha0, ↓reduceIte, regular] using regular_H_self_empty m a ha hwA
  let arg (t : multi.T) := if m = 0 ∧ a = .zero then convert (k + 3) (code t)
    else dropOne (convert (k + 3) (code t))
  have hNew (t : multi.T) (ht0 : t ≠ .Z) :
      convert (k + 3) (code (T.fund s t)) = .psi cut (arg t) := by
    rw [hf, heInsert t ht0]
    have htNZ : convert (k + 3) (code t) ≠ .zero :=
      fun he => ht0 ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 he)
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
      rw [hf] at hwFull ⊢
      refine RecursiveWF_P.2 ⟨?_, recursive_zero _, hwFull⟩
      intro i
      rw [V.get0_set base m t i (by rw [V.length_set]; omega)]
      split
      · exact ht
      · rw [hbidx]; split
        · exact hp
        · exact hcoords i
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
        · exact kumakuma.OT2.mem_H_dropOne he
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

theorem regular_lower_cutFund (k m : Nat)
    (hmk : m ≤ k) (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hfz : V.fnz xs = some (m + 1)) (hdOne : domF (V.get0 xs (m + 1)) = .one)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P xs .Z) cut := by
  obtain ⟨cut, hc, _, _, _⟩ := regular_lower_cutFund_image k m hmk xs hsD hfz hdOne hr hs
  exact ⟨cut, hc⟩

theorem highest_regular_cutFund_at (k : Nat) (b : multi.T)
    (hs : RecursiveWF (k + 3) (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b))) :
    CutFund k (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b))
      (pairCut (k + 1) (convert (k + 3) (code b))) := by
  have hb : RecursiveWF (k + 3) b := (recursive_succ_iff _ _ _).mp (high_recursive_image k _ hs)
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
    · exact Or.inr (Or.inr (Or.inr (Or.inl (kumakuma.OT2.mem_H_dropOne he))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
  · intro v z hz
    rw [highest_regular_fund_zero] at hz
    by_cases hb0 : b = .Z
    · rw [highest_base_image] at hz
      rw [hb0, convert_Z, ite_eq_left rfl] at hz
      exact Or.inl (H_one_mem hz)
    · rw [convert_topNode k b hb0] at hz
      rcases H_inacc_support (k + 1) _ hz with he | he
      · exact Or.inl he
      · apply Or.inr
        change z ∈ Term.H v (pairCut (k + 1) (convert (k + 3) (code b)))
        have hbNZ : convert (k + 3) (code b) ≠ .zero :=
          fun he => hb0 ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 he)
        simp only [pairCut, hbNZ, ↓reduceIte, Term.H, kumakuma.OT2.H_succTerm]
        exact List.mem_append_right _ (List.mem_append_left _ he)

theorem highest_regular_cutFund (k : Nat) (b : multi.T)
    (hs : RecursiveWF (k + 3) (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b))) :
    ∃ cut, CutFund k (topNode k (kumakuma.SourceSuccessor.succ (k + 3) b)) cut :=
  ⟨pairCut (k + 1) (convert (k + 3) (code b)), highest_regular_cutFund_at k b hs⟩

theorem regular_cutFund (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hfz : V.fnz xs = some (m + 1)) (hdOne : domF (V.get0 xs (m + 1)) = .one)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ cut, CutFund k (.P xs .Z) cut := by
  have hml : m + 1 < k + 3 := by have := fnz_lt_length hfz; rwa [hsD.length] at this
  by_cases hmk : m ≤ k
  · exact regular_lower_cutFund k m hmk xs hsD hfz hdOne hr hs
  · have heM : m = k + 1 := by omega
    subst heM
    obtain ⟨b, hb⟩ := dom_one_succ (V.get0 xs (k + 2)) (hsD.coord _) hdOne
    have heXs : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
      lastVec_of_low hsD.length (V.fnz_some_spec xs _ hfz).2
    have heSource : multi.T.P xs .Z = topNode k (kumakuma.SourceSuccessor.succ (k + 3) b) := by
      rw [topNode, ← hb]
      exact congrArg (fun us => multi.T.P us .Z) heXs
    rw [heSource] at hs ⊢
    exact highest_regular_cutFund k b hs

end kumakuma.GeneralImageOmegaSpine

namespace kumakuma.GeneralImageDominatedCoefficients

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageOmegaSpine kumakuma.SourceFundOrder
open kumakuma.SourceFundGap kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageUpperOmega kumakuma.GeneralImageHighestDiagonal
open kumakuma.GeneralImageCountableRecursion kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageCountableInheritance kumakuma.GeneralImageCountableLayers
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageOmegaContext
open kumakuma.GeneralImageOmegaCoefficients kumakuma.SourceOmegaHighest

universe u

def DominatedCoefficient (k : Nat) (v : Term) (s : multi.T) (z : Term) : Prop :=
  z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code s)) ∨
    ∃ a, Subterm a s ∧
      (convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) ∧
      Term.le z (convert (k + 3) (code a)) = true

theorem UpdatedCoefficient.dominated (k : Nat) (v : Term)
    (s t : multi.T) (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    {z : Term} (hc : UpdatedCoefficient k v s t z) : DominatedCoefficient k v s z := by
  rcases hc with he | he | ⟨a, ha, hw, hm, he⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · refine Or.inr (Or.inr ⟨a, ha, hm, ?_⟩)
    have haW := ha.recursiveWF hs
    have haD := ha.dim hsD
    by_cases ha0 : a = .Z
    · subst a
      rw [fund_Z, convert_Z] at he
      rw [convert_Z]
      rcases he with rfl | rfl <;> simp [dropOne, Term.le]
    · have hl := (convert_order k _ _ (Dim_fund a t haD htD) haD hw haW).mp (fund_lt a t ha0)
      rcases he with rfl | rfl
      · simp [Term.le, hl]
      · simp [Term.le, dropOne_lt_of_lt hw.wf haW.wf hl]

theorem closed_of_dominated_coefficients (k : Nat) (v : Term)
    (s t : multi.T) (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hs0 : convert (k + 3) (code s) ≠ .zero)
    (hn0 : convert (k + 3) (code (T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) → DominatedCoefficient k v s z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
      (convert (k + 3) (code (T.fund s t))) = true := by
  have hnD := Dim_fund s t hsD htD
  have oldBound (a : multi.T) (ha : Subterm a s)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) : a < s := by
    have haW := ha.recursiveWF hs
    apply (convert_order k _ _ (ha.dim hsD) hsD haW hs).mpr
    rcases hm with hm | hm
    · exact (Term.allLt_iff _ _).mp hH _ hm
    · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hs0 hhead ((Term.allLt_iff _ _).mp hH _ hm)
  have bound (a : multi.T) (ha : Subterm a s)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) :
      Term.lt (convert (k + 3) (code a)) (convert (k + 3) (code (T.fund s t))) = true :=
    (convert_order k _ _ (ha.dim hsD) hnD (ha.recursiveWF hs) hn).mp
      (small_lt_fund_all s t a (oldBound a ha hm) (hgap a ha))
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
    · exact kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ (H_coefficient_wf v _ hn.wf hz) (ha.recursiveWF hs).wf hn.wf
        he (bound a ha hm)

theorem dominated_child_coefficients_below_parent (k : Nat)
    (xs : V multi.T) (i : Nat) (t a : multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (htD : Dim (k + 3) t) (ht : t ≠ .Z) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t)) (ha : RecursiveWF (k + 3) a)
    (hhead : Term.head (convert (k + 3) (code (.P xs .Z))) ≠ Term.one)
    (hn0 : convert (k + 3) (code (T.fund (.P xs .Z) t)) ≠ .zero) (v : Term)
    (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (V.get0 xs i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))))
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code a)) →
      DominatedCoefficient k v (V.get0 xs i) z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code a)) →
      Term.lt z (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true := by
  have hc : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hnD := Dim_fund _ t hsD htD
  have hs0 : convert (k + 3) (code (.P xs .Z)) ≠ .zero := convert_ne_zero xs .Z
  have bound (b : multi.T) (hb : Subterm b (V.get0 xs i))
      (hm : convert (k + 3) (code b) ∈ Term.H v (convert (k + 3) (code (V.get0 xs i))) ∨
        dropOne (convert (k + 3) (code b)) ∈ Term.H v (convert (k + 3) (code (V.get0 xs i)))) :
      Term.lt (convert (k + 3) (code b)) (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true := by
    have hbW := hb.recursiveWF hc
    have hbD := hb.dim hcD
    have hbOld : b < .P xs .Z := by
      apply (convert_order k _ _ hbD hsD hbW hs).mpr
      rcases hm with hm | hm
      · exact (Term.allLt_iff _ _).mp hH _ (embed _ hm)
      · exact undrop_lt_head_ne_one _ _ hbW.wf hs.wf hs0 hhead
          ((Term.allLt_iff _ _).mp hH _ (embed _ hm))
    have hgap : mass b < gap (.P xs .Z) t := by
      have hmass := kumakuma.SourceCoefficientGap.mass_lt_of_subterm hb
      have hi := vectorMass_get0_le xs i
      rw [gap, ite_eq_right ht, mass_P, mass_Z]; omega
    exact (convert_order k _ _ hbD hnD hbW hn).mp (small_lt_fund_all (.P xs .Z) t b hbOld hgap)
  intro z hz
  rcases hcoef z hz with he | ho | ⟨b, hb, hm, he⟩
  · rw [he]; exact (zero_lt_iff _).mpr hn0
  · rcases H_convert_source k v (V.get0 xs i) ho with rfl | ⟨b, hb, he⟩
    · exact (zero_lt_iff _).mpr hn0
    · have hm := he.elim (fun h => Or.inl (h ▸ ho)) (fun h => Or.inr (h ▸ ho))
      rcases he with rfl | rfl
      · exact bound b hb hm
      · exact dropOne_lt_of_lt (hb.recursiveWF hc).wf hn.wf (bound b hb hm)
  · rcases (Term.le_iff_eq_or_lt _ _).mp he with he | he
    · rw [he]; exact bound b hb hm
    · exact kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ (H_coefficient_wf v _ ha.wf hz) (hb.recursiveWF hc).wf hn.wf
        he (bound b hb hm)

theorem inherited_omega_dominated_support (k : Nat)
    (xs : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hfz : V.fnz xs = some i) (hd : domF (V.get0 xs i) = .omega)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) (hnat : 0 < n)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (V.get0 xs i) (ofNatD (k + 3) n)))) →
      DominatedCoefficient k v (V.get0 xs i) z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))) →
      DominatedCoefficient k v (.P xs .Z) z := by
  have hil : i < xs.length := fnz_lt_length hfz
  have hik : i < k + 3 := by rw [← hsD.length]; exact hil
  have hlow := (V.fnz_some_spec xs i hfz).2
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hfz).1
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hdrop := drop_image_of_omega k _ hcD (hcoords i) hd
  have hnChild0 := omega_fund_nat_ne_zero _ hd (k + 3) n hnat
  have hf : T.fund (.P xs .Z) (ofNatD (k + 3) n) =
      .P (V.set xs i (T.fund (V.get0 xs i) (ofNatD (k + 3) n))) .Z := fund_omega hfz hd _
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) (ofNatD (k + 3) n)) := by
    have hw := (RecursiveWF_P.1 (hf ▸ hn)).1 i
    rwa [V.get0_set_same xs i _ hil] at hw
  have hnChildD : Dim (k + 3) (T.fund (V.get0 xs i) (ofNatD (k + 3) n)) :=
    Dim_fund _ _ hcD (Dim_ofNatD _ _)
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)) := Dim_fund _ _ hsD (Dim_ofNatD _ _)
  have hcNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  have hnNZ : convert (k + 3) (code (T.fund (V.get0 xs i) (ofNatD (k + 3) n))) ≠ .zero :=
    fun he => hnChild0 ((convert_eq_zero_iff _ _).1 he)
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (V.get0 xs i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term}
      (hc : DominatedCoefficient k v (V.get0 xs i) z) : DominatedCoefficient k v (.P xs .Z) z := by
    rcases hc with he | ho | ⟨a, ha, hmA, hle⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl (embed _ ho))
    · exact Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i),
        hmA.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), hle⟩)
  intro z hz
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff (k + 3) (k + 2) (V.get0 xs i)).mpr
      ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (V.get0 xs i)) .Z)
      hsD (Dim_lowVec hcD (Dim_Z _)) hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    rw [heSource, fund_low_omega (k + 2) _ _ hd, H_low_empty_above_Omega v hOmega] at hz; cases hz
  · by_cases hib : i ≤ k + 1
    · obtain ⟨w, heOld, heNew⟩ :=
        principal_replacement_psi_images k xs i hib hlow _ hcNZ hnNZ hdrop hIsLow
      have heFund := hf ▸ heNew
      have hlt := (convert_order k _ _ hnD hsD hn hs).mp (fund_lt (.P xs .Z) _ (by intro he; cases he))
      rw [heOld, heFund] at hlt
      rw [heFund] at hz
      rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz
        with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
      · exact Or.inr (Or.inl (heOld ▸ ho))
      · rcases he with he | hzChild
        · refine Or.inr (Or.inr ⟨V.get0 xs i, Subterm.coordinate xs .Z i,
            Or.inl (heOld ▸ hroot), ?_⟩)
          rw [he]
          have hl := (convert_order k _ _ hnChildD hcD hnChild (hcoords i)).mp (fund_lt _ _ hc0)
          simp [Term.le, dropOne_lt_of_lt hnChild.wf (hcoords i).wf hl]
        · exact lift (fun z hz => heOld ▸ hchild z hz) (hcoef z hzChild)
    · have hi : i = k + 2 := by omega
      subst hi
      have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := lastVec_of_low hsD.length hlow
      have heOld : multi.T.P xs .Z = topNode k (V.get0 xs (k + 2)) := by
        rw [topNode]; exact congrArg (fun us => multi.T.P us .Z) he
      have heR : V.set xs (k + 2) (T.fund (V.get0 xs (k + 2)) (ofNatD (k + 3) n)) =
          lastVec (k + 2) (T.fund (V.get0 xs (k + 2)) (ofNatD (k + 3) n)) := by
        have := lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
          (T.fund (V.get0 xs (k + 2)) (ofNatD (k + 3) n))
        rw [← he] at this; exact this
      have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) =
          Term.H v (convert (k + 3) (code (V.get0 xs (k + 2)))) := by
        rw [heOld, H_topNode_above_Omega k _ hc0 v hOmega, hdrop]
      rw [hf, heR, ← topNode, H_topNode_above_Omega k _ hnChild0 v hOmega] at hz
      exact lift (fun z hz => heH ▸ hz) (hcoef z (kumakuma.OT2.mem_H_dropOne hz))

theorem inherited_omega_dominated_relative_above (k : Nat)
    (xs : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hfz : V.fnz xs = some i) (hd : domF (V.get0 xs i) = .omega)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) (hnat : 0 < n)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (V.get0 xs i) (ofNatD (k + 3) n)))) →
      DominatedCoefficient k v (V.get0 xs i) z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))))
      (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))) = true := by
  classical
  have hil : i < xs.length := fnz_lt_length hfz
  have hik : i < k + 3 := by rw [← hsD.length]; exact hil
  have hlow := (V.fnz_some_spec xs i hfz).2
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hfz).1
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hdrop := drop_image_of_omega k _ hcD (hcoords i) hd
  have hnChild0 := omega_fund_nat_ne_zero _ hd (k + 3) n hnat
  have ht : ofNatD (k + 3) n ≠ .Z := by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    exact ofNatD_succ_ne _ _
  have hdom : domF (.P xs .Z) = .omega := domF_omega hfz hd
  have hhead := omega_image_head_ne_one k _ hsD hs hdom
  have hf : T.fund (.P xs .Z) (ofNatD (k + 3) n) =
      .P (V.set xs i (T.fund (V.get0 xs i) (ofNatD (k + 3) n))) .Z := fund_omega hfz hd _
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) (ofNatD (k + 3) n)) := by
    have hw := (RecursiveWF_P.1 (hf ▸ hn)).1 i
    rwa [V.get0_set_same xs i _ hil] at hw
  have hnChildD : Dim (k + 3) (T.fund (V.get0 xs i) (ofNatD (k + 3) n)) :=
    Dim_fund _ _ hcD (Dim_ofNatD _ _)
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)) := Dim_fund _ _ hsD (Dim_ofNatD _ _)
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := convert_ne_zero xs .Z
  have hnZ : convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n))) ≠ .zero := by
    rw [hf]; exact convert_ne_zero _ _
  by_cases hex : ∃ j, i ≠ j ∧ V.get0 xs j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact closed_of_dominated_coefficients k v _ _ hsD (Dim_ofNatD _ _) hs hn hhead hsZ hnZ
      (fun a ha => positive_principal_subterm_gap xs i j hij hc0 hj _ ht ha)
      (inherited_omega_dominated_support k xs i hsD hfz hd hs n hnat hn v hvR hv hOmega hcoef) hH
  · have hother : ∀ j, j ≠ i → V.get0 xs j = .Z := by
      intro j hj
      apply Classical.byContradiction; intro hz
      exact hex ⟨j, fun he => hj he.symm, hz⟩
    by_cases hi0 : i = 0
    · subst hi0
      have he : xs = lowVec (k + 2) (V.get0 xs 0) := by
        apply V.eq_of_get0 _ _ (by rw [hsD.length, lowVec_length])
        intro j
        rw [get0_lowVec]
        by_cases hj : j = 0
        · rw [ite_eq_left hj, hj]
        · rw [ite_eq_right hj]; exact hother j hj
      have hfLow : T.fund (.P xs .Z) (ofNatD (k + 3) n) =
          .P (lowVec (k + 2) (T.fund (V.get0 xs 0) (ofNatD (k + 3) n))) .Z := by
        have := fund_low_omega (k + 2) _ (ofNatD (k + 3) n) hd
        rw [← he] at this; exact this
      rw [hfLow, H_low_empty_above_Omega v hOmega]
      rfl
    · by_cases hib : i ≤ k + 1
      · have hip : 0 < i := by omega
        have hhigh (j : Nat) (hj : i < j) : V.get0 xs j = .Z := hother j (by omega)
        have heOld := convert_positive_single k xs i hip hib hlow hhigh hc0
        rw [hdrop] at heOld
        let ys := V.set xs i (T.fund (V.get0 xs i) (ofNatD (k + 3) n))
        have hys (j : Nat) : V.get0 ys j =
            if j = i then T.fund (V.get0 xs i) (ofNatD (k + 3) n) else V.get0 xs j :=
          V.get0_set xs i _ j hil
        have hnewLow (j : Nat) (hj : j < i) : V.get0 ys j = .Z := by
          rw [hys, ite_eq_right (by omega)]; exact hlow j hj
        have hnewHigh (j : Nat) (hj : i < j) : V.get0 ys j = .Z := by
          rw [hys, ite_eq_right (by omega)]; exact hhigh j hj
        have hnewIdx : V.get0 ys i = T.fund (V.get0 xs i) (ofNatD (k + 3) n) := by
          rw [hys, ite_eq_left rfl]
        have heNew := convert_positive_single k ys i hip hib hnewLow hnewHigh (hnewIdx ▸ hnChild0)
        rw [hnewIdx] at heNew
        have heFund : convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n))) =
            .psi (.inacc i .zero)
              (dropOne (convert (k + 3) (code (T.fund (V.get0 xs i) (ofNatD (k + 3) n))))) := by
          rw [hf]; exact heNew
        have hwOld := heOld ▸ hs.wf
        have hwNew := heFund ▸ hn.wf
        have hlt := (convert_order k _ _ hnD hsD hn hs).mp
          (fund_lt (.P xs .Z) _ (by intro he; cases he))
        rw [heOld, heFund] at hlt
        apply (Term.allLt_iff _ _).mpr
        intro z hz; rw [heFund] at hz
        rcases H_psi_replacement_support v _ _ _ hvR hv hwOld hwNew hlt hz
          with ⟨hctx, _⟩ | ⟨he, hroot, hchild⟩
        · simp [Term.H, Term.hOne, hOmega] at hctx
        · rcases he with he | hzChild
          · rw [he]
            have hOldArg : Term.lt (convert (k + 3) (code (V.get0 xs i)))
                (.psi (.inacc i .zero) (convert (k + 3) (code (V.get0 xs i)))) = true := by
              rw [← heOld]; exact (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
            have hOwn := (psi_argument_lt_iff _ _ hwOld).mp hOldArg
            have hChildLt := (convert_order k _ _ hnChildD hcD hnChild (hcoords i)).mp
              (fund_lt (V.get0 xs i) _ hc0)
            have hOwnW := ((Term.wf_psi_iff _ _).mp hwOld).2.1
            have hNewOwn := kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ hnChild.wf (hcoords i).wf hOwnW hChildLt hOwn
            rw [heFund]
            exact (psi_argument_lt_iff _ _ hwNew).mpr (dropOne_lt_of_lt hnChild.wf hOwnW hNewOwn)
          · exact dominated_child_coefficients_below_parent k xs i _ _ hsD (Dim_ofNatD _ _) ht hs hn
              hnChild hhead hnZ v (fun z hz => heOld ▸ hchild z hz) hcoef hH z hzChild
      · have hi : i = k + 2 := by omega
        subst hi
        have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := lastVec_of_low hsD.length hlow
        have heOld : multi.T.P xs .Z = topNode k (V.get0 xs (k + 2)) := by
          rw [topNode]; exact congrArg (fun us => multi.T.P us .Z) he
        have heR : V.set xs (k + 2) (T.fund (V.get0 xs (k + 2)) (ofNatD (k + 3) n)) =
            lastVec (k + 2) (T.fund (V.get0 xs (k + 2)) (ofNatD (k + 3) n)) := by
          have := lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
            (T.fund (V.get0 xs (k + 2)) (ofNatD (k + 3) n))
          rw [← he] at this; exact this
        have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) =
            Term.H v (convert (k + 3) (code (V.get0 xs (k + 2)))) := by
          rw [heOld, H_topNode_above_Omega k _ hc0 v hOmega, hdrop]
        apply (Term.allLt_iff _ _).mpr
        intro z hz
        rw [hf, heR, ← topNode, H_topNode_above_Omega k _ hnChild0 v hOmega] at hz
        exact dominated_child_coefficients_below_parent k xs (k + 2) _ _ hsD (Dim_ofNatD _ _) ht hs hn
          hnChild hhead hnZ v (fun z hz => heH ▸ hz) hcoef hH z (kumakuma.OT2.mem_H_dropOne hz)

end kumakuma.GeneralImageDominatedCoefficients

namespace kumakuma.GeneralImageLabelCut

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageMiddleCofinality
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageUpperOmega kumakuma.GeneralImageHighOmega
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant
open kumakuma.SourceOmegaTail
open kumakuma.SourceFundGap

open kumakuma.GeneralImageOmegaSpine

universe u

theorem Omega_fund_at_label_cut_invariant (k : Nat) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s →
    ∀ {q : V multi.T}, domF s = .Omega q →
    ∀ (κ : Term), CutFund k (.P q .Z) κ →
    ∀ (t : multi.T), Dim (k + 3) t → RecursiveWF (k + 3) t →
    Term.allLt (Term.H κ (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true →
    RecursiveWF (k + 3) (T.fund s t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P q .Z))) v = true →
        (∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) → UpdatedCoefficient k v s t z) ∧
        (Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
          Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
            (convert (k + 3) (code (T.fund s t))) = true)
  | .Z, _, _, _, _, hd, _, _, _, _, _, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, hsD, hr, hs, q, hd, κ, hcut, t, htD, ht, hHt => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · have hil := fnz_lt_length hf
        have hik : i < k + 3 := by rw [← hsD.length]; exact hil
        cases hc : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hc] at hd; cases hd
        | omega => rw [domF_omega hf hc] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hc] at hd
            cases hd
            have hn := hcut.fundWf t ht hHt
            have hrelative := fund_regular_cofinal_relative_all_of_wf k m xs hsD hf hc hr hs t htD hn
            refine ⟨hn, ?_⟩
            intro v hvR hv hOmega hlt
            exact ⟨fun z hz => H_fund_regular_cofinal_support k m xs hsD hf hc hs t v hvR hv hOmega hlt hz,
              hrelative v hvR hv hOmega hlt⟩
        | Omega q =>
          by_cases hlt : xs < q
          · rw [domF_diag hf hc hlt] at hd; cases hd
          · rw [domF_nondiag hf hc hlt] at hd
            cases hd
            have hd' : domF (.P xs .Z) = .Omega q := domF_nondiag hf hc hlt
            have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
            have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
            have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
            obtain ⟨hnChild, hchildInv⟩ := Omega_fund_at_label_cut_invariant k (V.get0 xs i) hchildDim
              hchildR (hcoords i) hc κ hcut t htD ht hHt
            have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
              fund_nondiag hf hc hlt t
            have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
            have hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t) := by
              rw [hfund]
              by_cases hib : i ≤ k + 1
              · apply principal_replace_cofinal_recursiveWF k xs i hib hsD
                  (V.fnz_some_spec xs i hf).2 hs _ hnChild hc0
                  (Omega_image_drop k _ hchildDim hchildR (hcoords i) hc)
                  (convert (k + 3) (code (.P q .Z))) (Omega_label_recursiveWF k _ hs hd').wf
                  (cofinality_image_le k _ hsD hr hs hd') (Omega_principal_image_ne_low k xs i hsD hs hd')
                intro v hvR hv hOmega hlt' hH
                exact (hchildInv v hvR hv hOmega hlt').2 hH
              · have hi : i = k + 2 := by omega
                subst hi
                have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
                  lastVec_of_low hsD.length (V.fnz_some_spec xs _ hf).2
                have hrplc : V.set xs (k + 2) (T.fund (V.get0 xs (k + 2)) t) =
                    lastVec (k + 2) (T.fund (V.get0 xs (k + 2)) t) := by
                  have := kumakuma.SourceOmegaHighest.lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
                    (T.fund (V.get0 xs (k + 2)) t)
                  rw [← he] at this
                  exact this
                rw [hrplc]
                exact topNode_recursiveWF k _ hnChild
            refine ⟨hn, ?_⟩
            intro v hvR hv hOmega hlt'
            have hcf := (hchildInv v hvR hv hOmega hlt').1
            exact ⟨parent_Omega_updated_support k xs q i hsD hf hc hr hs hd' t htD hn v hvR hv hOmega hcf,
              parent_Omega_relative_of_child_support k xs q i hsD hf hc hr hs hd' t htD hn v hvR hv
                hOmega hcf⟩
    · have hbr : Recursive b := (Recursive_P.1 hr).2.1
      have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
      have hdb : domF b = .Omega q := by rwa [domF_tail xs hb] at hd
      obtain ⟨hnB, htailInv⟩ :=
        Omega_fund_at_label_cut_invariant k b hsD.tail hbr hbw hdb κ hcut t htD ht hHt
      have hn := fund_nonzero_tail_recursiveWF k xs b t hsD htD hs hb hnB
      refine ⟨hn, ?_⟩
      intro v hvR hv hOmega hlt
      have hcoef (z : Term) (hz : z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs b) t)))) :
          UpdatedCoefficient k v (.P xs b) t z := by
        rw [fund_tail xs hb, convert_P] at hz
        rcases H_assemble_support v _ _ hz with hz | hz
        · exact Or.inr (Or.inl (by rw [convert_P]; exact H_assemble_left v _ _ hz))
        · rcases (htailInv v hvR hv hOmega hlt).1 z hz with he | ho | ⟨a, ha, hw, hmA, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl
            rw [convert_P]
            exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
            rw [convert_P]
            exact hmA.elim (fun h => Or.inl (H_assemble_right v _ _ h))
              (fun h => Or.inr (H_assemble_right v _ _ h))
      refine ⟨hcoef, ?_⟩
      intro hH
      have hsZ : convert (k + 3) (code (.P xs b)) ≠ .zero := convert_ne_zero xs b
      have hnZ : convert (k + 3) (code (T.fund (.P xs b) t)) ≠ .zero :=
        fun he => domOmega_fund_ne_zero _ t hd ((convert_eq_zero_iff _ _).1 he)
      exact closed_of_updated_coefficients k v _ t hsD htD hs hn (Omega_image_head_ne_one k _ hsD hr hs hd)
        hsZ hnZ (fun a ha => sum_subterm_gap xs b t hb (Omega_head_mass_pos xs b hr hd) hd ha) hcoef hH
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem Omega_label_recursive : ∀ (s : multi.T),
    Recursive s → ∀ {q : V multi.T}, domF s = .Omega q → Recursive (.P q .Z)
  | .Z, _, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, hr, q, hd => by
    have hr' := Recursive_P.1 hr
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hc : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hc] at hd; cases hd
        | omega => rw [domF_omega hf hc] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hc] at hd
            cases hd
            exact hr
        | Omega ys =>
          by_cases hv : xs < ys
          · rw [domF_diag hf hc hv] at hd; cases hd
          · rw [domF_nondiag hf hc hv] at hd
            cases hd
            exact Omega_label_recursive _ (hr'.1 i) hc
    · rw [domF_tail xs hb] at hd
      exact Omega_label_recursive b hr'.2.1 hd
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem Omega_label_cutFund (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q) :
    ∃ κ, CutFund k (.P q .Z) κ := by
  obtain ⟨i, hi, hfz, hdOne⟩ := domOmega_regular s hd
  cases i with
  | zero => omega
  | succ m =>
    exact regular_cutFund k m q (Dim_Omega_label hsD hd) hfz hdOne (Omega_label_recursive s hr hd)
      (Omega_label_recursiveWF k s hs hd)

end kumakuma.GeneralImageLabelCut

namespace kumakuma.GeneralImageParametricCut

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageMiddleCofinality
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageUpperOmega kumakuma.GeneralImageHighOmega
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant
open kumakuma.SourceOmegaTail

open kumakuma.GeneralImageOmegaSpine

open kumakuma.GeneralImageLabelCut kumakuma.GeneralImageOmegaCofinality
open kumakuma.SourceFundGap kumakuma.SourceOmegaHighest
open kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageDominatedCoefficients

universe u

theorem closed_of_updated_or_bounded (k : Nat) (v : Term)
    (s t : multi.T) (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hnewZero : convert (k + 3) (code (T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (extra : Term → Prop)
    (hBound : ∀ z, extra z → Term.lt z (convert (k + 3) (code (T.fund s t))) = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) →
      UpdatedCoefficient k v s t z ∨ extra z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
      (convert (k + 3) (code (T.fund s t))) = true := by
  have hzlt := (zero_lt_iff _).mpr hnewZero
  have hnD := Dim_fund s t hsD htD
  have oldBound (a : multi.T) (ha : Subterm a s)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) : a < s := by
    have hw := ha.recursiveWF hs
    apply (convert_order k _ _ (ha.dim hsD) hsD hw hs).mpr
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
        have hl := (convert_order k _ _ (ha.dim hsD) hnD hw hn).mp
          (small_lt_fund_all s t a hal (hgap a ha))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
    · by_cases ha0 : a = .Z
      · subst a
        rw [fund_Z, convert_Z] at he
        rcases he with rfl | rfl
        · exact hzlt
        · exact hzlt
      · have hal := oldBound a ha hm
        have haD := ha.dim hsD
        have hl := (convert_order k _ _ (Dim_fund a t haD htD) hnD hw hn).mp
          (T.lt_trans (fund_lt a t ha0) (small_lt_fund_all s t a hal (hgap a ha)))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
  · exact hBound z hex

theorem parent_Omega_updated_or_support (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hd : domF (.P xs .Z) = .Omega q) (t : multi.T) (htD : Dim (k + 3) t)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (extra : Term → Prop)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (V.get0 xs i) t))) →
      UpdatedCoefficient k v (V.get0 xs i) t z ∨ extra z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t))) →
      UpdatedCoefficient k v (.P xs .Z) t z ∨ extra z := by
  have hil : i < xs.length := fnz_lt_length hf
  have hik : i < k + 3 := by rw [← hsD.length]; exact hil
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hcNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  have haNZ : convert (k + 3) (code (T.fund (V.get0 xs i) t)) ≠ .zero :=
    fun he => domOmega_fund_ne_zero _ t hdq ((convert_eq_zero_iff _ _).1 he)
  have hnd : ¬ xs < q := not_diag_of_dom hf hdq hd
  have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
    fund_nondiag hf hdq hnd t
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) t) := Dim_fund _ _ hsD htD
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) t) := by
    have hw := hn
    rw [hfund] at hw
    have := (RecursiveWF_P.1 hw).1 i
    rwa [V.get0_set_same xs i _ hil] at this
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (V.get0 xs i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term}
      (hc : UpdatedCoefficient k v (V.get0 xs i) t z) : UpdatedCoefficient k v (.P xs .Z) t z := by
    rcases hc with he | ho | ⟨a, ha, hw, ho, he⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl (embed _ ho))
    · exact Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i), hw,
        ho.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), he⟩)
  intro z hz
  by_cases hib : i ≤ k + 1
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib
      (V.fnz_some_spec xs i hf).2 _ hcNZ haNZ
      (Omega_image_drop k _ hchildDim hchildR (hcoords i) hdq)
      (Omega_principal_image_ne_low k xs i hsD hs hd)
    have heFund := hfund ▸ heNew
    have hlt := (convert_order k _ _ hnD hsD hn hs).mp (fund_lt (.P xs .Z) t (by intro he; cases he))
    have hwOld := heOld ▸ hs.wf
    have hwNew := heFund ▸ hn.wf
    rw [heOld, heFund] at hlt
    rw [heFund] at hz
    rcases H_psi_replacement_support v w _ _ hvR hv hwOld hwNew hlt hz with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
    · exact Or.inl (Or.inr (Or.inl (heOld ▸ ho)))
    · rcases he with he | hzChild
      · exact Or.inl (Or.inr (Or.inr ⟨V.get0 xs i, Subterm.coordinate xs .Z i, hnChild,
          Or.inl (heOld ▸ hroot), Or.inr he⟩))
      · rcases hcoef z hzChild with hu | hex
        · exact Or.inl (lift (fun z hz => heOld ▸ hchild z hz) hu)
        · exact Or.inr hex
  · have hi : i = k + 2 := by omega
    subst hi
    have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
      lastVec_of_low hsD.length (V.fnz_some_spec xs _ hf).2
    have heOld : (multi.T.P xs .Z) = topNode k (V.get0 xs (k + 2)) :=
      congrArg (fun us => multi.T.P us .Z) he
    have heNew : T.fund (.P xs .Z) t = topNode k (T.fund (V.get0 xs (k + 2)) t) := by
      rw [hfund]
      show multi.T.P _ .Z = multi.T.P _ .Z
      congr 1
      have := kumakuma.SourceOmegaHighest.lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
        (T.fund (V.get0 xs (k + 2)) t)
      rw [← he] at this
      exact this
    have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) =
        Term.H v (convert (k + 3) (code (V.get0 xs (k + 2)))) := by
      rw [heOld]; exact H_topNode_Omega k _ hchildDim hchildR (hcoords _) hdq v hOmega
    rw [heNew, H_topNode_above_Omega k _ (domOmega_fund_ne_zero _ t hdq) v hOmega] at hz
    rcases hcoef z (kumakuma.OT2.mem_H_dropOne hz) with hu | hex
    · exact Or.inl (lift (fun z hz => heH ▸ hz) hu)
    · exact Or.inr hex

theorem topNode_relative_of_updated_or_bounded (k : Nat)
    (a t : multi.T) (haD : Dim (k + 3) a) (htD : Dim (k + 3) t)
    (hr : Recursive a) (ha : RecursiveWF (k + 3) a)
    {q : V multi.T} (hd : domF a = .Omega q)
    (hs : RecursiveWF (k + 3) (topNode k a))
    (hnChild : RecursiveWF (k + 3) (T.fund a t)) (v : Term)
    (hv : Term.lt Term.bigOmega v = true)
    (extra : Term → Prop)
    (hBound : ∀ z, extra z → Term.lt z (convert (k + 3) (code (T.fund (topNode k a) t))) = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund a t))) →
      UpdatedCoefficient k v a t z ∨ extra z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (topNode k a))))
      (convert (k + 3) (code (topNode k a))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund (topNode k a) t))))
      (convert (k + 3) (code (T.fund (topNode k a) t))) = true := by
  have hza : a ≠ .Z := by intro he; rw [he, domF_Z] at hd; cases hd
  have hzn := domOmega_fund_ne_zero a t hd
  have hsD : Dim (k + 3) (topNode k a) := Dim_topNode haD
  have hf : T.fund (topNode k a) t = topNode k (T.fund a t) :=
    highest_Omega_fund (k + 2) a t haD hr hd
  have hnD : Dim (k + 3) (T.fund (topNode k a) t) := Dim_fund _ _ hsD htD
  have hn : RecursiveWF (k + 3) (T.fund (topNode k a) t) := hf ▸ topNode_recursiveWF k _ hnChild
  have hhead : Term.head (convert (k + 3) (code (topNode k a))) ≠ Term.one := by
    rw [convert_topNode k a hza]
    simp only [Term.head, Term.one]
    intro he; cases he
  have hsZ : convert (k + 3) (code (topNode k a)) ≠ .zero := by
    rw [convert_topNode k a hza]; intro he; cases he
  have hnZ : convert (k + 3) (code (T.fund (topNode k a) t)) ≠ .zero := by
    rw [hf, convert_topNode k _ hzn]; intro he; cases he
  have heH := H_topNode_Omega k a haD hr ha hd v hv
  have oldBound (b : multi.T) (hb : Subterm b a)
      (hm : convert (k + 3) (code b) ∈ Term.H v (convert (k + 3) (code a)) ∨
        dropOne (convert (k + 3) (code b)) ∈ Term.H v (convert (k + 3) (code a))) :
      b < topNode k a := by
    have hw := hb.recursiveWF ha
    have oldMem : convert (k + 3) (code b) ∈ Term.H v (convert (k + 3) (code (topNode k a))) ∨
        dropOne (convert (k + 3) (code b)) ∈ Term.H v (convert (k + 3) (code (topNode k a))) := by
      rw [heH]; exact hm
    apply (convert_order k _ _ (hb.dim haD) hsD hw hs).mpr
    rcases oldMem with hm | hm
    · exact (Term.allLt_iff _ _).mp hH _ hm
    · exact undrop_lt_head_ne_one _ _ hw.wf hs.wf hsZ hhead ((Term.allLt_iff _ _).mp hH _ hm)
  have hzlt := (zero_lt_iff _).mpr hnZ
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  have hzOrig := hz
  rw [hf, H_topNode_above_Omega k _ hzn v hv] at hz
  have hzChild := kumakuma.OT2.mem_H_dropOne hz
  rcases hcoef z hzChild with hc | hex
  · rcases hc with he | ho | ⟨b, hb, hw, hm, he⟩
    · rw [he]; exact hzlt
    · rcases H_convert_source k v a ho with rfl | ⟨b, hb, he⟩
      · exact hzlt
      · have hw := hb.recursiveWF ha
        have hal := oldBound b hb (he.elim (fun he => Or.inl (he ▸ ho)) (fun he => Or.inr (he ▸ ho)))
        have hl := (convert_order k _ _ (hb.dim haD) hnD hw hn).mp
          (small_lt_fund_all _ t b hal (topNode_child_subterm_gap k a t haD hr hd hb))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
    · by_cases hb0 : b = .Z
      · subst b
        rw [fund_Z, convert_Z] at he
        rcases he with rfl | rfl
        · exact hzlt
        · exact hzlt
      · have hal := oldBound b hb hm
        have hl := (convert_order k _ _ (Dim_fund b t (hb.dim haD) htD) hnD hw hn).mp
          (T.lt_trans (fund_lt b t hb0)
            (small_lt_fund_all _ t b hal (topNode_child_subterm_gap k a t haD hr hd hb)))
        rcases he with rfl | rfl
        · exact hl
        · exact dropOne_lt_of_lt hw.wf hn.wf hl
  · exact hBound z hex

theorem parent_Omega_relative_of_updated_or_bounded (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hd : domF (.P xs .Z) = .Omega q) (t : multi.T) (htD : Dim (k + 3) t)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (extra : Term → Prop)
    (hBound : ∀ z, extra z → Term.lt z (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (V.get0 xs i) t))) →
      UpdatedCoefficient k v (V.get0 xs i) t z ∨ extra z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t))))
      (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true := by
  classical
  have hil : i < xs.length := fnz_lt_length hf
  have hik : i < k + 3 := by rw [← hsD.length]; exact hil
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hlow := (V.fnz_some_spec xs i hf).2
  have hnd : ¬ xs < q := not_diag_of_dom hf hdq hd
  have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
    fund_nondiag hf hdq hnd t
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) t) := Dim_fund _ _ hsD htD
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) t) := by
    have hw := hn
    rw [hfund] at hw
    have := (RecursiveWF_P.1 hw).1 i
    rwa [V.get0_set_same xs i _ hil] at this
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := convert_ne_zero xs .Z
  have hnZ : convert (k + 3) (code (T.fund (.P xs .Z) t)) ≠ .zero :=
    fun he => domOmega_fund_ne_zero _ t hd ((convert_eq_zero_iff _ _).1 he)
  have hhead := Omega_image_head_ne_one k _ hsD hr hs hd
  by_cases hex : ∃ j, i ≠ j ∧ V.get0 xs j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact closed_of_updated_or_bounded k v _ t hsD htD hs hn hhead hsZ hnZ
      (fun a ha => principal_subterm_gap xs i j hij hc0 hj hd t ha)
      extra hBound
      (parent_Omega_updated_or_support k xs q i hsD hf hdq hr hs hd t htD hn v hvR hv hOmega extra hcoef)
      hH
  · have hother : ∀ j, j ≠ i → V.get0 xs j = .Z := by
      intro j hj
      apply Classical.byContradiction
      intro hz
      exact hex ⟨j, fun he => hj he.symm, hz⟩
    by_cases hib : i ≤ k + 1
    · have hip : 0 < i := by
        apply Nat.pos_of_ne_zero
        intro hi0
        subst hi0
        have he : xs = lowVec (k + 2) (V.get0 xs 0) := by
          apply V.eq_of_get0 _ _ (by rw [hsD.length, lowVec_length])
          intro j
          rw [get0_lowVec]
          by_cases hj : j = 0
          · rw [ite_eq_left hj, hj]
          · rw [ite_eq_right hj]
            exact hother j hj
        have ho : Outer (k + 2) (.P (lowVec (k + 2) (V.get0 xs 0)) .Z) := .cons _ _ .zero
        have hdom := hd
        rw [he] at hdom
        exact SourceFundOrder.outer_not_Omega ho q hdom
      have hhigh (j : Nat) (hj : i < j) : V.get0 xs j = .Z := hother j (by omega)
      have hdrop := Omega_image_drop k _ hchildDim hchildR (hcoords i) hdq
      have heOld := convert_positive_single k xs i hip hib hlow hhigh hc0
      rw [hdrop] at heOld
      let ys := V.set xs i (T.fund (V.get0 xs i) t)
      have hnewLow (j : Nat) (hj : j < i) : V.get0 ys j = .Z := by
        show V.get0 (V.set xs i _) j = _
        rw [V.get0_set_ne xs i _ j (by omega)]
        exact hlow j hj
      have hnewHigh (j : Nat) (hj : i < j) : V.get0 ys j = .Z := by
        show V.get0 (V.set xs i _) j = _
        rw [V.get0_set_ne xs i _ j (by omega)]
        exact hhigh j hj
      have hnewIdx : V.get0 ys i = T.fund (V.get0 xs i) t := V.get0_set_same xs i _ hil
      have hnewNZ : V.get0 ys i ≠ .Z := hnewIdx ▸ domOmega_fund_ne_zero _ t hdq
      have heNew := convert_positive_single k ys i hip hib hnewLow hnewHigh hnewNZ
      rw [hnewIdx] at heNew
      have heFund : convert (k + 3) (code (T.fund (.P xs .Z) t)) =
          .psi (.inacc i .zero) (dropOne (convert (k + 3) (code (T.fund (V.get0 xs i) t)))) :=
        hfund ▸ heNew
      have hwOld := heOld ▸ hs.wf
      have hwNew := heFund ▸ hn.wf
      have hlt := (convert_order k _ _ hnD hsD hn hs).mp (fund_lt (.P xs .Z) t (by intro he; cases he))
      rw [heOld, heFund] at hlt
      have hgapChild (a : multi.T) (ha : Subterm a (V.get0 xs i)) : mass a < gap (.P xs .Z) t := by
        have hmA := kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha
        have hmI := vectorMass_get0_le xs i
        rw [gap_Omega _ _ _ hd, mass_P, mass_Z]
        omega
      have oldBound (a : multi.T) (ha : Subterm a (V.get0 xs i))
          (hmA : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
            dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) :
          a < .P xs .Z := by
        have haW := ha.recursiveWF (hcoords i)
        apply (convert_order k _ _ (ha.dim hchildDim) hsD haW hs).mpr
        rcases hmA with hmA | hmA
        · exact (Term.allLt_iff _ _).mp hH _ hmA
        · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hsZ hhead ((Term.allLt_iff _ _).mp hH _ hmA)
      apply (Term.allLt_iff _ _).mpr
      intro z hz
      have hzFull := hz
      rw [heFund] at hz
      rcases H_psi_replacement_support v _ _ _ hvR hv hwOld hwNew hlt hz with ⟨hctx, _⟩ | ⟨he, hroot, hchild⟩
      · simp [Term.H, Term.hOne, hOmega] at hctx
      · rcases he with he | hzChild
        · rw [he]
          have hOldArg : Term.lt (convert (k + 3) (code (V.get0 xs i)))
              (.psi (.inacc i .zero) (convert (k + 3) (code (V.get0 xs i)))) = true := by
            rw [← heOld]; exact (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
          have hOwn := (psi_argument_lt_iff _ _ hwOld).mp hOldArg
          have hChildLt := (convert_order k _ _ (Dim_fund _ _ hchildDim htD) hchildDim hnChild
            (hcoords i)).mp (fund_lt (V.get0 xs i) t hc0)
          have hOwnW := ((Term.wf_psi_iff _ _).mp hwOld).2.1
          have hNewOwn := kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ hnChild.wf (hcoords i).wf hOwnW hChildLt hOwn
          have hDropOwn := dropOne_lt_of_lt hnChild.wf hOwnW hNewOwn
          rw [heFund]
          exact (psi_argument_lt_iff _ _ hwNew).mpr hDropOwn
        · have embed (a : Term) (ha : a ∈ Term.H v (convert (k + 3) (code (V.get0 xs i)))) :
              a ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) := heOld ▸ hchild a ha
          rcases hcoef z hzChild with hu | hex
          · rcases hu with he | ho | ⟨a, ha, haW, hmA, he⟩
            · rw [he]; exact (zero_lt_iff _).mpr hnZ
            · rcases H_convert_source k v (V.get0 xs i) ho with rfl | ⟨a, ha, he⟩
              · exact (zero_lt_iff _).mpr hnZ
              · have haW := ha.recursiveWF (hcoords i)
                have hOld := oldBound a ha (he.elim (fun he => Or.inl (he ▸ embed _ ho))
                  (fun he => Or.inr (he ▸ embed _ ho)))
                have hNew := (convert_order k _ _ (ha.dim hchildDim) hnD haW hn).mp
                  (small_lt_fund_all (.P xs .Z) t a hOld (hgapChild a ha))
                rcases he with rfl | rfl
                · exact hNew
                · exact dropOne_lt_of_lt haW.wf hn.wf hNew
            · by_cases ha0 : a = .Z
              · subst a
                rw [fund_Z, convert_Z] at he
                rcases he with rfl | rfl
                · exact (zero_lt_iff _).mpr hnZ
                · exact (zero_lt_iff _).mpr hnZ
              · have hOld := oldBound a ha (hmA.elim (fun h => Or.inl (embed _ h))
                  (fun h => Or.inr (embed _ h)))
                have hSmall := small_lt_fund_all (.P xs .Z) t a hOld (hgapChild a ha)
                have hNew := (convert_order k _ _ (Dim_fund a t (ha.dim hchildDim) htD) hnD haW hn).mp
                  (T.lt_trans (fund_lt a t ha0) hSmall)
                rcases he with rfl | rfl
                · exact hNew
                · exact dropOne_lt_of_lt haW.wf hn.wf hNew
          · exact hBound z hex
    · have hi : i = k + 2 := by omega
      subst hi
      have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := lastVec_of_low hsD.length hlow
      have hsource : (multi.T.P xs .Z) = topNode k (V.get0 xs (k + 2)) :=
        congrArg (fun us => multi.T.P us .Z) he
      have htop := topNode_relative_of_updated_or_bounded k (V.get0 xs (k + 2)) t hchildDim htD hchildR
        (hcoords _) hdq (hsource ▸ hs) hnChild v hOmega extra
        (fun z hz => (congrArg (fun s => T.fund s t) hsource) ▸ hBound z hz) hcoef (hsource ▸ hH)
      rw [hsource]
      exact htop

theorem inserted_coefficient_bound_at_self
    (cut a b : Term) (ha : Term.wf a = true) (hb : Term.wf b = true)
    (hb0 : b ≠ .zero) (hSelf : Term.H cut cut = [])
    (hH : Term.allLt (Term.H cut a) a = true) (hNext : Term.lt a b = true)
    {z : Term} (hz : InsertedCoefficient cut cut a z) : Term.lt z b = true := by
  rcases hz with he | he | he | he | he
  · rw [he]; exact (zero_lt_iff _).mpr hb0
  · rw [he]; exact hNext
  · rw [he]; exact dropOne_lt_of_lt ha hb hNext
  · exact kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ (H_coefficient_wf cut _ ha he) ha hb
      ((Term.allLt_iff _ _).mp hH z he) hNext
  · rw [hSelf] at he; cases he

theorem Omega_fund_parametric_support (k : Nat) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s →
    ∀ {q : V multi.T}, domF s = .Omega q →
    ∀ (cut : Term), CutFund k (.P q .Z) cut → ∀ (t : multi.T), Dim (k + 3) t → t ≠ .Z →
    RecursiveWF (k + 3) (T.fund s t) →
    ∀ (v : Term), Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) →
      UpdatedCoefficient k v s t z ∨ InsertedCoefficient v cut (convert (k + 3) (code t)) z
  | .Z, _, _, _, _, hd, _, _, _, _, _, _, _, _, _, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, hsD, hr, hs, q, hd, cut, hc, t, htD, ht0, hn, v, hvR, hv, hOmega => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hcd : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hcd] at hd; cases hd
        | omega => rw [domF_omega hf hcd] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hcd] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hcd] at hd
            cases hd
            intro z hz
            exact Or.inr (hc.fundSupport t ht0 v z hz)
        | Omega ys =>
          by_cases hlt : xs < ys
          · rw [domF_diag hf hcd hlt] at hd; cases hd
          · have hd' := domF_nondiag hf hcd hlt
            have hil := fnz_lt_length hf
            have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
            have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
            have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
              fund_nondiag hf hcd hlt t
            have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) t) := by
              have hw := hn
              rw [hfund] at hw
              have := (RecursiveWF_P.1 hw).1 i
              rwa [V.get0_set_same xs i _ hil] at this
            rw [hd'] at hd
            cases hd
            have hchildCoef := Omega_fund_parametric_support k (V.get0 xs i) (hsD.coord i) hchildR
              (hcoords i) hcd cut hc t htD ht0 hnChild v hvR hv hOmega
            exact parent_Omega_updated_or_support k xs _ i hsD hf hcd hr hs hd' t htD hn v hvR hv hOmega
              (InsertedCoefficient v cut (convert (k + 3) (code t))) hchildCoef
    · have hbr : Recursive b := (Recursive_P.1 hr).2.1
      have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
      have hdb : domF b = .Omega q := by rwa [domF_tail xs hb] at hd
      have hnB : RecursiveWF (k + 3) (T.fund b t) := by
        have hw := hn
        rw [fund_tail xs hb] at hw
        exact (RecursiveWF_P.1 hw).2.1
      have htailCoef := Omega_fund_parametric_support k b hsD.tail hbr hbw hdb cut hc t htD ht0 hnB
        v hvR hv hOmega
      intro z hz
      rw [fund_tail xs hb, convert_P] at hz
      rcases H_assemble_support v _ _ hz with hz | hz
      · exact Or.inl (Or.inr (Or.inl (by rw [convert_P]; exact H_assemble_left v _ _ hz)))
      · rcases htailCoef z hz with hu | he
        · apply Or.inl
          rcases hu with he | ho | ⟨a, ha, hw, hmA, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl
            rw [convert_P]
            exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
            rw [convert_P]
            exact hmA.elim (fun h => Or.inl (H_assemble_right v _ _ h))
              (fun h => Or.inr (H_assemble_right v _ _ h))
        · exact Or.inr he
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem Omega_fund_relative_of_bounded_parameter (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (v : Term) (hvR : Term.isRT v = true)
    (hv : Term.wf v = true) (hOmega : Term.lt Term.bigOmega v = true)
    (hSource : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : multi.T) (htD : Dim (k + 3) t) (ht0 : t ≠ .Z)
    (hn : RecursiveWF (k + 3) (T.fund s t))
    (hBound : ∀ z, InsertedCoefficient v cut (convert (k + 3) (code t)) z →
      Term.lt z (convert (k + 3) (code (T.fund s t))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
      (convert (k + 3) (code (T.fund s t))) = true := by
  have hn0 : convert (k + 3) (code (T.fund s t)) ≠ .zero :=
    fun he => domOmega_fund_ne_zero _ _ hd ((convert_eq_zero_iff _ _).1 he)
  cases s with
  | Z => rw [domF_Z] at hd; cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hcd : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hcd] at hd; cases hd
        | omega => rw [domF_omega hf hcd] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hcd] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hcd] at hd
            cases hd
            apply (Term.allLt_iff _ _).mpr
            intro z hz
            exact hBound z (hc.fundSupport t ht0 v z hz)
        | Omega ys =>
          by_cases hlt : xs < ys
          · rw [domF_diag hf hcd hlt] at hd; cases hd
          · have hd' := domF_nondiag hf hcd hlt
            have hil := fnz_lt_length hf
            have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
            have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
            have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
              fund_nondiag hf hcd hlt t
            have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) t) := by
              have hw := hn
              rw [hfund] at hw
              have := (RecursiveWF_P.1 hw).1 i
              rwa [V.get0_set_same xs i _ hil] at this
            rw [hd'] at hd
            cases hd
            have hchildCoef := Omega_fund_parametric_support k (V.get0 xs i) (hsD.coord i) hchildR
              (hcoords i) hcd cut hc t htD ht0 hnChild v hvR hv hOmega
            exact parent_Omega_relative_of_updated_or_bounded k xs _ i hsD hf hcd hr hs hd' t htD hn
              v hvR hv hOmega (InsertedCoefficient v cut (convert (k + 3) (code t)))
              hBound hchildCoef hSource
    · have hs0 : convert (k + 3) (code (.P xs b)) ≠ .zero := convert_ne_zero xs b
      have hcoef := Omega_fund_parametric_support k (.P xs b) hsD hr hs hd cut hc t htD ht0 hn
        v hvR hv hOmega
      exact closed_of_updated_or_bounded k v _ t hsD htD hs hn (Omega_image_head_ne_one k _ hsD hr hs hd)
        hs0 hn0 (fun a ha => sum_subterm_gap xs b t hb (Omega_head_mass_pos xs b hr hd) hd ha)
        (InsertedCoefficient v cut (convert (k + 3) (code t))) hBound hcoef hSource

theorem Omega_fund_closed_at_cut_of_wf (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (hCut : Term.lt Term.bigOmega cut = true)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : multi.T) (htD : Dim (k + 3) t) (ht : RecursiveWF (k + 3) t)
    (hT : Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (hn : RecursiveWF (k + 3) (T.fund s t))
    (hNext : Term.lt (convert (k + 3) (code t)) (convert (k + 3) (code (T.fund s t))) = true) :
    Term.allLt (Term.H cut (convert (k + 3) (code (T.fund s t))))
      (convert (k + 3) (code (T.fund s t))) = true := by
  by_cases ht0 : t = .Z
  · subst t
    exact (zero_fund_invariant k s hsD hr hs).2.2 cut hc.regular hc.cutWf hSource
  have hn0 : convert (k + 3) (code (T.fund s t)) ≠ .zero :=
    fun he => domOmega_fund_ne_zero _ _ hd ((convert_eq_zero_iff _ _).1 he)
  apply Omega_fund_relative_of_bounded_parameter k s hsD hr hs hd cut hc cut hc.regular hc.cutWf hCut
    hSource t htD ht0 hn
  intro z hz
  exact inserted_coefficient_bound_at_self cut _ _ ht.wf hn.wf hn0 hc.selfEmpty hT hNext hz

theorem Omega_fund_at_label_cut_closed (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut) (hCut : Term.lt Term.bigOmega cut = true)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : multi.T) (htD : Dim (k + 3) t) (ht : RecursiveWF (k + 3) t)
    (hT : Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (hNext : t < T.fund s t) :
    RecursiveWF (k + 3) (T.fund s t) ∧
    Term.allLt (Term.H cut (convert (k + 3) (code (T.fund s t))))
      (convert (k + 3) (code (T.fund s t))) = true := by
  have hn := (Omega_fund_at_label_cut_invariant k s hsD hr hs hd cut hc t htD ht hT).1
  exact ⟨hn, Omega_fund_closed_at_cut_of_wf k s hsD hr hs hd cut hc hCut hSource t htD ht hT hn
    ((convert_order k _ _ htD (Dim_fund _ _ hsD htD) ht hn).mp hNext)⟩

theorem Omega_iter_at_label_cut (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (n : Nat) :
    Dim (k + 3) (multi.T.iter (T.fund s) (ofNatD (k + 3) n)) ∧
    RecursiveWF (k + 3) (multi.T.iter (T.fund s) (ofNatD (k + 3) n)) ∧
    Term.allLt (Term.H cut (convert (k + 3) (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n)))))
      (convert (k + 3) (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n)))) = true := by
  by_cases he : cut = Term.bigOmega
  · subst cut
    exact all_Omega_iter_closed k s hsD hr hs hd ((H_omega_bound_iff_subterms k s hsD hs hr).mp hSource) n
  have hCut : Term.lt Term.bigOmega cut = true := by
    rcases kumakuma.JaegerFacts.jaeger_order.2.2 Term.bigOmega cut Term.wf_bigOmega hc.cutWf with h | h | h
    · exact h
    · exact False.elim (he h.symm)
    · rw [kumakuma.CountableTarget.regular_not_below_omega hc.regular] at h; cases h
  induction n with
  | zero =>
    show Dim (k + 3) .Z ∧ RecursiveWF (k + 3) .Z ∧
      Term.allLt (Term.H cut (convert (k + 3) (code .Z))) (convert (k + 3) (code .Z)) = true
    exact ⟨Dim_Z _, recursive_zero _, by simp [convert_Z, Term.H, Term.allLt]⟩
  | succ n ih =>
    rw [iter_ofNat_succ]
    have hnD := Dim_fund s _ hsD ih.1
    obtain ⟨hn, hH⟩ := Omega_fund_at_label_cut_closed k s hsD hr hs hd cut hc hCut hSource _
      ih.1 ih.2.1 ih.2.2 (domOmega_iter_lt_next s hd (k + 3) n)
    exact ⟨hnD, hn, hH⟩

inductive OmegaLabelPath (q : V multi.T) : multi.T → Prop
  | regular (hq : RegularVector q) : OmegaLabelPath q (.P q .Z)
  | inherit (xs : V multi.T) (i : Nat) (hf : V.fnz xs = some i)
      (hdq : domF (V.get0 xs i) = .Omega q) (hnd : ¬ xs < q)
      (hc : OmegaLabelPath q (V.get0 xs i)) : OmegaLabelPath q (.P xs .Z)
  | tail (xs : V multi.T) (b : multi.T) (hb : b ≠ .Z)
      (hc : OmegaLabelPath q b) : OmegaLabelPath q (.P xs b)

theorem OmegaLabelPath.domain {q : V multi.T} {s : multi.T}
    (hp : OmegaLabelPath q s) : domF s = .Omega q := by
  induction hp with
  | regular hq => exact regularVector_dom hq
  | inherit xs i hf hdq hnd hc ih => exact domF_nondiag hf hdq hnd
  | tail xs b hb hc ih => rw [domF_tail xs hb]; exact ih

theorem OmegaLabelPath.of_domain : ∀ (s : multi.T) {q : V multi.T},
    domF s = .Omega q → OmegaLabelPath q s
  | .Z, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, q, hd => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hc : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hc] at hd; cases hd
        | omega => rw [domF_omega hf hc] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hc] at hd
            cases hd
            exact .regular ⟨m + 1, by omega, hf, hc⟩
        | Omega ys =>
          by_cases hv : xs < ys
          · rw [domF_diag hf hc hv] at hd; cases hd
          · rw [domF_nondiag hf hc hv] at hd
            cases hd
            exact .inherit xs i hf hc hv (OmegaLabelPath.of_domain _ hc)
    · rw [domF_tail xs hb] at hd
      exact .tail xs b hb (OmegaLabelPath.of_domain b hd)
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem Omega_label_subterm_lift (s : multi.T)
    {q : V multi.T} (hd : domF s = .Omega q)
    {a : multi.T} (ha : Subterm a (.P q .Z)) : Subterm a s := by
  have hp := OmegaLabelPath.of_domain s hd
  clear hd
  induction hp with
  | regular _ => exact ha
  | inherit xs i _ _ _ _ ih => exact Subterm.trans ih (Subterm.coordinate xs .Z i)
  | tail xs b _ _ ih => exact Subterm.trans ih (Subterm.tail xs b)

theorem Omega_label_coefficient_lift (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (.P q .Z))) →
      z ∈ Term.H v (convert (k + 3) (code s)) := by
  have hL := (Omega_label_recursiveWF k s hs hd).wf
  have hp := OmegaLabelPath.of_domain s hd
  clear hd
  induction hp with
  | regular _ => exact fun _ hz => hz
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
    have hCoef := ih hcD hcr hcw
    intro z hz
    have hChildCoef := hCoef z hz
    by_cases hib : i ≤ k + 1
    · obtain ⟨w, heOld, _⟩ := principal_replacement_psi_images k xs i hib
        (V.fnz_some_spec xs i hf).2 (V.get0 xs i) hNZ hNZ
        (Omega_image_drop k _ hcD hcr hcw hdq) (Omega_principal_image_ne_low k xs i hsD hs hdParent)
      have hw := ((Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)).2.1
      have hwR := ((Term.wf_psi_iff _ _).mp (heOld ▸ hs.wf)).1
      have hLw : Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
        cases w with
        | zero | add | psi => cases hwR
        | inacc n a =>
          exact le_psi_index_bound n a _ _ hL (heOld ▸ hs.wf)
            (heOld ▸ cofinality_image_le k _ hsD hr hs hdParent)
      have hVw : Term.lt v w = true := by
        rcases (Term.le_iff_eq_or_lt _ _).mp hVL with he | he
        · simpa only [← he] using hLw
        · exact kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ hv hL hw he hLw
      have hwV : Term.lt w v = false := by
        cases he : Term.lt w v with
        | false => rfl
        | true =>
          have hh := kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ hw hv hw he hVw
          rw [lt_self] at hh; cases hh
      by_cases hskip : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = true
      · have hLpred := target_le_trans hL hs.wf ((kumakuma.JaegerFacts.predR_facts hv hvR)).1
          (cofinality_image_le k _ hsD hr hs hdParent) hskip
        rw [H_eq_nil_of_le_pred v _ hvR hv hL hLpred] at hz; cases hz
      have hskipF : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) = false := by
        cases he : Term.le (convert (k + 3) (code (.P xs .Z))) (Term.predR v) <;> simp_all
      rw [heOld] at hskipF
      rw [heOld, Term.H, hskipF, hwV]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hChildCoef)
    · have hi : i = k + 2 := by omega
      subst hi
      have heXs : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
        lastVec_of_low hsD.length (V.fnz_some_spec xs _ hf).2
      have heSource : multi.T.P xs .Z = topNode k (V.get0 xs (k + 2)) :=
        congrArg (fun us => multi.T.P us .Z) heXs
      rw [heSource, H_topNode_above_Omega k _ hc0 v hOmega, Omega_image_drop k _ hcD hcr hcw hdq]
      exact hChildCoef
  | tail xs b hb hc ih =>
    have hbr : Recursive b := (Recursive_P.1 hr).2.1
    have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
    intro z hz
    rw [convert_P]
    exact H_assemble_right v _ _ (ih hsD.tail hbr hbw z hz)

theorem Omega_cut_dominated_below_label (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true) :
    ∀ z, z ∈ Term.H v cut → DominatedCoefficient k v s z := by
  have hlD := Dim_Omega_label hsD hd
  have hlr := Omega_label_recursive s hr hd
  have hlw := Omega_label_recursiveWF k s hs hd
  have embed := Omega_label_coefficient_lift k s hsD hr hs hd v hvR hv hOmega hVL
  intro z hz
  rcases hc.cutSupport v hOmega z hz with he | he
  · exact Or.inl he
  have hCoeff := UpdatedCoefficient.dominated k v (.P q .Z) .Z hlD (Dim_Z _) hlw
    ((zero_fund_invariant k (.P q .Z) hlD hlr hlw).2.1 v hvR hv hOmega z he)
  rcases hCoeff with he | he | ⟨a, ha, hmem, hbound⟩
  · exact Or.inl he
  · exact Or.inr (Or.inl (embed z he))
  · exact Or.inr (Or.inr ⟨a, Omega_label_subterm_lift s hd ha,
      hmem.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), hbound⟩)

theorem Omega_iter_coefficient_support_at_label_cut
    (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) (n : Nat) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n))))) :
    DominatedCoefficient k v s z ∨ Term.lt z (convert (k + 3) (code s)) = true := by
  have hs0 : s ≠ .Z := by intro he; rw [he, domF_Z] at hd; cases hd
  have hL := (Omega_label_recursiveWF k s hs hd).wf
  induction n with
  | zero =>
    have hz' : z ∈ Term.H v (convert (k + 3) (code .Z)) := hz
    rw [convert_Z, Term.H] at hz'; cases hz'
  | succ n ih =>
    rw [iter_ofNat_succ] at hz
    let t := multi.T.iter (T.fund s) (ofNatD (k + 3) n)
    by_cases ht0 : t = .Z
    · change z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) at hz
      rw [ht0] at hz
      exact Or.inl (UpdatedCoefficient.dominated k v s .Z hsD (Dim_Z _) hs
        ((zero_fund_invariant k s hsD hr hs).2.1 v hvR hv hOmega z hz))
    have hInv := Omega_iter_at_label_cut k s hsD hr hs hd cut hc hSource n
    have hInvF := Omega_fund_at_label_cut_invariant k s hsD hr hs hd cut hc t hInv.1 hInv.2.1 hInv.2.2
    have hn := hInvF.1
    by_cases hAbove : Term.lt (convert (k + 3) (code (.P q .Z))) v = true
    · exact Or.inl (UpdatedCoefficient.dominated k v s t hsD hInv.1 hs
        ((hInvF.2 v hvR hv hOmega hAbove).1 z hz))
    have hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true := by
      rcases kumakuma.JaegerFacts.jaeger_order.2.2 v _ hv hL with he | he | he
      · simp [Term.le, he]
      · simp [Term.le, he]
      · exact False.elim (hAbove he)
    have htLt : Term.lt (convert (k + 3) (code t)) (convert (k + 3) (code s)) = true := by
      apply (convert_order k _ _ hInv.1 hsD hInv.2.1 hs).mp
      cases n with
      | zero => exact False.elim (ht0 rfl)
      | succ n =>
        change multi.T.iter (T.fund s) (ofNatD (k + 3) (n + 1)) < s
        rw [iter_ofNat_succ]; exact fund_lt s _ hs0
    rcases Omega_fund_parametric_support k s hsD hr hs hd cut hc t hInv.1 ht0 hn v hvR hv hOmega z hz
      with ho | ho
    · exact Or.inl (UpdatedCoefficient.dominated k v s t hsD hInv.1 hs ho)
    · rcases ho with he | he | he | he | he
      · exact Or.inl (Or.inl he)
      · rw [he]; exact Or.inr htLt
      · rw [he]; exact Or.inr (dropOne_lt_of_lt hInv.2.1.wf hs.wf htLt)
      · exact ih he
      · exact Or.inl (Omega_cut_dominated_below_label k s hsD hr hs hd cut hc v hvR hv hOmega hVL z he)

end kumakuma.GeneralImageParametricCut


namespace kumakuma.GeneralImageEmptyCutDiagonal

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageCofinalityCoefficients
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageParametricCut
open kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageOmegaContext
open kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageCofinalityInheritance
open kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageHeadCuts
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageCountableInheritance
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageZeroFund
open kumakuma.SourceOmegaHighest kumakuma.GeneralImageHighOmega

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

end kumakuma.GeneralImageEmptyCutDiagonal

namespace kumakuma.GeneralImageLabelClosure

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageParametricCut kumakuma.GeneralImageOmegaSpine
open kumakuma.GeneralImageLabelCut kumakuma.GeneralImageCofinalityBounds
open kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageOmegaCoefficients kumakuma.GeneralImageOmegaCofinality
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageRelativePredecessor
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder kumakuma.SourceFundGap
open kumakuma.SourceSubtermBounds kumakuma.GeneralImageLimitSupport
open kumakuma.SourceOmegaInvariant

universe u

theorem Omega_label_mass_le (s : multi.T)
    {q : V multi.T} (hd : domF s = .Omega q) :
    mass (.P q .Z) ≤ mass s := by
  have hp := OmegaLabelPath.of_domain s hd
  clear hd
  induction hp with
  | regular _ => exact Nat.le_refl _
  | inherit xs i _ _ _ _ ih =>
    have hm := vectorMass_get0_le xs i
    have h1 := mass_P q .Z
    have h2 := mass_P xs .Z
    omega
  | tail xs b _ _ ih =>
    have h2 := mass_P xs b
    omega

theorem Omega_cut_bound_after_update (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true)
    (hSource : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (t : multi.T) (htD : Dim (k + 3) t) (ht0 : t ≠ .Z)
    (hn : RecursiveWF (k + 3) (T.fund s t)) :
    ∀ z, z ∈ Term.H v cut → Term.lt z (convert (k + 3) (code (T.fund s t))) = true := by
  have hlD := Dim_Omega_label hsD hd
  have hlr := Omega_label_recursive s hr hd
  have hlw := Omega_label_recursiveWF k s hs hd
  have hb := (zero_fund_invariant k (.P q .Z) hlD hlr hlw).1
  have hbD : Dim (k + 3) (T.fund (.P q .Z) .Z) := Dim_fund _ _ hlD (Dim_Z _)
  have hnD := Dim_fund s t hsD htD
  have hn0 : convert (k + 3) (code (T.fund s t)) ≠ .zero :=
    fun he => domOmega_fund_ne_zero _ _ hd ((convert_eq_zero_iff _ _).1 he)
  have hs0 : convert (k + 3) (code s) ≠ .zero := by
    intro he
    have heS : s = .Z := (convert_eq_zero_iff _ _).1 he
    rw [heS, domF_Z] at hd; cases hd
  have hhead := Omega_image_head_ne_one k s hsD hr hs hd
  have oldBound (a : multi.T) (ha : Subterm a s)
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
  have hDom := Omega_cut_dominated_below_label k s hsD hr hs hd cut hc v hvR hv hOmega hVL z hz
  have hOld : Term.lt z (convert (k + 3) (code s)) = true := by
    rcases hDom with he | he | ⟨a, ha, hmem, hle⟩
    · rw [he]; exact (zero_lt_iff _).mpr hs0
    · exact (Term.allLt_iff _ _).mp hSource _ he
    · rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
      · rw [he]; exact oldBound a ha hmem
      · exact kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ (H_coefficient_wf v cut hc.cutWf hz)
          (ha.recursiveWF hs).wf hs.wf he (oldBound a ha hmem)
  rcases H_convert_source k v (T.fund (.P q .Z) .Z) hBase with he | ⟨a, ha, he⟩
  · rw [he]; exact (zero_lt_iff _).mpr hn0
  · have haw := ha.recursiveWF hb
    have haD := ha.dim hbD
    have haOld : a < s := by
      apply (convert_order k _ _ haD hsD haw hs).mpr
      rcases he with he | he
      · simpa only [← he] using hOld
      · exact undrop_lt_head_ne_one _ _ haw.wf hs.wf hs0 hhead (he ▸ hOld)
    have hmass := kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha
    have hbMass := mass_fund_zero_le (.P q .Z)
    have hgMass := zeroGap_le_mass (.P q .Z)
    have hlMass := Omega_label_mass_le s hd
    have haGap : mass a < gap s t := by rw [gap_nonzero _ _ ht0]; omega
    have hNew := (convert_order k _ _ haD hnD haw hn).mp (small_lt_fund_all s t a haOld haGap)
    rcases he with rfl | rfl
    · exact hNew
    · exact dropOne_lt_of_lt haw.wf hn.wf hNew

theorem Omega_fund_at_label_cut_relative (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (t : multi.T) (htD : Dim (k + 3) t) (htr : Recursive t) (ht : RecursiveWF (k + 3) t)
    (hTC : Term.allLt (Term.H cut (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (hNext : t < T.fund s t) :
    RecursiveWF (k + 3) (T.fund s t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
          (convert (k + 3) (code (T.fund s t))) = true := by
  have hInv := Omega_fund_at_label_cut_invariant k s hsD hr hs hd cut hc t htD ht hTC
  have hn := hInv.1
  have hnD := Dim_fund s t hsD htD
  refine ⟨hn, ?_⟩
  intro v hvR hv hSource hT
  by_cases ht0 : t = .Z
  · subst t; exact (zero_fund_invariant k s hsD hr hs).2.2 v hvR hv hSource
  rcases kumakuma.JaegerFacts.jaeger_order.2.2 Term.bigOmega v Term.wf_bigOmega hv with hOmega | he | hOmega
  · by_cases hAbove : Term.lt (convert (k + 3) (code (.P q .Z))) v = true
    · exact (hInv.2 v hvR hv hOmega hAbove).2 hSource
    have hVL : Term.le v (convert (k + 3) (code (.P q .Z))) = true := by
      rcases kumakuma.JaegerFacts.jaeger_order.2.2 v _ hv (Omega_label_recursiveWF k s hs hd).wf with he | he | he
      · simp [Term.le, he]
      · simp [Term.le, he]
      · exact False.elim (hAbove he)
    have hn0 : convert (k + 3) (code (T.fund s t)) ≠ .zero :=
      fun he => domOmega_fund_ne_zero _ _ hd ((convert_eq_zero_iff _ _).1 he)
    have hNextImage := (convert_order k _ _ htD hnD ht hn).mp hNext
    apply Omega_fund_relative_of_bounded_parameter k s hsD hr hs hd cut hc v hvR hv hOmega hSource t
      htD ht0 hn
    intro z hz
    rcases hz with he | he | he | he | he
    · rw [he]; exact (zero_lt_iff _).mpr hn0
    · rw [he]; exact hNextImage
    · rw [he]; exact dropOne_lt_of_lt ht.wf hn.wf hNextImage
    · exact kumakuma.JaegerFacts.jaeger_order.2.1 _ _ _ (H_coefficient_wf v _ ht.wf he) ht.wf hn.wf
        ((Term.allLt_iff _ _).mp hT _ he) hNextImage
    · exact Omega_cut_bound_after_update k s hsD hr hs hd cut hc v hvR hv hOmega hVL hSource t htD ht0
        hn z he
  · subst v
    exact H_convert_bound_of_subterms k Term.bigOmega _ hnD hn
      (fund_Omega_subterms s t hr hd ((H_omega_bound_iff_subterms k s hsD hs hr).mp hSource)
        ((H_omega_bound_iff_subterms k t htD ht htr).mp hT) hNext)
  · rw [kumakuma.CountableTarget.regular_not_below_omega hvR] at hOmega; cases hOmega

theorem Omega_iter_at_label_cut_relative (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (cut : Term) (hc : CutFund k (.P q .Z) cut)
    (hSource : Term.allLt (Term.H cut (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    (n : Nat) :
    RecursiveWF (k + 3) (multi.T.iter (T.fund s) (ofNatD (k + 3) n)) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n)))))
          (convert (k + 3) (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n)))) = true := by
  induction n with
  | zero =>
    show RecursiveWF (k + 3) .Z ∧ ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code .Z))) (convert (k + 3) (code .Z)) = true
    exact ⟨recursive_zero _, by intros; simp [convert_Z, Term.H, Term.allLt]⟩
  | succ n ih =>
    have hInv := Omega_iter_at_label_cut k s hsD hr hs hd cut hc hSource n
    have htr := iter_recursive (T.fund s) (fun a ha => fund_recursive s a hr ha)
      (ofNatD (k + 3) n) (ofNat_recursive (k + 3) n)
    have hNew := Omega_fund_at_label_cut_relative k s hsD hr hs hd cut hc _ hInv.1 htr hInv.2.1
      hInv.2.2 (domOmega_iter_lt_next s hd (k + 3) n)
    rw [iter_ofNat_succ]
    exact ⟨hNew.1, fun v hvR hv hV => hNew.2 v hvR hv hV (ih.2 v hvR hv hV)⟩

end kumakuma.GeneralImageLabelClosure

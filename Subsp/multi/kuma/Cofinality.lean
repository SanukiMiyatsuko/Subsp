import Subsp.multi.kuma.Omega

/-! Cofinality bounds and preservation of wf under fund at 0 and along omega inheritance (the
`multi` version of `Subsp/Support/Cofinality.lean`). -/

namespace kumakuma.GeneralImageMiddleCofinality

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion kumakuma.GeneralImageChangingMiddle
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageCoefficients kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageOmegaCoefficients kumakuma.SourceOmegaInvariant
open kumakuma.SourceFundGap

universe u

/-- Coordinates after the update at a regular index `m + 1`. -/
theorem get0_set_set {xs : V multi.T} {m : Nat} (hml : m + 1 < xs.length) (p t : multi.T)
    (i : Nat) : V.get0 (V.set (V.set xs (m + 1) p) m t) i =
      if i = m then t else if i = m + 1 then p else V.get0 xs i := by
  rw [V.get0_set _ m t i (by rw [V.length_set]; omega), V.get0_set xs (m + 1) p i hml]

theorem principal_subterm_gap (xs : V multi.T)
    (i j : Nat) (hij : i ≠ j) (hi : V.get0 xs i ≠ .Z) (hj : V.get0 xs j ≠ .Z)
    {v : V multi.T} (hd : domF (.P xs .Z) = .Omega v)
    (t : multi.T) {a : multi.T} (ha : GeneralImageCoefficients.Subterm a (.P xs .Z)) :
    mass a < gap (.P xs .Z) t := by
  have hcoords : ∀ l, mass (V.get0 xs l) < vectorMass xs := by
    intro l
    by_cases hl : l = i
    · subst l
      have hp := vectorMass_pair_le xs i j hij
      have hz := mass_positive hj
      omega
    · have hp := vectorMass_pair_le xs l i hl
      have hz := mass_positive hi
      omega
  have hgap : gap (.P xs .Z) t = vectorMass xs := by
    rw [gap_Omega _ _ _ hd, mass_P, mass_Z]
    omega
  rw [hgap]
  have hgen : ∀ {a s : multi.T}, GeneralImageCoefficients.Subterm a s → s = .P xs .Z →
      mass a < vectorMass xs := by
    intro a s ha
    induction ha with
    | coordinate ys b l => intro he; cases he; exact hcoords l
    | tail ys b =>
      intro he; cases he
      rw [mass_Z]
      exact Nat.lt_of_lt_of_le (mass_positive hi) (vectorMass_get0_le xs i)
    | trans hab hbs iha ihb =>
      intro he
      exact Nat.lt_trans (kumakuma.SourceCoefficientGap.mass_lt_of_subterm hab) (ihb he)
  exact hgen ha rfl

theorem H_inacc_succ_support (v : Term) (n : Nat) (a : Term) {z : Term}
    (hz : z ∈ Term.H v (.inacc n a)) : z ∈ Term.H v (.inacc n (succTerm a)) := by
  rw [Term.H] at hz ⊢
  rcases List.mem_append.mp hz with hz | hz
  · exact List.mem_append_left _ hz
  · apply List.mem_append_right
    rw [kumakuma.OT2.H_succTerm]
    exact List.mem_append_left _ hz

theorem topPair_predecessor_lt [LargeCardinals.{u}] (n : Nat) (h b : Term)
    (hh : Term.wf h = true) (hb : Term.wf b = true) :
    Term.lt (topPair n h b) (topPair n h (succTerm b)) = true := by
  rw [topPair_order n hh hb hh (succTerm_wf hb)]
  simp only [lt_self, decide_true, Bool.true_and, Bool.false_or]
  rw [lt_succTerm_eq_le hb hb]
  simp [Term.le]

theorem H_topPair_predecessor_support [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (n : Nat) (h b : Term)
    (hh : Term.wf h = true) (hb : Term.wf b = true)
    (hi : Term.wf (.inacc n (dropOne h)) = true)
    (hw : Term.wf (topPair n h (succTerm b)) = true) {z : Term}
    (hz : z ∈ Term.H v (topPair n h b)) :
    z ∈ Term.H v (topPair n h (succTerm b)) ∨
      z = dropOne b ∧ dropOne (succTerm b) ∈ Term.H v (topPair n h (succTerm b)) := by
  have hn := topPair_successor_predecessor n h b hi hb hw
  have hl := topPair_predecessor_lt n h b hh hb
  have hp := (sem_of_wf.{u} hv).isR_pred hvR
  have heOld : topPair n h (succTerm b) = .psi (pairCut n h) (dropOne (succTerm b)) := by
    by_cases hh0 : h = .zero <;> simp only [topPair, hh0, succTerm_ne_zero, ↓reduceIte, pairCut]
  by_cases hs : Term.le (topPair n h (succTerm b)) (Term.predR v) = true
  · have he := target_le_trans hn hw hp.1 (by simp [Term.le, hl]) hs
    rw [H_eq_nil_of_le_pred v _ hvR hv hn he] at hz; cases hz
  · by_cases hb0 : b = .zero
    · subst b
      have hc : z ∈ Term.H v (pairCut n h) := by
        by_cases hh0 : h = .zero
        · simp only [topPair, hh0, ↓reduceIte, Term.H] at hz; cases hz
        · simp only [topPair, hh0, ↓reduceIte] at hz
          simpa only [pairCut, hh0, ↓reduceIte] using H_inacc_succ_support v n (dropOne h) hz
      have hsF : Term.le (.psi (pairCut n h) .zero) (Term.predR v) = false := by
        rw [heOld] at hs
        change ¬Term.le (.psi (pairCut n h) .zero) (Term.predR v) = true at hs
        cases he : Term.le (.psi (pairCut n h) .zero) (Term.predR v) <;> simp_all
      apply Or.inl
      rw [heOld]
      change z ∈ Term.H v (.psi (pairCut n h) .zero)
      rw [Term.H, hsF]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · exact hc
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ hc)
    · have heNew : topPair n h b = .psi (pairCut n h) (dropOne b) := by
        by_cases hh0 : h = .zero <;> simp only [topPair, hh0, hb0, ↓reduceIte, pairCut]
      rw [heNew] at hz
      rw [heOld, drop_succ b hb0] at hw
      rcases H_psi_successor_support v (pairCut n h) (dropOne b) hvR hv (dropOne_wf hb) hw hz
        with hm | ⟨he, hm⟩
      · apply Or.inl; rw [heOld, drop_succ b hb0]; exact hm
      · refine Or.inr ⟨he, ?_⟩
        rw [heOld, drop_succ b hb0]; exact hm

def UpdatedCoefficient (k : Nat) (v : Term) (s t : multi.T) (z : Term) : Prop :=
  z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code s)) ∨
    ∃ a, GeneralImageCoefficients.Subterm a s ∧ RecursiveWF (k + 3) (T.fund a t) ∧
      (convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) ∧
      (z = convert (k + 3) (code (T.fund a t)) ∨
        z = dropOne (convert (k + 3) (code (T.fund a t))))

end kumakuma.GeneralImageMiddleCofinality

namespace kumakuma.GeneralImageMiddleSums

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion kumakuma.GeneralImageChangingMiddle
open kumakuma.GeneralImageMiddleCofinality
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant kumakuma.SourceOmegaTail
open kumakuma.SourceFundGap

universe u

theorem undrop_lt_head_ne_one (a s : Term) (ha : Term.wf a = true) (hs : Term.wf s = true)
    (hz : s ≠ .zero) (hh : Term.head s ≠ Term.one)
    (hl : Term.lt (dropOne a) s = true) : Term.lt a s = true := by
  by_cases hhead : Term.head a = Term.one
  · obtain ⟨n, he⟩ := head_one_nat ha hhead
    rw [he]; exact nat_lt_of_head_ne hs hz hh (n + 1)
  · rwa [dropOne_of_head_ne hhead] at hl

theorem exists_nonzero_of_mass {xs : V multi.T} (hm : 0 < vectorMass xs) :
    ∃ i, V.get0 xs i ≠ .Z := by
  apply Classical.byContradiction
  intro hn
  have hz : ∀ i, V.get0 xs i = .Z := fun i => Classical.byContradiction (fun hi => hn ⟨i, hi⟩)
  rw [vectorMass_eq_zero xs hz] at hm
  exact Nat.lt_irrefl 0 hm

theorem Omega_image_head_ne_one [LargeCardinals.{u}] (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {v : V multi.T} (hd : domF s = .Omega v) :
    Term.head (convert (k + 3) (code s)) ≠ Term.one := by
  cases s with
  | Z => rw [domF_Z] at hd; cases hd
  | P xs b =>
    obtain ⟨i, hi⟩ := exists_nonzero_of_mass (Omega_head_mass_pos xs b hr hd)
    rw [convert_head]
    exact principal_image_ne_one k xs i (Dim_hd hsD) (recursive_head (.P xs b) hs) hi

theorem sum_subterm_gap (xs : V multi.T) (b t : multi.T)
    (hb : b ≠ .Z) (hx : 0 < vectorMass xs)
    {v : V multi.T} (hd : domF (.P xs b) = .Omega v)
    {a : multi.T} (ha : Subterm a (.P xs b)) : mass a < gap (.P xs b) t := by
  have hbp := mass_positive hb
  have hgap : gap (.P xs b) t = vectorMass xs + mass b := by
    rw [gap_Omega _ _ _ hd, mass_P]; omega
  rw [hgap]
  have hgen : ∀ {a s : multi.T}, Subterm a s → s = .P xs b →
      mass a < vectorMass xs + mass b := by
    intro a s ha
    induction ha with
    | coordinate ys c i =>
      intro he; cases he
      have hi := vectorMass_get0_le xs i
      omega
    | tail ys c => intro he; cases he; omega
    | trans hab hbs iha ihb =>
      intro he
      exact Nat.lt_trans (kumakuma.SourceCoefficientGap.mass_lt_of_subterm hab) (ihb he)
  exact hgen ha rfl

theorem closed_of_updated_coefficients [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : multi.T) (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hnewZero : convert (k + 3) (code (T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) →
      UpdatedCoefficient k v s t z)
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
  rcases hcoef z hz with he | ho | ⟨a, ha, hw, hm, he⟩
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

theorem Omega_image_drop [LargeCardinals.{u}] (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {v : V multi.T} (hd : domF s = .Omega v) :
    dropOne (convert (k + 3) (code s)) = convert (k + 3) (code s) :=
  dropOne_of_head_ne (Omega_image_head_ne_one k s hsD hr hs hd)

end kumakuma.GeneralImageMiddleSums

namespace kumakuma.GeneralImageUpperOmega

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion kumakuma.GeneralImageChangingMiddle
open kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageHighOmega kumakuma.SourceOmegaHighest
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant kumakuma.SourceOmegaTail
open kumakuma.SourceFundGap

universe u

theorem H_topNode_above_Omega (k : Nat) (a : multi.T) (ha : a ≠ .Z)
    (v : Term) (hv : Term.lt Term.bigOmega v = true) :
    Term.H v (convert (k + 3) (code (topNode k a))) =
      Term.H v (dropOne (convert (k + 3) (code a))) := by
  rw [convert_topNode k a ha, Term.H]
  simp only [show k + 1 ≠ 0 from by omega, ↓reduceIte, Term.hOne, hv, ite_self, List.nil_append]

theorem H_topNode_Omega [LargeCardinals.{u}] (k : Nat) (a : multi.T) (haD : Dim (k + 3) a)
    (hr : Recursive a) (ha : RecursiveWF (k + 3) a)
    {q : V multi.T} (hd : domF a = .Omega q)
    (v : Term) (hv : Term.lt Term.bigOmega v = true) :
    Term.H v (convert (k + 3) (code (topNode k a))) = Term.H v (convert (k + 3) (code a)) := by
  have hz : a ≠ .Z := by intro he; rw [he, domF_Z] at hd; cases hd
  rw [H_topNode_above_Omega k a hz v hv, Omega_image_drop k a haD hr ha hd]

theorem topNode_child_subterm_gap (k : Nat) (a t : multi.T) (haD : Dim (k + 3) a) (hr : Recursive a)
    {q : V multi.T} (hd : domF a = .Omega q)
    {z : multi.T} (hz : Subterm z a) : mass z < gap (topNode k a) t := by
  have hp := highest_Omega_domain (k + 2) a haD hr hd
  rw [topNode, gap_Omega _ _ _ hp, mass_P, vectorMass_lastVec, mass_Z]
  have hm := kumakuma.SourceCoefficientGap.mass_lt_of_subterm hz
  omega

theorem topNode_relative_of_child_support [LargeCardinals.{u}] (k : Nat)
    (a t : multi.T) (haD : Dim (k + 3) a) (htD : Dim (k + 3) t)
    (hr : Recursive a) (ha : RecursiveWF (k + 3) a)
    {q : V multi.T} (hd : domF a = .Omega q)
    (hs : RecursiveWF (k + 3) (topNode k a))
    (hnChild : RecursiveWF (k + 3) (T.fund a t)) (v : Term)
    (hv : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund a t))) → UpdatedCoefficient k v a t z)
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
  rw [hf, H_topNode_above_Omega k _ hzn v hv] at hz
  have hzChild := kumakuma.OT2.mem_H_dropOne hz
  rcases hcoef z hzChild with he | ho | ⟨b, hb, hw, hm, he⟩
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

end kumakuma.GeneralImageUpperOmega

namespace kumakuma.GeneralImageCofinalityBounds

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion kumakuma.GeneralImageChangingMiddle
open kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageUpperOmega
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant kumakuma.SourceOmegaTail
open kumakuma.SourceFundGap

universe u

theorem Omega_label_recursiveWF (k : Nat) : ∀ (s : multi.T),
    RecursiveWF (k + 3) s → ∀ {q : V multi.T}, domF s = .Omega q → RecursiveWF (k + 3) (.P q .Z)
  | .Z, _, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, hs, q, hd => by
    have hs' := RecursiveWF_P.1 hs
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
            exact hs
        | Omega ys =>
          by_cases hv : xs < ys
          · rw [domF_diag hf hc hv] at hd; cases hd
          · rw [domF_nondiag hf hc hv] at hd
            cases hd
            exact Omega_label_recursiveWF k _ (hs'.1 i) hc
    · rw [domF_tail xs hb] at hd
      exact Omega_label_recursiveWF k b hs'.2.1 hd
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem Dim_Omega_label {d : Nat} {s : multi.T} (hsD : Dim d s) {q : V multi.T}
    (hd : domF s = .Omega q) : Dim d (.P q .Z) := by
  obtain ⟨hl, hc⟩ := Dim_domF_Omega hsD hd
  exact Dim_P hl hc (Dim_Z d)

theorem H_lower_zeros_above_Omega (v : Term) (hv : Term.lt Term.bigOmega v = true)
    (j : Nat) (xs : List Term) (a : Term) (hz : ∀ i, i < j → xs[i]?.getD .zero = .zero) :
    Term.H v (lower j xs a) = Term.H v a := by
  induction j generalizing a with
  | zero => rfl
  | succ j ih =>
    rw [lower_succ, hz j (by omega), ih _ (fun i hi => hz i (by omega))]
    by_cases ha : a = .zero
    · subst a
      by_cases hj : j = 0
      · subst j
        simp only [step, ↓reduceIte]
        exact H_one_empty_above_Omega v hv
      · simp only [step, ↓reduceIte, hj, Term.H]
    · simp only [step, ha, ↓reduceIte]

theorem cofinality_image_le [LargeCardinals.{u}] (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) {q : V multi.T}
    (hd : domF s = .Omega q) :
    Term.le (convert (k + 3) (code (.P q .Z))) (convert (k + 3) (code s)) = true := by
  have hq := Omega_label_recursiveWF k s hs hd
  have hqD := Dim_Omega_label hsD hd
  have hl : multi.T.P q .Z ≤ s := T.le_trans (domain_principal_le_head s hr hd) (T.hd_le_self s)
  rcases hl with hl | he
  · have hlt := (convert_order k _ _ hqD hsD hq hs).mp hl
    simp only [Term.le, hlt, Bool.or_true]
  · have heq := eq_of_compare_eq hqD hsD he
    rw [heq]
    simp only [Term.le, decide_true, Bool.true_or]

theorem H_step_of_layerCut_lt (v : Term) (hv : Term.lt Term.bigOmega v = true)
    (n : Nat) (a c : Term) (hlt : Term.lt (layerCut n a) v = true) {z : Term}
    (hz : z ∈ Term.H v (step n a c)) : z ∈ Term.H v a := by
  have skip (w b : Term) (hw : Term.lt w v = true)
      (hz : z ∈ Term.H v (.psi w b)) : z ∈ Term.H v w := by
    rw [Term.H] at hz
    split at hz
    · cases hz
    · simpa only [hw, ↓reduceIte] using hz
  by_cases ha : a = .zero
  · subst a
    by_cases hn : n = 0
    · subst n
      simp only [step, ↓reduceIte] at hz
      have hh := skip Term.bigOmega c hv hz
      simp only [Term.bigOmega, Term.H] at hh
      cases hh
    · by_cases hc : c = .zero
      · simp only [step, ↓reduceIte, hn, hc, Term.H] at hz; cases hz
      · simp only [step, ↓reduceIte, hn, hc] at hz
        have hw : Term.lt (.inacc n .zero) v = true := by simpa only [layerCut, ↓reduceIte] using hlt
        have hh := skip _ _ hw hz
        simp only [Term.H, Term.hOne, hv, ↓reduceIte, ite_self, List.nil_append] at hh
        cases hh
  · by_cases hc : c = .zero
    · simpa only [step, ha, hc, ↓reduceIte] using hz
    · simp only [step, ha, hc, ↓reduceIte] at hz
      have hw : Term.lt (regular n a) v = true := by simpa only [layerCut, ha, ↓reduceIte, regular] using hlt
      have hh := skip _ _ hw hz
      simpa only [regular, Term.H, Term.hOne, hv, ↓reduceIte, ite_self, List.nil_append,
        kumakuma.OT2.H_succTerm, H_one_empty_above_Omega v hv, List.append_nil] using hh

theorem layerCut_lt_of_context_lt (n : Nat) (a b : Term)
    (ha : Context (n + 1) a) (hbf : n < Term.fT b) (hlt : Term.lt a b = true) :
    Term.lt (layerCut n a) b = true := by
  by_cases ha0 : a = .zero
  · subst a
    cases b with
    | zero | add => simp [Term.fT] at hbf
    | inacc m c =>
      simp only [Term.fT] at hbf
      simp only [layerCut, ↓reduceIte, Term.lt, hbf]
    | psi w c =>
      simp only [Term.fT] at hbf
      simp only [layerCut, ↓reduceIte, Term.lt, hbf, decide_true, show ¬Term.fT w ≤ n from by omega,
        decide_false, Bool.true_and, Bool.false_and, Bool.or_false]
  · have hp : Term.isPrin a = true := ((ha.resolve_left ha0).1)
    simp only [layerCut, ha0, ↓reduceIte]
    change Term.lt (regular n a) b = true
    rwa [regular_lt_context hp hbf]

theorem step_predecessor_cut_lt [LargeCardinals.{u}] (n : Nat) (a c : Term)
    (ha : Above (n + 1) a) (hc : Term.wf c = true)
    (hw : Term.wf (step (n + 1) a (succTerm c)) = true) :
    Term.lt (layerCut n (step (n + 1) a c)) (step (n + 1) a (succTerm c)) = true := by
  have hn := step_successor_predecessor (n + 1) a c ha hc hw
  have hwa := step_context_wf ha hw
  have hlt : Term.lt (step (n + 1) a c) (step (n + 1) a (succTerm c)) = true := by
    rw [step_order ha ha hwa hwa hc (succTerm_wf hc) hn hw]
    simp only [lt_self, decide_true, Bool.true_and, Bool.false_or]
    rw [lt_succTerm_eq_le hc hc]; simp [Term.le]
  have hf : Term.fT (step (n + 1) a (succTerm c)) = n + 1 := by
    by_cases ha0 : a = .zero <;> simp [step, ha0, succTerm_ne_zero, Term.fT, regular]
  exact layerCut_lt_of_context_lt n _ _ (step_shape _ ha) (by rw [hf]; omega) hlt

theorem step_successor_relative_support [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (n : Nat) (a b : Term)
    (ha : Above n a) (hb : Term.wf b = true)
    (hw : Term.wf (step n a (succTerm b)) = true) {z : Term}
    (hz : z ∈ Term.H v (step n a b)) :
    z ∈ Term.H v (step n a (succTerm b)) ∨
      (z = b ∨ z = dropOne b) ∧
        (succTerm b ∈ Term.H v (step n a (succTerm b)) ∨
          dropOne (succTerm b) ∈ Term.H v (step n a (succTerm b))) := by
  by_cases hn : n = 0
  · subst n; exact zero_step_relative_support v hvR hv a b ha hb hw hz
  · by_cases ha0 : a = .zero
    · subst a
      by_cases hb0 : b = .zero
      · simp only [step, ↓reduceIte, hn, hb0, Term.H] at hz; cases hz
      · have hd := drop_succ b hb0
        simp only [step, ↓reduceIte, hn, hb0, succTerm_ne_zero, hd] at hz hw ⊢
        rcases H_psi_successor_support v (.inacc n .zero) (dropOne b) hvR hv (dropOne_wf hb) hw hz
          with h | ⟨h, hs⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h, Or.inr hs⟩
    · by_cases hb0 : b = .zero
      · have hz' : z ∈ Term.H v a := by simpa only [step, ha0, hb0, ↓reduceIte] using hz
        exact Or.inl (H_step_context_of_wf v hvR hv n a (succTerm b) ha hw hz')
      · have hd := drop_succ b hb0
        simp only [step, ha0, hb0, succTerm_ne_zero, ↓reduceIte, hd] at hz hw ⊢
        rcases H_psi_successor_support v (regular n a) (dropOne b) hvR hv (dropOne_wf hb) hw hz
          with h | ⟨h, hs⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h, Or.inr hs⟩

theorem lower_regular_cofinal_support [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (hOmega : Term.lt Term.bigOmega v = true)
    (j m : Nat) (xs ys : List Term) (a c t : Term) (him : m + 1 < j)
    (hctx : Context j a) (hc : Term.wf c = true)
    (hx : xs[m + 1]?.getD .zero = succTerm c)
    (hy : ys[m + 1]?.getD .zero = c) (hyt : ys[m]?.getD .zero = t)
    (hzeroOld : ∀ i, i < m + 1 → xs[i]?.getD .zero = .zero)
    (hzeroNew : ∀ i, i < m → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, m + 1 < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero)
    (hw : Term.wf (lower j xs a) = true) (hlt : Term.lt (lower j xs a) v = true) {z : Term}
    (hz : z ∈ Term.H v (lower j ys a)) :
    z ∈ Term.H v (lower j xs a) ∨
      (z = c ∨ z = dropOne c) ∧
        (succTerm c ∈ Term.H v (lower j xs a) ∨ dropOne (succTerm c) ∈ Term.H v (lower j xs a)) := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    by_cases hij : m + 1 < j
    · rw [lower_succ] at hw hlt hz ⊢
      rw [hsame j hij (by omega)] at hz
      exact ih _ hij (step_shape _ (context_above hctx))
        (fun i hi hj => hsame i hi (by omega)) hw hlt hz
    · have he : j = m + 1 := by omega
      subst j
      let old := step (m + 1) a (succTerm c)
      let pre := step (m + 1) a c
      have hnz : old ≠ .zero := step_positive_nonzero (m + 1) (by omega) a _ (succTerm_ne_zero c)
      have heOld : lower (m + 2) xs a = old := by
        rw [lower_succ, hx]
        exact lower_keep (m + 1) xs old hnz hzeroOld
      have hOldW : Term.wf old = true := heOld ▸ hw
      have hOldLt : Term.lt old v = true := heOld ▸ hlt
      have hpreW : Term.wf pre = true := step_successor_predecessor (m + 1) a c (context_above hctx) hc hOldW
      have hpreCtx : Context (m + 1) pre := step_shape _ (context_above hctx)
      have hcutW := layerCut_wf m pre (context_above hpreCtx) hpreW
      have hcutLt : Term.lt (layerCut m pre) v = true :=
        lemma_6_1.{u}.2.1 _ _ _ hcutW hOldW hv (step_predecessor_cut_lt m a c (context_above hctx) hc hOldW) hOldLt
      rw [lower_succ, hy, lower_succ, hyt,
        H_lower_zeros_above_Omega v hOmega m ys _ hzeroNew] at hz
      have hpreMem := H_step_of_layerCut_lt v hOmega m pre t hcutLt hz
      rw [heOld]
      exact step_successor_relative_support v hvR hv (m + 1) a c (context_above hctx) hc hOldW hpreMem

theorem topPair_predecessor_cut_lt [LargeCardinals.{u}] (k : Nat) (h c : Term)
    (hh : Term.wf h = true) (hc : Term.wf c = true) :
    Term.lt (layerCut k (topPair (k + 1) h c)) (topPair (k + 1) h (succTerm c)) = true := by
  have hf : Term.fT (topPair (k + 1) h (succTerm c)) = k + 1 := by
    by_cases hh0 : h = .zero <;> simp [topPair, hh0, succTerm_ne_zero, Term.fT]
  exact layerCut_lt_of_context_lt k _ _ (topPair_context _ _ _) (by rw [hf]; omega)
    (topPair_predecessor_lt _ h c hh hc)

theorem H_topPair_of_pairCut_lt (v : Term)
    (n : Nat) (h t : Term) (hlt : Term.lt (pairCut n h) v = true) {z : Term}
    (hz : z ∈ Term.H v (topPair n h t)) : z ∈ Term.H v (pairCut n h) := by
  by_cases ht : t = .zero
  · subst t
    by_cases hh : h = .zero
    · simp only [topPair, ↓reduceIte, hh, Term.H] at hz; cases hz
    · simp only [topPair, ↓reduceIte, hh] at hz
      simp only [pairCut, hh, ↓reduceIte]
      exact H_inacc_succ_support v n (dropOne h) hz
  · simp only [topPair, ht, ↓reduceIte] at hz
    change z ∈ Term.H v (.psi (pairCut n h) (dropOne t)) at hz
    rw [Term.H] at hz
    split at hz
    · cases hz
    · simpa only [hlt, ↓reduceIte] using hz

end kumakuma.GeneralImageCofinalityBounds

namespace kumakuma.GeneralImageRegularCofinality

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion kumakuma.GeneralImageChangingMiddle
open kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageCofinalityBounds
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant kumakuma.SourceOmegaTail
open kumakuma.SourceFundGap

universe u

theorem H_fund_regular_cofinal_support [LargeCardinals.{u}] (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (t : multi.T)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hlt : Term.lt (convert (k + 3) (code (.P xs .Z))) v = true) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t)))) :
    UpdatedCoefficient k v (.P xs .Z) t z := by
  have hml : m + 1 < k + 3 := by have := fnz_lt_length hf; rwa [hsD.length] at this
  have hml' : m + 1 < xs.length := fnz_lt_length hf
  have hlow := (V.fnz_some_spec xs _ hf).2
  have hcoords : ∀ i, RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1
  let p := T.fund (V.get0 xs (m + 1)) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hsD.coord _) (hcoords _) hdom
  have hfArg : T.fund (V.get0 xs (m + 1)) t = p := fund_dom_one _ hdom t
  have hsucc : convert (k + 3) (code (V.get0 xs (m + 1))) =
      succTerm (convert (k + 3) (code p)) := by
    obtain ⟨a, he⟩ := dom_one_succ (V.get0 xs (m + 1)) (hsD.coord _) hdom
    show _ = succTerm (convert (k + 3) (code (T.fund (V.get0 xs (m + 1)) .Z)))
    rw [he, kumakuma.SourceSuccessor.fund_succ, convert_succ]
  let zs := V.set (V.set xs (m + 1) p) m t
  have zidx (i : Nat) : V.get0 zs i =
      if i = m then t else if i = m + 1 then p else V.get0 xs i := get0_set_set hml' p t i
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes zs))
  have oldGet (i : Nat) : oldArgs[i]?.getD .zero = convert (k + 3) (code (V.get0 xs i)) :=
    converted_coordinate xs i
  have newGet (i : Nat) : newArgs[i]?.getD .zero = convert (k + 3) (code (V.get0 zs i)) :=
    converted_coordinate zs i
  have newP : newArgs[m + 1]?.getD .zero = convert (k + 3) (code p) := by
    rw [newGet (m + 1), zidx, ite_eq_right (by omega), ite_eq_left rfl]
  have newT : newArgs[m]?.getD .zero = convert (k + 3) (code t) := by
    rw [newGet m, zidx, ite_eq_left rfl]
  have oldSucc : oldArgs[m + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by
    rw [oldGet (m + 1)]; exact hsucc
  have oldZero : ∀ i, i < m + 1 → oldArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [oldGet i, hlow i hi, convert_Z]
  have newZero : ∀ i, i < m → newArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [newGet i, zidx, ite_eq_right (by omega), ite_eq_right (by omega), hlow i (by omega),
      convert_Z]
  have newSame : ∀ i, m + 1 < i → i < k + 3 → newArgs[i]?.getD .zero = oldArgs[i]?.getD .zero := by
    intro i hi _
    rw [newGet i, oldGet i, zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
  have heOldFull : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have hold := hs.wf
  rw [heOldFull] at hold
  have hOldLt := hlt
  rw [heOldFull] at hOldLt
  have liftSupport (hmem : z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
      (z = convert (k + 3) (code p) ∨ z = dropOne (convert (k + 3) (code p))) ∧
        (succTerm (convert (k + 3) (code p)) ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
          dropOne (succTerm (convert (k + 3) (code p))) ∈ Term.H v (convert (k + 3) (code (.P xs .Z))))) :
      UpdatedCoefficient k v (.P xs .Z) t z := by
    rcases hmem with ho | ⟨he, ho⟩
    · exact Or.inr (Or.inl ho)
    · refine Or.inr (Or.inr ⟨V.get0 xs (m + 1), Subterm.coordinate xs .Z _, ?_, ?_, ?_⟩)
      · rw [hfArg]; exact hp
      · rw [hsucc]; exact ho
      · rw [hfArg]; exact he
  rw [fund_one_succ hf hdom t, convert_principal, principal_as_layers] at hz
  change z ∈ Term.H v (lower (k + 1) newArgs
    (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) at hz
  by_cases hhighest : m + 1 = k + 2
  · have he : m = k + 1 := by omega
    subst m
    let c := convert (k + 3) (code p)
    have heTop : topPair (k + 1) (succTerm c) .zero = pairCut (k + 1) c := by
      by_cases hc0 : c = .zero
      · simp [topPair, pairCut, hc0, succTerm, dropOne, Term.one, Term.bigOmega]
      · simp only [topPair, ↓reduceIte, succTerm_ne_zero, drop_succ c hc0, pairCut, hc0]
    have heOld : convert (k + 3) (code (.P xs .Z)) = pairCut (k + 1) c := by
      rw [heOldFull, oldSucc, oldZero (k + 1) (by omega), heTop]
      exact lower_keep (k + 1) oldArgs _ (by intro he; cases he) (fun i hi => oldZero i (by omega))
    rw [newP, newT, H_lower_zeros_above_Omega v hOmega (k + 1) newArgs _ newZero] at hz
    have hcutLt : Term.lt (pairCut (k + 1) c) v = true := heOld ▸ hlt
    have hzOld := H_topPair_of_pairCut_lt v (k + 1) c (convert (k + 3) (code t)) hcutLt hz
    exact Or.inr (Or.inl (heOld ▸ hzOld))
  · by_cases hmiddle : m + 1 = k + 1
    · have he : m = k := by omega
      subst m
      let h := oldArgs[k + 2]?.getD .zero
      let c := convert (k + 3) (code p)
      let old := topPair (k + 1) h (succTerm c)
      let pre := topPair (k + 1) h c
      have hh : Term.wf h = true := by
        change Term.wf (oldArgs[k + 2]?.getD .zero) = true
        rw [oldGet (k + 2)]; exact (hcoords _).wf
      have hi : Term.wf (.inacc (k + 1) (dropOne h)) = true := by
        change Term.wf (.inacc (k + 1) (dropOne (oldArgs[k + 2]?.getD .zero))) = true
        rw [oldGet (k + 2)]; exact inacc_image_drop_wf k _ (hcoords _)
      have hnz : old ≠ .zero := by simp [old, topPair, succTerm_ne_zero]
      have heOld : convert (k + 3) (code (.P xs .Z)) = old := by
        rw [heOldFull, oldSucc]
        exact lower_keep (k + 1) oldArgs old hnz oldZero
      have hwOld : Term.wf old = true := heOld ▸ hs.wf
      have hwPre : Term.wf pre = true := topPair_successor_predecessor (k + 1) h c hi hp.wf hwOld
      have hwCut := layerCut_wf k pre (context_above (topPair_context _ _ _)) hwPre
      have hCutLt : Term.lt (layerCut k pre) v = true := lemma_6_1.{u}.2.1 _ _ _ hwCut hwOld hv
        (topPair_predecessor_cut_lt k h c hh hp.wf) (heOld ▸ hlt)
      rw [newSame (k + 2) (by omega) (by omega), newP, lower_succ, newT,
        H_lower_zeros_above_Omega v hOmega k newArgs _ newZero] at hz
      have hzPre := H_step_of_layerCut_lt v hOmega k pre (convert (k + 3) (code t)) hCutLt hz
      rcases H_topPair_predecessor_support v hvR hv (k + 1) h c hh hp.wf hi hwOld hzPre with ho | ⟨he, ho⟩
      · apply liftSupport; exact Or.inl (heOld ▸ ho)
      · apply liftSupport; exact Or.inr ⟨Or.inr he, Or.inr (heOld ▸ ho)⟩
    · have him : m + 1 < k + 1 := by omega
      rw [newSame (k + 2) (by omega) (by omega), newSame (k + 1) (by omega) (by omega)] at hz
      have hmem := lower_regular_cofinal_support v hvR hv hOmega (k + 1) m oldArgs newArgs _ _ _ him
        (topPair_context _ _ _) hp.wf oldSucc newP newT oldZero newZero
        (fun i hi hik => newSame i hi (by omega)) hold hOldLt hz
      rw [← heOldFull] at hmem
      exact liftSupport hmem

theorem H_fund_regular_single_small [LargeCardinals.{u}] (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one)
    (hother : ∀ i, i ≠ m + 1 → V.get0 xs i = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (t : multi.T)
    (v : Term) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hlt : Term.lt (convert (k + 3) (code (.P xs .Z))) v = true) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t)))) :
    z = .zero ∨ ∃ a : multi.T, Dim (k + 3) a ∧ RecursiveWF (k + 3) a ∧
      mass a < gap (.P xs .Z) t ∧
      (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a))) := by
  have hml : m + 1 < k + 3 := by have := fnz_lt_length hf; rwa [hsD.length] at this
  have hml' : m + 1 < xs.length := fnz_lt_length hf
  have hlow := (V.fnz_some_spec xs _ hf).2
  have hcoords : ∀ i, RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1
  let p := T.fund (V.get0 xs (m + 1)) .Z
  let c := convert (k + 3) (code p)
  have hpD : Dim (k + 3) p := Dim_fund _ _ (hsD.coord _) (Dim_Z _)
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hsD.coord _) (hcoords _) hdom
  have hsucc : convert (k + 3) (code (V.get0 xs (m + 1))) = succTerm c := by
    obtain ⟨a, he⟩ := dom_one_succ (V.get0 xs (m + 1)) (hsD.coord _) hdom
    show _ = succTerm (convert (k + 3) (code (T.fund (V.get0 xs (m + 1)) .Z)))
    rw [he, kumakuma.SourceSuccessor.fund_succ, convert_succ]
  have hd : domF (.P xs .Z) = .Omega xs := domF_one_succ hf hdom
  have hpGap : mass p < gap (.P xs .Z) t := by
    have hmP := mass_fund_one (V.get0 xs (m + 1)) .Z hdom
    have hmI := vectorMass_get0_le xs (m + 1)
    rw [gap_Omega _ _ _ hd, mass_P, mass_Z]
    change mass p + 1 = mass (V.get0 xs (m + 1)) at hmP
    omega
  have fromP (h : z = .zero ∨ ArgCoefficient v z c) :
      z = .zero ∨ ∃ a : multi.T, Dim (k + 3) a ∧ RecursiveWF (k + 3) a ∧
        mass a < gap (.P xs .Z) t ∧
        (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a))) := by
    rcases h with he | he | he | he
    · exact Or.inl he
    · exact Or.inr ⟨p, hpD, hp, hpGap, Or.inl he⟩
    · exact Or.inr ⟨p, hpD, hp, hpGap, Or.inr he⟩
    · rcases H_convert_source k v p he with he | ⟨a, ha, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨a, ha.dim hpD, ha.recursiveWF hp,
          Nat.lt_trans (kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha) hpGap, he⟩
  let zs := V.set (V.set xs (m + 1) p) m t
  have zidx (i : Nat) : V.get0 zs i =
      if i = m then t else if i = m + 1 then p else V.get0 xs i := get0_set_set hml' p t i
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes zs))
  have oldGet (i : Nat) : oldArgs[i]?.getD .zero = convert (k + 3) (code (V.get0 xs i)) :=
    converted_coordinate xs i
  have newGet (i : Nat) : newArgs[i]?.getD .zero = convert (k + 3) (code (V.get0 zs i)) :=
    converted_coordinate zs i
  have newP : newArgs[m + 1]?.getD .zero = c := by
    rw [newGet (m + 1), zidx, ite_eq_right (by omega), ite_eq_left rfl]
  have newT : newArgs[m]?.getD .zero = convert (k + 3) (code t) := by
    rw [newGet m, zidx, ite_eq_left rfl]
  have oldZero : ∀ i, i < m + 1 → oldArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [oldGet i, hlow i hi, convert_Z]
  have newZero : ∀ i, i < m → newArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [newGet i, zidx, ite_eq_right (by omega), ite_eq_right (by omega),
      hother i (by omega), convert_Z]
  rw [fund_one_succ hf hdom t] at hz
  change z ∈ Term.H v (convert (k + 3) (code (.P zs .Z))) at hz
  by_cases hhighest : m + 1 = k + 2
  · have he : m = k + 1 := by omega
    subst m
    have heOld : convert (k + 3) (code (.P xs .Z)) = pairCut (k + 1) c := by
      rw [convert_principal, principal_as_layers]
      change lower (k + 1) oldArgs (topPair (k + 1)
        (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) = _
      rw [oldGet (k + 2), hsucc, oldZero (k + 1) (by omega)]
      have heTop : topPair (k + 1) (succTerm c) .zero = pairCut (k + 1) c := by
        by_cases hc0 : c = .zero
        · simp [topPair, pairCut, hc0, succTerm, dropOne, Term.one, Term.bigOmega]
        · simp only [topPair, ↓reduceIte, succTerm_ne_zero, drop_succ c hc0, pairCut, hc0]
      rw [heTop]
      exact lower_keep (k + 1) oldArgs _ (by intro he; cases he)
        (fun i hi => oldZero i (by omega))
    rw [convert_principal, principal_as_layers] at hz
    change z ∈ Term.H v (lower (k + 1) newArgs (topPair (k + 1)
      (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) at hz
    rw [newP, newT, H_lower_zeros_above_Omega v hOmega (k + 1) newArgs _ newZero] at hz
    have hcOld := H_topPair_of_pairCut_lt v (k + 1) c _ (heOld ▸ hlt) hz
    rcases H_inacc_support (k + 1) (if c = .zero then .zero else succTerm (dropOne c)) hcOld with he | he
    · exact fromP (Or.inl he)
    · by_cases hc0 : c = .zero
      · rw [ite_eq_left hc0, Term.H] at he; cases he
      · rw [ite_eq_right hc0] at he
        rcases H_succ_support (dropOne c) he with he | he
        · exact fromP (Or.inl he)
        · exact fromP (Or.inr (Or.inr (Or.inr (kumakuma.OT2.mem_H_dropOne he))))
  · have hib : m + 1 ≤ k + 1 := by omega
    have highOld (i : Nat) (hi : m + 1 < i) : V.get0 xs i = .Z := hother i (by omega)
    have highNew (i : Nat) (hi : m + 1 < i) : V.get0 zs i = .Z := by
      rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega), hother i (by omega)]
    have heOld : convert (k + 3) (code (.P xs .Z)) = step (m + 1) .zero (succTerm c) := by
      rw [convert_positive_layers k xs (m + 1) (by omega) hib highOld, hsucc]
      exact lower_keep (m + 1) oldArgs _
        (step_positive_nonzero (m + 1) (by omega) _ _ (succTerm_ne_zero c)) oldZero
    have hOldW := heOld ▸ hs.wf
    have hPreW := step_successor_predecessor (m + 1) .zero c (Or.inl rfl) hp.wf hOldW
    have hCutW := layerCut_wf m (step (m + 1) .zero c)
      (context_above (step_shape _ (Or.inl rfl))) hPreW
    have hCutLt : Term.lt (layerCut m (step (m + 1) .zero c)) v = true :=
      lemma_6_1.{u}.2.1 _ _ _ hCutW hOldW hv
        (step_predecessor_cut_lt m .zero c (Or.inl rfl) hp.wf hOldW) (heOld ▸ hlt)
    rw [convert_positive_layers k zs (m + 1) (by omega) hib highNew] at hz
    change z ∈ Term.H v (lower (m + 1) newArgs (step (m + 1) .zero _)) at hz
    rw [show convert (k + 3) (code (V.get0 zs (m + 1))) = c from by
      rw [zidx, ite_eq_right (by omega), ite_eq_left rfl], lower_succ, newT,
      H_lower_zeros_above_Omega v hOmega m newArgs _ newZero] at hz
    have hPre := H_step_of_layerCut_lt v hOmega m (step (m + 1) .zero c) _ hCutLt hz
    rcases H_step_support v (m + 1) .zero c hPre with he | he | he
    · exact fromP (Or.inl he)
    · cases he
    · exact fromP (Or.inr he)

theorem updated_coefficient_lt_old [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : multi.T) (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    {z : Term} (hc : UpdatedCoefficient k v s t z) :
    Term.lt z (convert (k + 3) (code s)) = true := by
  have hzlt := (zero_lt_iff _).mpr hzero
  rcases hc with he | ho | ⟨a, ha, hw, hm, he⟩
  · rw [he]; exact hzlt
  · exact (Term.allLt_iff _ _).mp hH _ ho
  · by_cases ha0 : a = .Z
    · subst a
      rw [fund_Z, convert_Z] at he
      rcases he with rfl | rfl
      · exact hzlt
      · exact hzlt
    · have haW := ha.recursiveWF hs
      have haD := ha.dim hsD
      have hal : a < s := by
        apply (convert_order k _ _ haD hsD haW hs).mpr
        rcases hm with hm | hm
        · exact (Term.allLt_iff _ _).mp hH _ hm
        · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hzero hhead ((Term.allLt_iff _ _).mp hH _ hm)
      have hl := (convert_order k _ _ (Dim_fund a t haD htD) hsD hw hs).mp
        (T.lt_trans (fund_lt a t ha0) hal)
      rcases he with rfl | rfl
      · exact hl
      · exact dropOne_lt_of_lt hw.wf hs.wf hl

theorem fund_regular_cofinal_relative_of_wf [LargeCardinals.{u}] (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one)
    (i j : Nat) (hij : i ≠ j) (hi : V.get0 xs i ≠ .Z) (hj : V.get0 xs j ≠ .Z)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (t : multi.T) (htD : Dim (k + 3) t)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t)) :
    ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P xs .Z))) v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t))))
          (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true := by
  have hd : domF (.P xs .Z) = .Omega xs := domF_one_succ hf hdom
  intro v hvR hv hOmega hlt hH
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := convert_ne_zero xs .Z
  have hnZ : convert (k + 3) (code (T.fund (.P xs .Z) t)) ≠ .zero := fun he =>
    domOmega_fund_ne_zero _ t hd ((convert_eq_zero_iff _ _).1 he)
  exact closed_of_updated_coefficients k v _ t hsD htD hs hn (Omega_image_head_ne_one k _ hsD hr hs hd)
    hsZ hnZ (fun a ha => principal_subterm_gap xs i j hij hi hj hd t ha)
    (fun z hz => H_fund_regular_cofinal_support k m xs hsD hf hdom hs t v hvR hv hOmega hlt hz) hH

theorem fund_regular_cofinal_relative_all_of_wf [LargeCardinals.{u}] (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (t : multi.T) (htD : Dim (k + 3) t)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t)) :
    ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P xs .Z))) v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t))))
          (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true := by
  classical
  have hi : V.get0 xs (m + 1) ≠ .Z := (V.fnz_some_spec xs _ hf).1
  by_cases hex : ∃ j, m + 1 ≠ j ∧ V.get0 xs j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact fund_regular_cofinal_relative_of_wf k m xs hsD hf hdom (m + 1) j hij hi hj hr hs t htD hn
  · have hother : ∀ j, j ≠ m + 1 → V.get0 xs j = .Z := by
      intro j hj
      apply Classical.byContradiction
      intro hn
      exact hex ⟨j, fun he => hj he.symm, hn⟩
    have hd : domF (.P xs .Z) = .Omega xs := domF_one_succ hf hdom
    have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := convert_ne_zero xs .Z
    have hnD : Dim (k + 3) (T.fund (.P xs .Z) t) := Dim_fund _ _ hsD htD
    have hnZ : convert (k + 3) (code (T.fund (.P xs .Z) t)) ≠ .zero := fun he =>
      domOmega_fund_ne_zero _ t hd ((convert_eq_zero_iff _ _).1 he)
    have hhead := Omega_image_head_ne_one k _ hsD hr hs hd
    intro v hvR hv hOmega hlt hH
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    have hzOld := updated_coefficient_lt_old k v _ t hsD htD hs hhead hsZ hH
      (H_fund_regular_cofinal_support k m xs hsD hf hdom hs t v hvR hv hOmega hlt hz)
    rcases H_fund_regular_single_small k m xs hsD hf hdom hother hs t v hv hOmega hlt hz
      with he | ⟨a, haD, ha, hmA, he⟩
    · rw [he]; exact (zero_lt_iff _).mpr hnZ
    · have hal : a < .P xs .Z := by
        apply (convert_order k _ _ haD hsD ha hs).mpr
        rcases he with he | he
        · exact he ▸ hzOld
        · exact undrop_lt_head_ne_one _ _ ha.wf hs.wf hsZ hhead (he ▸ hzOld)
      have hl := (convert_order k _ _ haD hnD ha hn).mp (small_lt_fund_all (.P xs .Z) t a hal hmA)
      rcases he with rfl | rfl
      · exact hl
      · exact dropOne_lt_of_lt ha.wf hn.wf hl

theorem fund_regular_cofinal_relative_all [LargeCardinals.{u}] (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (t : multi.T) (htD : Dim (k + 3) t) (ht : RecursiveWF (k + 3) t)
    (hHt : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code t)))
      (convert (k + 3) (code t)) = true) :
    RecursiveWF (k + 3) (T.fund (.P xs .Z) t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P xs .Z))) v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) t))))
          (convert (k + 3) (code (T.fund (.P xs .Z) t))) = true := by
  have hn := fund_regular_recursiveWF k m xs hsD hf hdom t hs ht hHt
  exact ⟨hn, fund_regular_cofinal_relative_all_of_wf k m xs hsD hf hdom hr hs t htD hn⟩

end kumakuma.GeneralImageRegularCofinality

import Subsp.Support.Omega

/-! Cofinality bounds and preservation of wf under fund at 0 and along omega inheritance. -/

namespace Support.GeneralImageMiddleCofinality

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion Support.GeneralImageChangingMiddle
open Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageCoefficients Support.SourceFundOrder Support.SourceRecursiveDescending
open Support.GeneralImageOmegaCoefficients Support.SourceOmegaInvariant
open Support.SourceFundGap

universe u

theorem principal_subterm_gap {lam : Nat} (xs : Vec (new.T lam) lam)
    (i j : Fin lam) (hij : i ≠ j) (hi : xs.idx i ≠ .Z) (hj : xs.idx j ≠ .Z)
    {v : Vec (new.T lam) lam} (hd : new.T.dom (.P xs .Z) = .Omega v)
    (t : new.T lam) {a : new.T lam} (ha : Subterm a (.P xs .Z)) :
    mass a < gap (.P xs .Z) t := by
  have hcoords : ∀ l, mass (xs.idx l) < vectorMass xs := by
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
    rw [gap_Omega _ _ _ hd, mass, mass]
    omega
  rw [hgap]
  have hgen : ∀ {a s : new.T lam}, Subterm a s → s = .P xs .Z → mass a < vectorMass xs := by
    intro a s ha
    induction ha with
    | coordinate ys b l => intro he; cases he; exact hcoords l
    | tail ys b =>
      intro he; cases he
      have hp := mass_positive hi
      have hv := vectorMass_idx_le xs i
      simp only [mass]; omega
    | trans hab hbs iha ihb =>
      intro he
      exact Nat.lt_trans (Support.SourceCoefficientGap.mass_lt_of_subterm hab) (ihb he)
  exact hgen ha rfl

theorem H_inacc_succ_support (v : Term) (n : Nat) (a : Term) {z : Term}
    (hz : z ∈ Term.H v (.inacc n a)) : z ∈ Term.H v (.inacc n (succTerm a)) := by
  rw [Term.H] at hz ⊢
  rcases List.mem_append.mp hz with hz | hz
  · exact List.mem_append_left _ hz
  · apply List.mem_append_right
    rw [Support.OT2.H_succTerm]
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

def UpdatedCoefficient (k : Nat) (v : Term) (s t : new.T (k + 3)) (z : Term) : Prop :=
  z = .zero ∨ z ∈ Term.H v (convert (k + 3) (code s)) ∨
    ∃ a, Subterm a s ∧ RecursiveWF (k + 3) (new.T.fund a t) ∧
      (convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code s)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code s))) ∧
      (z = convert (k + 3) (code (new.T.fund a t)) ∨
        z = dropOne (convert (k + 3) (code (new.T.fund a t))))

end Support.GeneralImageMiddleCofinality

namespace Support.GeneralImageMiddleSums

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion Support.GeneralImageChangingMiddle
open Support.GeneralImageMiddleCofinality
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant Support.SourceOmegaTail
open Support.SourceFundGap

universe u

theorem undrop_lt_head_ne_one (a s : Term) (ha : Term.wf a = true) (hs : Term.wf s = true)
    (hz : s ≠ .zero) (hh : Term.head s ≠ Term.one)
    (hl : Term.lt (dropOne a) s = true) : Term.lt a s = true := by
  by_cases hhead : Term.head a = Term.one
  · obtain ⟨n, he⟩ := head_one_nat ha hhead
    rw [he]; exact nat_lt_of_head_ne hs hz hh (n + 1)
  · rwa [dropOne_of_head_ne hhead] at hl

theorem Omega_image_head_ne_one [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {v : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega v) :
    Term.head (convert (k + 3) (code s)) ≠ Term.one := by
  cases s with
  | Z => cases hd
  | P xs b =>
    have hm := Omega_head_mass_pos xs b hr hd
    have hex : ∃ i, xs.idx i ≠ .Z := by
      apply Classical.byContradiction
      intro hn
      have hz : xs = zeros (k + 3) := by
        apply vec_ext
        intro i
        simp only [zeros, Vec.ofFn_idx]
        apply Classical.byContradiction
        intro hi; exact hn ⟨i, hi⟩
      have hh : vectorMass xs = 0 := by
        rw [hz]
        have hzero : ∀ m, vectorMass (zeros (lam := k + 3) m) = 0 := by
          intro m
          induction m with
          | zero => cases zeros (lam := k + 3) 0; rw [vectorMass]
          | succ m ih => simp only [zeros_succ, vectorMass, mass, ih, Nat.add_zero]
        exact hzero _
      omega
    obtain ⟨i, hi⟩ := hex
    rw [convert_head]
    exact principal_image_ne_one k xs i (recursive_head (.P xs b) hs) hi

theorem sum_subterm_gap {lam : Nat} (xs : Vec (new.T lam) lam) (b t : new.T lam)
    (hb : b ≠ .Z) (hx : 0 < vectorMass xs)
    {v : Vec (new.T lam) lam} (hd : new.T.dom (.P xs b) = .Omega v)
    {a : new.T lam} (ha : Subterm a (.P xs b)) : mass a < gap (.P xs b) t := by
  have hbp := mass_positive hb
  have hgap : gap (.P xs b) t = vectorMass xs + mass b := by
    rw [gap_Omega _ _ _ hd, mass]; omega
  rw [hgap]
  have hgen : ∀ {a s : new.T lam}, Subterm a s → s = .P xs b →
      mass a < vectorMass xs + mass b := by
    intro a s ha
    induction ha with
    | coordinate ys c i =>
      intro he; cases he
      have hi := vectorMass_idx_le xs i
      omega
    | tail ys c => intro he; cases he; omega
    | trans hab hbs iha ihb =>
      intro he
      exact Nat.lt_trans (Support.SourceCoefficientGap.mass_lt_of_subterm hab) (ihb he)
  exact hgen ha rfl

theorem closed_of_updated_coefficients [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (new.T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hnewZero : convert (k + 3) (code (new.T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s t))) →
      UpdatedCoefficient k v s t z)
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
  rcases hcoef z hz with he | ho | ⟨a, ha, hw, hm, he⟩
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

theorem Omega_image_drop [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {v : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega v) :
    dropOne (convert (k + 3) (code s)) = convert (k + 3) (code s) :=
  dropOne_of_head_ne (Omega_image_head_ne_one k s hr hs hd)

end Support.GeneralImageMiddleSums

namespace Support.GeneralImageUpperOmega

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion Support.GeneralImageChangingMiddle
open Support.GeneralImageMiddleCofinality Support.GeneralImageMiddleSums
open Support.GeneralImageHighOmega Support.SourceOmegaHighest
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant Support.SourceOmegaTail
open Support.SourceFundGap

universe u

theorem H_topNode_above_Omega (k : Nat) (a : new.T (k + 3)) (ha : a ≠ .Z)
    (v : Term) (hv : Term.lt Term.bigOmega v = true) :
    Term.H v (convert (k + 3) (code (topNode k a))) =
      Term.H v (dropOne (convert (k + 3) (code a))) := by
  rw [convert_topNode k a ha, Term.H]
  simp only [show k + 1 ≠ 0 from by omega, ↓reduceIte, Term.hOne, hv, ite_self, List.nil_append]

theorem H_topNode_Omega [LargeCardinals.{u}] (k : Nat) (a : new.T (k + 3))
    (hr : Recursive a) (ha : RecursiveWF (k + 3) a)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom a = .Omega q)
    (v : Term) (hv : Term.lt Term.bigOmega v = true) :
    Term.H v (convert (k + 3) (code (topNode k a))) = Term.H v (convert (k + 3) (code a)) := by
  have hz : a ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  rw [H_topNode_above_Omega k a hz v hv, Omega_image_drop k a hr ha hd]

theorem topNode_child_subterm_gap (k : Nat) (a t : new.T (k + 3)) (hr : Recursive a)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom a = .Omega q)
    {z : new.T (k + 3)} (hz : Subterm z a) : mass z < gap (topNode k a) t := by
  have hp := highest_Omega_domain (k + 2) a hr hd
  rw [topNode, gap_Omega _ _ _ hp, mass, vectorMass_lastVec, mass]
  have hm := Support.SourceCoefficientGap.mass_lt_of_subterm hz
  omega

theorem topNode_relative_of_child_support [LargeCardinals.{u}] (k : Nat)
    (a t : new.T (k + 3)) (hr : Recursive a) (ha : RecursiveWF (k + 3) a)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom a = .Omega q)
    (hs : RecursiveWF (k + 3) (topNode k a))
    (hnChild : RecursiveWF (k + 3) (new.T.fund a t)) (v : Term)
    (hv : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund a t))) → UpdatedCoefficient k v a t z)
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
  rcases hcoef z hzChild with he | ho | ⟨b, hb, hw, hm, he⟩
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

end Support.GeneralImageUpperOmega

namespace Support.GeneralImageCofinalityBounds

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion Support.GeneralImageChangingMiddle
open Support.GeneralImageMiddleCofinality Support.GeneralImageMiddleSums
open Support.GeneralImageUpperOmega
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant Support.SourceOmegaTail
open Support.SourceFundGap

universe u

theorem Omega_label_recursiveWF (k : Nat) (s : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) {q : Vec (new.T (k + 3)) (k + 3)}
    (hd : new.T.dom s = .Omega q) : RecursiveWF (k + 3) (.P q .Z) := by
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
            rw [← he]; exact hs
        | Omega ys =>
          simp only [hm] at hd
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte] at hd; cases hd
          · simp only [hv, ↓reduceIte] at hd
            have he := new.Dom.Omega.inj hd
            have hw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
            rw [← he]
            exact Omega_label_recursiveWF k (xs.idx i) hw hchild
    · rw [new.T.dom, ite_eq_right hb] at hd
      have hw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      exact Omega_label_recursiveWF k b hw hd
termination_by new.T.size s
decreasing_by
  all_goals simp_all only [new.T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

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

theorem cofinality_image_le [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) {q : Vec (new.T (k + 3)) (k + 3)}
    (hd : new.T.dom s = .Omega q) :
    Term.le (convert (k + 3) (code (.P q .Z))) (convert (k + 3) (code s)) = true := by
  have hq := Omega_label_recursiveWF k s hs hd
  have hl : new.T.le (.P q .Z) s :=
    Support.SourceDescending.le_trans (domain_principal_le_head s hr hd) (head_le_self s)
  rcases hl with hl | he
  · have hlt := (convert_order k _ _ hq hs).mp hl
    simp only [Term.le, hlt, Bool.or_true]
  · have heq := T_eq_sound _ _ he
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
        Support.OT2.H_succTerm, H_one_empty_above_Omega v hv, List.append_nil] using hh

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

end Support.GeneralImageCofinalityBounds

namespace Support.GeneralImageRegularCofinality

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion Support.GeneralImageChangingMiddle
open Support.GeneralImageMiddleCofinality Support.GeneralImageMiddleSums
open Support.GeneralImageCofinalityBounds
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant Support.SourceOmegaTail
open Support.SourceFundGap

universe u

theorem H_fund_regular_cofinal_support [LargeCardinals.{u}] (k m : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (hml : m + 1 < k + 3)
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (t : new.T (k + 3))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hlt : Term.lt (convert (k + 3) (code (.P xs .Z))) v = true) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t)))) :
    UpdatedCoefficient k v (.P xs .Z) t z := by
  have hdom := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ i, RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1
  let p := new.T.fund (xs.idx ⟨m + 1, hml⟩) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hcoords _) hdom
  have hfArg : new.T.fund (xs.idx ⟨m + 1, hml⟩) t = p := by
    obtain ⟨a, he⟩ := dom_one_succ (xs.idx ⟨m + 1, hml⟩) hdom
    simp only [p, he, Support.SourceSuccessor.fund_succ]
  have hsucc : convert (k + 3) (code (xs.idx ⟨m + 1, hml⟩)) =
      succTerm (convert (k + 3) (code p)) := by
    obtain ⟨a, he⟩ := dom_one_succ (xs.idx ⟨m + 1, hml⟩) hdom
    simp only [p, he, Support.SourceSuccessor.fund_succ, convert_succ]
  let zs := (xs.rplc ⟨m + 1, hml⟩ p).rplc ⟨m, by omega⟩ t
  have zidx (i : Fin (k + 3)) : zs.idx i =
      if i.val = m then t else if i.val = m + 1 then p else xs.idx i := by
    simp only [zs, vec_rplc_idx]
  have zhigh (i : Fin (k + 3)) (hi : m + 1 < i.val) : zs.idx i = xs.idx i := by
    rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
  have zlow (i : Fin (k + 3)) (hi : i.val < m) : zs.idx i = .Z := by
    rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hlow i (by change i.val < m + 1; omega)
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes zs))
  have oldGet (i : Fin (k + 3)) : oldArgs[i.val]?.getD .zero = convert (k + 3) (code (xs.idx i)) :=
    converted_coordinate xs i
  have newGet (i : Fin (k + 3)) : newArgs[i.val]?.getD .zero = convert (k + 3) (code (zs.idx i)) :=
    converted_coordinate zs i
  have newP : newArgs[m + 1]?.getD .zero = convert (k + 3) (code p) := by
    rw [newGet ⟨m + 1, hml⟩, zidx, ite_eq_right (by simp), ite_eq_left rfl]
  have newT : newArgs[m]?.getD .zero = convert (k + 3) (code t) := by
    rw [newGet ⟨m, by omega⟩, zidx, ite_eq_left rfl]
  have oldSucc : oldArgs[m + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by
    rw [oldGet ⟨m + 1, hml⟩]; exact hsucc
  have oldZero : ∀ i, i < m + 1 → oldArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [oldGet ⟨i, by omega⟩, hlow ⟨i, by omega⟩ hi, code, convert]
  have newZero : ∀ i, i < m → newArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [newGet ⟨i, by omega⟩, zlow ⟨i, by omega⟩ hi, code, convert]
  have newSame : ∀ i, m + 1 < i → i < k + 3 → newArgs[i]?.getD .zero = oldArgs[i]?.getD .zero := by
    intro i hi hik
    rw [newGet ⟨i, hik⟩, oldGet ⟨i, hik⟩, zhigh ⟨i, hik⟩ hi]
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
    · refine Or.inr (Or.inr ⟨xs.idx ⟨m + 1, hml⟩, Subterm.coordinate xs .Z _, ?_, ?_, ?_⟩)
      · rw [hfArg]; exact hp
      · rw [hsucc]; exact ho
      · rw [hfArg]; exact he
  rw [fund_regular_bound xs hml hm t, convert_principal, principal_as_layers] at hz
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
        rw [oldGet ⟨k + 2, by omega⟩]; exact (hcoords _).wf
      have hi : Term.wf (.inacc (k + 1) (dropOne h)) = true := by
        change Term.wf (.inacc (k + 1) (dropOne (oldArgs[k + 2]?.getD .zero))) = true
        rw [oldGet ⟨k + 2, by omega⟩]; exact inacc_image_drop_wf k _ (hcoords _)
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
    (xs : Vec (new.T (k + 3)) (k + 3)) (hml : m + 1 < k + 3)
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (hother : ∀ i : Fin (k + 3), i.val ≠ m + 1 → xs.idx i = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (t : new.T (k + 3))
    (v : Term) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hlt : Term.lt (convert (k + 3) (code (.P xs .Z))) v = true) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t)))) :
    z = .zero ∨ ∃ a : new.T (k + 3), RecursiveWF (k + 3) a ∧
      mass a < gap (.P xs .Z) t ∧
      (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a))) := by
  have hdom := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ i, RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1
  let p := new.T.fund (xs.idx ⟨m + 1, hml⟩) .Z
  let c := convert (k + 3) (code p)
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hcoords _) hdom
  have hsucc : convert (k + 3) (code (xs.idx ⟨m + 1, hml⟩)) = succTerm c := by
    obtain ⟨a, he⟩ := dom_one_succ (xs.idx ⟨m + 1, hml⟩) hdom
    simp only [p, c, he, Support.SourceSuccessor.fund_succ, convert_succ]
  have hd : new.T.dom (.P xs .Z) = .Omega xs :=
    regularVector_dom ⟨⟨m + 1, hml⟩, by change 0 < m + 1; omega, hm⟩
  have hpGap : mass p < gap (.P xs .Z) t := by
    have hmP := mass_fund_one (xs.idx ⟨m + 1, hml⟩) .Z hdom
    have hmI := vectorMass_idx_le xs ⟨m + 1, hml⟩
    rw [gap_Omega _ _ _ hd, mass]
    change mass p + 1 = mass (xs.idx ⟨m + 1, hml⟩) at hmP
    simp only [mass]
    omega
  have fromP (h : z = .zero ∨ ArgCoefficient v z c) :
      z = .zero ∨ ∃ a : new.T (k + 3), RecursiveWF (k + 3) a ∧
        mass a < gap (.P xs .Z) t ∧
        (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a))) := by
    rcases h with he | he | he | he
    · exact Or.inl he
    · exact Or.inr ⟨p, hp, hpGap, Or.inl he⟩
    · exact Or.inr ⟨p, hp, hpGap, Or.inr he⟩
    · rcases H_convert_source k v p he with he | ⟨a, ha, he⟩
      · exact Or.inl he
      · exact Or.inr ⟨a, ha.recursiveWF hp,
          Nat.lt_trans (Support.SourceCoefficientGap.mass_lt_of_subterm ha) hpGap, he⟩
  let zs := (xs.rplc ⟨m + 1, hml⟩ p).rplc ⟨m, by omega⟩ t
  have zidx (i : Fin (k + 3)) : zs.idx i =
      if i.val = m then t else if i.val = m + 1 then p else xs.idx i := by
    simp only [zs, vec_rplc_idx]
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes zs))
  have oldGet (i : Fin (k + 3)) : oldArgs[i.val]?.getD .zero = convert (k + 3) (code (xs.idx i)) :=
    converted_coordinate xs i
  have newGet (i : Fin (k + 3)) : newArgs[i.val]?.getD .zero = convert (k + 3) (code (zs.idx i)) :=
    converted_coordinate zs i
  have newP : newArgs[m + 1]?.getD .zero = c := by
    rw [newGet ⟨m + 1, hml⟩, zidx, ite_eq_right (by change m + 1 ≠ m; omega), ite_eq_left rfl]
  have newT : newArgs[m]?.getD .zero = convert (k + 3) (code t) := by
    rw [newGet ⟨m, by omega⟩, zidx, ite_eq_left rfl]
  have oldZero : ∀ i, i < m + 1 → oldArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [oldGet ⟨i, by omega⟩, hlow ⟨i, by omega⟩ hi, code, convert]
  have newZero : ∀ i, i < m → newArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [newGet ⟨i, by omega⟩, zidx, ite_eq_right (by change i ≠ m; omega),
      ite_eq_right (by change i ≠ m + 1; omega),
      hother ⟨i, by omega⟩ (by change i ≠ m + 1; omega), code, convert]
  rw [fund_regular_bound xs hml hm t] at hz
  change z ∈ Term.H v (convert (k + 3) (code (.P zs .Z))) at hz
  by_cases hhighest : m + 1 = k + 2
  · have he : m = k + 1 := by omega
    subst m
    have heOld : convert (k + 3) (code (.P xs .Z)) = pairCut (k + 1) c := by
      rw [convert_principal, principal_as_layers]
      change lower (k + 1) oldArgs (topPair (k + 1)
        (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) = _
      rw [oldGet ⟨k + 2, hml⟩, hsucc, oldZero (k + 1) (by omega)]
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
        · exact fromP (Or.inr (Or.inr (Or.inr (Support.OT2.mem_H_dropOne he))))
  · have hib : m + 1 ≤ k + 1 := by omega
    have highOld (i : Fin (k + 3)) (hi : m + 1 < i.val) : xs.idx i = .Z := hother i (by omega)
    have highNew (i : Fin (k + 3)) (hi : m + 1 < i.val) : zs.idx i = .Z := by
      rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega), hother i (by omega)]
    have heOld : convert (k + 3) (code (.P xs .Z)) = step (m + 1) .zero (succTerm c) := by
      rw [convert_positive_layers k xs ⟨m + 1, hml⟩ (by change 0 < m + 1; omega) hib highOld, hsucc]
      exact lower_keep (m + 1) oldArgs _
        (step_positive_nonzero (m + 1) (by omega) _ _ (succTerm_ne_zero c)) oldZero
    have hOldW := heOld ▸ hs.wf
    have hPreW := step_successor_predecessor (m + 1) .zero c (Or.inl rfl) hp.wf hOldW
    have hCutW := layerCut_wf m (step (m + 1) .zero c)
      (context_above (step_shape _ (Or.inl rfl))) hPreW
    have hCutLt : Term.lt (layerCut m (step (m + 1) .zero c)) v = true :=
      lemma_6_1.{u}.2.1 _ _ _ hCutW hOldW hv
        (step_predecessor_cut_lt m .zero c (Or.inl rfl) hp.wf hOldW) (heOld ▸ hlt)
    rw [convert_positive_layers k zs ⟨m + 1, hml⟩ (by change 0 < m + 1; omega) hib highNew] at hz
    change z ∈ Term.H v (lower (m + 1) newArgs (step (m + 1) .zero _)) at hz
    rw [show convert (k + 3) (code (zs.idx ⟨m + 1, hml⟩)) = c from by
      rw [zidx, ite_eq_right (by change m + 1 ≠ m; omega), ite_eq_left rfl], lower_succ, newT,
      H_lower_zeros_above_Omega v hOmega m newArgs _ newZero] at hz
    have hPre := H_step_of_layerCut_lt v hOmega m (step (m + 1) .zero c) _ hCutLt hz
    rcases H_step_support v (m + 1) .zero c hPre with he | he | he
    · exact fromP (Or.inl he)
    · cases he
    · exact fromP (Or.inr he)

theorem updated_coefficient_lt_old [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s t : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
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
      rcases he with rfl | rfl <;> simpa only [new.T.fund, code, convert, dropOne] using hzlt
    · have haW := ha.recursiveWF hs
      have hal : new.T.lt a s := by
        apply (convert_order k _ _ haW hs).mpr
        rcases hm with hm | hm
        · exact (Term.allLt_iff _ _).mp hH _ hm
        · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hzero hhead ((Term.allLt_iff _ _).mp hH _ hm)
      have hl := (convert_order k _ _ hw hs).mp (T_trans _ _ _ (fund_lt a t ha0) hal)
      rcases he with rfl | rfl
      · exact hl
      · exact dropOne_lt_of_lt hw.wf hs.wf hl

theorem fund_regular_cofinal_relative_of_wf [LargeCardinals.{u}] (k m : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (hml : m + 1 < k + 3)
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (i j : Fin (k + 3)) (hij : i ≠ j) (hi : xs.idx i ≠ .Z) (hj : xs.idx j ≠ .Z)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (t : new.T (k + 3))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t)) :
    ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P xs .Z))) v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t))))
          (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true := by
  have hd : new.T.dom (.P xs .Z) = .Omega xs := regularVector_dom ⟨⟨m + 1, hml⟩, by change 0 < m + 1; omega, hm⟩
  intro v hvR hv hOmega hlt hH
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := by
    rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
  have hnZ : convert (k + 3) (code (new.T.fund (.P xs .Z) t)) ≠ .zero := by
    intro he
    have hh : new.T.fund (.P xs .Z) t = .Z :=
      code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
    exact domOmega_fund_ne_zero _ t hd hh
  exact closed_of_updated_coefficients k v _ t hs hn (Omega_image_head_ne_one k _ hr hs hd) hsZ hnZ
    (fun a ha => principal_subterm_gap xs i j hij hi hj hd t ha)
    (fun z hz => H_fund_regular_cofinal_support k m xs hml hm hs t v hvR hv hOmega hlt hz) hH

theorem fund_regular_cofinal_relative_all_of_wf [LargeCardinals.{u}] (k m : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (hml : m + 1 < k + 3)
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (t : new.T (k + 3))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t)) :
    ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P xs .Z))) v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t))))
          (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true := by
  classical
  let i : Fin (k + 3) := ⟨m + 1, hml⟩
  have hi : xs.idx i ≠ .Z := by
    intro he
    have hdom := (Support.DimensionCut.minIdx_spec xs hm).1
    rw [show xs.idx ⟨m + 1, hml⟩ = .Z from he, new.T.dom] at hdom
    cases hdom
  by_cases hex : ∃ j : Fin (k + 3), i ≠ j ∧ xs.idx j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact fund_regular_cofinal_relative_of_wf k m xs hml hm i j hij hi hj hr hs t hn
  · have hother : ∀ j : Fin (k + 3), j.val ≠ m + 1 → xs.idx j = .Z := by
      intro j hj
      apply Classical.byContradiction
      intro hn
      apply hex
      refine ⟨j, ?_, hn⟩
      intro he
      exact hj (congrArg Fin.val he.symm)
    have hd : new.T.dom (.P xs .Z) = .Omega xs :=
      regularVector_dom ⟨⟨m + 1, hml⟩, by change 0 < m + 1; omega, hm⟩
    have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := by
      rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
    have hnZ : convert (k + 3) (code (new.T.fund (.P xs .Z) t)) ≠ .zero := by
      intro he
      have hh : new.T.fund (.P xs .Z) t = .Z :=
        code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
      exact domOmega_fund_ne_zero _ t hd hh
    have hhead := Omega_image_head_ne_one k _ hr hs hd
    intro v hvR hv hOmega hlt hH
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    have hzOld := updated_coefficient_lt_old k v _ t hs hhead hsZ hH
      (H_fund_regular_cofinal_support k m xs hml hm hs t v hvR hv hOmega hlt hz)
    rcases H_fund_regular_single_small k m xs hml hm hother hs t v hv hOmega hlt hz
      with he | ⟨a, ha, hmA, he⟩
    · rw [he]; exact (zero_lt_iff _).mpr hnZ
    · have hal : new.T.lt a (.P xs .Z) := by
        apply (convert_order k _ _ ha hs).mpr
        rcases he with he | he
        · exact he ▸ hzOld
        · exact undrop_lt_head_ne_one _ _ ha.wf hs.wf hsZ hhead (he ▸ hzOld)
      have hl := (convert_order k _ _ ha hn).mp (small_lt_fund_all (.P xs .Z) t a hal hmA)
      rcases he with rfl | rfl
      · exact hl
      · exact dropOne_lt_of_lt ha.wf hn.wf hl

theorem fund_regular_cofinal_relative_all [LargeCardinals.{u}] (k m : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (hml : m + 1 < k + 3)
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (t : new.T (k + 3)) (ht : RecursiveWF (k + 3) t)
    (hHt : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code t)))
      (convert (k + 3) (code t)) = true) :
    RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P xs .Z))) v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t))))
          (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) = true := by
  have hn := fund_regular_recursiveWF k m xs hml hm t hs ht hHt
  exact ⟨hn, fund_regular_cofinal_relative_all_of_wf k m xs hml hm hr hs t hn⟩

end Support.GeneralImageRegularCofinality

namespace Support.GeneralImageCofinalityInheritance

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageCountableLayers Support.GeneralImageRelativePredecessor
open Support.GeneralImageCountableRecursion Support.GeneralImageHeadCuts
open Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion
open Support.GeneralImageMiddleSums Support.GeneralImageCofinalityBounds
open Support.GeneralImageRegularCofinality Support.GeneralImageHighOmega
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant

universe u

theorem le_psi_index_bound [LargeCardinals.{u}] (n : Nat) (a b l : Term)
    (hl : Term.wf l = true) (hw : Term.wf (.psi (.inacc n a) b) = true)
    (hle : Term.le l (.psi (.inacc n a) b) = true) :
    Term.lt l (.inacc n a) = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  have hroot : Term.lt (.psi (.inacc n a) b) (.inacc n a) = true := by simp [Term.lt, Term.fT]
  rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
  · rw [he]; exact hroot
  · exact lemma_6_1.{u}.2.1 _ _ _ hl hw hp.2.1 he hroot

theorem step_psi_of_drop (n : Nat) (a c : Term)
    (hc : c ≠ .zero) (hd : dropOne c = c) :
    step n a c = .psi (layerCut n a) c := by
  by_cases ha : a = .zero
  · by_cases hn : n = 0 <;> simp [step, layerCut, ha, hn, hc, hd, Term.bigOmega]
  · simp [step, layerCut, regular, ha, hc, hd]

theorem Omega_principal_image_ne_low [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom (.P xs .Z) = .Omega q) :
    convert (k + 3) (code (.P xs .Z)) ≠ .psi Term.bigOmega (convert (k + 3) (code (xs.idx i))) := by
  intro he
  have harg : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
  have hw := he ▸ hs.wf
  have hlow : RecursiveWF (k + 3) (.P (lowVec (k + 2) (xs.idx i)) .Z) :=
    (low_principal_recursiveWF_iff _ _ _).mpr ⟨harg, ((Term.wf_psi_iff _ _).mp hw).2.2.2⟩
  have hsource := convert_injective k _ _ hs hlow (by rw [convert_low_principal]; exact he)
  have ho : Outer (.P (lowVec (k + 2) (xs.idx i)) .Z) := .cons _ _ .zero
  rw [hsource] at hd
  exact outer_not_Omega ho q hd

theorem step_replace_cofinal_wf [LargeCardinals.{u}] (n : Nat)
    (a c t l : Term) (ha : Above n a) (ht : Term.wf t = true)
    (hc : c ≠ .zero) (hd : dropOne c = c) (hl : Term.wf l = true)
    (hle : Term.le l (step n a c) = true)
    (hcut : Term.lt Term.bigOmega (layerCut n a) = true)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.lt Term.bigOmega v = true → Term.lt l v = true →
      Term.allLt (Term.H v c) c = true → Term.allLt (Term.H v t) t = true)
    (hw : Term.wf (step n a c) = true) : Term.wf (step n a t) = true := by
  by_cases ht0 : t = .zero
  · rw [ht0]; exact step_zero_wf n a (step_context_wf ha hw)
  · have he := step_psi_of_drop n a c hc hd
    rw [he] at hw hle
    have hp := (Term.wf_psi_iff _ _).mp hw
    have hlt : Term.lt l (layerCut n a) = true := le_psi_index_bound _ _ _ _ hl hw hle
    have hH := hrel _ hp.1 hp.2.1 hcut hlt hp.2.2.2
    have hnew : step n a t = .psi (layerCut n a) (dropOne t) := by
      by_cases ha0 : a = .zero
      · by_cases hn : n = 0
        · simp [layerCut, ha0, hn, Term.bigOmega, lt_self] at hcut
        · simp [step, layerCut, ha0, hn, ht0]
      · simp [step, layerCut, regular, ha0, ht0]
    rw [hnew]
    exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ht, H_drop_bound _ t ht hH⟩

theorem topPair_replace_cofinal_wf [LargeCardinals.{u}] (n : Nat) (hn : 0 < n)
    (a c t l : Term) (hi : Term.wf (.inacc n (dropOne a)) = true)
    (ht : Term.wf t = true) (hc : c ≠ .zero) (hd : dropOne c = c)
    (hl : Term.wf l = true) (hle : Term.le l (topPair n a c) = true)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.lt Term.bigOmega v = true → Term.lt l v = true →
      Term.allLt (Term.H v c) c = true → Term.allLt (Term.H v t) t = true)
    (hw : Term.wf (topPair n a c) = true) : Term.wf (topPair n a t) = true := by
  by_cases ht0 : t = .zero
  · by_cases ha0 : a = .zero
    · simp [topPair, ht0, ha0, Term.wf]
    · simpa only [topPair, ht0, ha0, ↓reduceIte] using hi
  · have he : topPair n a c = .psi (pairCut n a) c := by simp [topPair, pairCut, hc, hd]
    rw [he] at hw hle
    have hp := (Term.wf_psi_iff _ _).mp hw
    have hlt : Term.lt l (pairCut n a) = true := le_psi_index_bound _ _ _ _ hl hw hle
    have hH := hrel _ hp.1 hp.2.1 (pairCut_above_Omega n hn a) hlt hp.2.2.2
    have heNew : topPair n a t = .psi (pairCut n a) (dropOne t) := by simp [topPair, pairCut, ht0]
    rw [heNew]
    exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ht, H_drop_bound _ t ht hH⟩

theorem lower_replace_cofinal_wf [LargeCardinals.{u}] (j cut : Nat)
    (hj : cut < j) (xs ys : List Term) (a c t l : Term)
    (hctx : Context j a) (ht : Term.wf t = true) (hc : c ≠ .zero)
    (hd : dropOne c = c) (hl : Term.wf l = true)
    (hle : Term.le l (lower j xs a) = true)
    (hnotLow : lower j xs a ≠ .psi Term.bigOmega c)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.lt Term.bigOmega v = true → Term.lt l v = true →
      Term.allLt (Term.H v c) c = true → Term.allLt (Term.H v t) t = true)
    (hx : xs[cut]?.getD .zero = c) (hy : ys[cut]?.getD .zero = t)
    (hzeroOld : ∀ i, i < cut → xs[i]?.getD .zero = .zero)
    (hzeroNew : ∀ i, i < cut → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, cut < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero)
    (hw : Term.wf (lower j xs a) = true) : Term.wf (lower j ys a) = true := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    by_cases hij : cut < j
    · rw [lower_succ] at hw hle hnotLow ⊢
      rw [hsame j hij (by omega)]
      exact ih hij _ (step_shape _ (context_above hctx)) hle hnotLow
        (fun i hi hik => hsame i hi (by omega)) hw
    · have he : j = cut := by omega
      subst j
      have heOld : lower (cut + 1) xs a = step cut a c := by
        rw [lower_succ, hx]
        apply lower_keep cut xs _ _ hzeroOld
        rw [step_psi_of_drop cut a c hc hd]
        intro he; cases he
      rw [heOld] at hw hle hnotLow
      have hcut : Term.lt Term.bigOmega (layerCut cut a) = true := by
        by_cases hcut0 : cut = 0
        · subst cut
          have ha0 : a ≠ .zero := by
            intro he
            apply hnotLow
            simp [step, he]
          simpa only [layerCut, ha0, ↓reduceIte, Term.bigOmega, inacc_same_lt] using
            (zero_lt_iff (succTerm a)).mpr (succTerm_ne_zero a)
        · exact layerCut_above_Omega cut (by omega) a
      rw [lower_succ, hy]
      exact lower_zero_wf cut ys _ hzeroNew
        (step_replace_cofinal_wf cut a c t l (context_above hctx) ht hc hd hl hle hcut hrel hw)

theorem principal_replace_cofinal_recursiveWF [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hib : i.val ≤ k + 1)
    (hlow : ∀ j, j.val < i.val → xs.idx j = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (a : new.T (k + 3))
    (ha : RecursiveWF (k + 3) a) (hc0 : xs.idx i ≠ .Z)
    (hdrop : dropOne (convert (k + 3) (code (xs.idx i))) = convert (k + 3) (code (xs.idx i)))
    (l : Term) (hl : Term.wf l = true)
    (hle : Term.le l (convert (k + 3) (code (.P xs .Z))) = true)
    (hnotLow : convert (k + 3) (code (.P xs .Z)) ≠
      .psi Term.bigOmega (convert (k + 3) (code (xs.idx i))))
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.lt Term.bigOmega v = true → Term.lt l v = true →
      Term.allLt (Term.H v (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true →
      Term.allLt (Term.H v (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    RecursiveWF (k + 3) (.P (xs.rplc i a) .Z) := by
  let ys := xs.rplc i a
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have hold (j : Fin (k + 3)) : oldArgs[j.val]?.getD .zero = convert (k + 3) (code (xs.idx j)) :=
    converted_coordinate xs j
  have hnew (j : Fin (k + 3)) : newArgs[j.val]?.getD .zero = convert (k + 3) (code (ys.idx j)) :=
    converted_coordinate ys j
  have hnewa : newArgs[i.val]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew i]; simp only [ys, vec_rplc_idx, ↓reduceIte]
  have hzeroOld : ∀ j, j < i.val → oldArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hold ⟨j, by omega⟩, hlow ⟨j, by omega⟩ hj, code, convert]
  have hzeroNew : ∀ j, j < i.val → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew ⟨j, by omega⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
    rw [hlow ⟨j, by omega⟩ hj, code, convert]
  have hsame : ∀ j, i.val < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj hjk
    rw [hnew ⟨j, hjk⟩, hold ⟨j, hjk⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hcNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have hw := hs.wf
  have hbound := hle
  rw [convert_principal, principal_as_layers] at hw hbound hnotLow
  change Term.wf (lower (k + 1) oldArgs (topPair (k + 1)
    (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero))) = true at hw
  change Term.le l (lower (k + 1) oldArgs (topPair (k + 1)
    (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero))) = true at hbound
  rw [RecursiveWF]
  refine ⟨?_, recursive_zero _ _, ?_⟩
  · intro j
    simp only [vec_rplc_idx]
    split
    · exact ha
    · exact hcoords j
  · rw [convert_principal, principal_as_layers]
    change Term.wf (lower (k + 1) newArgs (topPair (k + 1)
      (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) = true
    rw [hsame (k + 2) (by omega) (by omega)]
    by_cases he : i.val = k + 1
    · have htopNZ : topPair (k + 1) (oldArgs[k + 2]?.getD .zero)
          (oldArgs[k + 1]?.getD .zero) ≠ .zero := by
        rw [← he, hold i]
        simp only [topPair, hcNZ, ↓reduceIte]
        intro he0; cases he0
      rw [lower_keep (k + 1) oldArgs _ htopNZ (by simpa only [he] using hzeroOld)] at hw hbound
      rw [← he, hnewa]
      apply lower_zero_wf i.val newArgs _ hzeroNew
      rw [← he, hold i] at hw hbound
      apply topPair_replace_cofinal_wf i.val (by rw [he]; omega) _ _ _ l _ ha.wf hcNZ hdrop hl hbound hrel hw
      rw [he, hold ⟨k + 2, by omega⟩]; exact inacc_image_drop_wf k _ (hcoords _)
    · rw [hsame (k + 1) (by omega) (by omega)]
      exact lower_replace_cofinal_wf (k + 1) i.val (by omega) oldArgs newArgs _ _ _ l
        (topPair_context _ _ _) ha.wf hcNZ hdrop hl hbound hnotLow hrel (hold i) hnewa
        hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega)) hw

end Support.GeneralImageCofinalityInheritance

namespace Support.GeneralImageCofinalityCoefficients

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleSums Support.GeneralImageMiddleCofinality
open Support.GeneralImageCofinalityBounds Support.GeneralImageRegularCofinality
open Support.GeneralImageCofinalityInheritance Support.GeneralImageUpperOmega
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceFundGap

universe u

theorem H_psi_replacement_support [LargeCardinals.{u}] (v w c t : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hw : Term.wf (.psi w c) = true) (hn : Term.wf (.psi w (dropOne t)) = true)
    (hlt : Term.lt (.psi w (dropOne t)) (.psi w c) = true) {z : Term}
    (hz : z ∈ Term.H v (.psi w (dropOne t))) :
    (z ∈ Term.H v w ∧ z ∈ Term.H v (.psi w c)) ∨
      (z = dropOne t ∨ z ∈ Term.H v t) ∧ c ∈ Term.H v (.psi w c) ∧
        (∀ a, a ∈ Term.H v c → a ∈ Term.H v (.psi w c)) := by
  by_cases hskip : Term.le (.psi w c) (Term.predR v) = true
  · have hp := (sem_of_wf.{u} hv).isR_pred hvR
    have hle := target_le_trans hn hw hp.1 (by simp [Term.le, hlt]) hskip
    rw [H_eq_nil_of_le_pred v _ hvR hv hn hle] at hz
    cases hz
  · have hskipF : Term.le (.psi w c) (Term.predR v) = false := by
      cases he : Term.le (.psi w c) (Term.predR v) <;> simp_all
    have ctx (a : Term) (ha : a ∈ Term.H v w) : a ∈ Term.H v (.psi w c) := by
      rw [Term.H, hskipF]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split
      · exact ha
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ ha)
    rw [Term.H] at hz
    split at hz
    · cases hz
    · by_cases hcut : Term.lt w v = true
      · simp only [hcut, ↓reduceIte] at hz
        exact Or.inl ⟨hz, ctx _ hz⟩
      · have hcutF : Term.lt w v = false := by cases he : Term.lt w v <;> simp_all
        simp only [hcutF, Bool.false_eq_true, ↓reduceIte] at hz
        have hroot : c ∈ Term.H v (.psi w c) := by
          rw [Term.H, hskipF, hcutF]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact List.mem_cons_self
        have hchild (a : Term) (ha : a ∈ Term.H v c) : a ∈ Term.H v (.psi w c) := by
          rw [Term.H, hskipF, hcutF]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
        rcases List.mem_cons.mp hz with he | hz
        · exact Or.inr ⟨Or.inl he, hroot, hchild⟩
        · rcases List.mem_append.mp hz with hz | hz
          · exact Or.inr ⟨Or.inr (Support.OT2.mem_H_dropOne hz), hroot, hchild⟩
          · exact Or.inl ⟨hz, ctx _ hz⟩

theorem step_ne_zero_of_argument (n : Nat) (a c : Term) (hc : c ≠ .zero) :
    step n a c ≠ .zero := by
  by_cases ha : a = .zero
  · by_cases hn : n = 0 <;> simp [step, ha, hn, hc]
  · simp [step, ha, hc]

theorem lower_selected_step (j cut : Nat) (hj : cut < j) (xs ys : List Term)
    (a c t : Term) (hc : c ≠ .zero) (ht : t ≠ .zero)
    (hx : xs[cut]?.getD .zero = c) (hy : ys[cut]?.getD .zero = t)
    (hzeroOld : ∀ i, i < cut → xs[i]?.getD .zero = .zero)
    (hzeroNew : ∀ i, i < cut → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, cut < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero) :
    ∃ b, lower j xs a = step cut b c ∧ lower j ys a = step cut b t := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    by_cases hij : cut < j
    · rw [lower_succ, lower_succ, hsame j hij (by omega)]
      exact ih hij _ (fun i hi hik => hsame i hi (by omega))
    · have he : j = cut := by omega
      subst j
      refine ⟨a, ?_, ?_⟩
      · rw [lower_succ, hx]
        exact lower_keep cut xs _ (step_ne_zero_of_argument cut a c hc) hzeroOld
      · rw [lower_succ, hy]
        exact lower_keep cut ys _ (step_ne_zero_of_argument cut a t ht) hzeroNew

theorem principal_replacement_psi_images (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hib : i.val ≤ k + 1)
    (hlow : ∀ j, j.val < i.val → xs.idx j = .Z) (a : new.T (k + 3))
    (hc : convert (k + 3) (code (xs.idx i)) ≠ .zero)
    (ha : convert (k + 3) (code a) ≠ .zero)
    (hd : dropOne (convert (k + 3) (code (xs.idx i))) = convert (k + 3) (code (xs.idx i)))
    (hnotLow : convert (k + 3) (code (.P xs .Z)) ≠
      .psi Term.bigOmega (convert (k + 3) (code (xs.idx i)))) :
    ∃ w, convert (k + 3) (code (.P xs .Z)) = .psi w (convert (k + 3) (code (xs.idx i))) ∧
      convert (k + 3) (code (.P (xs.rplc i a) .Z)) = .psi w (dropOne (convert (k + 3) (code a))) := by
  let ys := xs.rplc i a
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have hold (j : Fin (k + 3)) : oldArgs[j.val]?.getD .zero = convert (k + 3) (code (xs.idx j)) :=
    converted_coordinate xs j
  have hnew (j : Fin (k + 3)) : newArgs[j.val]?.getD .zero = convert (k + 3) (code (ys.idx j)) :=
    converted_coordinate ys j
  have hnewa : newArgs[i.val]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew i]; simp only [ys, vec_rplc_idx, ↓reduceIte]
  have hzeroOld : ∀ j, j < i.val → oldArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hold ⟨j, by omega⟩, hlow ⟨j, by omega⟩ hj, code, convert]
  have hzeroNew : ∀ j, j < i.val → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew ⟨j, by omega⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
    rw [hlow ⟨j, by omega⟩ hj, code, convert]
  have hsame : ∀ j, i.val < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj hjk
    rw [hnew ⟨j, hjk⟩, hold ⟨j, hjk⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
  have heOld : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have heNew : convert (k + 3) (code (.P ys .Z)) = lower (k + 1) newArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
    rw [hsame (k + 2) (by omega) (by omega)]
  by_cases hi : i.val = k + 1
  · let h := oldArgs[k + 2]?.getD .zero
    have htopOld : topPair (k + 1) h (convert (k + 3) (code (xs.idx i))) ≠ .zero := by simp [topPair, hc]
    have htopNew : topPair (k + 1) h (convert (k + 3) (code a)) ≠ .zero := by simp [topPair, ha]
    have hcOld : oldArgs[k + 1]?.getD .zero = convert (k + 3) (code (xs.idx i)) := by rw [← hi, hold i]
    have hcNew : newArgs[k + 1]?.getD .zero = convert (k + 3) (code a) := by rw [← hi, hnewa]
    refine ⟨pairCut (k + 1) h, ?_, ?_⟩
    · rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ htopOld (by simpa only [hi] using hzeroOld)]
      simp [topPair, pairCut, hc, hd, h]
    · rw [heNew, hcNew, lower_keep (k + 1) newArgs _ htopNew (by simpa only [hi] using hzeroNew)]
      simp [topPair, pairCut, ha, h]
  · rw [hsame (k + 1) (by omega) (by omega)] at heNew
    obtain ⟨b, hbOld, hbNew⟩ := lower_selected_step (k + 1) i.val (by omega) oldArgs newArgs _ _ _ hc ha
      (hold i) hnewa hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega))
    have heO : convert (k + 3) (code (.P xs .Z)) = step i.val b (convert (k + 3) (code (xs.idx i))) := heOld.trans hbOld
    have heN : convert (k + 3) (code (.P ys .Z)) = step i.val b (convert (k + 3) (code a)) := heNew.trans hbNew
    refine ⟨layerCut i.val b, heO.trans (step_psi_of_drop _ _ _ hc hd), ?_⟩
    rw [heN]
    by_cases hb0 : b = .zero
    · by_cases hi0 : i.val = 0
      · apply False.elim
        apply hnotLow
        rw [heO]
        simp [step, hb0, hi0]
      · simp [step, layerCut, hb0, hi0, ha]
    · simp [step, layerCut, regular, hb0, ha]

theorem parent_Omega_updated_support [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hd : new.T.dom (.P xs .Z) = .Omega q) (t : new.T (k + 3))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) t))) →
      UpdatedCoefficient k v (xs.idx i) t z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) t))) →
      UpdatedCoefficient k v (.P xs .Z) t z := by
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
    · exact Or.inr (Or.inl (heOld ▸ ho))
    · rcases he with he | hzChild
      · exact Or.inr (Or.inr ⟨xs.idx i, Subterm.coordinate xs .Z i, hnChild,
          Or.inl (heOld ▸ hroot), Or.inr he⟩)
      · exact lift (fun z hz => heOld ▸ hchild z hz) (hcoef z hzChild)
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
    exact lift (fun z hz => heH ▸ hz) (hcoef z (Support.OT2.mem_H_dropOne hz))

theorem parent_Omega_relative_of_child_support [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hd : new.T.dom (.P xs .Z) = .Omega q) (t : new.T (k + 3))
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) t))) →
      UpdatedCoefficient k v (xs.idx i) t z)
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
    exact closed_of_updated_coefficients k v _ t hs hn hhead hsZ hnZ
      (fun a ha => principal_subterm_gap xs i j hij hc0 hj hd t ha)
      (parent_Omega_updated_support k xs q i hm hr hs hd t hn v hvR hv hOmega hcoef) hH
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
          rcases hcoef z hzChild with he | ho | ⟨a, ha, haW, hmA, he⟩
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
      have htop := topNode_relative_of_child_support k (xs.idx i) t hchildR (hcoords i) hchildD
        (hsource ▸ hs) hnChild v hOmega hcoef (hsource ▸ hH)
      exact (congrArg (fun s => new.T.fund s t) hsource) ▸ htop

end Support.GeneralImageCofinalityCoefficients

namespace Support.GeneralImageOmegaCofinality

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

universe u

theorem Omega_fund_cofinal_invariant [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (t : new.T (k + 3)) (ht : RecursiveWF (k + 3) t)
    (hHt : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code t)))
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
            obtain ⟨hn, hrelative⟩ := fund_regular_cofinal_relative_all k m xs hin hm hr hs t ht hHt
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
            obtain ⟨hnChild, hchildInv⟩ := Omega_fund_cofinal_invariant k (xs.idx i) hchildR (hcoords i) hchildD t ht hHt
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
      obtain ⟨hnB, htailInv⟩ := Omega_fund_cofinal_invariant k b hbr hbw hdb t ht hHt
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

theorem all_Omega_iter_closed [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (hsub : ∀ a, Subterm a s → new.T.lt a s) (n : Nat) :
    RecursiveWF (k + 3) (new.T.iter (new.T.fund s) (new.T.ofNat n)) ∧
      Term.allLt (Term.H Term.bigOmega (convert (k + 3)
        (code (new.T.iter (new.T.fund s) (new.T.ofNat n)))))
        (convert (k + 3) (code (new.T.iter (new.T.fund s) (new.T.ofNat n)))) = true := by
  induction n with
  | zero =>
    simp only [new.T.ofNat, new.T.iter]
    exact ⟨recursive_zero _ _, by simp [code, convert, Term.H, Term.allLt]⟩
  | succ n ih =>
    rw [iter_ofNat_succ]
    have hn := (Omega_fund_cofinal_invariant k s hr hs hd _ ih.1 ih.2).1
    refine ⟨hn, ?_⟩
    exact H_convert_bound_of_subterms k Term.bigOmega _ hn
      (by simpa only [iter_ofNat_succ] using Omega_iter_subterms s hr hd hsub (n + 1))

end Support.GeneralImageOmegaCofinality

namespace Support.GeneralImageZeroFund

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageCountableLayers Support.GeneralImageRelativePredecessor
open Support.GeneralImageCountableRecursion Support.GeneralImageOmegaCoefficients
open Support.GeneralImageMiddleCofinality Support.GeneralImageMiddleSums Support.GeneralImageUpperOmega
open Support.GeneralImageCofinalityBounds Support.GeneralImageCofinalityInheritance
open Support.GeneralImageSharedTopPair
open Support.GeneralImageSharedContext
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularCofinality
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageOmegaCofinality

universe u

theorem lower_selected_step_context (j cut : Nat) (hj : cut < j) (xs ys : List Term)
    (a c t : Term) (hc : c ≠ .zero) (hctx : Context j a)
    (hx : xs[cut]?.getD .zero = c) (hy : ys[cut]?.getD .zero = t)
    (hzeroOld : ∀ i, i < cut → xs[i]?.getD .zero = .zero)
    (_hzeroNew : ∀ i, i < cut → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, cut < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero) :
    ∃ b, Above cut b ∧ lower j xs a = step cut b c ∧
      lower j ys a = lower cut ys (step cut b t) := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    by_cases hij : cut < j
    · rw [lower_succ, lower_succ, hsame j hij (by omega)]
      exact ih hij _ (step_shape _ (context_above hctx)) (fun i hi hik => hsame i hi (by omega))
    · have he : j = cut := by omega
      subst j
      refine ⟨a, context_above hctx, ?_, ?_⟩
      · rw [lower_succ, hx]; exact lower_keep cut xs _ (step_ne_zero_of_argument cut a c hc) hzeroOld
      · rw [lower_succ, hy]

theorem H_topPair_zero_support [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (n : Nat) (h c : Term)
    (hh : Term.wf h = true) (hc : Term.wf c = true) (hc0 : c ≠ .zero)
    (hi : Term.wf (.inacc n (dropOne h)) = true)
    (hw : Term.wf (topPair n h c) = true) {z : Term}
    (hz : z ∈ Term.H v (topPair n h .zero)) : z ∈ Term.H v (topPair n h c) := by
  have hn : Term.wf (topPair n h .zero) = true := by
    by_cases hh0 : h = .zero
    · simp [topPair, hh0, Term.wf]
    · simpa only [topPair, hh0, ↓reduceIte] using hi
  have hl : Term.lt (topPair n h .zero) (topPair n h c) = true := by
    rw [topPair_order n hh (show Term.wf .zero = true from rfl) hh hc]
    simp [lt_self, hc0, zero_lt_iff]
  have heOld : topPair n h c = .psi (pairCut n h) (dropOne c) := by
    by_cases hh0 : h = .zero <;> simp [topPair, pairCut, hh0, hc0]
  by_cases hs : Term.le (topPair n h c) (Term.predR v) = true
  · have hp := (sem_of_wf.{u} hv).isR_pred hvR
    have hle := target_le_trans hn hw hp.1 (by simp [Term.le, hl]) hs
    rw [H_eq_nil_of_le_pred v _ hvR hv hn hle] at hz; cases hz
  · have hcH : z ∈ Term.H v (pairCut n h) := by
      by_cases hh0 : h = .zero
      · simp [topPair, hh0, Term.H] at hz
      · simp only [topPair, hh0, ↓reduceIte] at hz
        simpa only [pairCut, hh0, ↓reduceIte] using H_inacc_succ_support v n (dropOne h) hz
    have hsF : Term.le (.psi (pairCut n h) (dropOne c)) (Term.predR v) = false := by
      rw [heOld] at hs
      cases he : Term.le (.psi (pairCut n h) (dropOne c)) (Term.predR v) <;> simp_all
    rw [heOld, Term.H, hsF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    split
    · exact hcH
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hcH)

theorem zero_relative_of_updated_support [LargeCardinals.{u}] (k : Nat)
    (s : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (new.T.fund s .Z))
    (v : Term) (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hsZ : convert (k + 3) (code s) ≠ .zero)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s .Z))) →
      UpdatedCoefficient k v s .Z z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s .Z))))
      (convert (k + 3) (code (new.T.fund s .Z))) = true := by
  by_cases hnZ : convert (k + 3) (code (new.T.fund s .Z)) = .zero
  · rw [hnZ, Term.H]; rfl
  · apply (Term.allLt_iff _ _).mpr
    intro z hz
    have hzOld := updated_coefficient_lt_old k v s .Z hs hhead hsZ hH (hcoef z hz)
    rcases H_convert_source k v (new.T.fund s .Z) hz with rfl | ⟨a, ha, he⟩
    · exact (zero_lt_iff _).mpr hnZ
    · have haW := ha.recursiveWF hn
      have haOld : new.T.lt a s := by
        apply (convert_order k _ _ haW hs).mpr
        rcases he with he | he
        · exact he ▸ hzOld
        · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hsZ hhead (he ▸ hzOld)
      have hmass : mass a < gap s .Z := by
        have haM := Support.SourceCoefficientGap.mass_lt_of_subterm ha
        have hfund := mass_fund_zero_le s
        simp only [gap, ↓reduceIte]
        omega
      have haNew := (convert_order k _ _ haW hn).mp (small_lt_fund_all s .Z a haOld hmass)
      rcases he with rfl | rfl
      · exact haNew
      · exact dropOne_lt_of_lt haW.wf hn.wf haNew

theorem parent_zero_updated_support [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hlow : ∀ j, j.val < i.val → xs.idx j = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (hc0 : xs.idx i ≠ .Z)
    (hdrop : dropOne (convert (k + 3) (code (xs.idx i))) = convert (k + 3) (code (xs.idx i)))
    (hf : new.T.fund (.P xs .Z) .Z = .P (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z)
    (hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) .Z))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (xs.idx i) .Z))) →
      UpdatedCoefficient k v (xs.idx i) .Z z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) .Z))) →
      UpdatedCoefficient k v (.P xs .Z) .Z z := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hnChild : RecursiveWF (k + 3) (new.T.fund (xs.idx i) .Z) := by
    have hw := hn
    rw [hf, RecursiveWF] at hw
    simpa only [vec_rplc_idx, ↓reduceIte] using hw.1 i
  have hcNZ : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro he; exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (xs.idx i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term}
      (hc : UpdatedCoefficient k v (xs.idx i) .Z z) : UpdatedCoefficient k v (.P xs .Z) .Z z := by
    rcases hc with he | ho | ⟨a, ha, hw, ho, he⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl (embed _ ho))
    · exact Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i), hw,
        ho.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), he⟩)
  intro z hz
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (xs.idx i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff _ _ _).mpr ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (xs.idx i)) .Z)
      hs hwLow (by rw [convert_low_principal]; exact hIsLow)
    have heVec := (new.T.P.inj heSource).1
    have hi0 : i.val = 0 := by
      by_cases hi : i.val = 0
      · exact hi
      · have hc := congrArg (fun us => us.idx i) heVec
        rw [lowVec_idx, ite_eq_right hi] at hc
        exact False.elim (hc0 hc)
    have heR : xs.rplc i (new.T.fund (xs.idx i) .Z) =
        lowVec (k + 2) (new.T.fund (xs.idx i) .Z) := by
      have hr := congrArg (fun us => us.rplc i (new.T.fund (xs.idx i) .Z)) heVec
      have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
      rw [hi, lowVec_rplc_zero] at hr
      simpa only [hi] using hr
    rw [hf, heR, H_low_empty_above_Omega v hOmega] at hz
    cases hz
  · by_cases hib : i.val ≤ k + 1
    · by_cases hnewNZ : convert (k + 3) (code (new.T.fund (xs.idx i) .Z)) ≠ .zero
      · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow _ hcNZ hnewNZ hdrop hIsLow
        have heFund := hf ▸ heNew
        have hlt := (convert_order k _ _ hn hs).mp (fund_lt (.P xs .Z) .Z (by intro he; cases he))
        have hwOld := heOld ▸ hs.wf
        have hwNew := heFund ▸ hn.wf
        rw [heOld, heFund] at hlt
        rw [heFund] at hz
        rcases H_psi_replacement_support v w _ _ hvR hv hwOld hwNew hlt hz
          with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
        · exact Or.inr (Or.inl (heOld ▸ ho))
        · rcases he with he | hzChild
          · exact Or.inr (Or.inr ⟨xs.idx i, Subterm.coordinate xs .Z i, hnChild,
              Or.inl (heOld ▸ hroot), Or.inr he⟩)
          · exact lift (fun z hz => heOld ▸ hchild z hz) (hcoef z hzChild)
      · have heZero : new.T.fund (xs.idx i) .Z = .Z := by
          apply code_injective
          apply (Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp
          exact Classical.not_not.mp hnewNZ
        let ys := xs.rplc i .Z
        let oldArgs := arguments (k + 3) (trim (codes xs))
        let newArgs := arguments (k + 3) (trim (codes ys))
        have hold (j : Fin (k + 3)) : oldArgs[j.val]?.getD .zero = convert (k + 3) (code (xs.idx j)) :=
          converted_coordinate xs j
        have hnew (j : Fin (k + 3)) : newArgs[j.val]?.getD .zero = convert (k + 3) (code (ys.idx j)) :=
          converted_coordinate ys j
        have hnewa : newArgs[i.val]?.getD .zero = .zero := by
          rw [hnew i]; simp only [ys, vec_rplc_idx, ↓reduceIte, code, convert]
        have hzeroOld : ∀ j, j < i.val → oldArgs[j]?.getD .zero = .zero := by
          intro j hj; rw [hold ⟨j, by omega⟩, hlow ⟨j, by omega⟩ hj, code, convert]
        have hzeroNew : ∀ j, j < i.val → newArgs[j]?.getD .zero = .zero := by
          intro j hj
          rw [hnew ⟨j, by omega⟩]
          simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
          rw [hlow ⟨j, by omega⟩ hj, code, convert]
        have hsame : ∀ j, i.val < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
          intro j hj hjk
          rw [hnew ⟨j, hjk⟩, hold ⟨j, hjk⟩]
          simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
        have heOld : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
            (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
          rw [convert_principal, principal_as_layers]
        have heNew : convert (k + 3) (code (new.T.fund (.P xs .Z) .Z)) = lower (k + 1) newArgs
            (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
          rw [hf, heZero, convert_principal, principal_as_layers]
          rw [hsame (k + 2) (by omega) (by omega)]
        by_cases hi : i.val = k + 1
        · have hcOld : oldArgs[k + 1]?.getD .zero = convert (k + 3) (code (xs.idx i)) := by rw [← hi, hold i]
          have hcNew : newArgs[k + 1]?.getD .zero = .zero := by rw [← hi, hnewa]
          have hcTop : topPair (k + 1) (oldArgs[k + 2]?.getD .zero)
              (convert (k + 3) (code (xs.idx i))) ≠ .zero := by simp [topPair, hcNZ]
          rw [heNew, hcNew, H_lower_zeros_above_Omega v hOmega _ _ _
            (by simpa only [hi] using hzeroNew)] at hz
          have hwOld := hs.wf
          rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ hcTop
            (by simpa only [hi] using hzeroOld)] at hwOld
          have hHigh := hcoords ⟨k + 2, by omega⟩
          have hh : Term.wf (oldArgs[k + 2]?.getD .zero) = true := by rw [hold ⟨k + 2, by omega⟩]; exact hHigh.wf
          have hI : Term.wf (.inacc (k + 1) (dropOne (oldArgs[k + 2]?.getD .zero))) = true := by
            rw [hold ⟨k + 2, by omega⟩]; exact inacc_image_drop_wf k _ hHigh
          have ho := H_topPair_zero_support v hvR hv (k + 1) _ _ hh (hcoords i).wf hcNZ hI hwOld hz
          apply Or.inr; apply Or.inl
          rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ hcTop (by simpa only [hi] using hzeroOld)]
          exact ho
        · rw [hsame (k + 1) (by omega) (by omega)] at heNew
          obtain ⟨b, hb, heO, heN⟩ := lower_selected_step_context (k + 1) i.val (by omega)
            oldArgs newArgs _ _ .zero hcNZ (topPair_context _ _ _) (hold i) hnewa hzeroOld hzeroNew
            (fun j hj hjk => hsame j hj (by omega))
          rw [heNew, heN, H_lower_zeros_above_Omega v hOmega _ _ _ hzeroNew] at hz
          have hw := hs.wf
          rw [heOld, heO] at hw
          have ho : z ∈ Term.H v (step i.val b (convert (k + 3) (code (xs.idx i)))) := by
            by_cases hb0 : b = .zero
            · by_cases hi0 : i.val = 0
              · simp only [step, hb0, hi0, ↓reduceIte] at hz
                change z ∈ Term.H v Term.one at hz
                rw [H_one_empty_above_Omega v hOmega] at hz
                cases hz
              · simp [step, hb0, hi0, Term.H] at hz
            · have hzB : z ∈ Term.H v b := by simpa only [step, hb0, ↓reduceIte] using hz
              exact H_step_context_of_wf v hvR hv i.val b _ hb hw hzB
          exact Or.inr (Or.inl ((heOld.trans heO) ▸ ho))
    · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      let c := xs.idx i
      have he : xs = lastVec (k + 2) c := by
        apply vec_ext
        intro j
        rw [lastVec_idx]
        by_cases hj : j.val = k + 2
        · rw [ite_eq_left hj]; have hji : j = i := Fin.ext (by rw [hi]; simpa using hj); rw [hji]
        · rw [ite_eq_right hj]; exact hlow j (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
      have heOld : (.P xs .Z : new.T (k + 3)) = topNode k c := congrArg (fun us => new.T.P us .Z) he
      have heNew : new.T.fund (.P xs .Z) .Z = topNode k (new.T.fund c .Z) := by
        rw [hf]
        have hrplc : xs.rplc i (new.T.fund c .Z) = lastVec (k + 2) (new.T.fund c .Z) := by
          have heR := congrArg (fun us => us.rplc i (new.T.fund c .Z)) he
          rw [hi, Support.SourceOmegaHighest.lastVec_replace_last] at heR
          simpa only [hi] using heR
        exact congrArg (fun us => new.T.P us .Z) hrplc
      have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) = Term.H v (convert (k + 3) (code c)) := by
        rw [heOld, H_topNode_above_Omega k c hc0 v hOmega, hdrop]
      by_cases hzC : new.T.fund c .Z = .Z
      · have hVec : lastVec (k + 2) (.Z : new.T (k + 3)) = lowVec (k + 2) .Z := by
          apply vec_ext; intro j; simp [lastVec_idx, lowVec_idx]
        rw [heNew, hzC, topNode, hVec, H_low_empty_above_Omega v hOmega] at hz
        cases hz
      · rw [heNew, H_topNode_above_Omega k _ hzC v hOmega] at hz
        exact lift (fun z hz => heH ▸ hz) (hcoef z (Support.OT2.mem_H_dropOne hz))

theorem regular_zero_updated_support [LargeCardinals.{u}] (k m : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (hml : m + 1 < k + 3)
    (hm : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one))
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) .Z))) →
      UpdatedCoefficient k v (.P xs .Z) .Z z := by
  have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
  have hcoords : ∀ i, RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1
  let p := new.T.fund (xs.idx ⟨m + 1, hml⟩) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hcoords _) hd
  have hsucc : convert (k + 3) (code (xs.idx ⟨m + 1, hml⟩)) =
      succTerm (convert (k + 3) (code p)) := by
    obtain ⟨a, he⟩ := dom_one_succ (xs.idx ⟨m + 1, hml⟩) hd
    simp only [p, he, Support.SourceSuccessor.fund_succ, convert_succ]
  let ys := xs.rplc ⟨m + 1, hml⟩ p
  have hf : new.T.fund (.P xs .Z) .Z = .P ys .Z := by
    rw [fund_regular_bound xs hml hm .Z]
    congr 1
    apply vec_ext; intro j
    simp only [ys, p, vec_rplc_idx]
    by_cases hj : j.val = m
    · rw [ite_eq_left hj, ite_eq_right (by omega)]
      exact (hlow j (by change j.val < m + 1; omega)).symm
    · rw [ite_eq_right hj]
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have oldGet (j : Fin (k + 3)) : oldArgs[j.val]?.getD .zero = convert (k + 3) (code (xs.idx j)) :=
    converted_coordinate xs j
  have newGet (j : Fin (k + 3)) : newArgs[j.val]?.getD .zero = convert (k + 3) (code (ys.idx j)) :=
    converted_coordinate ys j
  have hOld : oldArgs[m + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by
    rw [oldGet ⟨m + 1, hml⟩]; exact hsucc
  have hNew : newArgs[m + 1]?.getD .zero = convert (k + 3) (code p) := by
    rw [newGet ⟨m + 1, hml⟩]; simp [ys, vec_rplc_idx]
  have hzeroOld : ∀ j, j < m + 1 → oldArgs[j]?.getD .zero = .zero := by
    intro j hj; rw [oldGet ⟨j, by omega⟩, hlow ⟨j, by omega⟩ hj, code, convert]
  have hzeroNew : ∀ j, j < m + 1 → newArgs[j]?.getD .zero = .zero := by
    intro j hj; rw [newGet ⟨j, by omega⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ m + 1)]
    rw [hlow ⟨j, by omega⟩ hj, code, convert]
  have hsame : ∀ j, m + 1 < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj hjk; rw [newGet ⟨j, hjk⟩, oldGet ⟨j, hjk⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ m + 1)]
  have heOld : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have heNew : convert (k + 3) (code (new.T.fund (.P xs .Z) .Z)) = lower (k + 1) newArgs
      (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
    rw [hf, convert_principal, principal_as_layers]
  intro z hz
  have liftSupport (hh : z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
      (z = convert (k + 3) (code p) ∨ z = dropOne (convert (k + 3) (code p))) ∧
        (succTerm (convert (k + 3) (code p)) ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
          dropOne (succTerm (convert (k + 3) (code p))) ∈ Term.H v (convert (k + 3) (code (.P xs .Z))))) :
      UpdatedCoefficient k v (.P xs .Z) .Z z := by
    rcases hh with ho | ⟨he, ho⟩
    · exact Or.inr (Or.inl ho)
    · refine Or.inr (Or.inr ⟨xs.idx ⟨m + 1, hml⟩, Subterm.coordinate xs .Z _, hp, ?_, he⟩)
      rw [hsucc]; exact ho
  rw [heNew] at hz
  by_cases hi : m + 1 = k + 2
  · rw [hzeroNew (k + 1) (by omega), H_lower_zeros_above_Omega v hOmega _ _ _
      (fun j hj => hzeroNew j (by omega))] at hz
    have hcOld : oldArgs[k + 2]?.getD .zero = succTerm (convert (k + 3) (code p)) := by rw [← hi, hOld]
    have hcNew : newArgs[k + 2]?.getD .zero = convert (k + 3) (code p) := by rw [← hi, hNew]
    rw [hcNew] at hz
    have heOldTop : convert (k + 3) (code (.P xs .Z)) = topPair (k + 1)
        (succTerm (convert (k + 3) (code p))) .zero := by
      rw [heOld, hcOld, hzeroOld (k + 1) (by omega)]
      exact lower_keep _ _ _ (by simp [topPair, succTerm_ne_zero]) (fun j hj => hzeroOld j (by omega))
    by_cases hp0 : convert (k + 3) (code p) = .zero
    · simp [hp0, topPair, Term.H] at hz
    · apply Or.inr; apply Or.inl; rw [heOldTop]
      simp only [topPair, ↓reduceIte, succTerm_ne_zero, drop_succ _ hp0]
      simp only [topPair, hp0, ↓reduceIte] at hz
      exact H_inacc_succ_support v (k + 1) _ hz
  · by_cases him : m + 1 = k + 1
    · rw [hsame (k + 2) (by omega) (by omega)] at hz
      have hNewMid : newArgs[k + 1]?.getD .zero = convert (k + 3) (code p) := by rw [← him, hNew]
      have hOldMid : oldArgs[k + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by rw [← him, hOld]
      rw [hNewMid, H_lower_zeros_above_Omega v hOmega _ _ _ (fun j hj => hzeroNew j (by omega))] at hz
      have heOldTop : convert (k + 3) (code (.P xs .Z)) = topPair (k + 1)
          (oldArgs[k + 2]?.getD .zero) (succTerm (convert (k + 3) (code p))) := by
        rw [heOld, hOldMid]
        exact lower_keep _ _ _ (by simp [topPair, succTerm_ne_zero]) (fun j hj => hzeroOld j (by omega))
      have hh : Term.wf (oldArgs[k + 2]?.getD .zero) = true := by rw [oldGet ⟨k + 2, by omega⟩]; exact (hcoords _).wf
      have hI : Term.wf (.inacc (k + 1) (dropOne (oldArgs[k + 2]?.getD .zero))) = true := by
        rw [oldGet ⟨k + 2, by omega⟩]; exact inacc_image_drop_wf k _ (hcoords _)
      rcases H_topPair_predecessor_support v hvR hv (k + 1) _ _ hh hp.wf hI (heOldTop ▸ hs.wf) hz
        with ho | ⟨he, ho⟩
      · exact liftSupport (Or.inl (heOldTop ▸ ho))
      · exact liftSupport (Or.inr ⟨Or.inr he, Or.inr (heOldTop ▸ ho)⟩)
    · rw [hsame (k + 2) (by omega) (by omega), hsame (k + 1) (by omega) (by omega)] at hz
      obtain ⟨b, hb, heO, heN⟩ := lower_selected_step_context (k + 1) (m + 1) (by omega)
        oldArgs newArgs _ _ _ (succTerm_ne_zero _) (topPair_context _ _ _) hOld hNew
        hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega))
      rw [heN, H_lower_zeros_above_Omega v hOmega _ _ _ hzeroNew] at hz
      have hw := hs.wf
      rw [heOld, heO] at hw
      have ho := step_successor_relative_support v hvR hv (m + 1) b _ hb hp.wf hw hz
      rw [← heO, ← heOld] at ho
      exact liftSupport ho

theorem zero_relative_allcuts [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (new.T.fund s .Z))
    (hcoef : ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
      ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s .Z))) → UpdatedCoefficient k v s .Z z)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s .Z))))
      (convert (k + 3) (code (new.T.fund s .Z))) = true := by
  rcases lemma_6_1.{u}.2.2 Term.bigOmega v Term.wf_bigOmega hv with hOmega | he | hOmega
  · by_cases hh : Term.head (convert (k + 3) (code s)) = Term.one
    · obtain ⟨n, he⟩ := head_one_nat hs.wf hh
      have hsNat : s = new.T.ofNat (n + 1) := convert_injective k s _ hs
        (numeral_recursiveWF _ _ _) (he.trans (convert_numeral _ _ _).symm)
      rw [hsNat, ← Support.SourceSuccessor.nat_succ, Support.SourceSuccessor.fund_succ, convert_numeral]
      exact H_nat_bound v n
    · by_cases hsZ : convert (k + 3) (code s) = .zero
      · have heS : s = .Z := code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp hsZ)
        rw [heS, new.T.fund, code, convert, Term.H]; rfl
      · exact zero_relative_of_updated_support k s hs hn v hh hsZ (hcoef v hvR hv hOmega) hH
  · subst v
    exact H_convert_bound_of_subterms k Term.bigOmega _ hn
      (Support.SourceSubtermBounds.fund_zero_subterms s ((H_omega_bound_iff_subterms k s hs hr).mp hH))
  · rw [Support.CountableTarget.regular_not_below_omega hvR] at hOmega
    cases hOmega

theorem zero_fund_invariant [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) :
    RecursiveWF (k + 3) (new.T.fund s .Z) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s .Z))) → UpdatedCoefficient k v s .Z z) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s .Z))))
          (convert (k + 3) (code (new.T.fund s .Z))) = true) := by
  have finish (hn : RecursiveWF (k + 3) (new.T.fund s .Z))
      (hc : ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s .Z))) → UpdatedCoefficient k v s .Z z) :=
    And.intro hn (And.intro hc (zero_relative_allcuts k s hr hs hn hc))
  have empty (hf : new.T.fund s .Z = .Z) := by
    apply finish
    · rw [hf]; exact recursive_zero _ _
    · intro v _ _ _ z hz
      rw [hf, code, convert, Term.H] at hz; cases hz
  cases heS : s with
  | Z => rw [heS] at empty; exact empty (by rw [new.T.fund])
  | P xs b =>
    rw [heS] at hr hs finish empty
    by_cases hb : b = .Z
    · subst b
      cases hm : new.T.domVecMinIdx xs with
      | none => apply empty; simp [new.T.fund, hm]
      | some p =>
        obtain ⟨i, d⟩ := p
        have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
        have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
        have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
        cases d with
        | zero => exact False.elim ((Support.DimensionCut.minIdx_spec xs hm).2.1 rfl)
        | one =>
          obtain ⟨n, hin⟩ := i
          cases n with
          | zero =>
            apply empty
            simp only [new.T.fund, ↓reduceIte, hm]
            change new.T.mul (.P (xs.rplc ⟨0, hin⟩ (new.T.fund (xs.idx ⟨0, hin⟩) .Z)) .Z) .Z = .Z
            rw [new.T.mul]
          | succ m =>
            apply finish (fund_regular_recursiveWF k m xs hin hm .Z hs (recursive_zero _ _)
              (by simp only [code, convert, Term.H, Term.allLt, List.all_nil]))
            exact regular_zero_updated_support k m xs hin hm hs
        | omega | Omega ys =>
          obtain ⟨hnChild, hcChild, hrelChild⟩ := zero_fund_invariant k (xs.idx i) hchildR (hcoords i)
          have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
          have hdrop : dropOne (convert (k + 3) (code (xs.idx i))) = convert (k + 3) (code (xs.idx i)) := by
            first | exact drop_image_of_omega k _ (hcoords i) hd | exact Omega_image_drop k _ hchildR (hcoords i) hd
          have hf : new.T.fund (.P xs .Z) .Z = .P (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z := by
            simp only [new.T.fund, ↓reduceIte, hm, GetElem.getElem]
            all_goals split <;> simp only [new.T.iter]
          have hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) .Z) := by
            rw [hf]
            by_cases hib : i.val ≤ k + 1
            · exact principal_replace_relative_recursiveWF k xs i hib hlow hs _ hnChild hc0 hdrop hrelChild
            · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
              have he : xs = lastVec (k + 2) (xs.idx i) := by
                apply vec_ext; intro j; rw [lastVec_idx]
                by_cases hj : j.val = k + 2
                · rw [ite_eq_left hj]
                  have hji : j = i := Fin.ext (by rw [hi]; simpa using hj)
                  rw [hji]
                · rw [ite_eq_right hj]; exact hlow j (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
              have heR := congrArg (fun us => us.rplc i (new.T.fund (xs.idx i) .Z)) he
              rw [hi, Support.SourceOmegaHighest.lastVec_replace_last] at heR
              have heR' : xs.rplc i (new.T.fund (xs.idx i) .Z) = lastVec (k + 2) (new.T.fund (xs.idx i) .Z) := by
                simpa only [hi] using heR
              rw [heR']; exact topNode_recursiveWF k _ hnChild
          apply finish hn
          intro v hvR hv hOmega
          exact parent_zero_updated_support k xs i hlow hs hc0 hdrop hf hn v hvR hv hOmega (hcChild v hvR hv hOmega)
    · have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      obtain ⟨hnB, hcB, _⟩ := zero_fund_invariant k b hbr hbw
      apply finish (fund_nonzero_tail_recursiveWF k xs b .Z hs hb hnB)
      intro v hvR hv hOmega z hz
      rw [new.T.fund, ite_eq_right hb, code, convert] at hz
      rcases H_assemble_support v _ _ hz with hz | hz
      · exact Or.inr (Or.inl (by simp only [code, convert]; exact H_assemble_left v _ _ hz))
      · rcases hcB v hvR hv hOmega z hz with he | ho | ⟨a, ha, hw, ho, he⟩
        · exact Or.inl he
        · apply Or.inr; apply Or.inl; simp only [code, convert]; exact H_assemble_right v _ _ ho
        · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
          simp only [code, convert]
          exact ho.elim (fun h => Or.inl (H_assemble_right v _ _ h)) (fun h => Or.inr (H_assemble_right v _ _ h))
termination_by new.T.size s
decreasing_by
  all_goals rw [heS]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

end Support.GeneralImageZeroFund

namespace Support.GeneralImageCountableInheritance

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageCountableLayers Support.GeneralImageRelativePredecessor
open Support.GeneralImageCountableRecursion Support.GeneralImageOmegaCoefficients
open Support.GeneralImageMiddleCofinality Support.GeneralImageMiddleSums Support.GeneralImageUpperOmega
open Support.GeneralImageCofinalityBounds Support.GeneralImageCofinalityInheritance
open Support.GeneralImageSharedTopPair Support.GeneralImageSharedContext
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRegularCofinality
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageOmegaCofinality
open Support.GeneralImageZeroFund
open Support.GeneralImageOmegaContext

universe u

theorem omega_image_head_ne_one [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (hd : new.T.dom s = .omega) :
    Term.head (convert (k + 3) (code s)) ≠ Term.one := by
  intro hh
  obtain ⟨n, he⟩ := head_one_nat hs.wf hh
  have heS : s = new.T.ofNat (n + 1) := convert_injective k s _ hs
    (numeral_recursiveWF _ _ _) (he.trans (convert_numeral _ _ _).symm)
  rw [heS, ← Support.SourceSuccessor.nat_succ, Support.SourceSuccessor.dom_succ] at hd
  cases hd

theorem omega_fund_nat_ne_zero (k : Nat) (s : new.T (k + 3))
    (hd : new.T.dom s = .omega) (n : Nat) (hn : 0 < n) :
    new.T.fund s (new.T.ofNat n) ≠ .Z := by
  intro he
  have hl := Support.SourceCountableInvariant.ofNat_le_countable_fund s hd n
  rw [he] at hl
  have hz : new.T.ofNat (lam := k + 3) n ≠ .Z := by cases n with
    | zero => omega
    | succ n => intro he; cases he
  rcases hl with hl | hl
  · cases hc : new.T.ofNat (lam := k + 3) n with
    | Z => exact hz hc
    | P xs b => simp [hc, compareT] at hl
  · exact hz (T_eq_sound _ _ hl)

theorem positive_principal_subterm_gap {lam : Nat} (xs : Vec (new.T lam) lam)
    (i j : Fin lam) (hij : i ≠ j) (hi : xs.idx i ≠ .Z) (hj : xs.idx j ≠ .Z)
    (t : new.T lam) (ht : t ≠ .Z) {a : new.T lam} (ha : Subterm a (.P xs .Z)) :
    mass a < gap (.P xs .Z) t := by
  have hcoords : ∀ l, mass (xs.idx l) < vectorMass xs := by
    intro l
    by_cases hl : l = i
    · subst l
      have hp := vectorMass_pair_le xs i j hij
      have hz := mass_positive hj; omega
    · have hp := vectorMass_pair_le xs l i hl
      have hz := mass_positive hi; omega
  have hgap : gap (.P xs .Z) t = vectorMass xs := by simp [gap, ht, mass]
  rw [hgap]
  have hgen : ∀ {a s : new.T lam}, Subterm a s → s = .P xs .Z → mass a < vectorMass xs := by
    intro a s ha
    induction ha with
    | coordinate ys b l => intro he; cases he; exact hcoords l
    | tail ys b =>
      intro he; cases he
      have hp := mass_positive hi; have hv := vectorMass_idx_le xs i
      simp only [mass]; omega
    | trans hab hbs iha ihb =>
      intro he
      exact Nat.lt_trans (Support.SourceCoefficientGap.mass_lt_of_subterm hab) (ihb he)
  exact hgen ha rfl

theorem omega_relative_allcuts [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (hd : new.T.dom s = .omega)
    (n : Nat) (hn : RecursiveWF (k + 3) (new.T.fund s (new.T.ofNat n)))
    (hAbove : ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
      Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
      Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))))
        (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))) = true)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))))
      (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))) = true := by
  rcases lemma_6_1.{u}.2.2 Term.bigOmega v Term.wf_bigOmega hv with hlt | he | hlt
  · exact hAbove v hvR hv hlt hH
  · subst v
    exact H_convert_bound_of_subterms k Term.bigOmega _ hn
      (Support.SourceCountableInvariant.fund_omega_subterms (k + 2) s hr hd
        ((H_omega_bound_iff_subterms k s hs hr).mp hH) n)
  · rw [Support.CountableTarget.regular_not_below_omega hvR] at hlt; cases hlt

theorem positive_sum_subterm_gap {lam : Nat} (xs : Vec (new.T lam) lam) (b t : new.T lam)
    (hb : b ≠ .Z) (hx : 0 < vectorMass xs) (ht : t ≠ .Z)
    {a : new.T lam} (ha : Subterm a (.P xs b)) : mass a < gap (.P xs b) t := by
  have hbp := mass_positive hb
  have hgap : gap (.P xs b) t = vectorMass xs + mass b := by
    simp only [gap, ite_eq_right ht, mass]; omega
  rw [hgap]
  have hgen : ∀ {a s : new.T lam}, Subterm a s → s = .P xs b → mass a < vectorMass xs + mass b := by
    intro a s ha
    induction ha with
    | coordinate ys c i =>
      intro he; cases he
      have hi := vectorMass_idx_le xs i; omega
    | tail ys c => intro he; cases he; omega
    | trans hab hbs iha ihb =>
      intro he
      exact Nat.lt_trans (Support.SourceCoefficientGap.mass_lt_of_subterm hab) (ihb he)
  exact hgen ha rfl

end Support.GeneralImageCountableInheritance

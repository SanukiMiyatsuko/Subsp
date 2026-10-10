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
  rw [gap_Omega _ _ _ hd]; exact kumakuma.SourceCoefficientGap.principal_subterm_mass hij hi hj ha

theorem H_inacc_succ_support (v : Term) (n : Nat) (a : Term) {z : Term}
    (hz : z ∈ Term.H v (.inacc n a)) : z ∈ Term.H v (.inacc n (succTerm a)) := by
  rw [Term.H] at hz ⊢
  rcases List.mem_append.mp hz with hz | hz
  · exact List.mem_append_left _ hz
  · apply List.mem_append_right
    rw [kumakuma.OT2.H_succTerm]
    exact List.mem_append_left _ hz

theorem topPair_predecessor_lt (n : Nat) (h b : Term)
    (hh : Term.wf h = true) (hb : Term.wf b = true) :
    Term.lt (topPair n h b) (topPair n h (succTerm b)) = true := by
  rw [topPair_order n hh hb hh (succTerm_wf hb)]
  simp only [lt_self, decide_true, Bool.true_and, Bool.false_or]
  rw [lt_succTerm_eq_le hb hb]
  simp [Term.le]

theorem H_topPair_predecessor_support (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (n : Nat) (h b : Term)
    (hh : Term.wf h = true) (hb : Term.wf b = true)
    (hi : Term.wf (.inacc n (dropOne h)) = true)
    (hw : Term.wf (topPair n h (succTerm b)) = true) {z : Term}
    (hz : z ∈ Term.H v (topPair n h b)) :
    z ∈ Term.H v (topPair n h (succTerm b)) ∨
      z = dropOne b ∧ dropOne (succTerm b) ∈ Term.H v (topPair n h (succTerm b)) := by
  have hn := topPair_successor_predecessor n h b hi hb hw
  have hl := topPair_predecessor_lt n h b hh hb
  have hp := (kumakuma.JaegerFacts.predR_facts hv hvR)
  have heOld : topPair n h (succTerm b) = .psi (pairCut n h) (dropOne (succTerm b)) := by
    by_cases hh0 : h = .zero <;> simp only [topPair, hh0, succTerm_ne_zero, ↓reduceIte, pairCut]
  by_cases hs : Term.le (topPair n h (succTerm b)) (Term.predR v) = true
  · have he := Term.le_trans hn hw hp.1 (by simp [Term.le, hl]) hs
    rw [kumakuma.JaegerFacts.H_nil_of_le_predR hv hvR _ hn he] at hz; cases hz
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

theorem undrop_lt_head_ne_one (a s : Term) (ha : Term.wf a = true) (hs : Term.wf s = true)
    (hz : s ≠ .zero) (hh : Term.head s ≠ Term.one)
    (hl : Term.lt (dropOne a) s = true) : Term.lt a s = true := by
  by_cases hhead : Term.head a = Term.one
  · obtain ⟨n, he⟩ := head_one_nat ha hhead
    rw [he]; exact nat_lt_of_head_ne hs hz hh (n + 1)
  · rwa [dropOne_of_head_ne hhead] at hl

theorem exists_nonzero_of_mass {xs : V multi.T} (hm : 0 < vectorMass xs) :
    ∃ i, V.get0 xs i ≠ .Z := by
  rcases kumakuma.Decide.exists_ne_or_all xs with h | hz
  · exact h
  · rw [vectorMass_eq_zero xs hz] at hm
    exact absurd hm (Nat.lt_irrefl 0)

theorem Omega_image_head_ne_one (k : Nat) (s : multi.T)
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
  rw [gap_Omega _ _ _ hd]; exact kumakuma.SourceCoefficientGap.sum_subterm_mass hb hx ha

/-- An updated coefficient of a subterm `c` of `s` lies below the image of `s[t]`. -/
theorem updated_lt_fund (k : Nat) (v : Term) {s c t : multi.T} (hsD : Dim (k + 3) s)
    (hcD : Dim (k + 3) c) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    (hc : RecursiveWF (k + 3) c) (hn : RecursiveWF (k + 3) (T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hnewZero : convert (k + 3) (code (T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a c → mass a < gap s t)
    (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code c)) →
      z ∈ Term.H v (convert (k + 3) (code s)))
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true)
    {z : Term} (hz : UpdatedCoefficient k v c t z) :
    Term.lt z (convert (k + 3) (code (T.fund s t))) = true := by
  have hzlt := (zero_lt_iff _).mpr hnewZero
  have hnD := Dim_fund s t hsD htD
  have old (a : multi.T) (ha : Subterm a c)
      (hm : convert (k + 3) (code a) ∈ Term.H v (convert (k + 3) (code c)) ∨
        dropOne (convert (k + 3) (code a)) ∈ Term.H v (convert (k + 3) (code c))) :
      a < T.fund s t := by
    have hw := ha.recursiveWF hc
    refine small_lt_fund_all s t a ((convert_order k _ _ (ha.dim hcD) hsD hw hs).mpr ?_) (hgap a ha)
    rcases hm with hm | hm
    · exact (Term.allLt_iff _ _).mp hH _ (embed _ hm)
    · exact undrop_lt_head_ne_one _ _ hw.wf hs.wf hzero hhead
        ((Term.allLt_iff _ _).mp hH _ (embed _ hm))
  have fin (b : multi.T) (hbD : Dim (k + 3) b) (hbW : RecursiveWF (k + 3) b) (hb : b < T.fund s t)
      (he : z = convert (k + 3) (code b) ∨ z = dropOne (convert (k + 3) (code b))) :
      Term.lt z (convert (k + 3) (code (T.fund s t))) = true := by
    have hl := (convert_order k _ _ hbD hnD hbW hn).mp hb
    rcases he with rfl | rfl
    · exact hl
    · exact dropOne_lt_of_lt hbW.wf hn.wf hl
  rcases hz with rfl | ho | ⟨a, ha, hw, hm, he⟩
  · exact hzlt
  · rcases H_convert_source k v c ho with rfl | ⟨a, ha, he⟩
    · exact hzlt
    · exact fin a (ha.dim hcD) (ha.recursiveWF hc) (old a ha (he.elim (fun e => Or.inl (e ▸ ho)) (fun e => Or.inr (e ▸ ho)))) he
  · by_cases ha0 : a = .Z
    · subst a
      rw [fund_Z, convert_Z] at he
      rcases he with rfl | rfl <;> exact hzlt
    · exact fin _ (Dim_fund a t (ha.dim hcD) htD) hw (T.lt_trans (fund_lt a t ha0) (old a ha hm)) he

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
      (convert (k + 3) (code (T.fund s t))) = true :=
  (Term.allLt_iff _ _).mpr fun z hz => (hcoef z hz).elim
    (updated_lt_fund k v hsD hsD htD hs hs hn hhead hzero hnewZero hgap (fun _ h => h) hH) (hBound z)

theorem closed_of_updated_coefficients (k : Nat) (v : Term)
    (s t : multi.T) (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (T.fund s t))
    (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hzero : convert (k + 3) (code s) ≠ .zero)
    (hnewZero : convert (k + 3) (code (T.fund s t)) ≠ .zero)
    (hgap : ∀ a, Subterm a s → mass a < gap s t)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) →
      UpdatedCoefficient k v s t z) :
    Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
      (convert (k + 3) (code (T.fund s t))) = true :=
  closed_of_updated_or_bounded k v s t hsD htD hs hn hhead hzero hnewZero hgap (fun _ => False)
    (fun _ h => h.elim) (fun z hz => .inl (hcoef z hz))

theorem Omega_image_drop (k : Nat) (s : multi.T)
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

theorem H_topNode_above_Omega (k : Nat) (a : multi.T) (ha : a ≠ .Z)
    (v : Term) (hv : Term.lt Term.bigOmega v = true) :
    Term.H v (convert (k + 3) (code (topNode k a))) =
      Term.H v (dropOne (convert (k + 3) (code a))) := by
  rw [convert_topNode k a ha, Term.H]
  simp only [show k + 1 ≠ 0 from by omega, ↓reduceIte, Term.hOne, hv, ite_self, List.nil_append]

theorem H_topNode_Omega (k : Nat) (a : multi.T) (haD : Dim (k + 3) a)
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
  have hf : T.fund (topNode k a) t = topNode k (T.fund a t) :=
    highest_Omega_fund (k + 2) a t haD hr hd
  refine (Term.allLt_iff _ _).mpr fun z hz => ?_
  rw [hf, H_topNode_above_Omega k _ hzn v hv] at hz
  refine (hcoef z (kumakuma.OT2.mem_H_dropOne hz)).elim (updated_lt_fund k v (Dim_topNode haD) haD
    htD hs ha (hf ▸ topNode_recursiveWF k _ hnChild) ?_ ?_ ?_
    (fun b hb => topNode_child_subterm_gap k a t haD hr hd hb)
    (fun z h => (H_topNode_Omega k a haD hr ha hd v hv).symm ▸ h) hH) (hBound z)
  · rw [convert_topNode k a hza]; simp only [Term.head, Term.one]; intro he; cases he
  · rw [convert_topNode k a hza]; intro he; cases he
  · rw [hf, convert_topNode k _ hzn]; intro he; cases he

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

theorem cofinality_image_le (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
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

theorem step_predecessor_cut_lt (n : Nat) (a c : Term)
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

theorem step_successor_relative_support (v : Term)
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

theorem lower_regular_cofinal_support (v : Term)
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
        Term.lt_trans hcutW hOldW hv (step_predecessor_cut_lt m a c (context_above hctx) hc hOldW) hOldLt
      rw [lower_succ, hy, lower_succ, hyt,
        H_lower_zeros_above_Omega v hOmega m ys _ hzeroNew] at hz
      have hpreMem := H_step_of_layerCut_lt v hOmega m pre t hcutLt hz
      rw [heOld]
      exact step_successor_relative_support v hvR hv (m + 1) a c (context_above hctx) hc hOldW hpreMem

theorem topPair_predecessor_cut_lt (k : Nat) (h c : Term)
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

theorem H_fund_regular_cofinal_support (k m : Nat)
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
      have hCutLt : Term.lt (layerCut k pre) v = true := Term.lt_trans hwCut hwOld hv
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

theorem H_fund_regular_single_small (k m : Nat)
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
      Term.lt_trans hCutW hOldW hv
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

theorem updated_coefficient_lt_old (k : Nat) (v : Term)
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

theorem fund_regular_cofinal_relative_of_wf (k m : Nat)
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

theorem fund_regular_cofinal_relative_all_of_wf (k m : Nat)
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
  have hi : V.get0 xs (m + 1) ≠ .Z := (V.fnz_some_spec xs _ hf).1
  by_cases hex : ∃ j, m + 1 ≠ j ∧ V.get0 xs j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact fund_regular_cofinal_relative_of_wf k m xs hsD hf hdom (m + 1) j hij hi hj hr hs t htD hn
  · have hother : ∀ j, j ≠ m + 1 → V.get0 xs j = .Z := by
      intro j hj
      apply Decidable.byContradiction
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

end kumakuma.GeneralImageRegularCofinality

namespace kumakuma.GeneralImageCofinalityInheritance

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageCountableRecursion kumakuma.GeneralImageHeadCuts
open kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion
open kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageCofinalityBounds
open kumakuma.GeneralImageRegularCofinality kumakuma.GeneralImageHighOmega
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant

theorem le_psi_index_bound (n : Nat) (a b l : Term)
    (hl : Term.wf l = true) (hw : Term.wf (.psi (.inacc n a) b) = true)
    (hle : Term.le l (.psi (.inacc n a) b) = true) :
    Term.lt l (.inacc n a) = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  have hroot : Term.lt (.psi (.inacc n a) b) (.inacc n a) = true := by simp [Term.lt, Term.fT]
  rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | he
  · rw [he]; exact hroot
  · exact Term.lt_trans hl hw hp.2.1 he hroot

theorem step_psi_of_drop (n : Nat) (a c : Term)
    (hc : c ≠ .zero) (hd : dropOne c = c) :
    step n a c = .psi (layerCut n a) c := by
  by_cases ha : a = .zero
  · by_cases hn : n = 0 <;> simp [step, layerCut, ha, hn, hc, hd, Term.bigOmega]
  · simp [step, layerCut, regular, ha, hc, hd]


theorem Omega_principal_image_ne_low (k : Nat)
    (xs : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    {q : V multi.T} (hd : domF (.P xs .Z) = .Omega q) :
    convert (k + 3) (code (.P xs .Z)) ≠ .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i))) := by
  intro he
  have harg : RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1 i
  have hw := he ▸ hs.wf
  have hlow : RecursiveWF (k + 3) (.P (lowVec (k + 2) (V.get0 xs i)) .Z) :=
    (low_principal_recursiveWF_iff _ _ _).mpr ⟨harg, ((Term.wf_psi_iff _ _).mp hw).2.2.2⟩
  have hlowD : Dim (k + 3) (.P (lowVec (k + 2) (V.get0 xs i)) .Z) :=
    Dim_lowVec (hsD.coord i) (Dim_Z _)
  have hsource := convert_injective k _ _ hsD hlowD hs hlow (by rw [convert_low_principal]; exact he)
  have ho : Outer (k + 2) (.P (lowVec (k + 2) (V.get0 xs i)) .Z) := .cons _ _ .zero
  rw [hsource] at hd
  exact SourceFundOrder.outer_not_Omega ho q hd

theorem step_replace_cofinal_wf (n : Nat)
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

theorem topPair_replace_cofinal_wf (n : Nat) (hn : 0 < n)
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

theorem lower_replace_cofinal_wf (j cut : Nat)
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


theorem principal_replace_cofinal_recursiveWF (k : Nat)
    (xs : V multi.T) (i : Nat) (hib : i ≤ k + 1) (hsD : Dim (k + 3) (.P xs .Z))
    (hlow : ∀ j, j < i → V.get0 xs j = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (a : multi.T)
    (ha : RecursiveWF (k + 3) a) (hc0 : V.get0 xs i ≠ .Z)
    (hdrop : dropOne (convert (k + 3) (code (V.get0 xs i))) = convert (k + 3) (code (V.get0 xs i)))
    (l : Term) (hl : Term.wf l = true)
    (hle : Term.le l (convert (k + 3) (code (.P xs .Z))) = true)
    (hnotLow : convert (k + 3) (code (.P xs .Z)) ≠
      .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i))))
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.lt Term.bigOmega v = true → Term.lt l v = true →
      Term.allLt (Term.H v (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true →
      Term.allLt (Term.H v (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    RecursiveWF (k + 3) (.P (V.set xs i a) .Z) := by
  have hil : i < xs.length := by rw [hsD.length]; omega
  let ys := V.set xs i a
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have hold (j : Nat) : oldArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xs j)) :=
    converted_coordinate xs j
  have hnew (j : Nat) : newArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 ys j)) :=
    converted_coordinate ys j
  have hnewa : newArgs[i]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew i]; show convert (k + 3) (code (V.get0 (V.set xs i a) i)) = _
    rw [V.get0_set_same xs i a hil]
  have hzeroOld : ∀ j, j < i → oldArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hold j, hlow j hj, convert_Z]
  have hzeroNew : ∀ j, j < i → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew j]
    show convert (k + 3) (code (V.get0 (V.set xs i a) j)) = _
    rw [V.get0_set_ne xs i a j (by omega), hlow j hj, convert_Z]
  have hsame : ∀ j, i < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj _
    rw [hnew j, hold j]
    show convert (k + 3) (code (V.get0 (V.set xs i a) j)) = _
    rw [V.get0_set_ne xs i a j (by omega)]
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hcNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  have hw := hs.wf
  have hbound := hle
  rw [convert_principal, principal_as_layers] at hw hbound hnotLow
  change Term.wf (lower (k + 1) oldArgs (topPair (k + 1)
    (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero))) = true at hw
  change Term.le l (lower (k + 1) oldArgs (topPair (k + 1)
    (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero))) = true at hbound
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
  · intro j
    show RecursiveWF (k + 3) (V.get0 (V.set xs i a) j)
    rw [V.get0_set xs i a j hil]
    split
    · exact ha
    · exact hcoords j
  · rw [convert_principal, principal_as_layers]
    change Term.wf (lower (k + 1) newArgs (topPair (k + 1)
      (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) = true
    rw [hsame (k + 2) (by omega) (by omega)]
    by_cases he : i = k + 1
    · subst he
      have htopNZ : topPair (k + 1) (oldArgs[k + 2]?.getD .zero)
          (oldArgs[k + 1]?.getD .zero) ≠ .zero := by
        rw [hold (k + 1)]
        simp only [topPair, hcNZ, ↓reduceIte]
        intro he0; cases he0
      rw [lower_keep (k + 1) oldArgs _ htopNZ hzeroOld] at hw hbound
      rw [hnewa]
      apply lower_zero_wf (k + 1) newArgs _ hzeroNew
      rw [hold (k + 1)] at hw hbound
      apply topPair_replace_cofinal_wf (k + 1) (by omega) _ _ _ l _ ha.wf hcNZ hdrop hl hbound hrel hw
      rw [hold (k + 2)]; exact inacc_image_drop_wf k _ (hcoords _)
    · rw [hsame (k + 1) (by omega) (by omega)]
      exact lower_replace_cofinal_wf (k + 1) i (by omega) oldArgs newArgs _ _ _ l
        (topPair_context _ _ _) ha.wf hcNZ hdrop hl hbound hnotLow hrel (hold i) hnewa
        hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega)) hw

end kumakuma.GeneralImageCofinalityInheritance

namespace kumakuma.GeneralImageCofinalityCoefficients

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageMiddleCofinality
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCofinalityInheritance kumakuma.GeneralImageUpperOmega
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceFundGap

theorem H_psi_replacement_support (v w c t : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hw : Term.wf (.psi w c) = true) (hn : Term.wf (.psi w (dropOne t)) = true)
    (hlt : Term.lt (.psi w (dropOne t)) (.psi w c) = true) {z : Term}
    (hz : z ∈ Term.H v (.psi w (dropOne t))) :
    (z ∈ Term.H v w ∧ z ∈ Term.H v (.psi w c)) ∨
      (z = dropOne t ∨ z ∈ Term.H v t) ∧ c ∈ Term.H v (.psi w c) ∧
        (∀ a, a ∈ Term.H v c → a ∈ Term.H v (.psi w c)) := by
  by_cases hskip : Term.le (.psi w c) (Term.predR v) = true
  · have hp := (kumakuma.JaegerFacts.predR_facts hv hvR)
    have hle := Term.le_trans hn hw hp.1 (by simp [Term.le, hlt]) hskip
    rw [kumakuma.JaegerFacts.H_nil_of_le_predR hv hvR _ hn hle] at hz
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
          · exact Or.inr ⟨Or.inr (kumakuma.OT2.mem_H_dropOne hz), hroot, hchild⟩
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
  | zero => omega_c
  | succ j ih =>
    by_cases hij : cut < j
    · rw [lower_succ, lower_succ, hsame j hij (by omega_c)]
      exact ih hij _ (fun i hi hik => hsame i hi (by omega_c))
    · have he : j = cut := by omega_c
      subst j
      refine ⟨a, ?_, ?_⟩
      · rw [lower_succ, hx]
        exact lower_keep cut xs _ (step_ne_zero_of_argument cut a c hc) hzeroOld
      · rw [lower_succ, hy]
        exact lower_keep cut ys _ (step_ne_zero_of_argument cut a t ht) hzeroNew


theorem principal_replacement_psi_images (k : Nat)
    (xs : V multi.T) (i : Nat) (hib : i ≤ k + 1)
    (hlow : ∀ j, j < i → V.get0 xs j = .Z) (a : multi.T)
    (hc : convert (k + 3) (code (V.get0 xs i)) ≠ .zero)
    (ha : convert (k + 3) (code a) ≠ .zero)
    (hd : dropOne (convert (k + 3) (code (V.get0 xs i))) = convert (k + 3) (code (V.get0 xs i)))
    (hnotLow : convert (k + 3) (code (.P xs .Z)) ≠
      .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i)))) :
    ∃ w, convert (k + 3) (code (.P xs .Z)) = .psi w (convert (k + 3) (code (V.get0 xs i))) ∧
      convert (k + 3) (code (.P (V.set xs i a) .Z)) = .psi w (dropOne (convert (k + 3) (code a))) := by
  have hil : i < xs.length := by
    apply Nat.lt_of_not_le
    intro h
    rw [V.get0_ge xs i h, convert_Z] at hc
    exact hc rfl
  let ys := V.set xs i a
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have hold (j : Nat) : oldArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xs j)) :=
    converted_coordinate xs j
  have hnew (j : Nat) : newArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 ys j)) :=
    converted_coordinate ys j
  have hnewa : newArgs[i]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew i]; show convert (k + 3) (code (V.get0 (V.set xs i a) i)) = _
    rw [V.get0_set_same xs i a hil]
  have hzeroOld : ∀ j, j < i → oldArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hold j, hlow j hj, convert_Z]
  have hzeroNew : ∀ j, j < i → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew j]
    show convert (k + 3) (code (V.get0 (V.set xs i a) j)) = _
    rw [V.get0_set_ne xs i a j (by omega), hlow j hj, convert_Z]
  have hsame : ∀ j, i < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj _
    rw [hnew j, hold j]
    show convert (k + 3) (code (V.get0 (V.set xs i a) j)) = _
    rw [V.get0_set_ne xs i a j (by omega)]
  have heOld : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have heNew : convert (k + 3) (code (.P ys .Z)) = lower (k + 1) newArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
    change lower (k + 1) newArgs (topPair (k + 1) (newArgs[k + 2]?.getD .zero)
      (newArgs[k + 1]?.getD .zero)) = _
    rw [hsame (k + 2) (by omega) (by omega)]
  by_cases hi : i = k + 1
  · subst hi
    let h := oldArgs[k + 2]?.getD .zero
    have htopOld : topPair (k + 1) h (convert (k + 3) (code (V.get0 xs (k + 1)))) ≠ .zero := by
      simp [topPair, hc]
    have htopNew : topPair (k + 1) h (convert (k + 3) (code a)) ≠ .zero := by simp [topPair, ha]
    have hcOld : oldArgs[k + 1]?.getD .zero = convert (k + 3) (code (V.get0 xs (k + 1))) := hold _
    refine ⟨pairCut (k + 1) h, ?_, ?_⟩
    · rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ htopOld hzeroOld]
      simp [topPair, pairCut, hc, hd, h]
    · show convert (k + 3) (code (.P ys .Z)) = _
      rw [heNew, hnewa, lower_keep (k + 1) newArgs _ htopNew hzeroNew]
      simp [topPair, pairCut, ha, h]
  · rw [hsame (k + 1) (by omega) (by omega)] at heNew
    obtain ⟨b, hbOld, hbNew⟩ := lower_selected_step (k + 1) i (by omega) oldArgs newArgs _ _ _ hc ha
      (hold i) hnewa hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega))
    have heO : convert (k + 3) (code (.P xs .Z)) = step i b (convert (k + 3) (code (V.get0 xs i))) :=
      heOld.trans hbOld
    have heN : convert (k + 3) (code (.P ys .Z)) = step i b (convert (k + 3) (code a)) :=
      heNew.trans hbNew
    refine ⟨layerCut i b, heO.trans (step_psi_of_drop _ _ _ hc hd), ?_⟩
    show convert (k + 3) (code (.P ys .Z)) = _
    rw [heN]
    by_cases hb0 : b = .zero
    · by_cases hi0 : i = 0
      · apply False.elim
        apply hnotLow
        rw [heO]
        simp [step, hb0, hi0]
      · simp [step, layerCut, hb0, hi0, ha]
    · simp [step, layerCut, regular, hb0, ha]

theorem not_diag_of_dom {xs q : V multi.T} {i : Nat} (hf : V.fnz xs = some i)
    {r : V multi.T} (hdq : domF (V.get0 xs i) = .Omega r)
    (hd : domF (.P xs .Z) = .Omega q) : ¬ xs < r := by
  intro he
  rw [domF_diag hf hdq he] at hd
  cases hd

theorem lastVec_of_low {k : Nat} {xs : V multi.T} (hl : xs.length = k + 3)
    (hlow : ∀ j, j < k + 2 → V.get0 xs j = .Z) : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := by
  apply V.eq_of_get0 _ _ (by rw [hl, lastVec_length])
  intro j
  rw [get0_lastVec]
  by_cases hj : j = k + 2
  · rw [ite_eq_left hj, hj]
  · rw [ite_eq_right hj]
    by_cases hjl : j < k + 2
    · exact hlow j hjl
    · exact V.get0_ge xs j (by omega)

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
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
    fund_nondiag hf hdq (not_diag_of_dom hf hdq hd) t
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) t) := by
    have := (RecursiveWF_P.1 (hfund ▸ hn)).1 i
    rwa [V.get0_set_same xs i _ hil] at this
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (V.get0 xs i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term} :
      UpdatedCoefficient k v (V.get0 xs i) t z ∨ extra z →
        UpdatedCoefficient k v (.P xs .Z) t z ∨ extra z := by
    rintro ((he | ho | ⟨a, ha, hw, ho, he⟩) | hex)
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr (Or.inl (embed _ ho)))
    · exact Or.inl (Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i), hw,
        ho.imp (embed _) (embed _), he⟩))
    · exact Or.inr hex
  intro z hz
  by_cases hib : i ≤ k + 1
  · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib
      (V.fnz_some_spec xs i hf).2 _
      (fun he => (V.fnz_some_spec xs i hf).1 ((convert_eq_zero_iff _ _).1 he))
      (fun he => domOmega_fund_ne_zero _ t hdq ((convert_eq_zero_iff _ _).1 he))
      (Omega_image_drop k _ hchildDim hchildR (hcoords i) hdq)
      (Omega_principal_image_ne_low k xs i hsD hs hd)
    have heFund := hfund ▸ heNew
    have hlt := (convert_order k _ _ (Dim_fund _ _ hsD htD) hsD hn hs).mp
      (fund_lt (.P xs .Z) t (by intro he; cases he))
    rw [heOld, heFund] at hlt
    rw [heFund] at hz
    rcases H_psi_replacement_support v w _ _ hvR hv (heOld ▸ hs.wf) (heFund ▸ hn.wf) hlt hz with
      ⟨_, ho⟩ | ⟨he | hzChild, hroot, hchild⟩
    · exact Or.inl (Or.inr (Or.inl (heOld ▸ ho)))
    · exact Or.inl (Or.inr (Or.inr ⟨V.get0 xs i, Subterm.coordinate xs .Z i, hnChild,
        Or.inl (heOld ▸ hroot), Or.inr he⟩))
    · exact lift (fun z hz => heOld ▸ hchild z hz) (hcoef z hzChild)
  · have hi : i = k + 2 := by have := hsD.length; omega
    subst hi
    have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
      lastVec_of_low hsD.length (V.fnz_some_spec xs _ hf).2
    have heNew : T.fund (.P xs .Z) t = topNode k (T.fund (V.get0 xs (k + 2)) t) := by
      rw [hfund]
      show multi.T.P _ .Z = multi.T.P _ .Z
      congr 1
      have := kumakuma.SourceOmegaHighest.lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
        (T.fund (V.get0 xs (k + 2)) t)
      rwa [← he] at this
    have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) =
        Term.H v (convert (k + 3) (code (V.get0 xs (k + 2)))) := by
      rw [show multi.T.P xs .Z = topNode k (V.get0 xs (k + 2)) from congrArg (multi.T.P · .Z) he]
      exact H_topNode_Omega k _ hchildDim hchildR (hcoords _) hdq v hOmega
    rw [heNew, H_topNode_above_Omega k _ (domOmega_fund_ne_zero _ t hdq) v hOmega] at hz
    exact lift (fun z hz => heH ▸ hz) (hcoef z (kumakuma.OT2.mem_H_dropOne hz))

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
  have hil : i < xs.length := fnz_lt_length hf
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hlow := (V.fnz_some_spec xs i hf).2
  have hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z :=
    fund_nondiag hf hdq (not_diag_of_dom hf hdq hd) t
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) t) := by
    have := (RecursiveWF_P.1 (hfund ▸ hn)).1 i
    rwa [V.get0_set_same xs i _ hil] at this
  have hsZ : convert (k + 3) (code (.P xs .Z)) ≠ .zero := convert_ne_zero xs .Z
  have hnZ : convert (k + 3) (code (T.fund (.P xs .Z) t)) ≠ .zero :=
    fun he => domOmega_fund_ne_zero _ t hd ((convert_eq_zero_iff _ _).1 he)
  have hhead := Omega_image_head_ne_one k _ hsD hr hs hd
  by_cases hex : ∃ j, i ≠ j ∧ V.get0 xs j ≠ .Z
  · obtain ⟨j, hij, hj⟩ := hex
    exact closed_of_updated_or_bounded k v _ t hsD htD hs hn hhead hsZ hnZ
      (fun a ha => principal_subterm_gap xs i j hij hc0 hj hd t ha) extra hBound
      (parent_Omega_updated_or_support k xs q i hsD hf hdq hr hs hd t htD hn v hvR hv hOmega extra
        hcoef) hH
  have hother (j : Nat) (hj : j ≠ i) : V.get0 xs j = .Z :=
    Decidable.byContradiction fun hz => hex ⟨j, fun he => hj he.symm, hz⟩
  by_cases hib : i ≤ k + 1
  · have hip : 0 < i := by
      refine Nat.pos_of_ne_zero fun hi0 => ?_
      subst hi0
      have he : xs = lowVec (k + 2) (V.get0 xs 0) := by
        refine V.eq_of_get0 _ _ (by rw [hsD.length, lowVec_length]) fun j => ?_
        rw [get0_lowVec]
        by_cases hj : j = 0
        · rw [ite_eq_left hj, hj]
        · rw [ite_eq_right hj]; exact hother j hj
      have ho : Outer (k + 2) (.P (lowVec (k + 2) (V.get0 xs 0)) .Z) := .cons _ _ .zero
      exact SourceFundOrder.outer_not_Omega ho q (by rwa [he] at hd)
    have hhigh (j : Nat) (hj : i < j) : V.get0 xs j = .Z := hother j (by omega_c)
    have heOld := convert_positive_single k xs i hip hib hlow hhigh hc0
    rw [Omega_image_drop k _ hchildDim hchildR (hcoords i) hdq] at heOld
    have hnewIdx : V.get0 (V.set xs i (T.fund (V.get0 xs i) t)) i = T.fund (V.get0 xs i) t :=
      V.get0_set_same xs i _ hil
    have hnewNZ : V.get0 (V.set xs i (T.fund (V.get0 xs i) t)) i ≠ .Z :=
      by rw [hnewIdx]; exact domOmega_fund_ne_zero _ t hdq
    have heFund : convert (k + 3) (code (T.fund (.P xs .Z) t)) =
        .psi (.inacc i .zero) (dropOne (convert (k + 3) (code (T.fund (V.get0 xs i) t)))) := by
      rw [hfund, convert_positive_single k _ i hip hib
        (fun j hj => by rw [V.get0_set_ne xs i _ j (by omega_c)]; exact hlow j hj)
        (fun j hj => by rw [V.get0_set_ne xs i _ j (by omega_c)]; exact hhigh j hj) hnewNZ, hnewIdx]
    have hwOld := heOld ▸ hs.wf
    have hwNew := heFund ▸ hn.wf
    have hlt := (convert_order k _ _ (Dim_fund _ _ hsD htD) hsD hn hs).mp
      (fund_lt (.P xs .Z) t (by intro he; cases he))
    rw [heOld, heFund] at hlt
    have hgapChild (a : multi.T) (ha : Subterm a (V.get0 xs i)) : mass a < gap (.P xs .Z) t := by
      have hmA := kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha
      have hmI := vectorMass_get0_le xs i
      rw [gap_Omega _ _ _ hd, mass_P, mass_Z]
      omega_c
    refine (Term.allLt_iff _ _).mpr fun z hz => ?_
    rw [heFund] at hz
    rcases H_psi_replacement_support v _ _ _ hvR hv hwOld hwNew hlt hz with
      ⟨hctx, _⟩ | ⟨rfl | hzChild, hroot, hchild⟩
    · simp [Term.H, Term.hOne, hOmega] at hctx
    · have hOldArg : Term.lt (convert (k + 3) (code (V.get0 xs i)))
          (.psi (.inacc i .zero) (convert (k + 3) (code (V.get0 xs i)))) = true := by
        rw [← heOld]; exact (Term.allLt_iff _ _).mp hH _ (heOld ▸ hroot)
      have hOwnW := ((Term.wf_psi_iff _ _).mp hwOld).2.1
      rw [heFund]
      exact (kumakuma.JaegerFacts.lt_psi_self_iff hwNew).mpr (dropOne_lt_of_lt hnChild.wf hOwnW
        (Term.lt_trans hnChild.wf (hcoords i).wf hOwnW ((convert_order k _ _
          (Dim_fund _ _ hchildDim htD) hchildDim hnChild (hcoords i)).mp (fund_lt (V.get0 xs i) t hc0))
          ((kumakuma.JaegerFacts.lt_psi_self_iff hwOld).mp hOldArg)))
    · exact (hcoef z hzChild).elim (updated_lt_fund k v hsD hchildDim htD hs (hcoords i) hn hhead
        hsZ hnZ hgapChild (fun a ha => heOld ▸ hchild a ha) hH) (hBound z)
  · have hi : i = k + 2 := by have := hsD.length; omega
    subst hi
    have hsource : (multi.T.P xs .Z) = topNode k (V.get0 xs (k + 2)) :=
      congrArg (multi.T.P · .Z) (lastVec_of_low hsD.length hlow)
    rw [hsource]
    exact topNode_relative_of_updated_or_bounded k (V.get0 xs (k + 2)) t hchildDim htD hchildR
      (hcoords _) hdq (hsource ▸ hs) hnChild v hOmega extra
      (fun z hz => (congrArg (T.fund · t) hsource) ▸ hBound z hz) hcoef (hsource ▸ hH)

end kumakuma.GeneralImageCofinalityCoefficients

namespace kumakuma.GeneralImageOmegaCofinality

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

/-- The invariant of Omega fund, given the well-formedness of `fund` in the regular case where the
label is the term itself (`G` is an assumption on the label). -/
theorem Omega_fund_invariant (k : Nat) (G : V multi.T → Prop) (t : multi.T) (htD : Dim (k + 3) t)
    (hreg : ∀ m xs, Dim (k + 3) (.P xs .Z) → V.fnz xs = some (m + 1) →
      domF (V.get0 xs (m + 1)) = .one → G xs → RecursiveWF (k + 3) (.P xs .Z) →
      RecursiveWF (k + 3) (T.fund (.P xs .Z) t)) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s →
    ∀ {q : V multi.T}, domF s = .Omega q → G q →
    RecursiveWF (k + 3) (T.fund s t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P q .Z))) v = true →
        (∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) → UpdatedCoefficient k v s t z) ∧
        (Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
          Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
            (convert (k + 3) (code (T.fund s t))) = true)
  | .Z, _, _, _, _, hd, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, hsD, hr, hs, q, hd, hG => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      cases hc : domF (V.get0 xs i) with
      | zero => rw [domF_zero hf hc] at hd; cases hd
      | omega => rw [domF_omega hf hc] at hd; cases hd
      | one =>
        cases i with
        | zero => rw [domF_one_zero hf hc] at hd; cases hd
        | succ m =>
          rw [domF_one_succ hf hc] at hd
          cases hd
          have hn := hreg m xs hsD hf hc hG hs
          refine ⟨hn, fun v hvR hv hOmega hcut => ⟨fun z hz =>
            H_fund_regular_cofinal_support k m xs hsD hf hc hs t v hvR hv hOmega hcut hz,
            fund_regular_cofinal_relative_all_of_wf k m xs hsD hf hc hr hs t htD hn v hvR hv hOmega
              hcut⟩⟩
      | Omega q =>
        by_cases hlt : xs < q
        · rw [domF_diag hf hc hlt] at hd; cases hd
        rw [domF_nondiag hf hc hlt] at hd
        cases hd
        have hd' : domF (.P xs .Z) = .Omega q := domF_nondiag hf hc hlt
        have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
        have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
        have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
        obtain ⟨hnChild, hchildInv⟩ := Omega_fund_invariant k G t htD hreg (V.get0 xs i) hchildDim
          hchildR (hcoords i) hc hG
        have hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) t) := by
          rw [fund_nondiag hf hc hlt t]
          by_cases hib : i ≤ k + 1
          · exact principal_replace_cofinal_recursiveWF k xs i hib hsD
              (V.fnz_some_spec xs i hf).2 hs _ hnChild (V.fnz_some_spec xs i hf).1
              (Omega_image_drop k _ hchildDim hchildR (hcoords i) hc)
              (convert (k + 3) (code (.P q .Z))) (Omega_label_recursiveWF k _ hs hd').wf
              (cofinality_image_le k _ hsD hr hs hd') (Omega_principal_image_ne_low k xs i hsD hs hd')
              fun v hvR hv hOmega hcut hH => (hchildInv v hvR hv hOmega hcut).2 hH
          · have hi : i = k + 2 := by have := fnz_lt_length hf; rw [hsD.length] at this; omega
            subst hi
            have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) :=
              lastVec_of_low hsD.length (V.fnz_some_spec xs _ hf).2
            have hrplc := kumakuma.SourceOmegaHighest.lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
              (T.fund (V.get0 xs (k + 2)) t)
            rw [← he] at hrplc
            rw [hrplc]
            exact topNode_recursiveWF k _ hnChild
        refine ⟨hn, fun v hvR hv hOmega hcut => ?_⟩
        have hcf' := fun z hz => Or.inl (b := False) ((hchildInv v hvR hv hOmega hcut).1 z hz)
        exact ⟨fun z hz => (parent_Omega_updated_or_support k xs q i hsD hf hc hr hs hd' t htD hn v
            hvR hv hOmega _ hcf' z hz).resolve_right id,
          parent_Omega_relative_of_updated_or_bounded k xs q i hsD hf hc hr hs hd' t htD hn v hvR hv
            hOmega _ (fun _ h => h.elim) hcf'⟩
    · have hbr : Recursive b := (Recursive_P.1 hr).2.1
      have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
      have hdb : domF b = .Omega q := by rwa [domF_tail xs hb] at hd
      obtain ⟨hnB, htailInv⟩ := Omega_fund_invariant k G t htD hreg b hsD.tail hbr hbw hdb hG
      have hn := fund_nonzero_tail_recursiveWF k xs b t hsD htD hs hb hnB
      refine ⟨hn, fun v hvR hv hOmega hcut => ?_⟩
      have hcoef (z : Term) (hz : z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs b) t)))) :
          UpdatedCoefficient k v (.P xs b) t z := by
        rw [fund_tail xs hb, convert_P] at hz
        rcases H_assemble_support v _ _ hz with hz | hz
        · exact Or.inr (Or.inl (by rw [convert_P]; exact H_assemble_left v _ _ hz))
        rcases (htailInv v hvR hv hOmega hcut).1 z hz with he | ho | ⟨a, ha, hw, hmA, he⟩
        · exact Or.inl he
        · exact Or.inr (Or.inl (by rw [convert_P]; exact H_assemble_right v _ _ ho))
        · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
          rw [convert_P]
          exact hmA.imp (H_assemble_right v _ _) (H_assemble_right v _ _)
      exact ⟨hcoef, closed_of_updated_coefficients k v _ t hsD htD hs hn
        (Omega_image_head_ne_one k _ hsD hr hs hd) (convert_ne_zero xs b)
        (fun he => domOmega_fund_ne_zero _ t hd ((convert_eq_zero_iff _ _).1 he))
        (fun a ha => sum_subterm_gap xs b t hb (Omega_head_mass_pos xs b hr hd) hd ha) hcoef⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem Omega_fund_cofinal_invariant (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (t : multi.T) (htD : Dim (k + 3) t) (ht : RecursiveWF (k + 3) t)
    (hHt : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code t)))
      (convert (k + 3) (code t)) = true) :
    RecursiveWF (k + 3) (T.fund s t) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        Term.lt (convert (k + 3) (code (.P q .Z))) v = true →
        (∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s t))) → UpdatedCoefficient k v s t z) ∧
        (Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
          Term.allLt (Term.H v (convert (k + 3) (code (T.fund s t))))
            (convert (k + 3) (code (T.fund s t))) = true) :=
  Omega_fund_invariant k (fun _ => True) t htD
    (fun m xs hsD hf hc _ hs => fund_regular_recursiveWF k m xs hsD hf hc t hs ht hHt) s hsD hr hs hd
    trivial

theorem all_Omega_iter_closed (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    {q : V multi.T} (hd : domF s = .Omega q)
    (hsub : ∀ a, Subterm a s → a < s) (n : Nat) :
    Dim (k + 3) (multi.T.iter (T.fund s) (ofNatD (k + 3) n)) ∧
    RecursiveWF (k + 3) (multi.T.iter (T.fund s) (ofNatD (k + 3) n)) ∧
      Term.allLt (Term.H Term.bigOmega (convert (k + 3)
        (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n)))))
        (convert (k + 3) (code (multi.T.iter (T.fund s) (ofNatD (k + 3) n)))) = true := by
  induction n with
  | zero =>
    show Dim (k + 3) .Z ∧ RecursiveWF (k + 3) .Z ∧
      Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code .Z))) (convert (k + 3) (code .Z)) = true
    exact ⟨Dim_Z _, recursive_zero _, by simp [convert_Z, Term.H, Term.allLt]⟩
  | succ n ih =>
    rw [iter_ofNat_succ]
    have hn := (Omega_fund_cofinal_invariant k s hsD hr hs hd _ ih.1 ih.2.1 ih.2.2).1
    have hnD := Dim_fund s _ hsD ih.1
    refine ⟨hnD, hn, ?_⟩
    exact H_convert_bound_of_subterms k Term.bigOmega _ hnD hn
      (Omega_iter_subterms s hr hd hsub (k + 3) (n + 1))

end kumakuma.GeneralImageOmegaCofinality

namespace kumakuma.GeneralImageZeroFund

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageCountableRecursion kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageUpperOmega
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageCofinalityInheritance
open kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceFundGap kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageOmegaCofinality

theorem lower_selected_step_context (j cut : Nat) (hj : cut < j) (xs ys : List Term)
    (a c t : Term) (hc : c ≠ .zero) (hctx : Context j a)
    (hx : xs[cut]?.getD .zero = c) (hy : ys[cut]?.getD .zero = t)
    (hzeroOld : ∀ i, i < cut → xs[i]?.getD .zero = .zero)
    (_hzeroNew : ∀ i, i < cut → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, cut < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero) :
    ∃ b, Above cut b ∧ lower j xs a = step cut b c ∧
      lower j ys a = lower cut ys (step cut b t) := by
  induction j generalizing a with
  | zero => omega_c
  | succ j ih =>
    by_cases hij : cut < j
    · rw [lower_succ, lower_succ, hsame j hij (by omega_c)]
      exact ih hij _ (step_shape _ (context_above hctx)) (fun i hi hik => hsame i hi (by omega_c))
    · have he : j = cut := by omega_c
      subst j
      refine ⟨a, context_above hctx, ?_, ?_⟩
      · rw [lower_succ, hx]; exact lower_keep cut xs _ (step_ne_zero_of_argument cut a c hc) hzeroOld
      · rw [lower_succ, hy]

theorem H_topPair_zero_support (v : Term)
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
  · have hp := (kumakuma.JaegerFacts.predR_facts hv hvR)
    have hle := Term.le_trans hn hw hp.1 (by simp [Term.le, hl]) hs
    rw [kumakuma.JaegerFacts.H_nil_of_le_predR hv hvR _ hn hle] at hz; cases hz
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


theorem zero_relative_of_updated_support (k : Nat)
    (s : multi.T) (hsD : Dim (k + 3) s) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (T.fund s .Z))
    (v : Term) (hhead : Term.head (convert (k + 3) (code s)) ≠ Term.one)
    (hsZ : convert (k + 3) (code s) ≠ .zero)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s .Z))) →
      UpdatedCoefficient k v s .Z z)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s .Z))))
      (convert (k + 3) (code (T.fund s .Z))) = true := by
  have hnD : Dim (k + 3) (T.fund s .Z) := Dim_fund _ _ hsD (Dim_Z _)
  by_cases hnZ : convert (k + 3) (code (T.fund s .Z)) = .zero
  · rw [hnZ, Term.H]; rfl
  · apply (Term.allLt_iff _ _).mpr
    intro z hz
    have hzOld := updated_coefficient_lt_old k v s .Z hsD (Dim_Z _) hs hhead hsZ hH (hcoef z hz)
    rcases H_convert_source k v (T.fund s .Z) hz with rfl | ⟨a, ha, he⟩
    · exact (zero_lt_iff _).mpr hnZ
    · have haW := ha.recursiveWF hn
      have haD := ha.dim hnD
      have haOld : a < s := by
        apply (convert_order k _ _ haD hsD haW hs).mpr
        rcases he with he | he
        · exact he ▸ hzOld
        · exact undrop_lt_head_ne_one _ _ haW.wf hs.wf hsZ hhead (he ▸ hzOld)
      have hmass : mass a < gap s .Z := by
        have haM := kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha
        have hfund := mass_fund_zero_le s
        rw [gap, ite_eq_left rfl]
        omega
      have haNew := (convert_order k _ _ haD hnD haW hn).mp (small_lt_fund_all s .Z a haOld hmass)
      rcases he with rfl | rfl
      · exact haNew
      · exact dropOne_lt_of_lt haW.wf hn.wf haNew

theorem parent_zero_updated_support (k : Nat)
    (xs : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hlow : ∀ j, j < i → V.get0 xs j = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (hc0 : V.get0 xs i ≠ .Z)
    (hdrop : dropOne (convert (k + 3) (code (V.get0 xs i))) = convert (k + 3) (code (V.get0 xs i)))
    (hf : T.fund (.P xs .Z) .Z = .P (V.set xs i (T.fund (V.get0 xs i) .Z)) .Z)
    (hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) .Z))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true)
    (hcoef : ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (V.get0 xs i) .Z))) →
      UpdatedCoefficient k v (V.get0 xs i) .Z z) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) .Z))) →
      UpdatedCoefficient k v (.P xs .Z) .Z z := by
  have hil : i < xs.length := by
    apply Nat.lt_of_not_le; intro h; exact hc0 (V.get0_ge xs i h)
  have hik : i < k + 3 := by rw [← hsD.length]; exact hil
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hnD : Dim (k + 3) (T.fund (.P xs .Z) .Z) := Dim_fund _ _ hsD (Dim_Z _)
  have hnChild : RecursiveWF (k + 3) (T.fund (V.get0 xs i) .Z) := by
    have hw := hn
    rw [hf] at hw
    have := (RecursiveWF_P.1 hw).1 i
    rwa [V.get0_set_same xs i _ hil] at this
  have hcNZ : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun he => hc0 ((convert_eq_zero_iff _ _).1 he)
  have lift (embed : ∀ z, z ∈ Term.H v (convert (k + 3) (code (V.get0 xs i))) →
      z ∈ Term.H v (convert (k + 3) (code (.P xs .Z)))) {z : Term}
      (hc : UpdatedCoefficient k v (V.get0 xs i) .Z z) : UpdatedCoefficient k v (.P xs .Z) .Z z := by
    rcases hc with he | ho | ⟨a, ha, hw, ho, he⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl (embed _ ho))
    · exact Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs .Z i), hw,
        ho.elim (fun h => Or.inl (embed _ h)) (fun h => Or.inr (embed _ h)), he⟩)
  intro z hz
  by_cases hIsLow : convert (k + 3) (code (.P xs .Z)) =
      .psi Term.bigOmega (convert (k + 3) (code (V.get0 xs i)))
  · have hp := (Term.wf_psi_iff _ _).mp (hIsLow ▸ hs.wf)
    have hwLow := (low_principal_recursiveWF_iff (k + 3) (k + 2) (V.get0 xs i)).mpr ⟨hcoords i, hp.2.2.2⟩
    have heSource := convert_injective k (.P xs .Z) (.P (lowVec (k + 2) (V.get0 xs i)) .Z)
      hsD (Dim_lowVec (hsD.coord i) (Dim_Z _)) hs hwLow
      (by rw [convert_low_principal]; exact hIsLow)
    have heVec : xs = lowVec (k + 2) (V.get0 xs i) := by injection heSource
    have hi0 : i = 0 := by
      apply Decidable.byContradiction
      intro hi
      have hc : V.get0 xs i = V.get0 (lowVec (k + 2) (V.get0 xs i)) i :=
        congrArg (fun us => V.get0 us i) heVec
      rw [get0_lowVec, ite_eq_right hi] at hc
      exact hc0 hc
    subst hi0
    have heR : V.set xs 0 (T.fund (V.get0 xs 0) .Z) = lowVec (k + 2) (T.fund (V.get0 xs 0) .Z) := by
      have := lowVec_set_zero (k + 2) (V.get0 xs 0) (T.fund (V.get0 xs 0) .Z)
      rw [← heVec] at this
      exact this
    rw [hf, heR, H_low_empty_above_Omega v hOmega] at hz
    cases hz
  · by_cases hib : i ≤ k + 1
    · by_cases hnewNZ : convert (k + 3) (code (T.fund (V.get0 xs i) .Z)) ≠ .zero
      · obtain ⟨w, heOld, heNew⟩ := principal_replacement_psi_images k xs i hib hlow _ hcNZ hnewNZ hdrop hIsLow
        have heFund := hf ▸ heNew
        have hlt := (convert_order k _ _ hnD hsD hn hs).mp (fund_lt (.P xs .Z) .Z (by intro he; cases he))
        have hwOld := heOld ▸ hs.wf
        have hwNew := heFund ▸ hn.wf
        rw [heOld, heFund] at hlt
        rw [heFund] at hz
        rcases H_psi_replacement_support v w _ _ hvR hv hwOld hwNew hlt hz
          with ⟨_, ho⟩ | ⟨he, hroot, hchild⟩
        · exact Or.inr (Or.inl (heOld ▸ ho))
        · rcases he with he | hzChild
          · exact Or.inr (Or.inr ⟨V.get0 xs i, Subterm.coordinate xs .Z i, hnChild,
              Or.inl (heOld ▸ hroot), Or.inr he⟩)
          · exact lift (fun z hz => heOld ▸ hchild z hz) (hcoef z hzChild)
      · have heZero : T.fund (V.get0 xs i) .Z = .Z :=
          (convert_eq_zero_iff _ _).1 (Decidable.not_not.mp hnewNZ)
        let ys := V.set xs i .Z
        let oldArgs := arguments (k + 3) (trim (codes xs))
        let newArgs := arguments (k + 3) (trim (codes ys))
        have hold (j : Nat) : oldArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xs j)) :=
          converted_coordinate xs j
        have hnew (j : Nat) : newArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 ys j)) :=
          converted_coordinate ys j
        have hnewa : newArgs[i]?.getD .zero = .zero := by
          rw [hnew i]; show convert (k + 3) (code (V.get0 (V.set xs i .Z) i)) = _
          rw [V.get0_set_same xs i _ hil, convert_Z]
        have hzeroOld : ∀ j, j < i → oldArgs[j]?.getD .zero = .zero := by
          intro j hj; rw [hold j, hlow j hj, convert_Z]
        have hzeroNew : ∀ j, j < i → newArgs[j]?.getD .zero = .zero := by
          intro j hj
          rw [hnew j]
          show convert (k + 3) (code (V.get0 (V.set xs i .Z) j)) = _
          rw [V.get0_set_ne xs i _ j (by omega_c), hlow j hj, convert_Z]
        have hsame : ∀ j, i < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
          intro j hj _
          rw [hnew j, hold j]
          show convert (k + 3) (code (V.get0 (V.set xs i .Z) j)) = _
          rw [V.get0_set_ne xs i _ j (by omega_c)]
        have heOld : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
            (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
          rw [convert_principal, principal_as_layers]
        have heNew : convert (k + 3) (code (T.fund (.P xs .Z) .Z)) = lower (k + 1) newArgs
            (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
          rw [hf, heZero, convert_principal, principal_as_layers]
          change lower (k + 1) newArgs (topPair (k + 1) (newArgs[k + 2]?.getD .zero)
            (newArgs[k + 1]?.getD .zero)) = _
          rw [hsame (k + 2) (by omega_c) (by omega_c)]
        by_cases hi : i = k + 1
        · subst hi
          have hcOld : oldArgs[k + 1]?.getD .zero = convert (k + 3) (code (V.get0 xs (k + 1))) :=
            hold (k + 1)
          have hcTop : topPair (k + 1) (oldArgs[k + 2]?.getD .zero)
              (convert (k + 3) (code (V.get0 xs (k + 1)))) ≠ .zero := by simp [topPair, hcNZ]
          rw [heNew, hnewa, H_lower_zeros_above_Omega v hOmega _ _ _ hzeroNew] at hz
          have hwOld := hs.wf
          rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ hcTop hzeroOld] at hwOld
          have hHigh := hcoords (k + 2)
          have hh : Term.wf (oldArgs[k + 2]?.getD .zero) = true := by
            rw [hold (k + 2)]; exact hHigh.wf
          have hI : Term.wf (.inacc (k + 1) (dropOne (oldArgs[k + 2]?.getD .zero))) = true := by
            rw [hold (k + 2)]; exact inacc_image_drop_wf k _ hHigh
          have ho := H_topPair_zero_support v hvR hv (k + 1) _ _ hh (hcoords _).wf hcNZ hI hwOld hz
          apply Or.inr; apply Or.inl
          rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ hcTop hzeroOld]
          exact ho
        · rw [hsame (k + 1) (by omega_c) (by omega_c)] at heNew
          obtain ⟨b, hb, heO, heN⟩ := lower_selected_step_context (k + 1) i (by omega_c)
            oldArgs newArgs _ _ .zero hcNZ (topPair_context _ _ _) (hold i) hnewa hzeroOld hzeroNew
            (fun j hj hjk => hsame j hj (by omega_c))
          rw [heNew, heN, H_lower_zeros_above_Omega v hOmega _ _ _ hzeroNew] at hz
          have hw := hs.wf
          rw [heOld, heO] at hw
          have ho : z ∈ Term.H v (step i b (convert (k + 3) (code (V.get0 xs i)))) := by
            by_cases hb0 : b = .zero
            · by_cases hi0 : i = 0
              · simp only [step, hb0, hi0, ↓reduceIte] at hz
                change z ∈ Term.H v Term.one at hz
                rw [H_one_empty_above_Omega v hOmega] at hz
                cases hz
              · simp [step, hb0, hi0, Term.H] at hz
            · have hzB : z ∈ Term.H v b := by simpa only [step, hb0, ↓reduceIte] using hz
              exact H_step_context_of_wf v hvR hv i b _ hb hw hzB
          exact Or.inr (Or.inl ((heOld.trans heO) ▸ ho))
    · have hi : i = k + 2 := by omega_c
      subst hi
      have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := lastVec_of_low hsD.length hlow
      have heOld : multi.T.P xs .Z = topNode k (V.get0 xs (k + 2)) :=
        congrArg (fun us => multi.T.P us .Z) he
      have heNew : T.fund (.P xs .Z) .Z = topNode k (T.fund (V.get0 xs (k + 2)) .Z) := by
        rw [hf]
        show multi.T.P _ .Z = multi.T.P _ .Z
        congr 1
        have := kumakuma.SourceOmegaHighest.lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
          (T.fund (V.get0 xs (k + 2)) .Z)
        rw [← he] at this
        exact this
      have heH : Term.H v (convert (k + 3) (code (.P xs .Z))) =
          Term.H v (convert (k + 3) (code (V.get0 xs (k + 2)))) := by
        rw [heOld, H_topNode_above_Omega k _ hc0 v hOmega, hdrop]
      by_cases hzC : T.fund (V.get0 xs (k + 2)) .Z = .Z
      · have hVec : lastVec (k + 2) .Z = lowVec (k + 2) .Z := by
          rw [lowVec_Z]; rfl
        rw [heNew, hzC, topNode, hVec, H_low_empty_above_Omega v hOmega] at hz
        cases hz
      · rw [heNew, H_topNode_above_Omega k _ hzC v hOmega] at hz
        exact lift (fun z hz => heH ▸ hz) (hcoef z (kumakuma.OT2.mem_H_dropOne hz))

theorem regular_zero_updated_support (k m : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hfz : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one)
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hOmega : Term.lt Term.bigOmega v = true) :
    ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) .Z))) →
      UpdatedCoefficient k v (.P xs .Z) .Z z := by
  have hml : m + 1 < k + 3 := by have := fnz_lt_length hfz; rwa [hsD.length] at this
  have hml' : m + 1 < xs.length := fnz_lt_length hfz
  have hlow := (V.fnz_some_spec xs _ hfz).2
  have hcoords : ∀ i, RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1
  let p := T.fund (V.get0 xs (m + 1)) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hsD.coord _) (hcoords _) hdom
  have hsucc : convert (k + 3) (code (V.get0 xs (m + 1))) =
      succTerm (convert (k + 3) (code p)) := by
    obtain ⟨a, he⟩ := dom_one_succ (V.get0 xs (m + 1)) (hsD.coord _) hdom
    show _ = succTerm (convert (k + 3) (code (T.fund (V.get0 xs (m + 1)) .Z)))
    rw [he, kumakuma.SourceSuccessor.fund_succ, convert_succ]
  let ys := V.set xs (m + 1) p
  have hf : T.fund (.P xs .Z) .Z = .P ys .Z := by
    rw [fund_one_succ hfz hdom .Z]
    congr 1
    apply set_eq_self
    rw [V.get0_set_ne xs (m + 1) p m (by omega)]
    exact hlow m (by omega)
  have yidx (j : Nat) : V.get0 ys j = if j = m + 1 then p else V.get0 xs j := V.get0_set xs _ p j hml'
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have oldGet (j : Nat) : oldArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xs j)) :=
    converted_coordinate xs j
  have newGet (j : Nat) : newArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 ys j)) :=
    converted_coordinate ys j
  have hOld : oldArgs[m + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by
    rw [oldGet (m + 1)]; exact hsucc
  have hNew : newArgs[m + 1]?.getD .zero = convert (k + 3) (code p) := by
    rw [newGet (m + 1), yidx, ite_eq_left rfl]
  have hzeroOld : ∀ j, j < m + 1 → oldArgs[j]?.getD .zero = .zero := by
    intro j hj; rw [oldGet j, hlow j hj, convert_Z]
  have hzeroNew : ∀ j, j < m + 1 → newArgs[j]?.getD .zero = .zero := by
    intro j hj; rw [newGet j, yidx, ite_eq_right (by omega), hlow j hj, convert_Z]
  have hsame : ∀ j, m + 1 < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj _; rw [newGet j, oldGet j, yidx, ite_eq_right (by omega)]
  have heOld : convert (k + 3) (code (.P xs .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have heNew : convert (k + 3) (code (T.fund (.P xs .Z) .Z)) = lower (k + 1) newArgs
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
    · refine Or.inr (Or.inr ⟨V.get0 xs (m + 1), Subterm.coordinate xs .Z _, ?_, ?_, he⟩)
      · exact hp
      · rw [hsucc]; exact ho
  rw [heNew] at hz
  by_cases hi : m + 1 = k + 2
  · have hmk : m = k + 1 := by omega
    subst hmk
    rw [hzeroNew (k + 1) (by omega), H_lower_zeros_above_Omega v hOmega _ _ _
      (fun j hj => hzeroNew j (by omega))] at hz
    rw [hNew] at hz
    have heOldTop : convert (k + 3) (code (.P xs .Z)) = topPair (k + 1)
        (succTerm (convert (k + 3) (code p))) .zero := by
      rw [heOld, hOld, hzeroOld (k + 1) (by omega)]
      exact lower_keep _ _ _ (by simp [topPair, succTerm_ne_zero]) (fun j hj => hzeroOld j (by omega))
    by_cases hp0 : convert (k + 3) (code p) = .zero
    · simp [hp0, topPair, Term.H] at hz
    · apply Or.inr; apply Or.inl; rw [heOldTop]
      simp only [topPair, ↓reduceIte, succTerm_ne_zero, drop_succ _ hp0]
      simp only [topPair, hp0, ↓reduceIte] at hz
      exact H_inacc_succ_support v (k + 1) _ hz
  · by_cases him : m + 1 = k + 1
    · have hmk : m = k := by omega
      subst hmk
      rw [hsame (m + 2) (by omega) (by omega)] at hz
      rw [hNew, H_lower_zeros_above_Omega v hOmega _ _ _ (fun j hj => hzeroNew j (by omega))] at hz
      have heOldTop : convert (m + 3) (code (.P xs .Z)) = topPair (m + 1)
          (oldArgs[m + 2]?.getD .zero) (succTerm (convert (m + 3) (code p))) := by
        rw [heOld, hOld]
        exact lower_keep _ _ _ (by simp [topPair, succTerm_ne_zero]) (fun j hj => hzeroOld j (by omega))
      have hh : Term.wf (oldArgs[m + 2]?.getD .zero) = true := by
        rw [oldGet (m + 2)]; exact (hcoords _).wf
      have hI : Term.wf (.inacc (m + 1) (dropOne (oldArgs[m + 2]?.getD .zero))) = true := by
        rw [oldGet (m + 2)]; exact inacc_image_drop_wf m _ (hcoords _)
      rcases H_topPair_predecessor_support v hvR hv (m + 1) _ _ hh hp.wf hI (heOldTop ▸ hs.wf) hz
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

theorem zero_relative_allcuts (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    (hn : RecursiveWF (k + 3) (T.fund s .Z))
    (hcoef : ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
      ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s .Z))) → UpdatedCoefficient k v s .Z z)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s .Z))))
      (convert (k + 3) (code (T.fund s .Z))) = true := by
  rcases Term.lt_trichotomy Term.wf_bigOmega hv with hOmega | he | hOmega
  · by_cases hh : Term.head (convert (k + 3) (code s)) = Term.one
    · obtain ⟨n, he⟩ := head_one_nat hs.wf hh
      have hsNat : s = ofNatD (k + 3) (n + 1) := convert_injective k s _ hsD (Dim_ofNatD _ _) hs
        (numeral_recursiveWF _ _ _) (he.trans (convert_numeral _ _ _).symm)
      rw [hsNat, ← kumakuma.SourceSuccessor.nat_succ, kumakuma.SourceSuccessor.fund_succ,
        convert_numeral]
      exact H_nat_bound v n
    · by_cases hsZ : convert (k + 3) (code s) = .zero
      · have heS : s = .Z := (convert_eq_zero_iff _ _).1 hsZ
        rw [heS, fund_Z, convert_Z, Term.H]; rfl
      · exact zero_relative_of_updated_support k s hsD hs hn v hh hsZ (hcoef v hvR hv hOmega) hH
  · subst v
    exact H_convert_bound_of_subterms k Term.bigOmega _ (Dim_fund _ _ hsD (Dim_Z _)) hn
      (kumakuma.SourceSubtermBounds.fund_zero_subterms s
        ((H_omega_bound_iff_subterms k s hsD hs hr).mp hH))
  · rw [kumakuma.CountableTarget.regular_not_below_omega hvR] at hOmega
    cases hOmega

theorem zero_fund_invariant (k : Nat) : ∀ (s : multi.T), Dim (k + 3) s →
    Recursive s → RecursiveWF (k + 3) s →
    RecursiveWF (k + 3) (T.fund s .Z) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s .Z))) → UpdatedCoefficient k v s .Z z) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund s .Z))))
          (convert (k + 3) (code (T.fund s .Z))) = true)
  | s, hsD, hr, hs => by
    have finish (hn : RecursiveWF (k + 3) (T.fund s .Z))
        (hc : ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
          ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s .Z))) → UpdatedCoefficient k v s .Z z) :=
      And.intro hn (And.intro hc (zero_relative_allcuts k s hsD hr hs hn hc))
    have empty (hf : T.fund s .Z = .Z) := by
      apply finish
      · rw [hf]; exact recursive_zero _
      · intro v _ _ _ z hz
        rw [hf, convert_Z, Term.H] at hz; cases hz
    match s, hsD, hr, hs, finish, empty with
    | .Z, _, _, _, _, empty => exact empty (fund_Z _)
    | .P xs b, hsD, hr, hs, finish, empty =>
      by_cases hb : b = .Z
      · subst hb
        rcases hfz : V.fnz xs with _ | i
        · exact empty (fund_none hfz _)
        · have hil := fnz_lt_length hfz
          have hik : i < k + 3 := by rw [← hsD.length]; exact hil
          have hlow := (V.fnz_some_spec xs i hfz).2
          have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hfz).1
          have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
          have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
          have hchildDim : Dim (k + 3) (V.get0 xs i) := hsD.coord i
          have general (hdrop : dropOne (convert (k + 3) (code (V.get0 xs i))) =
                convert (k + 3) (code (V.get0 xs i)))
              (hf : T.fund (.P xs .Z) .Z = .P (V.set xs i (T.fund (V.get0 xs i) .Z)) .Z) :
              RecursiveWF (k + 3) (T.fund (.P xs .Z) .Z) ∧
              (∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
                ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) .Z))) →
                  UpdatedCoefficient k v (.P xs .Z) .Z z) ∧
              (∀ v, Term.isRT v = true → Term.wf v = true →
                Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
                  (convert (k + 3) (code (.P xs .Z))) = true →
                Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) .Z))))
                  (convert (k + 3) (code (T.fund (.P xs .Z) .Z))) = true) := by
            obtain ⟨hnChild, hcChild, hrelChild⟩ :=
              zero_fund_invariant k (V.get0 xs i) hchildDim hchildR (hcoords i)
            have hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) .Z) := by
              rw [hf]
              by_cases hib : i ≤ k + 1
              · exact principal_replace_relative_recursiveWF k xs i hib hsD hlow hs _ hnChild hc0
                  hdrop hrelChild
              · have hi : i = k + 2 := by omega
                subst hi
                have he : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := lastVec_of_low hsD.length hlow
                have heR : V.set xs (k + 2) (T.fund (V.get0 xs (k + 2)) .Z) =
                    lastVec (k + 2) (T.fund (V.get0 xs (k + 2)) .Z) := by
                  have := kumakuma.SourceOmegaHighest.lastVec_replace_last (k + 2) (V.get0 xs (k + 2))
                    (T.fund (V.get0 xs (k + 2)) .Z)
                  rw [← he] at this
                  exact this
                rw [heR]; exact topNode_recursiveWF k _ hnChild
            apply finish hn
            intro v hvR hv hOmega
            exact parent_zero_updated_support k xs i hsD hlow hs hc0 hdrop hf hn v hvR hv hOmega
              (hcChild v hvR hv hOmega)
          cases hd : domF (V.get0 xs i) with
          | zero => exact absurd ((domF_eq_zero_iff _).1 hd) hc0
          | one =>
            cases i with
            | zero =>
              apply empty
              rw [fund_one_zero hfz hd]
              rfl
            | succ m =>
              apply finish (fund_regular_recursiveWF k m xs hsD hfz hd .Z hs (recursive_zero _)
                (by simp only [convert_Z, Term.H, Term.allLt, List.all_nil]))
              exact regular_zero_updated_support k m xs hsD hfz hd hs
          | omega =>
            exact general (drop_image_of_omega k _ hchildDim (hcoords i) hd) (fund_omega hfz hd .Z)
          | Omega ys =>
            have hdrop := Omega_image_drop k _ hchildDim hchildR (hcoords i) hd
            by_cases hv : xs < ys
            · exact general hdrop (fund_diag hfz hd hv .Z)
            · exact general hdrop (fund_nondiag hfz hd hv .Z)
      · have hbr : Recursive b := (Recursive_P.1 hr).2.1
        have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
        obtain ⟨hnB, hcB, _⟩ := zero_fund_invariant k b hsD.tail hbr hbw
        apply finish (fund_nonzero_tail_recursiveWF k xs b .Z hsD (Dim_Z _) hs hb hnB)
        intro v hvR hv hOmega z hz
        rw [fund_tail xs hb, convert_P] at hz
        rcases H_assemble_support v _ _ hz with hz | hz
        · exact Or.inr (Or.inl (by rw [convert_P]; exact H_assemble_left v _ _ hz))
        · rcases hcB v hvR hv hOmega z hz with he | ho | ⟨a, ha, hw, ho, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl; rw [convert_P]; exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), hw, ?_, he⟩)
            rw [convert_P]
            exact ho.elim (fun h => Or.inl (H_assemble_right v _ _ h))
              (fun h => Or.inr (H_assemble_right v _ _ h))
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

end kumakuma.GeneralImageZeroFund

namespace kumakuma.GeneralImageCountableInheritance

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageCountableRecursion kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageMiddleCofinality kumakuma.GeneralImageMiddleSums kumakuma.GeneralImageUpperOmega
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageCofinalityInheritance
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRegularCofinality
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceFundGap kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageOmegaCofinality
open kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageOmegaContext

theorem omega_image_head_ne_one (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hs : RecursiveWF (k + 3) s) (hd : domF s = .omega) :
    Term.head (convert (k + 3) (code s)) ≠ Term.one := by
  intro hh
  obtain ⟨n, he⟩ := head_one_nat hs.wf hh
  have heS : s = ofNatD (k + 3) (n + 1) := convert_injective k s _ hsD (Dim_ofNatD _ _) hs
    (numeral_recursiveWF _ _ _) (he.trans (convert_numeral _ _ _).symm)
  rw [heS, ← kumakuma.SourceSuccessor.nat_succ, kumakuma.SourceSuccessor.dom_succ] at hd
  cases hd

theorem omega_fund_nat_ne_zero (s : multi.T)
    (hd : domF s = .omega) (lam n : Nat) (hn : 0 < n) :
    T.fund s (ofNatD lam n) ≠ .Z := by
  intro he
  have hl := kumakuma.SourceCountableInvariant.ofNat_le_countable_fund s hd lam n
  rw [he] at hl
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rcases hl with hl | hl
  · exact T.not_lt_Z _ hl
  · exact ofNatD_succ_ne lam n' (T.eqv_Z_iff.1 hl)

theorem positive_principal_subterm_gap (xs : V multi.T)
    (i j : Nat) (hij : i ≠ j) (hi : V.get0 xs i ≠ .Z) (hj : V.get0 xs j ≠ .Z)
    (t : multi.T) (ht : t ≠ .Z) {a : multi.T} (ha : Subterm a (.P xs .Z)) :
    mass a < gap (.P xs .Z) t := by
  rw [gap, ite_eq_right ht]; exact kumakuma.SourceCoefficientGap.principal_subterm_mass hij hi hj ha

theorem omega_relative_allcuts (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (hd : domF s = .omega)
    (n : Nat) (hn : RecursiveWF (k + 3) (T.fund s (ofNatD (k + 3) n)))
    (hAbove : ∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
      Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
      Term.allLt (Term.H v (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))))
        (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))) = true)
    (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (hH : Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))))
      (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))) = true := by
  rcases Term.lt_trichotomy Term.wf_bigOmega hv with hlt | he | hlt
  · exact hAbove v hvR hv hlt hH
  · subst v
    exact H_convert_bound_of_subterms k Term.bigOmega _ (Dim_fund _ _ hsD (Dim_ofNatD _ _)) hn
      (kumakuma.SourceCountableInvariant.fund_omega_subterms s hr hd
        ((H_omega_bound_iff_subterms k s hsD hs hr).mp hH) (k + 3) n)
  · rw [kumakuma.CountableTarget.regular_not_below_omega hvR] at hlt; cases hlt

theorem positive_sum_subterm_gap (xs : V multi.T) (b t : multi.T)
    (hb : b ≠ .Z) (hx : 0 < vectorMass xs) (ht : t ≠ .Z)
    {a : multi.T} (ha : Subterm a (.P xs b)) : mass a < gap (.P xs b) t := by
  rw [gap, ite_eq_right ht]; exact kumakuma.SourceCoefficientGap.sum_subterm_mass hb hx ha

end kumakuma.GeneralImageCountableInheritance

import Subsp.Support.Diagonal

/-! The uniform closure invariant `UC`, closed diagonals under `UC`, `UCTree`, and preservation of `UC` by Omega fund. -/

namespace Support.GeneralImageUniformClosure

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageCoefficients Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageCofinalityCoefficients Support.GeneralImageRelativePredecessor
open Support.GeneralImageCriticalZeroDiagonal Support.GeneralImageLimitSupport

universe u

def lift {lam : Nat} (xs : Vec (new.T lam) lam) (j r : Fin lam) : Vec (new.T lam) lam :=
  Vec.ofFn lam (fun l => if r.val < l.val then xs.idx l else if l.val = r.val then xs.idx j else .Z)

theorem lift_idx {lam : Nat} (xs : Vec (new.T lam) lam) (j r l : Fin lam) :
    (lift xs j r).idx l =
      if r.val < l.val then xs.idx l else if l.val = r.val then xs.idx j else .Z := by
  rw [lift, Vec.ofFn_idx]

theorem lift_low {lam : Nat} (xs : Vec (new.T lam) lam) (j r l : Fin lam) (hl : l.val < r.val) :
    (lift xs j r).idx l = .Z := by
  rw [lift_idx, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem lift_at {lam : Nat} (xs : Vec (new.T lam) lam) (j r : Fin lam) :
    (lift xs j r).idx r = xs.idx j := by
  rw [lift_idx, ite_eq_right (by omega), ite_eq_left rfl]

theorem lift_high {lam : Nat} (xs : Vec (new.T lam) lam) (j r l : Fin lam) (hl : r.val < l.val) :
    (lift xs j r).idx l = xs.idx l := by
  rw [lift_idx, ite_eq_left hl]

theorem lift_eq_rplc {lam : Nat} (xs : Vec (new.T lam) lam) (j r : Fin lam) (hjr : j.val < r.val)
    (a : new.T lam) : (lift xs j r).rplc r a = lift (xs.rplc j a) j r := by
  apply vec_ext; intro l
  simp only [vec_rplc_idx, lift_idx]
  by_cases hl : l.val = r.val
  · simp [hl]
  · by_cases hlr : r.val < l.val
    · have hlj : l.val ≠ j.val := by omega
      simp [hl, hlr, hlj]
    · simp [hl, hlr]

def VecUC (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3)) : Prop :=
  ∀ j r : Fin (k + 3), j.val < r.val → r.val ≤ k + 1 → xs.idx j ≠ .Z →
    RecursiveWF (k + 3) (.P (lift xs j r) .Z)

def UC (k : Nat) (s : new.T (k + 3)) : Prop :=
  ∀ xs b, (new.T.P xs b = s ∨ Subterm (new.T.P xs b) s) → VecUC k xs

theorem not_subterm_zero {lam : Nat} (a : new.T lam) : ¬Subterm a (.Z : new.T lam) := by
  intro h
  have := Subterm.size_lt h
  simp only [new.T.size] at this
  omega

theorem subterm_P_cases_aux {lam : Nat} {a c : new.T lam} (hc : Subterm a c) :
    ∀ (ys : Vec (new.T lam) lam) (d : new.T lam), c = .P ys d →
      (∃ j, a = ys.idx j ∨ Subterm a (ys.idx j)) ∨ (a = d ∨ Subterm a d) := by
    induction hc with
    | coordinate zs e i =>
      intro ys d he
      cases he
      exact Or.inl ⟨i, Or.inl rfl⟩
    | tail zs e =>
      intro ys d he
      cases he
      exact Or.inr (Or.inl rfl)
    | trans h₁ h₂ _ ih₂ =>
      intro ys d he
      rcases ih₂ ys d he with ⟨j, hj⟩ | hd
      · refine Or.inl ⟨j, Or.inr ?_⟩
        rcases hj with he' | hs
        · rw [← he']; exact h₁
        · exact Subterm.trans h₁ hs
      · refine Or.inr (Or.inr ?_)
        rcases hd with he' | hs
        · rw [← he']; exact h₁
        · exact Subterm.trans h₁ hs

theorem subterm_P_cases {lam : Nat} {a : new.T lam} {xs : Vec (new.T lam) lam} {b : new.T lam}
    (h : Subterm a (.P xs b)) :
    (∃ j, a = xs.idx j ∨ Subterm a (xs.idx j)) ∨ (a = b ∨ Subterm a b) :=
  subterm_P_cases_aux h xs b rfl

theorem UC_zero (k : Nat) : UC k (.Z : new.T (k + 3)) := by
  intro xs b h
  rcases h with h | h
  · cases h
  · exact False.elim (not_subterm_zero _ h)

theorem UC_P_iff (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3)) :
    UC k (.P xs b) ↔ VecUC k xs ∧ (∀ j, UC k (xs.idx j)) ∧ UC k b := by
  constructor
  · intro h
    refine ⟨h xs b (Or.inl rfl), ?_, ?_⟩
    · intro j ys d hd
      apply h ys d (Or.inr ?_)
      rcases hd with he | hs
      · rw [he]; exact .coordinate xs b j
      · exact .trans hs (.coordinate xs b j)
    · intro ys d hd
      apply h ys d (Or.inr ?_)
      rcases hd with he | hs
      · rw [he]; exact .tail xs b
      · exact .trans hs (.tail xs b)
  · rintro ⟨hv, hc, hb⟩ ys d hd
    rcases hd with he | hs
    · cases he; exact hv
    · rcases subterm_P_cases hs with ⟨j, hj⟩ | hj
      · exact hc j ys d hj
      · exact hb ys d hj

theorem UC.vec {k : Nat} {xs : Vec (new.T (k + 3)) (k + 3)} {b : new.T (k + 3)}
    (h : UC k (.P xs b)) : VecUC k xs := ((UC_P_iff k xs b).mp h).1

theorem UC.coord {k : Nat} {xs : Vec (new.T (k + 3)) (k + 3)} {b : new.T (k + 3)}
    (h : UC k (.P xs b)) (j : Fin (k + 3)) : UC k (xs.idx j) := ((UC_P_iff k xs b).mp h).2.1 j

theorem UC.tail {k : Nat} {xs : Vec (new.T (k + 3)) (k + 3)} {b : new.T (k + 3)}
    (h : UC k (.P xs b)) : UC k b := ((UC_P_iff k xs b).mp h).2.2

theorem virtual_pair_images (k : Nat) (ys : Vec (new.T (k + 3)) (k + 3)) (r : Fin (k + 3))
    (hr0 : 0 < r.val) (hrk : r.val ≤ k + 1) (hlow : ∀ j, j.val < r.val → ys.idx j = .Z)
    (c a : new.T (k + 3))
    (hc : convert (k + 3) (code c) ≠ .zero) (ha : convert (k + 3) (code a) ≠ .zero) :
    ∃ w, convert (k + 3) (code (.P (ys.rplc r c) .Z)) = .psi w (dropOne (convert (k + 3) (code c))) ∧
      convert (k + 3) (code (.P (ys.rplc r a) .Z)) = .psi w (dropOne (convert (k + 3) (code a))) := by
  let xc := ys.rplc r c
  let xa := ys.rplc r a
  let oldArgs := arguments (k + 3) (trim (codes xc))
  let newArgs := arguments (k + 3) (trim (codes xa))
  have hold (j : Fin (k + 3)) : oldArgs[j.val]?.getD .zero = convert (k + 3) (code (xc.idx j)) :=
    converted_coordinate xc j
  have hnew (j : Fin (k + 3)) : newArgs[j.val]?.getD .zero = convert (k + 3) (code (xa.idx j)) :=
    converted_coordinate xa j
  have holdc : oldArgs[r.val]?.getD .zero = convert (k + 3) (code c) := by
    rw [hold r]; simp only [xc, vec_rplc_idx, ↓reduceIte]
  have hnewa : newArgs[r.val]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew r]; simp only [xa, vec_rplc_idx, ↓reduceIte]
  have hzeroOld : ∀ j, j < r.val → oldArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hold ⟨j, by omega⟩]
    simp only [xc, vec_rplc_idx, ite_eq_right (by omega : j ≠ r.val)]
    rw [hlow ⟨j, by omega⟩ hj, code, convert]
  have hzeroNew : ∀ j, j < r.val → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew ⟨j, by omega⟩]
    simp only [xa, vec_rplc_idx, ite_eq_right (by omega : j ≠ r.val)]
    rw [hlow ⟨j, by omega⟩ hj, code, convert]
  have hsame : ∀ j, r.val < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj hjk
    rw [hnew ⟨j, hjk⟩, hold ⟨j, hjk⟩]
    simp only [xa, xc, vec_rplc_idx, ite_eq_right (by omega : j ≠ r.val)]
  have heOld : convert (k + 3) (code (.P xc .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have heNew : convert (k + 3) (code (.P xa .Z)) = lower (k + 1) newArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
    rw [hsame (k + 2) (by omega) (by omega)]
  by_cases hi : r.val = k + 1
  · let h := oldArgs[k + 2]?.getD .zero
    have htopOld : topPair (k + 1) h (convert (k + 3) (code c)) ≠ .zero := by simp [topPair, hc]
    have htopNew : topPair (k + 1) h (convert (k + 3) (code a)) ≠ .zero := by simp [topPair, ha]
    have hcOld : oldArgs[k + 1]?.getD .zero = convert (k + 3) (code c) := by rw [← hi, holdc]
    have hcNew : newArgs[k + 1]?.getD .zero = convert (k + 3) (code a) := by rw [← hi, hnewa]
    refine ⟨.inacc (k + 1) (if h = .zero then .zero else succTerm (dropOne h)), ?_, ?_⟩
    · rw [heOld, hcOld, lower_keep (k + 1) oldArgs _ htopOld (by simpa only [hi] using hzeroOld)]
      simp only [topPair, hc, ↓reduceIte, h]
    · rw [heNew, hcNew, lower_keep (k + 1) newArgs _ htopNew (by simpa only [hi] using hzeroNew)]
      simp only [topPair, ha, ↓reduceIte, h]
  · rw [hsame (k + 1) (by omega) (by omega)] at heNew
    obtain ⟨b, hbOld, hbNew⟩ := lower_selected_step (k + 1) r.val (by omega) oldArgs newArgs _ _ _ hc ha
      holdc hnewa hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega))
    have heO : convert (k + 3) (code (.P xc .Z)) = step r.val b (convert (k + 3) (code c)) :=
      heOld.trans hbOld
    have heN : convert (k + 3) (code (.P xa .Z)) = step r.val b (convert (k + 3) (code a)) :=
      heNew.trans hbNew
    have hr0' : r.val ≠ 0 := by omega
    by_cases hb0 : b = .zero
    · refine ⟨.inacc r.val .zero, ?_, ?_⟩
      · rw [heO]; simp only [step, hb0, hr0', hc, ↓reduceIte]
      · rw [heN]; simp only [step, hb0, hr0', ha, ↓reduceIte]
    · refine ⟨regular r.val b, ?_, ?_⟩
      · rw [heO]; simp only [step, hb0, hc, ↓reduceIte]
      · rw [heN]; simp only [step, hb0, ha, ↓reduceIte]

theorem convert_ne_zero_of_ne {k : Nat} {a : new.T (k + 3)} (ha : a ≠ .Z) :
    convert (k + 3) (code a) ≠ .zero := by
  intro he
  exact ha (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))

theorem virtual_replace [LargeCardinals.{u}] (k : Nat) (ys : Vec (new.T (k + 3)) (k + 3))
    (r : Fin (k + 3)) (hr0 : 0 < r.val) (hrk : r.val ≤ k + 1)
    (hlow : ∀ j, j.val < r.val → ys.idx j = .Z)
    (c a : new.T (k + 3)) (hc0 : c ≠ .Z) (ha0 : a ≠ .Z)
    (hold : RecursiveWF (k + 3) (.P (ys.rplc r c) .Z)) (ha : RecursiveWF (k + 3) a)
    (hrel : ∀ w, convert (k + 3) (code (.P (ys.rplc r c) .Z)) =
        .psi w (dropOne (convert (k + 3) (code c))) →
      Term.isRT w = true → Term.wf w = true →
      Term.allLt (Term.H w (convert (k + 3) (code c))) (convert (k + 3) (code c)) = true →
      Term.allLt (Term.H w (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    RecursiveWF (k + 3) (.P (ys.rplc r a) .Z) := by
  have hc := convert_ne_zero_of_ne hc0
  have ha' := convert_ne_zero_of_ne ha0
  obtain ⟨w, heOld, heNew⟩ := virtual_pair_images k ys r hr0 hrk hlow c a hc ha'
  have hcoords : ∀ j, RecursiveWF (k + 3) ((ys.rplc r c).idx j) := by
    rw [RecursiveWF] at hold; exact hold.1
  have hcw : RecursiveWF (k + 3) c := by
    have := hcoords r; simpa only [vec_rplc_idx, ↓reduceIte] using this
  have hOldWf := heOld ▸ hold.wf
  have hp := (Term.wf_psi_iff _ _).mp hOldWf
  have hWhole := (Term.wf_psi_iff _ _).mp (psi_wf_of_dropOne w _ hcw.wf hOldWf)
  have hA := hrel w heOld hp.1 hp.2.1 hWhole.2.2.2
  rw [RecursiveWF]
  refine ⟨?_, recursive_zero _ _, ?_⟩
  · intro j
    rw [vec_rplc_idx]
    split
    · exact ha
    · have := hcoords j
      rename_i hne
      rwa [vec_rplc_idx, ite_eq_right hne] at this
  · change Term.wf (convert (k + 3) (code (.P (ys.rplc r a) .Z))) = true
    rw [heNew]
    exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ha.wf, H_drop_bound w _ ha.wf hA⟩

theorem rplc_self {lam : Nat} (xs : Vec (new.T lam) lam) (i : Fin lam) : xs.rplc i (xs.idx i) = xs := by
  apply vec_ext; intro j
  rw [vec_rplc_idx]
  split
  · rename_i h; rw [Fin.ext h]
  · rfl

theorem lift_rplc_self {lam : Nat} (xs : Vec (new.T lam) lam) (j r : Fin lam) :
    (lift xs j r).rplc r (xs.idx j) = lift xs j r := by
  have h := rplc_self (lift xs j r) r
  rw [lift_at] at h
  exact h

theorem lift_congr {lam : Nat} (xs ys : Vec (new.T lam) lam) (j j' r : Fin lam)
    (hj : xs.idx j = ys.idx j') (hhigh : ∀ l : Fin lam, r.val < l.val → xs.idx l = ys.idx l) :
    lift xs j r = lift ys j' r := by
  apply vec_ext; intro l
  rw [lift_idx, lift_idx]
  by_cases hl : r.val < l.val
  · simp only [hl, ↓reduceIte]; exact hhigh l hl
  · simp only [hl, ↓reduceIte, hj]

theorem rplc_idx_ne {lam : Nat} (xs : Vec (new.T lam) lam) (i j : Fin lam) (a : new.T lam)
    (h : j.val ≠ i.val) : (xs.rplc i a).idx j = xs.idx j := by
  rw [vec_rplc_idx, ite_eq_right h]

theorem rplc_idx_eq {lam : Nat} (xs : Vec (new.T lam) lam) (i : Fin lam) (a : new.T lam) :
    (xs.rplc i a).idx i = a := by
  rw [vec_rplc_idx, ite_eq_left rfl]

theorem VecUC_replace_min [LargeCardinals.{u}] (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3))
    (i : Fin (k + 3)) (hlow : ∀ j, j.val < i.val → xs.idx j = .Z) (huc : VecUC k xs)
    (hc0 : xs.idx i ≠ .Z) (a : new.T (k + 3)) (ha : RecursiveWF (k + 3) a)
    (hrel : ∀ r : Fin (k + 3), i.val < r.val → r.val ≤ k + 1 → a ≠ .Z → ∀ w,
      convert (k + 3) (code (.P (lift xs i r) .Z)) =
        .psi w (dropOne (convert (k + 3) (code (xs.idx i)))) →
      Term.isRT w = true → Term.wf w = true →
      Term.allLt (Term.H w (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true →
      Term.allLt (Term.H w (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    VecUC k (xs.rplc i a) := by
  intro j r hjr hrk hj0
  by_cases hji : j.val = i.val
  · have heJ : j = i := Fin.ext hji
    subst heJ
    rw [rplc_idx_eq] at hj0
    rw [← lift_eq_rplc xs j r hjr a]
    have hold := huc j r hjr hrk hc0
    rw [← lift_rplc_self xs j r] at hold
    apply virtual_replace k (lift xs j r) r (by omega) hrk (fun l hl => lift_low xs j r l hl)
      (xs.idx j) a hc0 hj0 hold ha
    intro w hw
    rw [lift_rplc_self] at hw
    exact hrel r hjr hrk hj0 w hw
  · by_cases hjl : j.val < i.val
    · rw [rplc_idx_ne xs i j a hji, hlow j hjl] at hj0
      exact absurd rfl hj0
    · rw [rplc_idx_ne xs i j a hji] at hj0
      have he : lift (xs.rplc i a) j r = lift xs j r :=
        lift_congr _ _ j j r (rplc_idx_ne xs i j a hji)
          (fun l hl => rplc_idx_ne xs i l a (by omega))
      rw [he]
      exact huc j r hjr hrk hj0

theorem VecUC_insert (k : Nat) (ys : Vec (new.T (k + 3)) (k + 3)) (j0 : Fin (k + 3))
    (hlow : ∀ j, j.val < j0.val → ys.idx j = .Z) (huc : VecUC k ys)
    (t : new.T (k + 3))
    (htop : t ≠ .Z → ∀ r : Fin (k + 3), j0.val < r.val → r.val ≤ k + 1 →
      RecursiveWF (k + 3) (.P (lift (ys.rplc j0 t) j0 r) .Z)) :
    VecUC k (ys.rplc j0 t) := by
  intro j r hjr hrk hj0
  by_cases hji : j.val = j0.val
  · have heJ : j = j0 := Fin.ext hji
    subst heJ
    rw [rplc_idx_eq] at hj0
    exact htop hj0 r hjr hrk
  · by_cases hjl : j.val < j0.val
    · rw [rplc_idx_ne ys j0 j t hji, hlow j hjl] at hj0
      exact absurd rfl hj0
    · rw [rplc_idx_ne ys j0 j t hji] at hj0
      have he : lift (ys.rplc j0 t) j r = lift ys j r :=
        lift_congr _ _ j j r (rplc_idx_ne ys j0 j t hji)
          (fun l hl => rplc_idx_ne ys j0 l t (by omega))
      rw [he]
      exact huc j r hjr hrk hj0

theorem UC_succ {k : Nat} : ∀ (s : new.T (k + 3)), UC k (Support.SourceSuccessor.succ s) → UC k s
  | .Z, _ => UC_zero k
  | .P xs b, h => by
    have h' : UC k (.P xs (Support.SourceSuccessor.succ b)) := h
    rw [UC_P_iff] at h' ⊢
    exact ⟨h'.1, h'.2.1, UC_succ b h'.2.2⟩
termination_by s => new.T.size s
decreasing_by exact new.T.add_size_lt_P _ _

theorem UC_oplus_principal {k : Nat} (w : Vec (new.T (k + 3)) (k + 3)) (t : new.T (k + 3))
    (hw : VecUC k w) (hc : ∀ j, UC k (w.idx j)) (ht : UC k t) :
    UC k (new.T.oplus (.P w .Z) t) := by
  change UC k (.P w (new.T.oplus .Z t))
  rw [UC_P_iff]
  exact ⟨hw, hc, ht⟩

theorem UC_mul {k : Nat} (w : Vec (new.T (k + 3)) (k + 3)) (hw : UC k (.P w .Z)) :
    ∀ t : new.T (k + 3), UC k (new.T.mul (.P w .Z) t)
  | .Z => UC_zero k
  | .P ys add => by
    change UC k (new.T.oplus (.P w .Z) (new.T.mul (.P w .Z) add))
    exact UC_oplus_principal w _ hw.vec (fun j => hw.coord j) (UC_mul w hw add)
termination_by t => new.T.size t
decreasing_by exact new.T.add_size_lt_P _ _

end Support.GeneralImageUniformClosure

namespace Support.GeneralImageUniformDiagonal

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageLimitSupport Support.GeneralImageRelativePredecessor
open Support.GeneralImageContextBoundDiagonal Support.GeneralImageHighestContextDiagonal
open Support.GeneralImageSharedLowerContext
open Support.GeneralImageSharedContext Support.GeneralImageSharedTopPair
open Support.GeneralImageHighestDiagonal Support.GeneralImageClosedDiagonal
open Support.GeneralImageParametricCut Support.GeneralImageLabelCut
open Support.GeneralImageOmegaSpine Support.GeneralImageMiddleSums
open Support.GeneralImageCofinalityBounds Support.GeneralImageLimitBranches
open Support.GeneralImageDominatedCoefficients Support.GeneralImageCoefficients
open Support.GeneralImageRegularLimit
open Support.GeneralImageMiddleRecursion Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceSuccessor Support.SourceRecursiveDescending Support.SourceFundOrder
open Support.GeneralImageCriticalDiagonal Support.GeneralImageStrictHighestDiagonal
open Support.GeneralImageDiagonalPartition Support.GeneralImageHigherDiagonal
open Support.GeneralImageCountableObstructions
open Support.GeneralImageCountableInheritance Support.GeneralImageUniformClosure
open Support.GeneralImageZeroFund Support.GeneralImageCountableLayers Support.GeneralImageCountableRecursion
open Support.GeneralImageOmegaCoefficients Support.SourceFundGap Support.GeneralImageUpperOmega

universe u

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

theorem critical_virtual_closed [LargeCardinals.{u}] (k m : Nat) (hm0 : 0 < m) (hmk : m ≤ k + 1)
    (ys q : Vec (new.T (k + 3)) (k + 3))
    (hq : new.T.domVecMinIdx q = some (⟨m + 1, by omega⟩, .one))
    (b : new.T (k + 3)) (hb : q.idx ⟨m + 1, by omega⟩ = Support.SourceSuccessor.succ b)
    (hp : ys.idx ⟨m + 1, by omega⟩ = b)
    (hh : ∀ j, m + 1 < j.val → ys.idx j = q.idx j)
    (hcr : Recursive (ys.idx ⟨m, by omega⟩))
    (hd : new.T.dom (ys.idx ⟨m, by omega⟩) = .Omega q)
    (hs : RecursiveWF (k + 3) (.P ys .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (ys.idx ⟨m, by omega⟩))))
        (convert (k + 3) (code (ys.idx ⟨m, by omega⟩))) = true := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (ys.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hc0 : ys.idx ⟨m, by omega⟩ ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  have hmid0 : convert (k + 3) (code (ys.idx ⟨m, by omega⟩)) ≠ .zero := convert_ne_zero_of_ne hc0
  suffices hsuff : ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.wf (.psi cut (dropOne (convert (k + 3) (code (ys.idx ⟨m, by omega⟩))))) = true by
    obtain ⟨cut, hc, hw⟩ := hsuff
    rw [Omega_image_drop k _ hcr (hcoords _) hd] at hw
    exact ⟨cut, hc, ((Term.wf_psi_iff _ _).mp hw).2.2.2⟩
  by_cases hmk' : m ≤ k
  · have hqr := Omega_label_recursive k _ hcr hd
    have hqw := Omega_label_recursiveWF k _ (hcoords _) hd
    obtain ⟨a, ha, haw, heF0, hc, hpred⟩ := regular_lower_label_cut_context k m hmk' q hq hqr hqw
    let base := q.rplc ⟨m + 1, by omega⟩ b
    have hzBase : ∀ j, j.val < m + 1 → base.idx j = .Z := by
      intro j hj
      simp only [base, vec_rplc_idx, ite_eq_right (by change j.val ≠ m + 1; omega)]
      exact (Support.DimensionCut.minIdx_spec q hq).2.2 j hj
    have hf0 : new.T.fund (.P q .Z) .Z = .P base .Z := by
      rw [fund_regular_bound q (by omega) hq, hb, fund_succ]
      congr 1; apply vec_ext; intro j
      simp only [vec_rplc_idx, base]
      split
      · simpa only [base, vec_rplc_idx] using (hzBase j (by omega)).symm
      · rfl
    have heBase : convert (k + 3) (code (.P base .Z)) = (if a = .zero then Term.one else a) := by
      rwa [hf0] at heF0
    have hsame : ∀ j, m < j.val → ys.idx j = base.idx j := by
      intro j hj; simp only [base, vec_rplc_idx]
      split
      · rename_i heJ
        have he : j = ⟨m + 1, by omega⟩ := Fin.ext heJ
        rw [he]; exact hp
      · rename_i hne; exact hh j (by omega)
    have heLower := principal_shared_lower_image k m hmk' base ys hzBase hsame a ha heBase
    rw [lower_succ, converted_coordinate ys ⟨m, by omega⟩] at heLower
    have hTop : Term.wf (step m a (convert (k + 3) (code (ys.idx ⟨m, by omega⟩)))) = true :=
      lower_context_wf m _ _ (step_shape _ ha) (heLower ▸ hs.wf)
    have heStep : step m a (convert (k + 3) (code (ys.idx ⟨m, by omega⟩))) =
        .psi (layerCut m a) (dropOne (convert (k + 3) (code (ys.idx ⟨m, by omega⟩)))) := by
      by_cases ha0 : a = .zero <;>
        simp only [step, layerCut, regular, ha0, hmid0, Nat.ne_of_gt hm0, ↓reduceIte]
    rw [heStep] at hTop
    exact ⟨layerCut m a, hc, hTop⟩
  · have heM : m = k + 1 := by omega
    subst m
    have heQ : q = lastVec (k + 2) (Support.SourceSuccessor.succ b) := by
      apply vec_ext; intro j; rw [lastVec_idx]
      by_cases hj : j.val = k + 2
      · rw [ite_eq_left hj]
        have heJ : j = ⟨k + 2, by omega⟩ := Fin.ext hj
        rw [heJ]; exact hb
      · rw [ite_eq_right hj]
        exact (Support.DimensionCut.minIdx_spec q hq).2.2 j
          (by change j.val < k + 1 + 1; have := j.isLt; omega)
    have hbWf : RecursiveWF (k + 3) b := hp ▸ hcoords ⟨k + 2, by omega⟩
    have hLabelWf := topNode_recursiveWF k (Support.SourceSuccessor.succ b)
      ((recursive_succ_iff _ _).mpr hbWf)
    let cut := pairCut (k + 1) (convert (k + 3) (code b))
    have hc : CutFund k (.P q .Z) cut := by
      rw [heQ]; exact highest_regular_cutFund_at k b hLabelWf
    have hTop : Term.wf (topPair (k + 1) (convert (k + 3) (code b))
        (convert (k + 3) (code (ys.idx ⟨k + 1, by omega⟩)))) = true := by
      have hw := hs.wf
      rw [convert_principal, principal_as_layers, converted_coordinate ys ⟨k + 2, by omega⟩,
        converted_coordinate ys ⟨k + 1, by omega⟩, hp] at hw
      exact lower_context_wf (k + 1) _ _ (topPair_context _ _ _) hw
    have heTop : topPair (k + 1) (convert (k + 3) (code b))
        (convert (k + 3) (code (ys.idx ⟨k + 1, by omega⟩))) =
        .psi cut (dropOne (convert (k + 3) (code (ys.idx ⟨k + 1, by omega⟩)))) := by
      simp only [topPair, hmid0, ↓reduceIte]; rfl
    rw [heTop] at hTop
    exact ⟨cut, hc, hTop⟩

theorem diagonal_closed [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (huc : VecUC k xs) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true := by
  have hchild := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hd : new.T.dom (.P xs .Z) = .omega := by simp only [new.T.dom, ↓reduceIte, hm, hdiag]
  have hib := closed_diagonal_selector_bound k xs q i hm hdiag hr hs
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchild; cases hchild
  obtain ⟨⟨j, hj⟩, hjPos, hq⟩ := domOmega_regular (xs.idx i) hchild
  cases j with
  | zero => change 0 < 0 at hjPos; omega
  | succ m =>
    have hmk : m ≤ k + 1 := by omega
    by_cases hmi : m < i.val
    · exact higher_source_closed k m hmk xs q i hmi hib hm hq
        (higher_selector_zero_label_bound k m hmk xs q i hmi hm hq hd).1 hr hs
    · by_cases hie : i.val = m
      · have heI : i = ⟨m, by omega⟩ := Fin.ext hie
        rw [heI] at hm ⊢
        by_cases hml : m ≤ k
        · exact context_bound_diagonal_source_closed k m hml xs q ⟨m, by omega⟩ (Nat.le_refl _) hm hq
            (consecutive_diagonal_context_bound k m hmk xs q hm hq hdiag) hr hs
        · have heM : m = k + 1 := by omega
          subst heM
          exact highest_consecutive_source_closed k xs q hm hq hdiag hr hs
      · have him : i.val < m := by omega
        obtain ⟨b, hb⟩ := dom_one_succ (q.idx ⟨m + 1, by omega⟩)
          ((Support.DimensionCut.minIdx_spec q hq).1.symm)
        by_cases hcrit : xs.idx ⟨m + 1, by omega⟩ = b ∧ ∀ j, m + 1 < j.val → xs.idx j = q.idx j
        · have hv := huc i ⟨m, by omega⟩ him hmk hc0
          have hres := critical_virtual_closed k m (by omega) hmk (lift xs i ⟨m, by omega⟩) q hq b hb
            (by rw [lift_high xs i ⟨m, by omega⟩ ⟨m + 1, by omega⟩ (by simp)]; exact hcrit.1)
            (fun j hj => by rw [lift_high xs i ⟨m, by omega⟩ j (by simp; omega)]; exact hcrit.2 j hj)
            (by rw [lift_at]; exact hcr) (by rw [lift_at]; exact hchild) hv
          simpa only [lift_at] using hres
        · by_cases hml : m ≤ k
          · exact context_bound_diagonal_source_closed k m hml xs q i (by omega) hm hq
              (noncritical_diagonal_context_bound k m hmk xs q i hm hq b hb hdiag hcrit) hr hs
          · have heM : m = k + 1 := by omega
            subst m
            obtain ⟨c, heQ⟩ := highest_regular_label_shape k q hq
            have heBC : b = c := by
              have hsc : Support.SourceSuccessor.succ b = Support.SourceSuccessor.succ c := by
                rw [← hb, heQ, lastVec_idx, ite_eq_left rfl]
              simpa only [Support.SourceSuccessor.fund_succ] using
                congrArg (fun s => new.T.fund s .Z) hsc
            subst c
            rcases highest_diagonal_parent_bound k xs q b heQ hdiag with hl | he
            · exact strict_highest_diagonal_source_closed k xs q i hm b heQ hl hr hs
            · exact False.elim (hcrit ⟨new.T_eq_sound _ _ he, by intro j hj; have := j.isLt; omega⟩)

inductive UCTree (k : Nat) : new.T (k + 3) → Prop
  | successor (xs : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
      (hx : xs.idx ⟨0, by omega⟩ = Support.SourceSuccessor.succ b) : UCTree k (.P xs .Z)
  | closedDiagonal (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
      (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
      (cut : Term) (hc : CutFund k (.P q .Z) cut)
      (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (xs.idx i))))
        (convert (k + 3) (code (xs.idx i))) = true) : UCTree k (.P xs .Z)
  | inherit (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
      (hm : new.T.domVecMinIdx xs = some (i, .omega)) (hc : UCTree k (xs.idx i)) :
      UCTree k (.P xs .Z)
  | tail (xs : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
      (hb : b ≠ .Z) (hc : UCTree k b) : UCTree k (.P xs b)

theorem UCTree.domain (k : Nat) {s : new.T (k + 3)} (hc : UCTree k s) : new.T.dom s = .omega := by
  induction hc with
  | successor xs b hx =>
    have hd : new.T.dom (xs.idx ⟨0, by omega⟩) = .one := by rw [hx]; exact Support.SourceSuccessor.dom_succ b
    have hm := minIdx_first xs (by rw [hd]; intro he; cases he)
    simp only [new.T.dom, ↓reduceIte, hm, hd]
  | closedDiagonal xs q i hm hdiag => simp only [new.T.dom, ↓reduceIte, hm, hdiag]
  | inherit xs i hm => simp only [new.T.dom, ↓reduceIte, hm]
  | tail xs b hb _ ih => rw [new.T.dom, ite_eq_right hb]; exact ih

theorem ucTree_fund_invariant [LargeCardinals.{u}] (k : Nat) {s : new.T (k + 3)}
    (hc : UCTree k s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (n : Nat) :
    RecursiveWF (k + 3) (new.T.fund s (new.T.ofNat n)) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))) →
          DominatedCoefficient k v s z) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))))
          (convert (k + 3) (code (new.T.fund s (new.T.ofNat n)))) = true) := by
  cases n with
  | zero =>
    obtain ⟨hn, hcoef, hrel⟩ := zero_fund_invariant k s hr hs
    refine ⟨hn, ?_, hrel⟩
    intro v hvR hv hOmega z hz
    exact UpdatedCoefficient.dominated k v s .Z hs (hcoef v hvR hv hOmega z hz)
  | succ n =>
    induction hc generalizing n with
    | successor xs b hx =>
      obtain ⟨hn, hrel⟩ := fund_zero_successor_relative k xs b hx hs (n + 1)
      refine ⟨hn, ?_, hrel⟩
      intro v hvR hv _ z hz
      apply UpdatedCoefficient.dominated k v _ (new.T.ofNat (n + 1)) hs
      rw [fund_zero_coordinate_successor k xs b _ hx] at hz
      have hp := H_mul_principal_support (k + 3) (xs.rplc ⟨0, by omega⟩ b) (n + 1) v hz
      rcases zero_coordinate_relative_support k v hvR hv xs b hx hs hp with ho | ⟨he, ho⟩
      · exact Or.inr (Or.inl ho)
      · have hbW : RecursiveWF (k + 3) b := by
          have hw := hs; rw [RecursiveWF] at hw
          exact (recursive_succ_iff _ _).mp (hx ▸ hw.1 ⟨0, by omega⟩)
        refine Or.inr (Or.inr ⟨xs.idx ⟨0, by omega⟩, Subterm.coordinate xs .Z _, ?_, ?_, ?_⟩)
        · rw [hx, Support.SourceSuccessor.fund_succ]; exact hbW
        · rw [hx]; exact ho
        · rw [hx, Support.SourceSuccessor.fund_succ]; exact he
    | closedDiagonal xs q i hm hdiag cut hc hSource =>
      have hn := closed_diagonal_recursiveWF k xs q i hm hdiag cut hc hSource hr hs (n + 1)
      refine ⟨hn, ?_, ?_⟩
      · intro v hvR hv hOmega
        exact closed_diagonal_dominated_support k xs q i hm hdiag cut hc hSource hr hs (n + 1) v hvR hv hOmega
      · intro v hvR hv hH
        exact closed_diagonal_relative k xs q i hm hdiag cut hc hSource hr hs (n + 1) v hvR hv hH
    | inherit xs i hm hc ih =>
      have hd := (Support.DimensionCut.minIdx_spec xs hm).1.symm
      have hlow := (Support.DimensionCut.minIdx_spec xs hm).2.2
      have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
      have hchildR : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
      obtain ⟨hnChild, hcChild, hrelChild⟩ := ih hchildR (hcoords i) n
      have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
      have hf : new.T.fund (.P xs .Z) (new.T.ofNat (n + 1)) =
          .P (xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat (n + 1)))) .Z := by
        simp only [new.T.fund, ↓reduceIte, hm, GetElem.getElem]
      have hn : RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat (n + 1))) := by
        rw [hf]
        by_cases hib : i.val ≤ k + 1
        · exact principal_replace_relative_recursiveWF k xs i hib hlow hs _
            hnChild hc0 (drop_image_of_omega k _ (hcoords i) hd) hrelChild
        · have hi : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
          have he : xs = lastVec (k + 2) (xs.idx i) := by
            apply vec_ext; intro j; rw [lastVec_idx]
            by_cases hj : j.val = k + 2
            · rw [ite_eq_left hj]
              have hji : j = i := Fin.ext (by rw [hi]; simpa using hj); rw [hji]
            · rw [ite_eq_right hj]; exact hlow j (by have := j.isLt; rw [hi]; simp only [Fin.val_last]; omega)
          have heR := congrArg (fun us => us.rplc i (new.T.fund (xs.idx i) (new.T.ofNat (n + 1)))) he
          rw [hi, Support.SourceOmegaHighest.lastVec_replace_last] at heR
          have heR' : xs.rplc i (new.T.fund (xs.idx i) (new.T.ofNat (n + 1))) =
              lastVec (k + 2) (new.T.fund (xs.idx i) (new.T.ofNat (n + 1))) := by simpa only [hi] using heR
          rw [heR']; exact topNode_recursiveWF k _ hnChild
      refine ⟨hn, ?_, ?_⟩
      · intro v hvR hv hOmega
        exact inherited_omega_dominated_support k xs i hm hs (n + 1) (by omega) hn v hvR hv hOmega
          (hcChild v hvR hv hOmega)
      · apply omega_relative_allcuts k _ hr hs (UCTree.domain k (.inherit xs i hm hc)) (n + 1) hn
        intro v hvR hv hOmega hH
        exact inherited_omega_dominated_relative_above k xs i hm hs (n + 1) (by omega) hn v hvR hv hOmega
          (hcChild v hvR hv hOmega) hH
    | tail xs b hb hc ih =>
      have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      obtain ⟨hnB, hcB, _⟩ := ih hbr hbw n
      have hd := UCTree.domain k (.tail xs b hb hc)
      have hn := fund_nonzero_tail_recursiveWF k xs b (new.T.ofNat (n + 1)) hs hb hnB
      have hcoef (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
          (hOmega : Term.lt Term.bigOmega v = true) :
          ∀ z, z ∈ Term.H v (convert (k + 3) (code (new.T.fund (.P xs b) (new.T.ofNat (n + 1))))) →
            DominatedCoefficient k v (.P xs b) z := by
        intro z hz
        rw [new.T.fund, ite_eq_right hb, code, convert] at hz
        rcases H_assemble_support v _ _ hz with hz | hz
        · exact Or.inr (Or.inl (by simp only [code, convert]; exact H_assemble_left v _ _ hz))
        · rcases hcB v hvR hv hOmega z hz with he | ho | ⟨a, ha, ho, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl; simp only [code, convert]; exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), ?_, he⟩)
            simp only [code, convert]
            exact ho.elim (fun h => Or.inl (H_assemble_right v _ _ h)) (fun h => Or.inr (H_assemble_right v _ _ h))
      refine ⟨hn, hcoef, ?_⟩
      apply omega_relative_allcuts k _ hr hs hd (n + 1) hn
      intro v hvR hv hOmega hH
      have hsZ : convert (k + 3) (code (.P xs b)) ≠ .zero := by
        intro he
        have heS : (.P xs b : new.T (k + 3)) = .Z :=
          code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
        cases heS
      have hnZ : convert (k + 3) (code (new.T.fund (.P xs b) (new.T.ofNat (n + 1)))) ≠ .zero := by
        intro he
        exact omega_fund_nat_ne_zero k _ hd (n + 1) (by omega)
          (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
      exact closed_of_dominated_coefficients k v _ _ hs hn (omega_image_head_ne_one k _ hs hd) hsZ hnZ
        (fun a ha => positive_sum_subterm_gap xs b _ hb
          (Support.SourceCountableInvariant.omega_head_mass_pos xs b hr hd) (by intro he; cases he) ha)
        (hcoef v hvR hv hOmega) hH

theorem tree_of_UC [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s)
    (hd : new.T.dom s = .omega) : UCTree k s := by
  cases s with
  | Z => simp only [new.T.dom] at hd; cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [new.T.dom, ↓reduceIte, hm] at hd; cases hd
      | some sel =>
        obtain ⟨i, d⟩ := sel
        have hchild := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        cases d with
        | zero => exact False.elim ((Support.DimensionCut.minIdx_spec xs hm).2.1 rfl)
        | one =>
          have hi : i.val = 0 := by
            by_cases hi : i.val = 0
            · exact hi
            · simp only [new.T.dom, ↓reduceIte, hm, hi] at hd; cases hd
          have he : i = ⟨0, by omega⟩ := Fin.ext hi
          rw [he] at hchild
          obtain ⟨c, hc⟩ := dom_one_succ (xs.idx ⟨0, by omega⟩) hchild
          exact .successor xs c hc
        | omega =>
          have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
          have hcw : RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1 i
          exact .inherit xs i hm (tree_of_UC k (xs.idx i) hcr hcw (huc.coord i) hchild)
        | Omega q =>
          have hdiag : Vec.lt xs q := by
            by_cases hl : Vec.lt xs q
            · exact hl
            · simp only [new.T.dom, ↓reduceIte, hm, hl] at hd; cases hd
          obtain ⟨cut, hc, hSource⟩ := diagonal_closed k xs q i hm hdiag hr hs huc.vec
          exact .closedDiagonal xs q i hm hdiag cut hc hSource
    · have hdb : new.T.dom b = .omega := by rwa [new.T.dom, ite_eq_right hb] at hd
      have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      exact .tail xs b hb (tree_of_UC k b hbr hbw huc.tail hdb)
termination_by new.T.size s
decreasing_by
  all_goals simp_all only [new.T.size]
  all_goals first | (have hx := Vec.idx_size_lt xs i; omega) | omega

end Support.GeneralImageUniformDiagonal

namespace Support.GeneralImageUniformContext

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageLimitSupport Support.GeneralImageRelativePredecessor
open Support.GeneralImageContextBoundDiagonal Support.GeneralImageSharedLowerContext
open Support.GeneralImageSharedContext Support.GeneralImageRegularDiagonal
open Support.GeneralImageRegularLimit Support.GeneralImageHeadCuts
open Support.BinaryTranslation Support.TargetArithmetic Support.SourceFundOrder
open Support.GeneralImageUniformClosure Support.GeneralImageSharedTopPair

universe u

def upperVec {lam : Nat} (xs : Vec (new.T lam) lam) (r : Fin lam) : Vec (new.T lam) lam :=
  Vec.ofFn lam (fun l => if r.val < l.val then xs.idx l else .Z)

theorem upperVec_idx {lam : Nat} (xs : Vec (new.T lam) lam) (r l : Fin lam) :
    (upperVec xs r).idx l = if r.val < l.val then xs.idx l else .Z := by
  rw [upperVec, Vec.ofFn_idx]

theorem upperVec_low {lam : Nat} (xs : Vec (new.T lam) lam) (r l : Fin lam) (hl : l.val ≤ r.val) :
    (upperVec xs r).idx l = .Z := by
  rw [upperVec_idx, ite_eq_right (by omega)]

theorem upperVec_high {lam : Nat} (xs : Vec (new.T lam) lam) (r l : Fin lam) (hl : r.val < l.val) :
    (upperVec xs r).idx l = xs.idx l := by
  rw [upperVec_idx, ite_eq_left hl]

theorem lift_eq_upper_rplc {lam : Nat} (xs : Vec (new.T lam) lam) (j r : Fin lam) :
    lift xs j r = (upperVec xs r).rplc r (xs.idx j) := by
  apply vec_ext; intro l
  rw [lift_idx, vec_rplc_idx, upperVec_idx]
  by_cases hl : l.val = r.val
  · simp [hl]
  · by_cases hlr : r.val < l.val
    · simp [hl, hlr]
    · simp [hl, hlr]

theorem compareVec_lt_witness {lam m : Nat} (xs ys : Vec (new.T lam) m)
    (h : new.compareVec xs ys = .lt) :
    ∃ p : Fin m, new.compareT (xs.idx p) (ys.idx p) = .lt ∧
      ∀ j : Fin m, p.val < j.val → xs.idx j = ys.idx j := by
  induction xs with
  | nil => cases ys; simp [new.compareVec] at h
  | snoc m xs x ih =>
    cases ys with
    | snoc _ ys y =>
      cases hc : new.compareT x y with
      | lt =>
        refine ⟨Fin.last m, by simpa only [vec_snoc_idx_last] using hc, ?_⟩
        intro j hj; have := j.isLt; simp only [Fin.val_last] at hj; omega
      | gt => simp only [new.compareVec, hc] at h; cases h
      | eq =>
        have hxy := new.T_eq_sound x y hc
        have hlow : new.compareVec xs ys = .lt := by simpa only [new.compareVec, hc] using h
        obtain ⟨p, hp, hhigh⟩ := ih ys hlow
        refine ⟨p.castSucc, by simpa only [vec_snoc_idx_cast] using hp, ?_⟩
        intro j hj
        by_cases hjm : j.val < m
        · have he : j = (⟨j.val, hjm⟩ : Fin m).castSucc := Fin.ext rfl
          rw [he, vec_snoc_idx_cast, vec_snoc_idx_cast]
          exact hhigh ⟨j.val, hjm⟩ (by simpa only [Fin.val_castSucc] using hj)
        · have he : j = Fin.last m := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
          rw [he, vec_snoc_idx_last, vec_snoc_idx_last, hxy]

theorem upper_le_of_not_lt {lam : Nat} (xs q : Vec (new.T lam) lam) (r : Fin lam)
    (hnd : ¬Vec.lt xs q) :
    new.T.le (.P (upperVec q r) .Z) (.P (upperVec xs r) .Z) := by
  rcases Vec_total xs q with hl | hl | he
  · exact False.elim (hnd hl)
  · obtain ⟨p, hp, hhigh⟩ := compareVec_lt_witness q xs hl
    by_cases hpr : r.val < p.val
    · apply Or.inl
      change new.compareT (.P (upperVec q r) .Z) (.P (upperVec xs r) .Z) = .lt
      simp only [new.compareT]
      rw [compareVec_of_lt_at _ _ p (by rwa [upperVec_high _ _ _ hpr, upperVec_high _ _ _ hpr])
        (fun j hj => by rw [upperVec_high _ _ _ (by omega), upperVec_high _ _ _ (by omega)];
                        exact hhigh j hj)]
    · apply Or.inr
      have heq : upperVec q r = upperVec xs r := by
        apply vec_ext; intro l
        rw [upperVec_idx, upperVec_idx]
        by_cases hl : r.val < l.val
        · simp only [hl, ↓reduceIte]; exact hhigh l (by omega)
        · simp only [hl, ↓reduceIte]
      rw [heq]; exact new.T_refl _
  · subst he; exact Or.inr (new.T_refl _)

theorem upper_context [LargeCardinals.{u}] (k r : Nat) (hr : r ≤ k) (xs : Vec (new.T (k + 3)) (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ a, Above r a ∧ Term.wf a = true ∧
      RecursiveWF (k + 3) (.P (upperVec xs ⟨r, by omega⟩) .Z) ∧
      convert (k + 3) (code (.P (upperVec xs ⟨r, by omega⟩) .Z)) =
        (if a = .zero then Term.one else a) ∧
      convert (k + 3) (code (.P xs .Z)) = lower (r + 1) (arguments (k + 3) (trim (codes xs))) a ∧
      ∀ t : new.T (k + 3), t ≠ .Z →
        convert (k + 3) (code (.P ((upperVec xs ⟨r, by omega⟩).rplc ⟨r, by omega⟩ t) .Z)) =
          step r a (convert (k + 3) (code t)) := by
  let base := upperVec xs ⟨r, by omega⟩
  have hzero : ∀ i, i.val < r + 1 → base.idx i = .Z :=
    fun i hi => upperVec_low xs _ i (by change i.val ≤ r; omega)
  obtain ⟨a, ha, heBase, heInsert⟩ := principal_insertion_context k r hr base hzero
  have hsame : ∀ j, r < j.val → xs.idx j = base.idx j :=
    fun j hj => (upperVec_high xs _ j (by change r < j.val; exact hj)).symm
  have heX := principal_shared_lower_image k r hr base xs hzero hsame a ha heBase
  have hctx : Context (r + 1) a := by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr ⟨above_principal ha, by omega⟩
  have haw : Term.wf a = true := lower_context_wf (r + 1) _ a hctx (heX ▸ hs.wf)
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hbaseW : RecursiveWF (k + 3) (.P base .Z) := by
    rw [RecursiveWF]
    refine ⟨fun j => ?_, recursive_zero _ _, ?_⟩
    · change RecursiveWF (k + 3) ((upperVec xs ⟨r, by omega⟩).idx j)
      rw [upperVec_idx]
      split
      · exact hcoords j
      · exact recursive_zero _ _
    · change Term.wf (convert (k + 3) (code (.P base .Z))) = true
      rw [heBase]
      split
      · exact Term.wf_one
      · exact haw
  exact ⟨a, ha, haw, hbaseW, heBase, heX, heInsert⟩

theorem step_layerCut (r : Nat) (hr : r ≠ 0) (a y : Term) (hy : y ≠ .zero) :
    step r a y = .psi (layerCut r a) (dropOne y) := by
  by_cases ha : a = .zero <;> simp [step, layerCut, regular, ha, hy, hr]

theorem step_lt_inacc (l n : Nat) (hl : l < n) (h y z : Term) (hctx : Above l h)
    (hh : Term.lt h (.inacc n z) = true) : Term.lt (step l h y) (.inacc n z) = true := by
  by_cases h0 : h = .zero
  · subst h
    by_cases hl0 : l = 0
    · subst l
      simp [step, Term.lt, Term.fT, Term.bigOmega, hl]
    · by_cases hy : y = .zero
      · simp [step, hl0, hy, Term.lt]
      · simp [step, hl0, hy, Term.lt, Term.fT, hl, show ¬n < l by omega, show l ≤ n by omega]
  · by_cases hy : y = .zero
    · simpa [step, h0, hy] using hh
    · have hp := above_principal (hctx.resolve_left h0)
      have hsucc : Term.lt (succTerm h) (.inacc n z) = true := by
        rw [succ_principal hp, Term.lt]
        exact hh
      simp only [step, h0, hy, ↓reduceIte]
      simp [Term.lt, regular, Term.fT, hl, show ¬n < l by omega, show l ≤ n by omega, hsucc]

theorem lower_lt_inacc (j n : Nat) (hj : j ≤ n) (xs : List Term) (h z : Term) (hctx : Context j h)
    (hh : Term.lt h (.inacc n z) = true) : Term.lt (lower j xs h) (.inacc n z) = true := by
  induction j generalizing h with
  | zero => exact hh
  | succ j ih =>
    rw [lower_succ]
    exact ih (by omega) _ (step_shape _ (context_above hctx))
      (step_lt_inacc j n (by omega) h _ z (context_above hctx) hh)

theorem step_lt_layerCut (r : Nat) (a y : Term) (ha : Above r a) :
    Term.lt (step r a y) (layerCut r a) = true := by
  by_cases ha0 : a = .zero
  · subst a
    by_cases hr0 : r = 0
    · subst r; simp [step, layerCut, Term.lt, Term.fT, Term.bigOmega]
    · by_cases hy : y = .zero
      · simp [step, layerCut, hr0, hy, Term.lt]
      · simp [step, layerCut, hr0, hy, Term.lt, Term.fT]
  · have hf := ha.resolve_left ha0
    have hp := above_principal hf
    by_cases hy : y = .zero
    · simp only [step, ha0, hy, ↓reduceIte, layerCut]
      change Term.lt a (regular r a) = true
      rw [context_lt_regular hf hp]; simp [Term.le]
    · simp only [step, ha0, hy, ↓reduceIte, layerCut]
      simp [Term.lt, regular, Term.fT]

theorem principal_lt_layerCut (k r : Nat) (xs : Vec (new.T (k + 3)) (k + 3)) (a : Term)
    (ha : Above r a)
    (heX : convert (k + 3) (code (.P xs .Z)) = lower (r + 1) (arguments (k + 3) (trim (codes xs))) a) :
    Term.lt (convert (k + 3) (code (.P xs .Z))) (layerCut r a) = true := by
  rw [heX, lower_succ]
  exact lower_lt_inacc r r (Nat.le_refl _) _ _ _ (step_shape _ ha) (step_lt_layerCut r a _ ha)

theorem principal_top_image (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3)) :
    convert (k + 3) (code (.P xs .Z)) = lower (k + 1) (arguments (k + 3) (trim (codes xs)))
      (topPair (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))
        (convert (k + 3) (code (xs.idx ⟨k + 1, by omega⟩)))) := by
  rw [convert_principal, principal_as_layers, converted_coordinate xs ⟨k + 2, by omega⟩,
    converted_coordinate xs ⟨k + 1, by omega⟩]

theorem topPair_lt_pairCut [LargeCardinals.{u}] (n : Nat) (h m : Term) (hh : Term.wf h = true) :
    Term.lt (topPair n h m) (pairCut n h) = true := by
  by_cases hm0 : m = .zero
  · by_cases hh0 : h = .zero
    · simp [topPair, pairCut, hm0, hh0, Term.lt]
    · simp only [topPair, pairCut, hm0, hh0, ↓reduceIte, inacc_same_lt]
      rw [lt_succTerm_eq_le (dropOne_wf hh) (dropOne_wf hh)]
      simp [Term.le]
  · simp [topPair, pairCut, hm0, Term.lt, Term.fT]

theorem principal_lt_pairCut [LargeCardinals.{u}] (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    Term.lt (convert (k + 3) (code (.P xs .Z)))
      (pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))) = true := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  rw [principal_top_image]
  exact lower_lt_inacc (k + 1) (k + 1) (Nat.le_refl _) _ _ _ (topPair_context _ _ _)
    (topPair_lt_pairCut _ _ _ (hcoords _).wf)

theorem term_lt_of_lt_of_le [LargeCardinals.{u}] {a b c : Term}
    (ha : Term.wf a = true) (hb : Term.wf b = true) (hc : Term.wf c = true)
    (hab : Term.lt a b = true) (hbc : Term.le b c = true) : Term.lt a c = true := by
  rcases (Term.le_iff_eq_or_lt _ _).mp hbc with he | hl
  · rw [← he]; exact hab
  · exact lemma_6_1.{u}.2.1 _ _ _ ha hb hc hab hl

theorem uc_image_le_of_le [LargeCardinals.{u}] (k : Nat) (s t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t) (h : new.T.le s t) :
    Term.le (convert (k + 3) (code s)) (convert (k + 3) (code t)) = true := by
  rcases h with hl | he
  · have := (convert_order k s t hs ht).mp hl
    simp [Term.le, this]
  · rw [new.T_eq_sound _ _ he]; simp [Term.le]

theorem lift_image_layer [LargeCardinals.{u}] (k r : Nat) (hr0 : 0 < r) (hr : r ≤ k)
    (xs : Vec (new.T (k + 3)) (k + 3)) (j : Fin (k + 3)) (hj : xs.idx j ≠ .Z) (a : Term)
    (heIns : ∀ t : new.T (k + 3), t ≠ .Z →
      convert (k + 3) (code (.P ((upperVec xs ⟨r, by omega⟩).rplc ⟨r, by omega⟩ t) .Z)) =
        step r a (convert (k + 3) (code t))) :
    convert (k + 3) (code (.P (lift xs j ⟨r, by omega⟩) .Z)) =
      .psi (layerCut r a) (dropOne (convert (k + 3) (code (xs.idx j)))) := by
  rw [lift_eq_upper_rplc, heIns _ hj, step_layerCut r (by omega) a _ (convert_ne_zero_of_ne hj)]

theorem lift_image_top (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3)) (j : Fin (k + 3))
    (hj : xs.idx j ≠ .Z) :
    convert (k + 3) (code (.P (lift xs j ⟨k + 1, by omega⟩) .Z)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩))))
        (dropOne (convert (k + 3) (code (xs.idx j)))) := by
  have hy := convert_ne_zero_of_ne hj
  rw [principal_top_image, lift_high xs j _ _ (by simp), lift_at]
  rw [lower_keep (k + 1) _ _ (by simp [topPair, hy]) (fun l hl => by
    rw [converted_coordinate (lift xs j ⟨k + 1, by omega⟩) ⟨l, by omega⟩,
      lift_low xs j _ _ (by simp; omega), code, convert])]
  simp [topPair, pairCut, hy]

theorem nondiagonal_virtual_cut_above_label [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hnd : ¬Vec.lt xs q)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (r : Fin (k + 3)) (hir : i.val < r.val)
    (hrk : r.val ≤ k + 1) (w : Term)
    (hw : convert (k + 3) (code (.P (lift xs i r) .Z)) =
      .psi w (dropOne (convert (k + 3) (code (xs.idx i))))) :
    Term.lt Term.bigOmega w = true ∧ Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hchild := (Support.DimensionCut.minIdx_spec xs hm).1.symm
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchild; cases hchild
  have hqW := Support.GeneralImageCofinalityBounds.Omega_label_recursiveWF k _ (hcoords i) hchild
  have hqcoords : ∀ j, RecursiveWF (k + 3) (q.idx j) := by rw [RecursiveWF] at hqW; exact hqW.1
  by_cases hrk' : r.val ≤ k
  · obtain ⟨a, ha, haw, hbase, heBase, heX, heIns⟩ := upper_context k r.val hrk' xs hs
    obtain ⟨aq, haq, haqw, hbaseQ, heBaseQ, heQ, _⟩ := upper_context k r.val hrk' q hqW
    have hrEq : (⟨r.val, by omega⟩ : Fin (k + 3)) = r := Fin.ext rfl
    have hlift := lift_image_layer k r.val (by omega) hrk' xs i hc0 a heIns
    rw [hrEq, hw] at hlift
    have hwEq : w = layerCut r.val a := (Term.psi.inj hlift).1
    subst hwEq
    refine ⟨layerCut_above_Omega r.val (by omega) a, ?_⟩
    have hq1 := principal_lt_layerCut k r.val q aq haq heQ
    have hle := uc_image_le_of_le k _ _ hbaseQ hbase (upper_le_of_not_lt xs q _ hnd)
    rw [heBaseQ, heBase] at hle
    have hcut := (layerCut_comparable_of_erased_le r.val r.val (Nat.le_refl _) aq a haq ha haqw haw hle).1
    exact term_lt_of_lt_of_le hqW.wf (layerCut_wf r.val aq haq haqw) (layerCut_wf r.val a ha haw) hq1 hcut
  · have hrK : r.val = k + 1 := by omega
    have hrEq : r = ⟨k + 1, by omega⟩ := Fin.ext hrK
    rw [hrEq, lift_image_top k xs i hc0] at hw
    have hwEq := (Term.psi.inj hw).1
    subst hwEq
    refine ⟨by simp [pairCut, Term.bigOmega, Term.lt], ?_⟩
    have hq1 := principal_lt_pairCut k q hqW

    have htop : new.T.le (q.idx ⟨k + 2, by omega⟩) (xs.idx ⟨k + 2, by omega⟩) := by
      rcases Vec_total xs q with hl | hl | he
      · exact False.elim (hnd hl)
      · obtain ⟨p, hp, hhigh⟩ := compareVec_lt_witness q xs hl
        by_cases hpk : p.val = k + 2
        · have heP : p = ⟨k + 2, by omega⟩ := Fin.ext hpk
          rw [heP] at hp; exact Or.inl hp
        · rw [hhigh ⟨k + 2, by omega⟩ (by have := p.isLt; simp; omega)]
          exact Or.inr (new.T_refl _)
      · rw [he]; exact Or.inr (new.T_refl _)
    have hpair := (Support.GeneralImageHighestContextDiagonal.pairCut_image_comparable k _ _
      (hqcoords _) (hcoords _) htop).1
    have hcutQ := Support.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hqcoords ⟨k + 2, by omega⟩)
    have hcutX := Support.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hcoords ⟨k + 2, by omega⟩)
    exact term_lt_of_lt_of_le hqW.wf hcutQ hcutX hq1 hpair

end Support.GeneralImageUniformContext

namespace Support.GeneralImageUniformPreservation

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageCoefficients Support.SourceRecursiveDescending Support.SourceFundOrder
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageZeroFund
open Support.GeneralImageUniformClosure Support.GeneralImageUniformContext

universe u

set_option maxRecDepth 10000

def TopOK (k : Nat) (q : Vec (new.T (k + 3)) (k + 3)) (t : new.T (k + 3)) : Prop :=
  t ≠ .Z → ∀ (m : Nat) (hml : m + 1 < k + 3),
    new.T.domVecMinIdx q = some (⟨m + 1, hml⟩, .one) →
    ∀ r : Fin (k + 3), m < r.val → r.val ≤ k + 1 →
      RecursiveWF (k + 3) (.P (lift (q.rplc ⟨m, by omega⟩ t) ⟨m, by omega⟩ r) .Z)

theorem fund_tail_eq {lam : Nat} (xs : Vec (new.T lam) lam) (b t : new.T lam) (hb : b ≠ .Z) :
    new.T.fund (.P xs b) t = .P xs (new.T.fund b t) := by
  rw [new.T.fund]; simp only [hb, ↓reduceIte]

theorem fund_nondiagonal_Omega_eq {lam : Nat} (xs : Vec (new.T lam) lam) (i : Fin lam)
    (q : Vec (new.T lam) lam) (hm : new.T.domVecMinIdx xs = some (i, .Omega q))
    (hnd : ¬Vec.lt xs q) (t : new.T lam) :
    new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
  rw [new.T.fund]
  simp only [↓reduceIte, hm]
  rw [ite_eq_right hnd]
  rfl

theorem fund_omega_child_eq {lam : Nat} (xs : Vec (new.T lam) lam) (i : Fin lam)
    (hm : new.T.domVecMinIdx xs = some (i, .omega)) (t : new.T lam) :
    new.T.fund (.P xs .Z) t = .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z := by
  rw [new.T.fund]
  simp only [↓reduceIte, hm]
  rfl

theorem VecUC_replace_zero_fund [LargeCardinals.{u}] (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3))
    (i : Fin (k + 3)) (hlow : ∀ j, j.val < i.val → xs.idx j = .Z) (huc : VecUC k xs)
    (hc0 : xs.idx i ≠ .Z) (hcr : Recursive (xs.idx i)) (hcw : RecursiveWF (k + 3) (xs.idx i)) :
    VecUC k (xs.rplc i (new.T.fund (xs.idx i) .Z)) := by
  have hz := zero_fund_invariant k (xs.idx i) hcr hcw
  exact VecUC_replace_min k xs i hlow huc hc0 _ hz.1
    (fun _ _ _ _ w _ hwR hww hH => hz.2.2 w hwR hww hH)

theorem UC_fund_Omega [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom s = .Omega q)
    (κ : Term) (hκ : CutFund k (.P q .Z) κ)
    (t : new.T (k + 3)) (htw : RecursiveWF (k + 3) t) (htuc : UC k t)
    (hHt : Term.allLt (Term.H κ (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true)
    (htop : TopOK k q t) : UC k (new.T.fund s t) := by
  cases heS : s with
  | Z => rw [heS] at hd; simp only [new.T.dom] at hd; cases hd
  | P xs b =>
    rw [heS] at hr hs huc hd
    have hcoordsR : ∀ j, Recursive (xs.idx j) := by rw [Recursive] at hr; exact hr.1
    have hcoordsW : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
    by_cases hb : b = .Z
    · subst b
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [new.T.dom, ↓reduceIte, hm] at hd; cases hd
      | some sel =>
        obtain ⟨i, d⟩ := sel
        have hspec := Support.DimensionCut.minIdx_spec xs hm
        have hchild := hspec.1.symm
        have hlow := hspec.2.2
        cases d with
        | zero => exact False.elim (hspec.2.1 rfl)
        | omega => simp only [new.T.dom, ↓reduceIte, hm] at hd; cases hd
        | one =>
          by_cases hi0 : i.val = 0
          · simp only [new.T.dom, ↓reduceIte, hm, hi0] at hd; cases hd
          · have hq : xs = q := by
              simp only [new.T.dom, ↓reduceIte, hm, hi0] at hd
              exact new.Dom.Omega.inj hd
            subst hq
            obtain ⟨m, hmEq⟩ : ∃ m, i.val = m + 1 := ⟨i.val - 1, by omega⟩
            have hml : m + 1 < k + 3 := by have := i.isLt; omega
            have heI : i = ⟨m + 1, hml⟩ := Fin.ext hmEq
            subst heI
            have hc0 : xs.idx ⟨m + 1, hml⟩ ≠ .Z := by
              intro he; rw [he, new.T.dom] at hchild; cases hchild
            obtain ⟨c₀, hc⟩ := dom_one_succ _ hchild
            rw [fund_regular_bound xs hml hm t]
            have hfz : new.T.fund (xs.idx ⟨m + 1, hml⟩) .Z = c₀ := by
              rw [hc, Support.SourceSuccessor.fund_succ]
            rw [hfz]
            have hU1 := VecUC_replace_zero_fund k xs ⟨m + 1, hml⟩ hlow huc.vec hc0
              (hcoordsR _) (hcoordsW _)
            rw [hfz] at hU1
            rw [UC_P_iff]
            refine ⟨?_, ?_, UC_zero k⟩
            · apply VecUC_insert k (xs.rplc ⟨m + 1, hml⟩ c₀) ⟨m, by omega⟩
                (fun j hj => by
                  change j.val < m at hj
                  rw [rplc_idx_ne _ _ _ _ (show j.val ≠ m + 1 by omega)]
                  exact hlow j (show j.val < m + 1 by omega))
                hU1 t
              intro ht0 r hmr hrk
              change m < r.val at hmr
              have he : lift ((xs.rplc ⟨m + 1, hml⟩ c₀).rplc ⟨m, by omega⟩ t) ⟨m, by omega⟩ r =
                  lift (xs.rplc ⟨m, by omega⟩ t) ⟨m, by omega⟩ r := by
                apply lift_congr _ _ _ _ r (by rw [rplc_idx_eq, rplc_idx_eq])
                intro l hl
                rw [rplc_idx_ne _ _ _ _ (show l.val ≠ m by omega),
                  rplc_idx_ne _ _ _ _ (show l.val ≠ m + 1 by omega),
                  rplc_idx_ne _ _ _ _ (show l.val ≠ m by omega)]
              rw [he]
              exact htop ht0 m hml hm r hmr hrk
            · intro j
              rw [vec_rplc_idx]
              split
              · exact htuc
              · rw [vec_rplc_idx]
                split
                · have hcu := huc.coord ⟨m + 1, hml⟩
                  rw [hc] at hcu
                  exact UC_succ c₀ hcu
                · exact huc.coord j
        | Omega q' =>
          by_cases hdiag : Vec.lt xs q'
          · simp only [new.T.dom, ↓reduceIte, hm, hdiag] at hd; cases hd
          · have hq : q' = q := by
              simp only [new.T.dom, ↓reduceIte, hm, hdiag] at hd
              exact new.Dom.Omega.inj hd
            subst hq
            have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchild; cases hchild
            rw [fund_nondiagonal_Omega_eq xs i q' hm hdiag t]
            have hInv := Omega_fund_at_label_cut_invariant k (xs.idx i) (hcoordsR i) (hcoordsW i)
              hchild κ hκ t htw hHt
            rw [UC_P_iff]
            refine ⟨?_, ?_, UC_zero k⟩
            · apply VecUC_replace_min k xs i hlow huc.vec hc0 _ hInv.1
              intro r hir hrk _ w hw hwR hww hH
              obtain ⟨hOmega, hAbove⟩ :=
                nondiagonal_virtual_cut_above_label k xs q' i hm hdiag hs r hir hrk w hw
              exact (hInv.2 w hwR hww hOmega hAbove).2 hH
            · intro j
              rw [vec_rplc_idx]
              split
              · rename_i hji
                have heJ : j = i := Fin.ext hji
                subst heJ
                exact UC_fund_Omega k (xs.idx j) (hcoordsR j) (hcoordsW j) (huc.coord j) hchild
                  κ hκ t htw htuc hHt htop
              · exact huc.coord j
    · have hdb : new.T.dom b = .Omega q := by rwa [new.T.dom, ite_eq_right hb] at hd
      have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      rw [fund_tail_eq xs b t hb, UC_P_iff]
      exact ⟨huc.vec, huc.coord, UC_fund_Omega k b hbr hbw huc.tail hdb κ hκ t htw htuc hHt htop⟩
termination_by new.T.size s
decreasing_by
  all_goals rw [heS]
  all_goals first
    | exact new.T.idx_size_lt_P _ _ _
    | exact new.T.add_size_lt_P _ _

end Support.GeneralImageUniformPreservation

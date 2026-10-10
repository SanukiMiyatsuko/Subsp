import Subsp.multi.kuma.Diagonal

/-! The uniform closure invariant `UC`, closed diagonals under `UC`, `UCTree`, and preservation of
`UC` by Omega fund (the `multi` version of `Subsp/Support/Uniform.lean`). -/

namespace kumakuma.GeneralImageUniformClosure

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageCoefficients kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageCofinalityCoefficients kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageCriticalZeroDiagonal kumakuma.GeneralImageLimitSupport

/-- The virtual vector moving coordinate `j` of `xs` to slot `r` and erasing everything below. -/
def lift (xs : V multi.T) (j r : Nat) : V multi.T :=
  vOf (fun l => if r < l then V.get0 xs l else if l = r then V.get0 xs j else .Z) xs.length

theorem lift_length (xs : V multi.T) (j r : Nat) : (lift xs j r).length = xs.length :=
  vOf_length _ _

theorem get0_lift (xs : V multi.T) (j r l : Nat) (hr : r < xs.length) :
    V.get0 (lift xs j r) l =
      if r < l then V.get0 xs l else if l = r then V.get0 xs j else .Z := by
  rw [lift, get0_vOf]
  by_cases hl : l < xs.length
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl, ite_eq_left (by omega), V.get0_ge xs l (by omega)]

theorem lift_low (xs : V multi.T) (j r l : Nat) (hr : r < xs.length) (hl : l < r) :
    V.get0 (lift xs j r) l = .Z := by
  rw [get0_lift xs j r l hr, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem lift_at (xs : V multi.T) (j r : Nat) (hr : r < xs.length) :
    V.get0 (lift xs j r) r = V.get0 xs j := by
  rw [get0_lift xs j r r hr, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]

theorem lift_high (xs : V multi.T) (j r l : Nat) (hr : r < xs.length) (hl : r < l) :
    V.get0 (lift xs j r) l = V.get0 xs l := by
  rw [get0_lift xs j r l hr, ite_eq_left hl]

theorem Dim_lift {d : Nat} {xs : V multi.T} (hsD : Dim d (.P xs .Z)) (j r : Nat) (hr : r < xs.length) :
    Dim d (.P (lift xs j r) .Z) := by
  refine Dim_P (by rw [lift_length]; exact hsD.length) (fun l => ?_) (Dim_Z d)
  rw [get0_lift xs j r l hr]
  split
  · exact hsD.coord l
  · split
    · exact hsD.coord j
    · exact Dim_Z d

theorem lift_eq_rplc (xs : V multi.T) (j r : Nat) (hjr : j < r) (hr : r < xs.length)
    (a : multi.T) : V.set (lift xs j r) r a = lift (V.set xs j a) j r := by
  have hr' : r < (V.set xs j a).length := by rw [V.length_set]; exact hr
  apply V.eq_of_get0 _ _ (by rw [V.length_set, lift_length, lift_length, V.length_set])
  intro l
  rw [V.get0_set _ r a l (by rw [lift_length]; exact hr), get0_lift _ _ _ l hr', get0_lift _ _ _ l hr]
  by_cases hl : l = r
  · rw [hl, ite_eq_left rfl, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl,
      V.get0_set_same xs j a (by omega)]
  · rw [ite_eq_right hl]
    by_cases hlr : r < l
    · rw [ite_eq_left hlr, ite_eq_left hlr, V.get0_set_ne xs j a l (by omega)]
    · rw [ite_eq_right hlr, ite_eq_right hlr, ite_eq_right hl, ite_eq_right hl]

def VecUC (k : Nat) (xs : V multi.T) : Prop :=
  ∀ j r : Nat, j < r → r ≤ k + 1 → V.get0 xs j ≠ .Z →
    RecursiveWF (k + 3) (.P (lift xs j r) .Z)

def UC (k : Nat) (s : multi.T) : Prop :=
  ∀ xs b, (multi.T.P xs b = s ∨ Subterm (multi.T.P xs b) s) → VecUC k xs

theorem not_subterm_zero (a : multi.T) : ¬Subterm a .Z := by
  intro h
  have := Subterm.size_lt h
  simp only [multi.T.size] at this
  omega

theorem subterm_P_cases_aux {a c : multi.T} (hc : Subterm a c) :
    ∀ (ys : V multi.T) (d : multi.T), c = .P ys d →
      (∃ j, a = V.get0 ys j ∨ Subterm a (V.get0 ys j)) ∨ (a = d ∨ Subterm a d) := by
  induction hc with
  | coordinate zs e i =>
    intro ys d he
    cases he
    exact Or.inl ⟨i, Or.inl rfl⟩
  | tail zs e =>
    intro ys d he
    cases he
    exact Or.inr (Or.inl rfl)
  | trans h₁ _ _ ih₂ =>
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

theorem subterm_P_cases {a : multi.T} {xs : V multi.T} {b : multi.T}
    (h : Subterm a (.P xs b)) :
    (∃ j, a = V.get0 xs j ∨ Subterm a (V.get0 xs j)) ∨ (a = b ∨ Subterm a b) :=
  subterm_P_cases_aux h xs b rfl

theorem UC_zero (k : Nat) : UC k .Z := by
  intro xs b h
  rcases h with h | h
  · cases h
  · exact False.elim (not_subterm_zero _ h)

theorem UC_P_iff (k : Nat) (xs : V multi.T) (b : multi.T) :
    UC k (.P xs b) ↔ VecUC k xs ∧ (∀ j, UC k (V.get0 xs j)) ∧ UC k b := by
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

theorem UC.vec {k : Nat} {xs : V multi.T} {b : multi.T}
    (h : UC k (.P xs b)) : VecUC k xs := ((UC_P_iff k xs b).mp h).1

theorem UC.coord {k : Nat} {xs : V multi.T} {b : multi.T}
    (h : UC k (.P xs b)) (j : Nat) : UC k (V.get0 xs j) := ((UC_P_iff k xs b).mp h).2.1 j

theorem UC.tail {k : Nat} {xs : V multi.T} {b : multi.T}
    (h : UC k (.P xs b)) : UC k b := ((UC_P_iff k xs b).mp h).2.2

theorem virtual_pair_images (k : Nat) (ys : V multi.T) (hl : ys.length = k + 3) (r : Nat)
    (hr0 : 0 < r) (hrk : r ≤ k + 1) (hlow : ∀ j, j < r → V.get0 ys j = .Z)
    (c a : multi.T)
    (hc : convert (k + 3) (code c) ≠ .zero) (ha : convert (k + 3) (code a) ≠ .zero) :
    ∃ w, convert (k + 3) (code (.P (V.set ys r c) .Z)) = .psi w (dropOne (convert (k + 3) (code c))) ∧
      convert (k + 3) (code (.P (V.set ys r a) .Z)) = .psi w (dropOne (convert (k + 3) (code a))) := by
  have hrl : r < ys.length := by omega
  let xc := V.set ys r c
  let xa := V.set ys r a
  let oldArgs := arguments (k + 3) (trim (codes xc))
  let newArgs := arguments (k + 3) (trim (codes xa))
  have hold (j : Nat) : oldArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xc j)) :=
    converted_coordinate xc j
  have hnew (j : Nat) : newArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xa j)) :=
    converted_coordinate xa j
  have holdc : oldArgs[r]?.getD .zero = convert (k + 3) (code c) := by
    rw [hold r]; show convert (k + 3) (code (V.get0 (V.set ys r c) r)) = _
    rw [V.get0_set_same ys r c hrl]
  have hnewa : newArgs[r]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew r]; show convert (k + 3) (code (V.get0 (V.set ys r a) r)) = _
    rw [V.get0_set_same ys r a hrl]
  have hzeroOld : ∀ j, j < r → oldArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hold j]; show convert (k + 3) (code (V.get0 (V.set ys r c) j)) = _
    rw [V.get0_set_ne ys r c j (by omega), hlow j hj, convert_Z]
  have hzeroNew : ∀ j, j < r → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew j]; show convert (k + 3) (code (V.get0 (V.set ys r a) j)) = _
    rw [V.get0_set_ne ys r a j (by omega), hlow j hj, convert_Z]
  have hsame : ∀ j, r < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj _
    rw [hnew j, hold j]
    show convert (k + 3) (code (V.get0 (V.set ys r a) j)) =
      convert (k + 3) (code (V.get0 (V.set ys r c) j))
    rw [V.get0_set_ne ys r a j (by omega), V.get0_set_ne ys r c j (by omega)]
  have heOld : convert (k + 3) (code (.P xc .Z)) = lower (k + 1) oldArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
  have heNew : convert (k + 3) (code (.P xa .Z)) = lower (k + 1) newArgs
      (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero)) := by
    rw [convert_principal, principal_as_layers]
    rw [hsame (k + 2) (by omega) (by omega)]
  by_cases hi : r = k + 1
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
    obtain ⟨b, hbOld, hbNew⟩ := lower_selected_step (k + 1) r (by omega) oldArgs newArgs _ _ _ hc ha
      holdc hnewa hzeroOld hzeroNew (fun j hj hjk => hsame j hj (by omega))
    have heO : convert (k + 3) (code (.P xc .Z)) = step r b (convert (k + 3) (code c)) :=
      heOld.trans hbOld
    have heN : convert (k + 3) (code (.P xa .Z)) = step r b (convert (k + 3) (code a)) :=
      heNew.trans hbNew
    have hr0' : r ≠ 0 := by omega
    by_cases hb0 : b = .zero
    · refine ⟨.inacc r .zero, ?_, ?_⟩
      · rw [heO]; simp only [step, hb0, hr0', hc, ↓reduceIte]
      · rw [heN]; simp only [step, hb0, hr0', ha, ↓reduceIte]
    · refine ⟨regular r b, ?_, ?_⟩
      · rw [heO]; simp only [step, hb0, hc, ↓reduceIte]
      · rw [heN]; simp only [step, hb0, ha, ↓reduceIte]

theorem convert_ne_zero_of_ne {k : Nat} {a : multi.T} (ha : a ≠ .Z) :
    convert (k + 3) (code a) ≠ .zero :=
  fun he => ha ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 he)

theorem virtual_replace (k : Nat) (ys : V multi.T) (hl : ys.length = k + 3)
    (r : Nat) (hr0 : 0 < r) (hrk : r ≤ k + 1)
    (hlow : ∀ j, j < r → V.get0 ys j = .Z)
    (c a : multi.T) (hc0 : c ≠ .Z) (ha0 : a ≠ .Z)
    (hold : RecursiveWF (k + 3) (.P (V.set ys r c) .Z)) (ha : RecursiveWF (k + 3) a)
    (hrel : ∀ w, convert (k + 3) (code (.P (V.set ys r c) .Z)) =
        .psi w (dropOne (convert (k + 3) (code c))) →
      Term.isRT w = true → Term.wf w = true →
      Term.allLt (Term.H w (convert (k + 3) (code c))) (convert (k + 3) (code c)) = true →
      Term.allLt (Term.H w (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    RecursiveWF (k + 3) (.P (V.set ys r a) .Z) := by
  have hrl : r < ys.length := by omega
  have hc := convert_ne_zero_of_ne (k := k) hc0
  have ha' := convert_ne_zero_of_ne (k := k) ha0
  obtain ⟨w, heOld, heNew⟩ := virtual_pair_images k ys hl r hr0 hrk hlow c a hc ha'
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 (V.set ys r c) j) := (RecursiveWF_P.1 hold).1
  have hcw : RecursiveWF (k + 3) c := by
    have := hcoords r; rwa [V.get0_set_same ys r c hrl] at this
  have hOldWf := heOld ▸ hold.wf
  have hp := (Term.wf_psi_iff _ _).mp hOldWf
  have hWhole := (Term.wf_psi_iff _ _).mp (psi_wf_of_dropOne w _ hcw.wf hOldWf)
  have hA := hrel w heOld hp.1 hp.2.1 hWhole.2.2.2
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
  · intro j
    rw [V.get0_set ys r a j hrl]
    split
    · exact ha
    · rename_i hne
      have := hcoords j
      rwa [V.get0_set_ne ys r c j hne] at this
  · rw [heNew]
    exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ha.wf, H_drop_bound w _ ha.wf hA⟩

theorem lift_rplc_self (xs : V multi.T) (j r : Nat) (hr : r < xs.length) :
    V.set (lift xs j r) r (V.get0 xs j) = lift xs j r :=
  set_eq_self _ _ _ (lift_at xs j r hr)

theorem lift_congr (xs ys : V multi.T) (j j' r : Nat)
    (hj : V.get0 xs j = V.get0 ys j') (hhigh : ∀ l, r < l → V.get0 xs l = V.get0 ys l)
    (hlen : xs.length = ys.length) (hr : r < xs.length) :
    lift xs j r = lift ys j' r := by
  apply V.eq_of_get0 _ _ (by rw [lift_length, lift_length, hlen])
  intro l
  rw [get0_lift xs j r l hr, get0_lift ys j' r l (by rw [← hlen]; exact hr)]
  by_cases hl : r < l
  · rw [ite_eq_left hl, ite_eq_left hl]; exact hhigh l hl
  · rw [ite_eq_right hl, ite_eq_right hl, hj]

theorem VecUC_replace_min (k : Nat) (xs : V multi.T) (hxl : xs.length = k + 3)
    (i : Nat) (hlow : ∀ j, j < i → V.get0 xs j = .Z) (huc : VecUC k xs)
    (hc0 : V.get0 xs i ≠ .Z) (a : multi.T) (ha : RecursiveWF (k + 3) a)
    (hrel : ∀ r : Nat, i < r → r ≤ k + 1 → a ≠ .Z → ∀ w,
      convert (k + 3) (code (.P (lift xs i r) .Z)) =
        .psi w (dropOne (convert (k + 3) (code (V.get0 xs i)))) →
      Term.isRT w = true → Term.wf w = true →
      Term.allLt (Term.H w (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true →
      Term.allLt (Term.H w (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    VecUC k (V.set xs i a) := by
  intro j r hjr hrk hj0
  have hrl : r < xs.length := by omega
  by_cases hji : j = i
  · rw [hji] at hjr hj0 ⊢
    have hil : i < xs.length := by omega
    rw [V.get0_set_same xs i a hil] at hj0
    rw [← lift_eq_rplc xs i r hjr hrl a]
    have hold := huc i r hjr hrk hc0
    rw [← lift_rplc_self xs i r hrl] at hold
    apply virtual_replace k (lift xs i r) (by rw [lift_length]; exact hxl) r (by omega) hrk
      (fun l hl => lift_low xs i r l hrl hl) (V.get0 xs i) a hc0 hj0 hold ha
    intro w hw
    rw [lift_rplc_self xs i r hrl] at hw
    exact hrel r hjr hrk hj0 w hw
  · by_cases hjl : j < i
    · rw [V.get0_set_ne xs i a j hji, hlow j hjl] at hj0
      exact absurd rfl hj0
    · rw [V.get0_set_ne xs i a j hji] at hj0
      have he : lift (V.set xs i a) j r = lift xs j r :=
        lift_congr _ _ j j r (V.get0_set_ne xs i a j hji)
          (fun l hl => V.get0_set_ne xs i a l (by omega)) (V.length_set _ _ _)
          (by rw [V.length_set]; exact hrl)
      rw [he]
      exact huc j r hjr hrk hj0

theorem VecUC_insert (k : Nat) (ys : V multi.T) (hyl : ys.length = k + 3) (j0 : Nat)
    (hlow : ∀ j, j < j0 → V.get0 ys j = .Z) (huc : VecUC k ys)
    (t : multi.T)
    (htop : t ≠ .Z → ∀ r : Nat, j0 < r → r ≤ k + 1 →
      RecursiveWF (k + 3) (.P (lift (V.set ys j0 t) j0 r) .Z)) :
    VecUC k (V.set ys j0 t) := by
  intro j r hjr hrk hj0
  have hrl : r < ys.length := by omega
  by_cases hji : j = j0
  · rw [hji] at hjr hj0 ⊢
    rw [V.get0_set_same ys j0 t (by omega)] at hj0
    exact htop hj0 r hjr hrk
  · by_cases hjl : j < j0
    · rw [V.get0_set_ne ys j0 t j hji, hlow j hjl] at hj0
      exact absurd rfl hj0
    · rw [V.get0_set_ne ys j0 t j hji] at hj0
      have he : lift (V.set ys j0 t) j r = lift ys j r :=
        lift_congr _ _ j j r (V.get0_set_ne ys j0 t j hji)
          (fun l hl => V.get0_set_ne ys j0 t l (by omega)) (V.length_set _ _ _)
          (by rw [V.length_set]; exact hrl)
      rw [he]
      exact huc j r hjr hrk hj0

theorem UC_succ {k : Nat} : ∀ (s : multi.T),
    UC k (kumakuma.SourceSuccessor.succ (k + 3) s) → UC k s
  | .Z, _ => UC_zero k
  | .P xs b, h => by
    have h' : UC k (.P xs (kumakuma.SourceSuccessor.succ (k + 3) b)) := h
    rw [UC_P_iff] at h' ⊢
    exact ⟨h'.1, h'.2.1, UC_succ b h'.2.2⟩
termination_by s => s.size
decreasing_by exact multi.T.size_lt_P_right _ _

theorem UC_oplus_principal {k : Nat} (w : V multi.T) (t : multi.T)
    (hw : VecUC k w) (hc : ∀ j, UC k (V.get0 w j)) (ht : UC k t) :
    UC k (multi.T.P w .Z + t) := by
  change UC k (.P w t)
  rw [UC_P_iff]
  exact ⟨hw, hc, ht⟩

theorem UC_mul {k : Nat} (w : V multi.T) (hw : UC k (.P w .Z)) :
    ∀ t : multi.T, UC k (multi.T.mul (.P w .Z) t)
  | .Z => UC_zero k
  | .P ys add => by
    change UC k (multi.T.P w .Z + multi.T.mul (.P w .Z) add)
    exact UC_oplus_principal w _ hw.vec (fun j => hw.coord j) (UC_mul w hw add)
termination_by t => t.size
decreasing_by exact multi.T.size_lt_P_right _ _

end kumakuma.GeneralImageUniformClosure

namespace kumakuma.GeneralImageUniformDiagonal

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageContextBoundDiagonal kumakuma.GeneralImageHighestContextDiagonal
open kumakuma.GeneralImageSharedLowerContext
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageHighestDiagonal kumakuma.GeneralImageClosedDiagonal
open kumakuma.GeneralImageParametricCut kumakuma.GeneralImageLabelCut
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageMiddleSums
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageLimitBranches
open kumakuma.GeneralImageDominatedCoefficients kumakuma.GeneralImageCoefficients
open kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageMiddleRecursion kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder
open kumakuma.GeneralImageCriticalDiagonal kumakuma.GeneralImageStrictHighestDiagonal
open kumakuma.GeneralImageDiagonalPartition kumakuma.GeneralImageHigherDiagonal
open kumakuma.GeneralImageCountableObstructions
open kumakuma.GeneralImageCountableInheritance kumakuma.GeneralImageUniformClosure
open kumakuma.GeneralImageZeroFund kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageOmegaCoefficients kumakuma.SourceFundGap kumakuma.GeneralImageUpperOmega
open kumakuma.GeneralImageCofinalityCoefficients

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

theorem critical_virtual_closed (k m : Nat) (hm0 : 0 < m)
    (ys q : V multi.T) (hysD : Dim (k + 3) (.P ys .Z))
    (hqf : V.fnz q = some (m + 1)) (hqOne : domF (V.get0 q (m + 1)) = .one)
    (b : multi.T) (hb : V.get0 q (m + 1) = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hp : V.get0 ys (m + 1) = b)
    (hh : ∀ j, m + 1 < j → V.get0 ys j = V.get0 q j)
    (hcr : Recursive (V.get0 ys m))
    (hd : domF (V.get0 ys m) = .Omega q)
    (hs : RecursiveWF (k + 3) (.P ys .Z)) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 ys m))))
        (convert (k + 3) (code (V.get0 ys m))) = true := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 ys j) := (RecursiveWF_P.1 hs).1
  have hcD : Dim (k + 3) (V.get0 ys m) := hysD.coord m
  have hc0 : V.get0 ys m ≠ .Z := by intro he; rw [he, domF_Z] at hd; cases hd
  have hmid0 : convert (k + 3) (code (V.get0 ys m)) ≠ .zero := convert_ne_zero_of_ne hc0
  have hqD := Dim_Omega_label hcD hd
  have hql : m + 1 < q.length := fnz_lt_length hqf
  have hmk : m ≤ k + 1 := by rw [hqD.length] at hql; omega
  have hqlow := (V.fnz_some_spec q _ hqf).2
  suffices hsuff : ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.wf (.psi cut (dropOne (convert (k + 3) (code (V.get0 ys m))))) = true by
    obtain ⟨cut, hc, hw⟩ := hsuff
    rw [Omega_image_drop k _ hcD hcr (hcoords _) hd] at hw
    exact ⟨cut, hc, ((Term.wf_psi_iff _ _).mp hw).2.2.2⟩
  by_cases hmk' : m ≤ k
  · have hqr := Omega_label_recursive _ hcr hd
    have hqw := Omega_label_recursiveWF k _ (hcoords _) hd
    obtain ⟨a, ha, _, heF0, hc, _⟩ := regular_lower_label_cut_context k m hmk' q hqD hqf hqOne hqr hqw
    have hzBase : ∀ j, j < m + 1 → V.get0 (V.set q (m + 1) b) j = .Z := by
      intro j hj
      rw [V.get0_set_ne q _ b j (by omega)]; exact hqlow j hj
    have hf0 : T.fund (.P q .Z) .Z = .P (V.set q (m + 1) b) .Z :=
      regular_fund_zero_shape k m q hqf hqOne b hb
    have heBase : convert (k + 3) (code (.P (V.set q (m + 1) b) .Z)) =
        (if a = .zero then Term.one else a) := by
      rwa [hf0] at heF0
    have hsame : ∀ j, m < j → V.get0 ys j = V.get0 (V.set q (m + 1) b) j := by
      intro j hj
      by_cases hjm : j = m + 1
      · rw [hjm, V.get0_set_same q _ b hql]; exact hp
      · rw [V.get0_set_ne q _ b j hjm]; exact hh j (by omega)
    have heLower := principal_shared_lower_image k m hmk' _ ys hzBase hsame a ha heBase
    rw [lower_succ, converted_coordinate ys m] at heLower
    have hTop : Term.wf (step m a (convert (k + 3) (code (V.get0 ys m)))) = true :=
      lower_context_wf m _ _ (step_shape _ ha) (heLower ▸ hs.wf)
    have heStep : step m a (convert (k + 3) (code (V.get0 ys m))) =
        .psi (layerCut m a) (dropOne (convert (k + 3) (code (V.get0 ys m)))) := by
      by_cases ha0 : a = .zero <;>
        simp only [step, layerCut, regular, ha0, hmid0, Nat.ne_of_gt hm0, ↓reduceIte]
    rw [heStep] at hTop
    exact ⟨layerCut m a, hc, hTop⟩
  · have heM : m = k + 1 := by omega
    subst m
    have hp' : V.get0 ys (k + 2) = b := hp
    have heQ : q = lastVec (k + 2) (kumakuma.SourceSuccessor.succ (k + 3) b) := by
      rw [← hb]; exact lastVec_of_low hqD.length hqlow
    have hbWf : RecursiveWF (k + 3) b := by have := hcoords (k + 2); rwa [hp'] at this
    have hLabelWf := topNode_recursiveWF k (kumakuma.SourceSuccessor.succ (k + 3) b)
      ((recursive_succ_iff _ _ _).mpr hbWf)
    have hc : CutFund k (.P q .Z) (pairCut (k + 1) (convert (k + 3) (code b))) := by
      rw [heQ]; exact highest_regular_cutFund_at k b hLabelWf
    have hTop : Term.wf (topPair (k + 1) (convert (k + 3) (code b))
        (convert (k + 3) (code (V.get0 ys (k + 1))))) = true := by
      have hw := hs.wf
      rw [convert_principal, principal_as_layers, converted_coordinate ys (k + 2),
        converted_coordinate ys (k + 1), hp'] at hw
      exact lower_context_wf (k + 1) _ _ (topPair_context _ _ _) hw
    have heTop : topPair (k + 1) (convert (k + 3) (code b))
        (convert (k + 3) (code (V.get0 ys (k + 1)))) =
        .psi (pairCut (k + 1) (convert (k + 3) (code b)))
          (dropOne (convert (k + 3) (code (V.get0 ys (k + 1))))) := by
      simp only [topPair, hmid0, ↓reduceIte]; rfl
    rw [heTop] at hTop
    exact ⟨_, hc, hTop⟩

theorem diagonal_closed (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (huc : VecUC k xs) :
    ∃ cut, CutFund k (.P q .Z) cut ∧
      Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true := by
  have hd : domF (.P xs .Z) = .omega := domF_diag hf hdq hdiag
  have hib := closed_diagonal_selector_bound k xs q i hsD hf hdq hdiag hr hs
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hxl : xs.length = k + 3 := hsD.length
  have hqD := Dim_Omega_label (hsD.coord i) hdq
  obtain ⟨j, hjPos, hqf, hqOne⟩ := domOmega_regular (V.get0 xs i) hdq
  cases j with
  | zero => omega_c
  | succ m =>
    have hmk : m ≤ k + 1 := by have := fnz_lt_length hqf; rw [hqD.length] at this; omega_c
    by_cases hmi : m < i
    · exact higher_source_closed k m xs q i hmi hib hsD hf hdq hqf hqOne
        (higher_selector_zero_label_bound k m xs q i hmi hsD hf hdq hqf hqOne hd).1 hr hs
    · by_cases hie : i = m
      · rw [← hie] at hqf hqOne
        by_cases hml : i ≤ k
        · exact context_bound_diagonal_source_closed k i hml xs q i (Nat.le_refl _) hsD hf hdq hqf
            hqOne (consecutive_diagonal_context_bound k i xs q hsD hf hdq hqf hqOne hdiag) hr hs
        · have heM : i = k + 1 := by omega_c
          rw [heM] at hf hdq hqf hqOne ⊢
          exact highest_consecutive_source_closed k xs q hsD hf hdq hqf hqOne hdiag hr hs
      · have him : i < m := by omega_c
        obtain ⟨b, hb⟩ := dom_one_succ (V.get0 q (m + 1)) (hqD.coord _) hqOne
        by_cases hcrit : V.get0 xs (m + 1) = b ∧ ∀ j, m + 1 < j → V.get0 xs j = V.get0 q j
        · have hv := huc i m him hmk hc0
          have hmx : m < xs.length := by omega_c
          have hres := critical_virtual_closed k m (by omega_c) (lift xs i m) q
            (Dim_lift hsD i m hmx) hqf hqOne b hb
            (by rw [lift_high xs i m (m + 1) hmx (by omega_c)]; exact hcrit.1)
            (fun j hj => by rw [lift_high xs i m j hmx (by omega_c)]; exact hcrit.2 j hj)
            (by rw [lift_at xs i m hmx]; exact hcr) (by rw [lift_at xs i m hmx]; exact hdq) hv
          rw [lift_at xs i m hmx] at hres
          exact hres
        · by_cases hml : m ≤ k
          · exact context_bound_diagonal_source_closed k m hml xs q i (by omega_c) hsD hf hdq hqf hqOne
              (noncritical_diagonal_context_bound k m xs q i hsD hqD hf hqf hqOne b hb hdiag hcrit) hr hs
          · have heM : m = k + 1 := by omega_c
            subst heM
            obtain ⟨c, heQ⟩ := highest_regular_label_shape k q hqD hqf hqOne
            have heBC : b = c := by
              have hsc : kumakuma.SourceSuccessor.succ (k + 3) b =
                  kumakuma.SourceSuccessor.succ (k + 3) c := by
                rw [← hb, heQ, get0_lastVec, ite_eq_left rfl]
              have := congrArg (fun s => T.fund s .Z) hsc
              simpa only [kumakuma.SourceSuccessor.fund_succ] using this
            subst heBC
            rcases highest_diagonal_parent_bound k xs q b heQ hdiag with hl | he
            · exact strict_highest_diagonal_source_closed k xs q i hsD hf hdq b heQ hl hr hs
            · apply False.elim (hcrit ⟨?_, ?_⟩)
              · have hbD : Dim (k + 3) b := by
                  have h := hqD.coord (k + 1 + 1)
                  rw [hb] at h
                  exact kumakuma.GeneralImageRelativePredecessor.Dim_of_oplus h
                exact eq_of_norm_eq (hsD.coord _) hbD ((compareT_eq_iff _ _).1 he)
              · intro j hj
                rw [V.get0_ge xs j (by omega_c), V.get0_ge q j (by rw [hqD.length]; omega_c)]

inductive UCTree (k : Nat) : multi.T → Prop
  | successor (xs : V multi.T) (b : multi.T)
      (hx : V.get0 xs 0 = kumakuma.SourceSuccessor.succ (k + 3) b) : UCTree k (.P xs .Z)
  | closedDiagonal (xs q : V multi.T) (i : Nat)
      (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
      (cut : Term) (hc : CutFund k (.P q .Z) cut)
      (hSource : Term.allLt (Term.H cut (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true) : UCTree k (.P xs .Z)
  | inherit (xs : V multi.T) (i : Nat)
      (hf : V.fnz xs = some i) (hdi : domF (V.get0 xs i) = .omega) (hc : UCTree k (V.get0 xs i)) :
      UCTree k (.P xs .Z)
  | tail (xs : V multi.T) (b : multi.T)
      (hb : b ≠ .Z) (hc : UCTree k b) : UCTree k (.P xs b)

theorem UCTree.domain (k : Nat) {s : multi.T} (hc : UCTree k s) : domF s = .omega := by
  induction hc with
  | successor xs b hx =>
    have hd : domF (V.get0 xs 0) = .one := by rw [hx]; exact kumakuma.SourceSuccessor.dom_succ _ b
    have hf : V.fnz xs = some 0 :=
      fnz_eq_some (by rw [hx]; exact kumakuma.SourceSuccessor.succ_ne_zero _ _)
        (fun j hj => absurd hj (Nat.not_lt_zero j))
    exact domF_one_zero hf hd
  | closedDiagonal xs q i hf hdq hdiag => exact domF_diag hf hdq hdiag
  | inherit xs i hf hdi => exact domF_omega hf hdi
  | tail xs b hb _ ih => rw [domF_tail xs hb]; exact ih

theorem ucTree_fund_invariant (k : Nat) {s : multi.T}
    (hc : UCTree k s) (hsD : Dim (k + 3) s) (hr : Recursive s) (hs : RecursiveWF (k + 3) s)
    (n : Nat) :
    RecursiveWF (k + 3) (T.fund s (ofNatD (k + 3) n)) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true → Term.lt Term.bigOmega v = true →
        ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))) →
          DominatedCoefficient k v s z) ∧
      (∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))))
          (convert (k + 3) (code (T.fund s (ofNatD (k + 3) n)))) = true) := by
  cases n with
  | zero =>
    obtain ⟨hn, hcoef, hrel⟩ := zero_fund_invariant k s hsD hr hs
    refine ⟨hn, ?_, hrel⟩
    intro v hvR hv hOmega z hz
    exact UpdatedCoefficient.dominated k v s .Z hsD (Dim_Z _) hs (hcoef v hvR hv hOmega z hz)
  | succ n =>
    induction hc generalizing n with
    | successor xs b hx =>
      obtain ⟨hn, hrel⟩ := fund_zero_successor_relative k xs b hsD hx hs (n + 1)
      refine ⟨hn, ?_, hrel⟩
      intro v hvR hv _ z hz
      apply UpdatedCoefficient.dominated k v _ (ofNatD (k + 3) (n + 1)) hsD (Dim_ofNatD _ _) hs
      rw [fund_zero_coordinate_successor k xs b _ hx] at hz
      have hp := H_mul_principal_support (k + 3) (V.set xs 0 b) (k + 3) v (n + 1) hz
      rcases zero_coordinate_relative_support k v hvR hv xs b hsD hx hs hp with ho | ⟨he, ho⟩
      · exact Or.inr (Or.inl ho)
      · have hbW : RecursiveWF (k + 3) b := by
          have hw := (RecursiveWF_P.1 hs).1 0
          rw [hx] at hw
          exact (recursive_succ_iff _ _ _).mp hw
        refine Or.inr (Or.inr ⟨V.get0 xs 0, Subterm.coordinate xs .Z 0, ?_, ?_, ?_⟩)
        · rw [hx, kumakuma.SourceSuccessor.fund_succ]; exact hbW
        · rw [hx]; exact ho
        · rw [hx, kumakuma.SourceSuccessor.fund_succ]; exact he
    | closedDiagonal xs q i hf hdq hdiag cut hc hSource =>
      have hn := closed_diagonal_recursiveWF k xs q i hsD hf hdq hdiag cut hc hSource hr hs (n + 1)
      refine ⟨hn, ?_, ?_⟩
      · intro v hvR hv hOmega
        exact closed_diagonal_dominated_support k xs q i hsD hf hdq hdiag cut hc hSource hr hs (n + 1)
          v hvR hv hOmega
      · intro v hvR hv hH
        exact closed_diagonal_relative k xs q i hsD hf hdq hdiag cut hc hSource hr hs (n + 1) v hvR hv hH
    | inherit xs i hf hdi hc ih =>
      have hil := fnz_lt_length hf
      have hik : i < k + 3 := by rw [← hsD.length]; exact hil
      have hlow := (V.fnz_some_spec xs i hf).2
      have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
      have hchildR : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
      have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
      obtain ⟨hnChild, hcChild, hrelChild⟩ := ih hcD hchildR (hcoords i) n
      have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
      have hf' : T.fund (.P xs .Z) (ofNatD (k + 3) (n + 1)) =
          .P (V.set xs i (T.fund (V.get0 xs i) (ofNatD (k + 3) (n + 1)))) .Z := fund_omega hf hdi _
      have hn : RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) (n + 1))) := by
        rw [hf']
        by_cases hib : i ≤ k + 1
        · exact principal_replace_relative_recursiveWF k xs i hib hsD hlow hs _
            hnChild hc0 (drop_image_of_omega k _ hcD (hcoords i) hdi) hrelChild
        · have hi : i = k + 2 := by omega
          rw [hi] at hlow hnChild ⊢
          rw [set_last_of_low hsD.length hlow]; exact topNode_recursiveWF k _ hnChild
      refine ⟨hn, ?_, ?_⟩
      · intro v hvR hv hOmega
        exact inherited_omega_dominated_support k xs i hsD hf hdi hs (n + 1) (by omega) hn v hvR hv
          hOmega (hcChild v hvR hv hOmega)
      · apply omega_relative_allcuts k _ hsD hr hs (domF_omega hf hdi) (n + 1) hn
        intro v hvR hv hOmega hH
        exact inherited_omega_dominated_relative_above k xs i hsD hf hdi hs (n + 1) (by omega) hn v hvR
          hv hOmega (hcChild v hvR hv hOmega) hH
    | tail xs b hb hc ih =>
      have hbr : Recursive b := (Recursive_P.1 hr).2.1
      have hbw : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
      obtain ⟨hnB, hcB, _⟩ := ih hsD.tail hbr hbw n
      have hd := UCTree.domain k (.tail xs b hb hc)
      have hn := fund_nonzero_tail_recursiveWF k xs b (ofNatD (k + 3) (n + 1)) hsD (Dim_ofNatD _ _)
        hs hb hnB
      have hcoef (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true)
          (hOmega : Term.lt Term.bigOmega v = true) :
          ∀ z, z ∈ Term.H v (convert (k + 3) (code (T.fund (.P xs b) (ofNatD (k + 3) (n + 1))))) →
            DominatedCoefficient k v (.P xs b) z := by
        intro z hz
        rw [fund_tail xs hb, convert_P] at hz
        rcases H_assemble_support v _ _ hz with hz | hz
        · exact Or.inr (Or.inl (by rw [convert_P]; exact H_assemble_left v _ _ hz))
        · rcases hcB v hvR hv hOmega z hz with he | ho | ⟨a, ha, ho, he⟩
          · exact Or.inl he
          · apply Or.inr; apply Or.inl; rw [convert_P]; exact H_assemble_right v _ _ ho
          · refine Or.inr (Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), ?_, he⟩)
            rw [convert_P]
            exact ho.elim (fun h => Or.inl (H_assemble_right v _ _ h))
              (fun h => Or.inr (H_assemble_right v _ _ h))
      refine ⟨hn, hcoef, ?_⟩
      apply omega_relative_allcuts k _ hsD hr hs hd (n + 1) hn
      intro v hvR hv hOmega hH
      have hsZ : convert (k + 3) (code (.P xs b)) ≠ .zero := convert_ne_zero xs b
      have hnZ : convert (k + 3) (code (T.fund (.P xs b) (ofNatD (k + 3) (n + 1)))) ≠ .zero :=
        fun he => omega_fund_nat_ne_zero _ hd (k + 3) (n + 1) (by omega) ((convert_eq_zero_iff _ _).1 he)
      exact closed_of_dominated_coefficients k v _ _ hsD (Dim_ofNatD _ _) hs hn
        (omega_image_head_ne_one k _ hsD hs hd) hsZ hnZ
        (fun a ha => positive_sum_subterm_gap xs b _ hb
          (kumakuma.SourceCountableInvariant.omega_head_mass_pos xs b hr hd) (ofNatD_succ_ne _ _) ha)
        (hcoef v hvR hv hOmega) hH

theorem tree_of_UC (k : Nat) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s → UC k s → domF s = .omega → UCTree k s
  | .Z, _, _, _, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, hsD, hr, hs, huc, hd => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hc : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hc) (V.fnz_some_spec xs i hf).1
        | one =>
          cases i with
          | zero =>
            obtain ⟨c, hcc⟩ := dom_one_succ (V.get0 xs 0) (hsD.coord 0) hc
            exact .successor xs c hcc
          | succ m => rw [domF_one_succ hf hc] at hd; cases hd
        | omega =>
          exact .inherit xs i hf hc (tree_of_UC k _ (hsD.coord i) ((Recursive_P.1 hr).1 i)
            ((RecursiveWF_P.1 hs).1 i) (huc.coord i) hc)
        | Omega q =>
          by_cases hdiag : xs < q
          · obtain ⟨cut, hcut, hSource⟩ := diagonal_closed k xs q i hsD hf hc hdiag hr hs huc.vec
            exact .closedDiagonal xs q i hf hc hdiag cut hcut hSource
          · rw [domF_nondiag hf hc hdiag] at hd; cases hd
    · have hdb : domF b = .omega := by rwa [domF_tail xs hb] at hd
      exact .tail xs b hb (tree_of_UC k b hsD.tail (Recursive_P.1 hr).2.1 (RecursiveWF_P.1 hs).2.1
        huc.tail hdb)
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

end kumakuma.GeneralImageUniformDiagonal

namespace kumakuma.GeneralImageUniformContext

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageContextBoundDiagonal kumakuma.GeneralImageSharedLowerContext
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageRegularDiagonal
open kumakuma.GeneralImageRegularLimit kumakuma.GeneralImageHeadCuts
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.SourceFundOrder
open kumakuma.GeneralImageUniformClosure kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageCofinalityBounds

/-- The coordinates of `xs` strictly above slot `r`, with zeros below. -/
def upperVec (xs : V multi.T) (r : Nat) : V multi.T :=
  vOf (fun l => if r < l then V.get0 xs l else .Z) xs.length

theorem upperVec_length (xs : V multi.T) (r : Nat) : (upperVec xs r).length = xs.length :=
  vOf_length _ _

theorem get0_upperVec (xs : V multi.T) (r l : Nat) :
    V.get0 (upperVec xs r) l = if r < l then V.get0 xs l else .Z := by
  rw [upperVec, get0_vOf]
  by_cases hl : l < xs.length
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl, V.get0_ge xs l (by omega)]
    split <;> rfl

theorem Dim_upperVec {d : Nat} {xs : V multi.T} (hsD : Dim d (.P xs .Z)) (r : Nat) :
    Dim d (.P (upperVec xs r) .Z) := by
  refine Dim_P (by rw [upperVec_length]; exact hsD.length) (fun l => ?_) (Dim_Z d)
  rw [get0_upperVec]
  split
  · exact hsD.coord l
  · exact Dim_Z d

theorem lift_eq_upper_rplc (xs : V multi.T) (j r : Nat) (hr : r < xs.length) :
    lift xs j r = V.set (upperVec xs r) r (V.get0 xs j) := by
  apply V.eq_of_get0 _ _ (by rw [lift_length, V.length_set, upperVec_length])
  intro l
  rw [get0_lift xs j r l hr, V.get0_set _ r _ l (by rw [upperVec_length]; exact hr), get0_upperVec]
  by_cases hl : l = r
  · rw [hl, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right hl, ite_eq_right hl]

theorem upper_le_of_not_lt (xs q : V multi.T) (r : Nat) (hnd : ¬ xs < q) :
    multi.T.P (upperVec q r) .Z ≤ multi.T.P (upperVec xs r) .Z := by
  have heqv (hall : ∀ l, r < l → compareT (V.get0 q l) (V.get0 xs l) = .eq) :
      multi.T.P (upperVec q r) .Z ≤ multi.T.P (upperVec xs r) .Z := by
    apply T.le_of_eqv
    apply (T.P_eqv_iff _ _ _ _).2 ⟨?_, compareT_ZZ⟩
    apply (V.eqv_iff_get0 _ _).2
    intro l
    rw [get0_upperVec, get0_upperVec]
    by_cases hl : r < l
    · rw [ite_eq_left hl, ite_eq_left hl]; exact hall l hl
    · rw [ite_eq_right hl, ite_eq_right hl]; exact compareT_ZZ
  rcases V.lt_trichotomy xs q with hl | he | hl
  · exact absurd hl hnd
  · apply heqv
    intro l _
    exact T.eqv_symm (((V.eqv_iff_get0 _ _).1 ((compareV_eq_iff _ _).2 he)) l)
  · obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot q xs).1 hl
    by_cases hpr : r < p
    · apply T.le_of_lt
      apply T.P_lt_P_of_vlt
      apply V.lt_of_pivot p
      · intro l hl'
        rw [get0_upperVec, get0_upperVec, ite_eq_left (by omega), ite_eq_left (by omega)]
        exact habove l hl'
      · rw [get0_upperVec, get0_upperVec, ite_eq_left hpr, ite_eq_left hpr]; exact hp
    · apply heqv
      intro l hl'
      exact habove l (by omega)

theorem upper_context (k r : Nat) (hr : r ≤ k) (xs : V multi.T)
    (hsD : Dim (k + 3) (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    ∃ a, Above r a ∧ Term.wf a = true ∧
      RecursiveWF (k + 3) (.P (upperVec xs r) .Z) ∧
      convert (k + 3) (code (.P (upperVec xs r) .Z)) = (if a = .zero then Term.one else a) ∧
      convert (k + 3) (code (.P xs .Z)) = lower (r + 1) (arguments (k + 3) (trim (codes xs))) a ∧
      ∀ t : multi.T, t ≠ .Z →
        convert (k + 3) (code (.P (V.set (upperVec xs r) r t) .Z)) =
          step r a (convert (k + 3) (code t)) := by
  have hbaseD : Dim (k + 3) (.P (upperVec xs r) .Z) := Dim_upperVec hsD r
  have hzero : ∀ i, i < r + 1 → V.get0 (upperVec xs r) i = .Z := by
    intro i hi; rw [get0_upperVec, ite_eq_right (by omega)]
  obtain ⟨a, ha, heBase, heInsert⟩ := principal_insertion_context k r hr (upperVec xs r) hbaseD hzero
  have hsame : ∀ j, r < j → V.get0 xs j = V.get0 (upperVec xs r) j := by
    intro j hj; rw [get0_upperVec, ite_eq_left hj]
  have heX := principal_shared_lower_image k r hr (upperVec xs r) xs hzero hsame a ha heBase
  have hctx : Context (r + 1) a := by
    rcases ha with ha | ha
    · exact Or.inl ha
    · exact Or.inr ⟨above_principal ha, by omega⟩
  have haw : Term.wf a = true := lower_context_wf (r + 1) _ a hctx (heX ▸ hs.wf)
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hbaseW : RecursiveWF (k + 3) (.P (upperVec xs r) .Z) := by
    refine RecursiveWF_P.2 ⟨fun j => ?_, recursive_zero _, ?_⟩
    · rw [get0_upperVec]
      split
      · exact hcoords j
      · exact recursive_zero _
    · rw [heBase]
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

theorem principal_lt_layerCut (k r : Nat) (xs : V multi.T) (a : Term)
    (ha : Above r a)
    (heX : convert (k + 3) (code (.P xs .Z)) = lower (r + 1) (arguments (k + 3) (trim (codes xs))) a) :
    Term.lt (convert (k + 3) (code (.P xs .Z))) (layerCut r a) = true := by
  rw [heX, lower_succ]
  exact lower_lt_inacc r r (Nat.le_refl _) _ _ _ (step_shape _ ha) (step_lt_layerCut r a _ ha)

theorem principal_top_image (k : Nat) (xs : V multi.T) :
    convert (k + 3) (code (.P xs .Z)) = lower (k + 1) (arguments (k + 3) (trim (codes xs)))
      (topPair (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))
        (convert (k + 3) (code (V.get0 xs (k + 1))))) := by
  rw [convert_principal, principal_as_layers, converted_coordinate xs (k + 2),
    converted_coordinate xs (k + 1)]

theorem topPair_lt_pairCut (n : Nat) (h m : Term) (hh : Term.wf h = true) :
    Term.lt (topPair n h m) (pairCut n h) = true := by
  by_cases hm0 : m = .zero
  · by_cases hh0 : h = .zero
    · simp [topPair, pairCut, hm0, hh0, Term.lt]
    · simp only [topPair, pairCut, hm0, hh0, ↓reduceIte, inacc_same_lt]
      rw [lt_succTerm_eq_le (dropOne_wf hh) (dropOne_wf hh)]
      simp [Term.le]
  · simp [topPair, pairCut, hm0, Term.lt, Term.fT]

theorem principal_lt_pairCut (k : Nat) (xs : V multi.T)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    Term.lt (convert (k + 3) (code (.P xs .Z)))
      (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))) = true := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  rw [principal_top_image]
  exact lower_lt_inacc (k + 1) (k + 1) (Nat.le_refl _) _ _ _ (topPair_context _ _ _)
    (topPair_lt_pairCut _ _ _ (hcoords _).wf)

theorem uc_image_le_of_le (k : Nat) (s t : multi.T)
    (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t)
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t) (h : s ≤ t) :
    Term.le (convert (k + 3) (code s)) (convert (k + 3) (code t)) = true := by
  rcases h with hl | he
  · have := (convert_order k s t hsD htD hs ht).mp hl
    simp [Term.le, this]
  · rw [code_congr he]; simp [Term.le]

theorem lift_image_layer (k r : Nat) (hr0 : 0 < r) (hr : r ≤ k)
    (xs : V multi.T) (hxl : xs.length = k + 3) (j : Nat) (hj : V.get0 xs j ≠ .Z) (a : Term)
    (heIns : ∀ t : multi.T, t ≠ .Z →
      convert (k + 3) (code (.P (V.set (upperVec xs r) r t) .Z)) =
        step r a (convert (k + 3) (code t))) :
    convert (k + 3) (code (.P (lift xs j r) .Z)) =
      .psi (layerCut r a) (dropOne (convert (k + 3) (code (V.get0 xs j)))) := by
  rw [lift_eq_upper_rplc xs j r (by omega), heIns _ hj,
    step_layerCut r (by omega) a _ (convert_ne_zero_of_ne hj)]

theorem lift_image_top (k : Nat) (xs : V multi.T) (hxl : xs.length = k + 3) (j : Nat)
    (hj : V.get0 xs j ≠ .Z) :
    convert (k + 3) (code (.P (lift xs j (k + 1)) .Z)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
        (dropOne (convert (k + 3) (code (V.get0 xs j)))) := by
  have hy := convert_ne_zero_of_ne (k := k) hj
  have hr : k + 1 < xs.length := by omega
  rw [principal_top_image, lift_high xs j (k + 1) (k + 2) hr (by omega), lift_at xs j (k + 1) hr]
  rw [lower_keep (k + 1) _ _ (by simp [topPair, hy]) (fun l hl => by
    rw [converted_coordinate (lift xs j (k + 1)) l, lift_low xs j (k + 1) l hr hl, convert_Z])]
  simp [topPair, pairCut, hy]

theorem nondiagonal_virtual_cut_above_label (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hnd : ¬ xs < q)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (r : Nat) (hir : i < r)
    (hrk : r ≤ k + 1) (w : Term)
    (hw : convert (k + 3) (code (.P (lift xs i r) .Z)) =
      .psi w (dropOne (convert (k + 3) (code (V.get0 xs i))))) :
    Term.lt Term.bigOmega w = true ∧ Term.lt (convert (k + 3) (code (.P q .Z))) w = true := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hxl := hsD.length
  have hqD := Dim_Omega_label (hsD.coord i) hdq
  have hqW := Omega_label_recursiveWF k _ (hcoords i) hdq
  have hqcoords : ∀ j, RecursiveWF (k + 3) (V.get0 q j) := (RecursiveWF_P.1 hqW).1
  by_cases hrk' : r ≤ k
  · obtain ⟨a, ha, haw, hbase, heBase, _, heIns⟩ := upper_context k r hrk' xs hsD hs
    obtain ⟨aq, haq, haqw, hbaseQ, heBaseQ, heQ, _⟩ := upper_context k r hrk' q hqD hqW
    have hlift := lift_image_layer k r (by omega) hrk' xs hxl i hc0 a heIns
    rw [hw] at hlift
    have hwEq : w = layerCut r a := (Term.psi.inj hlift).1
    subst hwEq
    refine ⟨layerCut_above_Omega r (by omega) a, ?_⟩
    have hq1 := principal_lt_layerCut k r q aq haq heQ
    have hle := uc_image_le_of_le k _ _ (Dim_upperVec hqD r) (Dim_upperVec hsD r) hbaseQ hbase
      (upper_le_of_not_lt xs q r hnd)
    rw [heBaseQ, heBase] at hle
    have hcut := (layerCut_comparable_of_erased_le r r (Nat.le_refl _) aq a haq ha haqw haw hle).1
    exact Term.lt_of_lt_of_le hqW.wf (layerCut_wf r aq haq haqw) (layerCut_wf r a ha haw) hq1 hcut
  · have hrK : r = k + 1 := by omega
    subst hrK
    rw [lift_image_top k xs hxl i hc0] at hw
    have hwEq := (Term.psi.inj hw).1
    subst hwEq
    refine ⟨by simp [pairCut, Term.bigOmega, Term.lt], ?_⟩
    have hq1 := principal_lt_pairCut k q hqW
    have htop : V.get0 q (k + 2) ≤ V.get0 xs (k + 2) := by
      rcases V.lt_trichotomy xs q with hl | he | hl
      · exact absurd hl hnd
      · exact T.le_of_eqv (T.eqv_symm (((V.eqv_iff_get0 _ _).1 ((compareV_eq_iff _ _).2 he)) (k + 2)))
      · obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot q xs).1 hl
        by_cases hpk : p = k + 2
        · rw [hpk] at hp; exact T.le_of_lt hp
        · have hpk' : p < k + 2 := by
            apply Nat.lt_of_le_of_ne _ hpk
            apply Nat.le_of_not_lt; intro hlt
            rw [V.get0_ge xs p (by omega)] at hp
            exact T.not_lt_Z _ hp
          exact T.le_of_eqv (habove (k + 2) hpk')
    have hpair := (kumakuma.GeneralImageHighestContextDiagonal.pairCut_image_comparable k _ _
      (hqD.coord _) (hsD.coord _) (hqcoords _) (hcoords _) htop).1
    have hcutQ := kumakuma.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hqcoords (k + 2))
    have hcutX := kumakuma.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hcoords (k + 2))
    exact Term.lt_of_lt_of_le hqW.wf hcutQ hcutX hq1 hpair

end kumakuma.GeneralImageUniformContext

namespace kumakuma.GeneralImageUniformPreservation

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageCoefficients kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageLabelCut kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageUniformClosure kumakuma.GeneralImageUniformContext

set_option maxRecDepth 10000

def TopOK (k : Nat) (q : V multi.T) (t : multi.T) : Prop :=
  t ≠ .Z → ∀ m : Nat, V.fnz q = some (m + 1) → domF (V.get0 q (m + 1)) = .one →
    ∀ r : Nat, m < r → r ≤ k + 1 →
      RecursiveWF (k + 3) (.P (lift (V.set q m t) m r) .Z)

theorem VecUC_replace_zero_fund (k : Nat) (xs : V multi.T)
    (i : Nat) (hxl : xs.length = k + 3) (hlow : ∀ j, j < i → V.get0 xs j = .Z) (huc : VecUC k xs)
    (hc0 : V.get0 xs i ≠ .Z) (hcD : Dim (k + 3) (V.get0 xs i)) (hcr : Recursive (V.get0 xs i))
    (hcw : RecursiveWF (k + 3) (V.get0 xs i)) :
    VecUC k (V.set xs i (T.fund (V.get0 xs i) .Z)) := by
  have hz := zero_fund_invariant k (V.get0 xs i) hcD hcr hcw
  exact VecUC_replace_min k xs hxl i hlow huc hc0 _ hz.1
    (fun _ _ _ _ w _ hwR hww hH => hz.2.2 w hwR hww hH)

theorem UC_fund_Omega (k : Nat) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s → UC k s →
    ∀ {q : V multi.T}, domF s = .Omega q →
    ∀ (κ : Term), CutFund k (.P q .Z) κ →
    ∀ (t : multi.T), Dim (k + 3) t → RecursiveWF (k + 3) t → UC k t →
    Term.allLt (Term.H κ (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true →
    TopOK k q t → UC k (T.fund s t)
  | .Z, _, _, _, _, _, hd, _, _, _, _, _, _, _, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, hsD, hr, hs, huc, q, hd, κ, hκ, t, htD, htw, htuc, hHt, htop => by
    have hcoordsR : ∀ j, Recursive (V.get0 xs j) := (Recursive_P.1 hr).1
    have hcoordsW : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
    have hxl : xs.length = k + 3 := hsD.length
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · have hil := fnz_lt_length hf
        have hlow := (V.fnz_some_spec xs i hf).2
        have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
        cases hcd : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hcd] at hd; cases hd
        | omega => rw [domF_omega hf hcd] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hcd] at hd; cases hd
          | succ m =>
            rw [domF_one_succ hf hcd] at hd
            cases hd
            obtain ⟨c₀, hc⟩ := dom_one_succ _ (hsD.coord (m + 1)) hcd
            rw [fund_one_succ hf hcd t]
            have hfz : T.fund (V.get0 xs (m + 1)) .Z = c₀ := by
              rw [hc, kumakuma.SourceSuccessor.fund_succ]
            rw [hfz]
            have hU1 := VecUC_replace_zero_fund k xs (m + 1) hxl hlow huc.vec hc0 (hsD.coord _)
              (hcoordsR _) (hcoordsW _)
            rw [hfz] at hU1
            rw [UC_P_iff]
            refine ⟨?_, ?_, UC_zero k⟩
            · apply VecUC_insert k (V.set xs (m + 1) c₀) (by rw [V.length_set]; exact hxl) m
                (fun j hj => by
                  rw [V.get0_set_ne xs _ c₀ j (by omega)]
                  exact hlow j (by omega))
                hU1 t
              intro ht0 r hmr hrk
              have he : lift (V.set (V.set xs (m + 1) c₀) m t) m r = lift (V.set xs m t) m r := by
                apply lift_congr _ _ _ _ r
                · rw [V.get0_set_same _ _ _ (by rw [V.length_set]; omega),
                    V.get0_set_same _ _ _ (by omega)]
                · intro l hl
                  rw [V.get0_set_ne _ m t l (by omega), V.get0_set_ne _ (m + 1) c₀ l (by omega),
                    V.get0_set_ne _ m t l (by omega)]
                · rw [V.length_set, V.length_set, V.length_set]
                · rw [V.length_set, V.length_set]; omega
              rw [he]
              exact htop ht0 m hf hcd r hmr hrk
            · intro j
              rw [V.get0_set _ m t j (by rw [V.length_set]; omega)]
              split
              · exact htuc
              · rw [V.get0_set _ (m + 1) c₀ j hil]
                split
                · have hcu := huc.coord (m + 1)
                  rw [hc] at hcu
                  exact UC_succ c₀ hcu
                · exact huc.coord j
        | Omega q' =>
          by_cases hdiag : xs < q'
          · rw [domF_diag hf hcd hdiag] at hd; cases hd
          · have hd' := domF_nondiag hf hcd hdiag
            rw [hd'] at hd
            cases hd
            rw [fund_nondiag hf hcd hdiag t]
            have hInv := Omega_fund_at_label_cut_invariant k (V.get0 xs i) (hsD.coord i) (hcoordsR i)
              (hcoordsW i) hcd κ hκ t htD htw hHt
            rw [UC_P_iff]
            refine ⟨?_, ?_, UC_zero k⟩
            · apply VecUC_replace_min k xs hxl i hlow huc.vec hc0 _ hInv.1
              intro r hir hrk _ w hw hwR hww hH
              obtain ⟨hOmega, hAbove⟩ :=
                nondiagonal_virtual_cut_above_label k xs _ i hsD hf hcd hdiag hs r hir hrk w hw
              exact (hInv.2 w hwR hww hOmega hAbove).2 hH
            · intro j
              rw [V.get0_set _ i _ j hil]
              split
              · exact UC_fund_Omega k (V.get0 xs i) (hsD.coord i) (hcoordsR i) (hcoordsW i)
                  (huc.coord i) hcd κ hκ t htD htw htuc hHt htop
              · exact huc.coord j
    · have hdb : domF b = .Omega q := by rwa [domF_tail xs hb] at hd
      rw [fund_tail xs hb t, UC_P_iff]
      exact ⟨huc.vec, huc.coord, UC_fund_Omega k b hsD.tail (Recursive_P.1 hr).2.1
        (RecursiveWF_P.1 hs).2.1 huc.tail hdb κ hκ t htD htw htuc hHt htop⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

end kumakuma.GeneralImageUniformPreservation

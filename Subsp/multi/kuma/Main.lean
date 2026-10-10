import Subsp.multi.kuma.Uniform

/-! Top-layer closure of diagonals, generation of `RecursiveWF ∧ UC` for all OT, and
`global_certificate` (the `multi` version of `Subsp/Support/Main.lean`). -/

namespace kumakuma.GeneralImageUniformTop

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageContextBoundDiagonal kumakuma.GeneralImageSharedLowerContext
open kumakuma.GeneralImageSharedContext kumakuma.GeneralImageRegularDiagonal
open kumakuma.GeneralImageRegularLimit kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageSharedTopPair
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageComparableCuts
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.SourceFundOrder kumakuma.SourceFundGap
open kumakuma.SourceRecursiveDescending
open kumakuma.GeneralImageUniformClosure kumakuma.GeneralImageUniformContext
open kumakuma.GeneralImageUniformPreservation
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageHighestDiagonal

universe u

set_option maxRecDepth 10000

/-- The pivot of a strict vector comparison, with equal coordinates above it (fixed dimension). -/
theorem lt_pivot_eq {d : Nat} {xs ys : V multi.T} (hxD : Dim d (.P xs .Z)) (hyD : Dim d (.P ys .Z))
    (h : xs < ys) : ∃ p, V.get0 xs p < V.get0 ys p ∧ ∀ j, p < j → V.get0 xs j = V.get0 ys j := by
  obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot xs ys).1 h
  exact ⟨p, hp, fun j hj => eq_of_norm_eq (hxD.coord j) (hyD.coord j)
    ((compareT_eq_iff _ _).1 (habove j hj))⟩

theorem predR_lt_psi [LargeCardinals.{u}] (v b : Term) (hw : Term.wf (.psi v b) = true) :
    Term.lt (Term.predR v) (.psi v b) = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  have hpred := (sem_of_wf.{u} hp.2.1).isR_pred hp.1
  rw [lt_iff_V hpred.1 hw, hpred.2.1]
  exact regPred_lt_Ψ _ _

theorem upperVec_le_succ (q : V multi.T) (r : Nat) :
    multi.T.P (upperVec q (r + 1)) .Z ≤ multi.T.P (upperVec q r) .Z := by
  by_cases hz : V.get0 q (r + 1) = .Z
  · apply T.le_of_eqv
    apply (T.P_eqv_iff _ _ _ _).2 ⟨?_, compareT_ZZ⟩
    apply (V.eqv_iff_get0 _ _).2
    intro l
    rw [get0_upperVec, get0_upperVec]
    by_cases h1 : r + 1 < l
    · rw [ite_eq_left h1, ite_eq_left (by omega)]; exact compareT_self _
    · rw [ite_eq_right h1]
      by_cases h2 : r < l
      · rw [ite_eq_left h2, show l = r + 1 by omega, hz]; exact compareT_ZZ
      · rw [ite_eq_right h2]; exact compareT_ZZ
  · apply T.le_of_lt
    apply T.P_lt_P_of_vlt
    apply V.lt_of_pivot (r + 1)
    · intro l hl
      rw [get0_upperVec, get0_upperVec, ite_eq_left hl, ite_eq_left (by omega)]
      exact compareT_self _
    · rw [get0_upperVec, get0_upperVec, ite_eq_right (Nat.lt_irrefl _), ite_eq_left (by omega)]
      exact T.Z_lt_of_ne hz

theorem upperVec_mono (q : V multi.T) (r : Nat) :
    ∀ d : Nat, multi.T.P (upperVec q (r + d)) .Z ≤ multi.T.P (upperVec q r) .Z
  | 0 => T.le_of_eqv (compareT_self _)
  | d + 1 => T.le_trans (upperVec_le_succ q (r + d)) (upperVec_mono q r d)

theorem context_le_of_image_le [LargeCardinals.{u}] {r s : Nat} {a b : Term}
    (ha : Above r a) (haw : Term.wf a = true) (hb : Above s b) (hbw : Term.wf b = true)
    (h : Term.le (if a = .zero then Term.one else a) (if b = .zero then Term.one else b) = true) :
    Term.le a b = true := by
  by_cases ha0 : a = .zero
  · subst a
    by_cases hb0 : b = .zero
    · subst b; simp [Term.le]
    · simp [Term.le, (zero_lt_iff _).mpr hb0]
  · have hfa := ha.resolve_left ha0
    by_cases hb0 : b = .zero
    · rw [ite_eq_right ha0, ite_eq_left hb0] at h
      have he := (principal_le_one_iff (above_principal hfa) haw).mp h
      rw [he] at hfa; simp [Term.one, Term.bigOmega, Term.fT] at hfa
    · rwa [ite_eq_right ha0, ite_eq_right hb0] at h

theorem context_lt_of_image_lt [LargeCardinals.{u}] {r s : Nat} {a b : Term}
    (ha : Above r a) (haw : Term.wf a = true) (_hb : Above s b) (_hbw : Term.wf b = true)
    (h : Term.lt (if a = .zero then Term.one else a) (if b = .zero then Term.one else b) = true) :
    Term.lt a b = true ∧ b ≠ .zero := by
  by_cases hb0 : b = .zero
  · exfalso
    rw [ite_eq_left hb0] at h
    by_cases ha0 : a = .zero
    · rw [ite_eq_left ha0, lt_self] at h; cases h
    · rw [ite_eq_right ha0] at h
      have hle := one_le_principal (above_principal (ha.resolve_left ha0)) haw
      rcases (Term.le_iff_eq_or_lt _ _).mp hle with he | hl
      · rw [← he, lt_self] at h; cases h
      · have := lemma_6_1.{u}.2.1 _ _ _ Term.wf_one haw Term.wf_one hl h
        rw [lt_self] at this; cases this
  · refine ⟨?_, hb0⟩
    by_cases ha0 : a = .zero
    · subst a; exact (zero_lt_iff _).mpr hb0
    · rwa [ite_eq_right ha0, ite_eq_right hb0] at h

theorem lift_rplc_eq_upper (q : V multi.T) (m r : Nat) (hmr : m < r) (hr : r < q.length)
    (c : multi.T) : lift (V.set q m c) m r = V.set (upperVec q r) r c := by
  rw [lift_eq_upper_rplc _ m r (by rw [V.length_set]; exact hr), V.get0_set_same q m c (by omega)]
  congr 1
  apply V.eq_of_get0 _ _ (by rw [upperVec_length, upperVec_length, V.length_set])
  intro l
  rw [get0_upperVec, get0_upperVec]
  by_cases hl : r < l
  · rw [ite_eq_left hl, ite_eq_left hl, V.get0_set_ne q m c l (by omega)]
  · rw [ite_eq_right hl, ite_eq_right hl]

theorem predR_regular {n : Nat} {h : Term} (hh : Above n h) (h0 : h ≠ .zero) (hw : Term.wf h = true) :
    Term.predR (regular n h) = h := by
  simp only [regular, Term.predR, succTerm_ne_zero, ↓reduceIte, predT_succTerm hw,
    show ¬Term.fT h ≤ n from Nat.not_le.mpr (hh.resolve_left h0)]

theorem H_lower_visible [LargeCardinals.{u}] (n : Nat) (zz : Term)
    (hwR : Term.isRT (.inacc n zz) = true) (hww : Term.wf (.inacc n zz) = true) :
    ∀ (j : Nat), j ≤ n → ∀ (args : List Term) (h : Term), Context j h →
      Term.lt h (.inacc n zz) = true → Term.lt (Term.predR (.inacc n zz)) h = true →
      Term.wf (lower j args h) = true → ∀ z, z ∈ Term.H (.inacc n zz) h →
      z ∈ Term.H (.inacc n zz) (lower j args h) := by
  have hpw := ((sem_of_wf.{u} hww).isR_pred hwR).1
  intro j
  induction j with
  | zero => intro _ _ _ _ _ _ _ z hz; exact hz
  | succ j ih =>
    intro hj args h hctx hlt hpred hwf z hz
    rw [lower_succ] at hwf ⊢
    have habove := context_above hctx
    have hstepWf := lower_context_wf j args _ (step_shape _ habove) hwf
    have hh0 : h ≠ .zero := by
      intro he; rw [he] at hpred
      cases hpz : Term.predR (.inacc n zz) <;> rw [hpz] at hpred <;> simp [Term.lt] at hpred
    have hhw : Term.wf h = true := step_context_wf habove hstepWf
    by_cases hy : args[j]?.getD .zero = .zero
    · have hstep : step j h (args[j]?.getD .zero) = h := by simp [step, hy, hh0]
      rw [hstep] at hwf ⊢
      exact ih (by omega) args h (by rw [← hstep]; exact step_shape _ habove) hlt hpred hwf z hz
    · have hstep : step j h (args[j]?.getD .zero) =
          .psi (regular j h) (dropOne (args[j]?.getD .zero)) := by simp [step, hy, hh0]
      have hpsiW : Term.wf (.psi (regular j h) (dropOne (args[j]?.getD .zero))) = true := hstep ▸ hstepWf
      have hhPsi : Term.lt h (.psi (regular j h) (dropOne (args[j]?.getD .zero))) = true := by
        have := predR_lt_psi _ _ hpsiW
        rwa [predR_regular habove hh0 hhw] at this
      have hpredPsi := lemma_6_1.{u}.2.1 _ _ _ hpw hhw hpsiW hpred hhPsi
      have hregLt : Term.lt (regular j h) (.inacc n zz) = true := by
        simp only [regular, Term.lt, show j < n by omega, ↓reduceIte]
        rw [succ_principal (above_principal (habove.resolve_left hh0)), Term.lt]
        exact hlt
      have hnotLe : Term.le (.psi (regular j h) (dropOne (args[j]?.getD .zero)))
          (Term.predR (.inacc n zz)) = false := by
        cases he : Term.le (.psi (regular j h) (dropOne (args[j]?.getD .zero))) (Term.predR (.inacc n zz))
        · rfl
        · rcases (Term.le_iff_eq_or_lt _ _).mp he with he' | hl
          · rw [he', lt_self] at hpredPsi; cases hpredPsi
          · have := lemma_6_1.{u}.2.1 _ _ _ hpw hpsiW hpw hpredPsi hl
            rw [lt_self] at this; cases this
      apply ih (by omega) args _ (step_shape _ habove)
        (step_lt_inacc j n (by omega) h _ zz habove hlt)
        (by rw [hstep]; exact hpredPsi) hwf z
      rw [hstep, Term.H, hnotLe]
      simp only [Bool.false_eq_true, ↓reduceIte, hregLt]
      change z ∈ (if j = 0 then [] else Term.hOne (.inacc n zz)) ++ Term.H (.inacc n zz) (succTerm h)
      rw [kumakuma.OT2.H_succTerm]
      exact List.mem_append_right _ (List.mem_append_left _ hz)

theorem lift_self_of_low (xs : V multi.T) (i : Nat) (hi : i < xs.length)
    (hlow : ∀ j, j < i → V.get0 xs j = .Z) : lift xs i i = xs := by
  apply V.eq_of_get0 _ _ (lift_length _ _ _)
  intro l
  rw [get0_lift xs i i l hi]
  by_cases hl : i < l
  · rw [ite_eq_left hl]
  · rw [ite_eq_right hl]
    by_cases he : l = i
    · rw [ite_eq_left he, he]
    · rw [ite_eq_right he]; exact (hlow l (by omega)).symm

theorem psi_self_visible [LargeCardinals.{u}] (w Q : Term) (hw : Term.wf (.psi w Q) = true) :
    Q ∈ Term.H w (.psi w Q) := by
  have hpr := predR_lt_psi w Q hw
  have hp := (Term.wf_psi_iff _ _).mp hw
  have hpw := ((sem_of_wf.{u} hp.2.1).isR_pred hp.1).1
  have hnotLe : Term.le (.psi w Q) (Term.predR w) = false := by
    cases he : Term.le (.psi w Q) (Term.predR w)
    · rfl
    · rcases (Term.le_iff_eq_or_lt _ _).mp he with he' | hl
      · rw [he', lt_self] at hpr; cases hpr
      · have := lemma_6_1.{u}.2.1 _ _ _ hpw hw hpw hpr hl
        rw [lt_self] at this; cases this
  rw [Term.H, hnotLe]
  simp [lt_self]

theorem higher_equal_context_false [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hi0 : 0 < i) (hib : i ≤ k + 1)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hhigh : ∀ l, i < l → V.get0 xs l = V.get0 q l)
    (hlt : V.get0 xs i < V.get0 q i) : False := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hlow := (V.fnz_some_spec xs i hf).2
  have hcr : Recursive (V.get0 xs i) := (Recursive_P.1 hr).1 i
  have hcw := hcoords i
  have hcD : Dim (k + 3) (V.get0 xs i) := hsD.coord i
  have hxl := hsD.length
  have hc0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
  have hcy := convert_ne_zero_of_ne (k := k) hc0
  have hdrop := kumakuma.GeneralImageMiddleSums.Omega_image_drop k _ hcD hcr hcw hdq
  have hqD := Dim_Omega_label hcD hdq
  have hqW := Omega_label_recursiveWF k _ hcw hdq
  have hqcoords : ∀ j, RecursiveWF (k + 3) (V.get0 q j) := (RecursiveWF_P.1 hqW).1
  have hqi0 : V.get0 q i ≠ .Z := T.ne_Z_of_lt hlt
  have hqy := convert_ne_zero_of_ne (k := k) hqi0
  have hxsLift := lift_self_of_low xs i (by omega) hlow
  have key : ∃ w, Term.isRT w = true ∧ Term.wf w = true ∧ Term.lt Term.bigOmega w = true ∧
      Term.allLt (Term.H w (convert (k + 3) (code (V.get0 xs i))))
        (convert (k + 3) (code (V.get0 xs i))) = true ∧
      dropOne (convert (k + 3) (code (V.get0 q i))) ∈ Term.H w (convert (k + 3) (code (.P q .Z))) := by
    by_cases hik : i ≤ k
    · obtain ⟨a, ha, _, _, heBase, _, heIns⟩ := upper_context k i hik xs hsD hs
      have hxsImg := lift_image_layer k i hi0 hik xs hxl i hc0 a heIns
      rw [hxsLift] at hxsImg
      have hp := (Term.wf_psi_iff _ _).mp (hxsImg ▸ hs.wf)
      have hzero : ∀ j, j < i + 1 → V.get0 (upperVec xs i) j = .Z :=
        fun j hj => by rw [get0_upperVec, ite_eq_right (by omega)]
      have hsame : ∀ j, i < j → V.get0 q j = V.get0 (upperVec xs i) j :=
        fun j hj => by rw [get0_upperVec, ite_eq_left hj]; exact (hhigh j hj).symm
      have heQ := principal_shared_lower_image k i hik _ q hzero hsame a ha heBase
      rw [lower_succ, converted_coordinate q i, step_layerCut i (by omega) a _ hqy] at heQ
      refine ⟨layerCut i a, hp.1, hp.2.1, layerCut_above_Omega i hi0 a,
        by rw [← hdrop]; exact hp.2.2.2, ?_⟩
      have hqWf := heQ ▸ hqW.wf
      have hpsiW := lower_context_wf i _ _ (Or.inr ⟨rfl, by simp [layerCut, Term.fT]⟩) hqWf
      rw [heQ]
      exact H_lower_visible i _ hp.1 hp.2.1 i (Nat.le_refl _) _ _
        (Or.inr ⟨rfl, by simp [Term.fT]⟩) (by simp [Term.lt, Term.fT])
        (predR_lt_psi _ _ hpsiW) hqWf _ (psi_self_visible _ _ hpsiW)
    · have hiK : i = k + 1 := by omega
      subst hiK
      have hxsImg := lift_image_top k xs hxl (k + 1) hc0
      rw [hxsLift] at hxsImg
      have hp := (Term.wf_psi_iff _ _).mp (hxsImg ▸ hs.wf)
      have htop : V.get0 xs (k + 2) = V.get0 q (k + 2) := hhigh _ (by omega)
      have heQ := principal_top_image k q
      rw [← htop] at heQ
      have htp : topPair (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))
          (convert (k + 3) (code (V.get0 q (k + 1)))) =
          .psi (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
            (dropOne (convert (k + 3) (code (V.get0 q (k + 1))))) := by
        simp [topPair, pairCut, hqy]
      rw [htp] at heQ
      refine ⟨_, hp.1, hp.2.1, pairCut_above_Omega (k + 1) (by omega) _,
        by rw [← hdrop]; exact hp.2.2.2, ?_⟩
      have hqWf := heQ ▸ hqW.wf
      have hpsiW := lower_context_wf (k + 1) _ _ (Or.inr ⟨rfl, by simp [pairCut, Term.fT]⟩) hqWf
      rw [heQ]
      exact H_lower_visible (k + 1) _ hp.1 hp.2.1 (k + 1) (Nat.le_refl _) _ _
        (Or.inr ⟨rfl, by simp [Term.fT]⟩) (by simp [Term.lt, Term.fT])
        (predR_lt_psi _ _ hpsiW) hqWf _ (psi_self_visible _ _ hpsiW)
  obtain ⟨w, hwR, hww, hΩw, hHc, hvis⟩ := key
  have hRel := kumakuma.GeneralImageHigherDiagonal.Omega_label_relative_bound k _ hcD hcr hcw hdq w _
    hwR hww hΩw hcw.wf hHc
  have hQ := (Term.allLt_iff _ _).mp hRel _ hvis
  have hcq := (convert_order k _ _ hcD (hqD.coord i) hcw (hqcoords i)).mp hlt
  have hdo := dropOne_order (hqcoords i).wf hcw.wf hqy hcy
  rw [hdrop, hQ] at hdo
  have hself := lemma_6_1.{u}.2.1 _ _ _ hcw.wf (hqcoords i).wf hcw.wf hcq hdo.symm
  rw [lt_self] at hself; cases hself

theorem predR_lt_self [LargeCardinals.{u}] (v : Term) (hvR : Term.isRT v = true) (hv : Term.wf v = true) :
    Term.lt (Term.predR v) v = true := by
  have sv := sem_of_wf.{u} hv
  have hp := sv.isR_pred hvR
  rw [lt_iff_V hp.1 hv, hp.2.1]
  exact regPred_lt (sv.isR_iff.mp hvR) sv.lt_Λ₀

theorem succ_le_of_lt_source (lam : Nat) {x y : multi.T} (h : x < y) :
    kumakuma.SourceSuccessor.succ lam x ≤ y := by
  rcases T.lt_trichotomy (kumakuma.SourceSuccessor.succ lam x) y with hl | he | hl
  · exact T.le_of_lt hl
  · exact T.le_of_eqv ((compareT_eq_iff _ _).2 he)
  · have hle := (kumakuma.SourceSuccessor.lt_succ_iff_le lam y x).mp hl
    exact absurd (T.lt_of_lt_of_le h hle) (T.lt_irrefl _)

theorem label_virtual_recursiveWF (k : Nat) (q : V multi.T) (r : Nat) (hr : r < q.length)
    (c : multi.T) (hc : RecursiveWF (k + 3) c)
    (hqcoords : ∀ j, RecursiveWF (k + 3) (V.get0 q j)) (wq : Term)
    (hwqR : Term.isRT wq = true) (hwqW : Term.wf wq = true)
    (himg : convert (k + 3) (code (.P (V.set (upperVec q r) r c) .Z)) =
      .psi wq (dropOne (convert (k + 3) (code c))))
    (hH : Term.allLt (Term.H wq (dropOne (convert (k + 3) (code c))))
      (dropOne (convert (k + 3) (code c))) = true) :
    RecursiveWF (k + 3) (.P (V.set (upperVec q r) r c) .Z) := by
  refine RecursiveWF_P.2 ⟨fun j => ?_, recursive_zero _, ?_⟩
  · rw [V.get0_set _ r c j (by rw [upperVec_length]; exact hr)]
    split
    · exact hc
    · rw [get0_upperVec]; split
      · exact hqcoords j
      · exact recursive_zero _
  · rw [himg]
    exact (Term.wf_psi_iff _ _).mpr ⟨hwqR, hwqW, dropOne_wf hc.wf, hH⟩

theorem upper_image_top (k : Nat) (q : V multi.T) (hql : q.length = k + 3) (c : multi.T)
    (hc : c ≠ .Z) :
    convert (k + 3) (code (.P (V.set (upperVec q (k + 1)) (k + 1) c) .Z)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code (V.get0 q (k + 2)))))
        (dropOne (convert (k + 3) (code c))) := by
  generalize hW : V.set (upperVec q (k + 1)) (k + 1) c = W
  have hWl : W.length = k + 3 := by rw [← hW, V.length_set, upperVec_length, hql]
  have hW1 : V.get0 W (k + 1) = c := by
    rw [← hW]; exact V.get0_set_same _ _ _ (by rw [upperVec_length]; omega)
  have hW2 : V.get0 W (k + 2) = V.get0 q (k + 2) := by
    rw [← hW, V.get0_set_ne _ _ _ _ (by omega), get0_upperVec, ite_eq_left (by omega)]
  have hlow : ∀ j, j < k + 1 → V.get0 W j = .Z := by
    intro j hj
    rw [← hW, V.get0_set_ne _ _ _ j (by omega), get0_upperVec, ite_eq_right (by omega)]
  have hV := lift_image_top k W hWl (k + 1) (by rw [hW1]; exact hc)
  rw [lift_self_of_low W (k + 1) (by omega) hlow, hW1, hW2] at hV
  exact hV

theorem topOK_same_layer [LargeCardinals.{u}] (k : Nat) (xs q : V multi.T)
    (hxD : Dim (k + 3) (.P xs .Z)) (hqD : Dim (k + 3) (.P q .Z))
    (i r p : Nat) (hrk : r ≤ k + 1) (hr0 : 0 < r) (hpr : r < p)
    (hp : V.get0 xs p < V.get0 q p)
    (hhigh : ∀ j, p < j → V.get0 xs j = V.get0 q j)
    (hc0 : V.get0 xs i ≠ .Z) (hxsW : RecursiveWF (k + 3) (.P xs .Z))
    (hqW : RecursiveWF (k + 3) (.P q .Z))
    (hvx : RecursiveWF (k + 3) (.P (lift xs i r) .Z)) :
    RecursiveWF (k + 3) (.P (V.set (upperVec q r) r (V.get0 xs i)) .Z) := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hxsW).1
  have hqcoords : ∀ j, RecursiveWF (k + 3) (V.get0 q j) := (RecursiveWF_P.1 hqW).1
  have hcw := hcoords i
  have hxl := hxD.length
  have hql := hqD.length
  by_cases hrk' : r ≤ k
  · obtain ⟨ax, hax, haxw, hbaseX, heBaseX, _, heInsX⟩ := upper_context k r hrk' xs hxD hxsW
    obtain ⟨aq, haq, haqw, hbaseQ, heBaseQ, _, heInsQ⟩ := upper_context k r hrk' q hqD hqW
    have hx := lift_image_layer k r hr0 hrk' xs hxl i hc0 ax heInsX
    have hq := heInsQ _ hc0
    rw [step_layerCut r (by omega) aq _ (convert_ne_zero_of_ne hc0)] at hq
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hvx.wf)
    have hupper : multi.T.P (upperVec xs r) .Z ≤ multi.T.P (upperVec q r) .Z := by
      apply T.le_of_lt
      apply T.P_lt_P_of_vlt
      apply V.lt_of_pivot p
      · intro j hj
        rw [get0_upperVec, get0_upperVec, ite_eq_left (by omega), ite_eq_left (by omega), hhigh j hj]
        exact compareT_self _
      · rw [get0_upperVec, get0_upperVec, ite_eq_left hpr, ite_eq_left hpr]; exact hp
    have hle := uc_image_le_of_le k _ _ (Dim_upperVec hxD r) (Dim_upperVec hqD r) hbaseX hbaseQ hupper
    rw [heBaseX, heBaseQ] at hle
    obtain ⟨hcut, hpred⟩ := layerCut_comparable_of_erased_le r r (Nat.le_refl _) ax aq hax haq
      haxw haqw hle
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 (layerCut_regular r aq)
      (layerCut_wf r aq haq haqw) (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q r (by omega) _ hcw hqcoords _ (layerCut_regular r aq)
      (layerCut_wf r aq haq haqw) hq hH
  · have hrK : r = k + 1 := by omega
    subst hrK
    have hpK : p = k + 2 := by
      apply Nat.le_antisymm _ (by omega)
      apply Nat.le_of_not_lt; intro h
      rw [V.get0_ge q p (by omega)] at hp
      exact T.not_lt_Z _ hp
    subst hpK
    have hx := lift_image_top k xs hxl i hc0
    have hq := upper_image_top k q hql _ hc0
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hvx.wf)
    obtain ⟨hcut, hpred⟩ := kumakuma.GeneralImageHighestContextDiagonal.pairCut_image_comparable k _ _
      (hxD.coord _) (hqD.coord _) (hcoords _) (hqcoords _) (T.le_of_lt hp)
    have hqcut := kumakuma.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hqcoords (k + 2))
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 (pairCut_regular _ _) hqcut
      (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q _ (by omega) _ hcw hqcoords _ (pairCut_regular _ _) hqcut hq hH

theorem topOK_higher [LargeCardinals.{u}] (k : Nat) (xs q : V multi.T)
    (hxD : Dim (k + 3) (.P xs .Z)) (hqD : Dim (k + 3) (.P q .Z))
    (i r p : Nat) (hr0 : 0 < r) (hri : r < i) (hib : i ≤ k + 1)
    (hip : i < p)
    (hp : V.get0 xs p < V.get0 q p)
    (hhigh : ∀ j, p < j → V.get0 xs j = V.get0 q j)
    (hlow : ∀ j, j < i → V.get0 xs j = .Z)
    (hc0 : V.get0 xs i ≠ .Z) (hxsW : RecursiveWF (k + 3) (.P xs .Z))
    (hqW : RecursiveWF (k + 3) (.P q .Z)) :
    RecursiveWF (k + 3) (.P (V.set (upperVec q r) r (V.get0 xs i)) .Z) := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hxsW).1
  have hqcoords : ∀ j, RecursiveWF (k + 3) (V.get0 q j) := (RecursiveWF_P.1 hqW).1
  have hcw := hcoords i
  have hcy := convert_ne_zero_of_ne (k := k) hc0
  have hxl := hxD.length
  have hql := hqD.length
  have hrk : r ≤ k := by omega
  obtain ⟨aqr, haqr, haqrw, hbaseQr, heBaseQr, _, heInsQr⟩ := upper_context k r hrk q hqD hqW
  have hq := heInsQr _ hc0
  rw [step_layerCut r (by omega) aqr _ hcy] at hq
  have hxsLift := lift_self_of_low xs i (by omega) hlow
  have hmono : ∀ d, r ≤ d → multi.T.P (upperVec q d) .Z ≤ multi.T.P (upperVec q r) .Z := by
    intro d hd
    have := upperVec_mono q r (d - r)
    rwa [show r + (d - r) = d by omega] at this
  have hcutR : Term.isRT (layerCut r aqr) = true := layerCut_regular r aqr
  have hcutW : Term.wf (layerCut r aqr) = true := layerCut_wf r aqr haqr haqrw
  have hCof (h0 : aqr ≠ .zero) : Term.lt aqr (layerCut r aqr) = true := by
    have hfr := haqr.resolve_left h0
    simp only [layerCut, h0, ↓reduceIte]
    change Term.lt aqr (regular r aqr) = true
    rw [context_lt_regular hfr (above_principal hfr)]; simp [Term.le]
  have hPr (h0 : aqr ≠ .zero) : Term.predR (layerCut r aqr) = aqr := by
    simp only [layerCut, h0, ↓reduceIte]; exact predR_regular haqr h0 haqrw
  by_cases hik : i ≤ k
  · obtain ⟨ax, hax, haxw, hbaseX, heBaseX, _, heInsX⟩ := upper_context k i hik xs hxD hxsW
    obtain ⟨aqi, haqi, haqiw, hbaseQi, heBaseQi, _, _⟩ := upper_context k i hik q hqD hqW
    have hx := lift_image_layer k i (by omega) hik xs hxl i hc0 ax heInsX
    rw [hxsLift] at hx
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hxsW.wf)
    have hstrict : multi.T.P (upperVec xs i) .Z < multi.T.P (upperVec q i) .Z := by
      apply T.P_lt_P_of_vlt
      apply V.lt_of_pivot p
      · intro j hj
        rw [get0_upperVec, get0_upperVec, ite_eq_left (by omega), ite_eq_left (by omega), hhigh j hj]
        exact compareT_self _
      · rw [get0_upperVec, get0_upperVec, ite_eq_left hip, ite_eq_left hip]; exact hp
    have himg := (convert_order k _ _ (Dim_upperVec hxD i) (Dim_upperVec hqD i) hbaseX hbaseQi).mp
      hstrict
    rw [heBaseX, heBaseQi] at himg
    obtain ⟨hlt, haqi0⟩ := context_lt_of_image_lt hax haxw haqi haqiw himg
    have hle2 := uc_image_le_of_le k _ _ (Dim_upperVec hqD i) (Dim_upperVec hqD r) hbaseQi hbaseQr
      (hmono i (by omega))
    rw [heBaseQi, heBaseQr] at hle2
    have hle := context_le_of_image_le haqi haqiw haqr haqrw hle2
    have haqr0 : aqr ≠ .zero := by
      intro he; rw [he] at hle
      rcases (Term.le_iff_eq_or_lt _ _).mp hle with he' | hl
      · exact haqi0 he'
      · cases aqi <;> simp [Term.lt] at hl
    have hfi := haqi.resolve_left haqi0
    have hA : Term.lt (layerCut i ax) aqi = true :=
      kumakuma.GeneralImageCofinalityBounds.layerCut_lt_of_context_lt i ax aqi
        (by rcases hax with h | h
            · exact Or.inl h
            · exact Or.inr ⟨above_principal h, by omega⟩) hfi hlt
    have hcutXW := layerCut_wf i ax hax haxw
    have hAle := term_lt_of_lt_of_le hcutXW haqiw haqrw hA hle
    have hcut : Term.le (layerCut i ax) (layerCut r aqr) = true := by
      have := lemma_6_1.{u}.2.1 _ _ _ hcutXW haqrw hcutW hAle (hCof haqr0)
      simp [Term.le, this]
    have hpred : Term.le (Term.predR (layerCut i ax)) (Term.predR (layerCut r aqr)) = true := by
      rw [hPr haqr0]
      by_cases hax0 : ax = .zero
      · simp only [layerCut, hax0, ↓reduceIte, Term.predR, Term.le]
        simp [(zero_lt_iff _).mpr haqr0]
      · have hPx : Term.predR (layerCut i ax) = ax := by
          simp only [layerCut, hax0, ↓reduceIte]; exact predR_regular hax hax0 haxw
        rw [hPx]
        have := term_lt_of_lt_of_le haxw haqiw haqrw hlt hle
        simp [Term.le, this]
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 hcutR hcutW
      (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q r (by omega) _ hcw hqcoords _ hcutR hcutW hq hH
  · have hiK : i = k + 1 := by omega
    subst hiK
    have hpK : p = k + 2 := by
      apply Nat.le_antisymm _ (by omega)
      apply Nat.le_of_not_lt; intro h
      rw [V.get0_ge q p (by omega)] at hp
      exact T.not_lt_Z _ hp
    subst hpK
    have hx := lift_image_top k xs hxl (k + 1) hc0
    rw [hxsLift] at hx
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hxsW.wf)
    have hsl := succ_le_of_lt_source (k + 3) hp
    have hsrc : topNode k (kumakuma.SourceSuccessor.succ (k + 3) (V.get0 xs (k + 2))) ≤
        multi.T.P (upperVec q r) .Z := by
      rcases hsl with hl | he
      · apply T.le_of_lt
        show multi.T.P _ .Z < multi.T.P _ .Z
        apply T.P_lt_P_of_vlt
        apply V.lt_of_pivot (k + 2)
        · intro j hj
          rw [get0_lastVec, ite_eq_right (by omega), get0_upperVec, ite_eq_left (by omega),
            V.get0_ge q j (by omega)]
          exact compareT_ZZ
        · rw [get0_lastVec, ite_eq_left rfl, get0_upperVec, ite_eq_left (by omega)]; exact hl
      · refine T.le_trans ?_ (hmono (k + 1) (by omega))
        apply T.le_of_eqv
        show compareT (multi.T.P _ .Z) (multi.T.P _ .Z) = .eq
        apply (T.P_eqv_iff _ _ _ _).2 ⟨?_, compareT_ZZ⟩
        apply (V.eqv_iff_get0 _ _).2
        intro l
        rw [get0_lastVec, get0_upperVec]
        by_cases hl : l = k + 2
        · rw [ite_eq_left hl, ite_eq_left (by omega), hl]; exact he
        · rw [ite_eq_right hl]
          by_cases hl' : k + 1 < l
          · rw [ite_eq_left hl', V.get0_ge q l (by omega)]; exact compareT_ZZ
          · rw [ite_eq_right hl']; exact compareT_ZZ
    have hTopW := topNode_recursiveWF k _ ((recursive_succ_iff (k + 3) (k + 3) _).mpr (hcoords (k + 2)))
    have hTopD : Dim (k + 3) (topNode k (kumakuma.SourceSuccessor.succ (k + 3) (V.get0 xs (k + 2)))) :=
      Dim_topNode (kumakuma.SourceSuccessor.Dim_succ (hxD.coord _))
    have hle0 := uc_image_le_of_le k _ _ hTopD (Dim_upperVec hqD r) hTopW hbaseQr hsrc
    rw [highest_regular_image, heBaseQr] at hle0
    have hcutX := kumakuma.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hcoords (k + 2))
    have haqr0 : aqr ≠ .zero := by
      intro he
      rw [he, ite_eq_left rfl] at hle0
      have := (principal_le_one_iff (by simp [pairCut, Term.isPrin]) hcutX).mp hle0
      simp [pairCut, Term.one] at this
    rw [ite_eq_right haqr0] at hle0
    have hltCut : Term.lt (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
        (layerCut r aqr) = true := by
      rcases (Term.le_iff_eq_or_lt _ _).mp hle0 with he | hl
      · rw [he]; exact hCof haqr0
      · exact lemma_6_1.{u}.2.1 _ _ _ hcutX haqrw hcutW hl (hCof haqr0)
    have hcut : Term.le (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2)))))
        (layerCut r aqr) = true := by simp [Term.le, hltCut]
    have hpred : Term.le (Term.predR (pairCut (k + 1) (convert (k + 3) (code (V.get0 xs (k + 2))))))
        (Term.predR (layerCut r aqr)) = true := by
      rw [hPr haqr0]
      have hpl := predR_lt_self _ (pairCut_regular _ _) hcutX
      have hpw := ((sem_of_wf.{u} hcutX).isR_pred (pairCut_regular _ _)).1
      have := term_lt_of_lt_of_le hpw hcutX haqrw hpl hle0
      simp [Term.le, this]
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 hcutR hcutW
      (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q r (by omega) _ hcw hqcoords _ hcutR hcutW hq hH

theorem diagonal_topOK [LargeCardinals.{u}] (k : Nat)
    (xs q : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hf : V.fnz xs = some i) (hdq : domF (V.get0 xs i) = .Omega q) (hdiag : xs < q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (huc : VecUC k xs) :
    TopOK k q (V.get0 xs i) := by
  intro hc0 m _ _ r hmr hrk
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hlow := (V.fnz_some_spec xs i hf).2
  have hcw := hcoords i
  have hqD := Dim_Omega_label (hsD.coord i) hdq
  have hqW := Omega_label_recursiveWF k _ hcw hdq
  have hxl := hsD.length
  have hql := hqD.length
  have hil : i < k + 3 := by have := fnz_lt_length hf; omega
  have hib := kumakuma.GeneralImageClosedDiagonal.closed_diagonal_selector_bound k xs q i hsD hf hdq
    hdiag hr hs
  rw [lift_rplc_eq_upper q m r hmr (by omega)]
  have hneq : ∀ j, V.get0 xs i ≠ V.get0 q j := by
    intro j he
    have hmass := kumakuma.GeneralImageLabelClosure.Omega_label_mass_le (V.get0 xs i) hdq
    have hidx := mass_idx_lt q .Z j
    rw [he] at hmass
    omega
  by_cases hag : ∀ l, r < l → V.get0 xs l = V.get0 q l
  · rcases Nat.lt_trichotomy i r with hir | hir | hir
    · have he : V.set (upperVec q r) r (V.get0 xs i) = lift xs i r := by
        rw [lift_eq_upper_rplc xs i r (by omega)]
        congr 1
        apply V.eq_of_get0 _ _ (by rw [upperVec_length, upperVec_length, hxl, hql])
        intro l
        rw [get0_upperVec, get0_upperVec]
        by_cases hl : r < l
        · rw [ite_eq_left hl, ite_eq_left hl]; exact (hag l hl).symm
        · rw [ite_eq_right hl, ite_eq_right hl]
      rw [he]
      exact huc i r hir hrk hc0
    · have he : V.set (upperVec q r) r (V.get0 xs i) = xs := by
        apply V.eq_of_get0 _ _ (by rw [V.length_set, upperVec_length, hxl, hql])
        intro l
        rw [V.get0_set _ r _ l (by rw [upperVec_length]; omega), get0_upperVec]
        by_cases hl : l = r
        · rw [ite_eq_left hl, hl, hir]
        · rw [ite_eq_right hl]
          by_cases hlr : r < l
          · rw [ite_eq_left hlr]; exact (hag l hlr).symm
          · rw [ite_eq_right hlr]; exact (hlow l (by omega)).symm
      rw [he]; exact hs
    · exact False.elim (hneq i (hag i hir))
  · obtain ⟨p, hp, hhigh⟩ := lt_pivot_eq hsD hqD hdiag
    have hpr : r < p := by
      apply Classical.byContradiction; intro hpr
      apply hag
      intro l hl
      exact hhigh l (by omega)
    have hpi : i ≤ p := by
      apply Classical.byContradiction; intro hpi
      apply hneq i
      exact hhigh i (by omega)
    by_cases hir : i ≤ r
    · have hvx : RecursiveWF (k + 3) (.P (lift xs i r) .Z) := by
        rcases Nat.lt_or_eq_of_le hir with hlt | heq
        · exact huc i r hlt hrk hc0
        · rw [← heq, lift_self_of_low xs i (by omega) hlow]; exact hs
      exact topOK_same_layer k xs q hsD hqD i r p hrk (by omega) hpr hp hhigh hc0 hs hqW hvx
    · by_cases hpe : p = i
      · rw [hpe] at hp hhigh
        exact False.elim (higher_equal_context_false k xs q i hsD hf hdq (by omega) hib hr hs hhigh hp)
      · exact topOK_higher k xs q hsD hqD i r p (by omega) (by omega) hib (by omega) hp hhigh hlow hc0
          hs hqW

end kumakuma.GeneralImageUniformTop

namespace kumakuma.GeneralImageUniformMain

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageCoefficients kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder
open kumakuma.GeneralImageOmegaSpine kumakuma.GeneralImageLabelCut kumakuma.GeneralImageZeroFund
open kumakuma.GeneralImageLabelClosure kumakuma.GeneralImageParametricCut
open kumakuma.GeneralImageUniformClosure kumakuma.GeneralImageUniformContext
open kumakuma.GeneralImageUniformDiagonal kumakuma.GeneralImageUniformPreservation
open kumakuma.GeneralImageUniformTop kumakuma.BinaryTranslation kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageCofinalityBounds kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageClosedDiagonal kumakuma.TargetArithmetic
open kumakuma.GeneralImageLimitSupport

universe u

set_option maxRecDepth 10000

theorem topOK_transfer [LargeCardinals.{u}] (k : Nat) (q : V multi.T) (hql : q.length = k + 3)
    (c t : multi.T) (hc : TopOK k q c) (hc0 : c ≠ .Z) (ht : RecursiveWF (k + 3) t)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v (convert (k + 3) (code c))) (convert (k + 3) (code c)) = true →
      Term.allLt (Term.H v (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true) :
    TopOK k q t := by
  intro ht0 m hqf hqOne r hmr hrk
  have hold := hc hc0 m hqf hqOne r hmr hrk
  rw [lift_rplc_eq_upper q m r hmr (by omega)] at hold ⊢
  exact virtual_replace k (upperVec q r) (by rw [upperVec_length]; exact hql) r (by omega) hrk
    (fun l hl => by rw [get0_upperVec, ite_eq_right (by omega)])
    c t hc0 ht0 hold ht (fun w _ hwR hww hH => hrel w hwR hww hH)

theorem UC_ofNat (k : Nat) : ∀ n : Nat, UC k (ofNatD (k + 3) n)
  | 0 => UC_zero k
  | n + 1 => by
    change UC k (.P (zeros (k + 3)) (ofNatD (k + 3) n))
    rw [UC_P_iff]
    refine ⟨?_, ?_, UC_ofNat k n⟩
    · intro j r _ _ hj; rw [get0_zeros] at hj; exact absurd rfl hj
    · intro j; rw [get0_zeros]; exact UC_zero k

theorem UC_diagonal_iterates [LargeCardinals.{u}] (k : Nat) (c : multi.T) (hcD : Dim (k + 3) c)
    (hcr : Recursive c) (hcw : RecursiveWF (k + 3) c) (hcuc : UC k c)
    {q : V multi.T} (hd : domF c = .Omega q)
    (κ : Term) (hκ : CutFund k (.P q .Z) κ)
    (hSource : Term.allLt (Term.H κ (convert (k + 3) (code c))) (convert (k + 3) (code c)) = true)
    (htop : TopOK k q c) :
    ∀ j : Nat, UC k (multi.T.iter (T.fund c) (ofNatD (k + 3) j)) := by
  have hc0 : c ≠ .Z := by intro he; rw [he, domF_Z] at hd; cases hd
  have hql : q.length = k + 3 := (Dim_Omega_label hcD hd).length
  intro j
  induction j with
  | zero => exact UC_zero k
  | succ j ih =>
    rw [iter_ofNat_succ]
    have hIter := Omega_iter_at_label_cut_relative k c hcD hcr hcw hd κ hκ hSource j
    have hItD := (Omega_iter_at_label_cut k c hcD hcr hcw hd κ hκ hSource j).1
    exact UC_fund_Omega k c hcD hcr hcw hcuc hd κ hκ _ hItD hIter.1 ih
      (hIter.2 κ hκ.regular hκ.cutWf hSource)
      (topOK_transfer k q hql c _ htop hc0 hIter.1 hIter.2)

theorem UC_fund_zero [LargeCardinals.{u}] (k : Nat) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s → UC k s → UC k (T.fund s .Z)
  | .Z, _, _, _, _ => by rw [fund_Z]; exact UC_zero k
  | .P xs b, hsD, hr, hs, huc => by
    have omegaCase (q : V multi.T) (hd : domF (.P xs b) = .Omega q) :
        UC k (T.fund (.P xs b) .Z) := by
      obtain ⟨κ, hκ⟩ := Omega_label_cutFund k _ hsD hr hs hd
      exact UC_fund_Omega k _ hsD hr hs huc hd κ hκ .Z (Dim_Z _) (recursive_zero _) (UC_zero k)
        (by simp [convert_Z, Term.H, Term.allLt]) (fun h => absurd rfl h)
    have hcoordsR : ∀ j, Recursive (V.get0 xs j) := (Recursive_P.1 hr).1
    have hcoordsW : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
    have hxl : xs.length = k + 3 := hsD.length
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf]; exact UC_zero k
      · have hil := fnz_lt_length hf
        have hlow := (V.fnz_some_spec xs i hf).2
        have hc0 := (V.fnz_some_spec xs i hf).1
        cases hcd : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hcd) hc0
        | one =>
          cases i with
          | zero =>
            obtain ⟨c, hcc⟩ := dom_one_succ _ (hsD.coord 0) hcd
            rw [fund_zero_coordinate_successor k xs c _ hcc]
            exact UC_zero k
          | succ m => exact omegaCase xs (domF_one_succ hf hcd)
        | Omega q =>
          by_cases hdiag : xs < q
          · have hf0 : T.fund (.P xs .Z) .Z = .P (V.set xs i (T.fund (V.get0 xs i) .Z)) .Z :=
              fund_diag hf hcd hdiag .Z
            rw [hf0, UC_P_iff]
            refine ⟨VecUC_replace_zero_fund k xs i hxl hlow huc.vec hc0 (hsD.coord i) (hcoordsR i)
              (hcoordsW i), ?_, UC_zero k⟩
            intro j
            rw [V.get0_set xs i _ j hil]
            split
            · obtain ⟨κ, hκ⟩ := Omega_label_cutFund k _ (hsD.coord i) (hcoordsR i) (hcoordsW i) hcd
              exact UC_fund_Omega k _ (hsD.coord i) (hcoordsR i) (hcoordsW i) (huc.coord i) hcd κ hκ .Z
                (Dim_Z _) (recursive_zero _) (UC_zero k) (by simp [convert_Z, Term.H, Term.allLt])
                (fun h => absurd rfl h)
            · exact huc.coord j
          · exact omegaCase q (domF_nondiag hf hcd hdiag)
        | omega =>
          rw [fund_omega hf hcd, UC_P_iff]
          refine ⟨VecUC_replace_zero_fund k xs i hxl hlow huc.vec hc0 (hsD.coord i) (hcoordsR i)
            (hcoordsW i), ?_, UC_zero k⟩
          intro j
          rw [V.get0_set xs i _ j hil]
          split
          · exact UC_fund_zero k (V.get0 xs i) (hsD.coord i) (hcoordsR i) (hcoordsW i) (huc.coord i)
          · exact huc.coord j
    · rw [fund_tail xs hb, UC_P_iff]
      exact ⟨huc.vec, huc.coord, UC_fund_zero k b hsD.tail (Recursive_P.1 hr).2.1
        (RecursiveWF_P.1 hs).2.1 huc.tail⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem UC_fund_omega [LargeCardinals.{u}] (k : Nat) : ∀ (s : multi.T),
    Dim (k + 3) s → Recursive s → RecursiveWF (k + 3) s → UC k s → domF s = .omega →
    ∀ n : Nat, UC k (T.fund s (ofNatD (k + 3) n))
  | .Z, _, _, _, _, hd, _ => by rw [domF_Z] at hd; cases hd
  | .P xs b, hsD, hr, hs, huc, hd, n => by
    have hcoordsR : ∀ j, Recursive (V.get0 xs j) := (Recursive_P.1 hr).1
    have hcoordsW : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
    have hxl : xs.length = k + 3 := hsD.length
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · have hil := fnz_lt_length hf
        have hlow := (V.fnz_some_spec xs i hf).2
        have hc0 := (V.fnz_some_spec xs i hf).1
        cases hcd : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hcd) hc0
        | one =>
          cases i with
          | zero =>
            obtain ⟨c, hcc⟩ := dom_one_succ _ (hsD.coord 0) hcd
            rw [fund_zero_coordinate_successor k xs c _ hcc]
            apply UC_mul
            have hfz : T.fund (V.get0 xs 0) .Z = c := by
              rw [hcc, kumakuma.SourceSuccessor.fund_succ]
            have hU := VecUC_replace_zero_fund k xs 0 hxl (fun j hj => absurd hj (Nat.not_lt_zero j))
              huc.vec hc0 (hsD.coord 0) (hcoordsR 0) (hcoordsW 0)
            rw [hfz] at hU
            rw [UC_P_iff]
            refine ⟨hU, ?_, UC_zero k⟩
            intro j
            rw [V.get0_set xs 0 c j hil]
            split
            · have hcu := huc.coord 0
              rw [hcc] at hcu
              exact UC_succ c hcu
            · exact huc.coord j
          | succ m => rw [domF_one_succ hf hcd] at hd; cases hd
        | omega =>
          have htree := tree_of_UC k (V.get0 xs i) (hsD.coord i) (hcoordsR i) (hcoordsW i)
            (huc.coord i) hcd
          have hInv := ucTree_fund_invariant k htree (hsD.coord i) (hcoordsR i) (hcoordsW i) n
          rw [fund_omega hf hcd, UC_P_iff]
          refine ⟨VecUC_replace_min k xs hxl i hlow huc.vec hc0 _ hInv.1
            (fun _ _ _ _ w _ hwR hww hH => hInv.2.2 w hwR hww hH), ?_, UC_zero k⟩
          intro j
          rw [V.get0_set xs i _ j hil]
          split
          · exact UC_fund_omega k (V.get0 xs i) (hsD.coord i) (hcoordsR i) (hcoordsW i)
              (huc.coord i) hcd n
          · exact huc.coord j
        | Omega q =>
          have hdiag : xs < q := by
            by_cases hl : xs < q
            · exact hl
            · rw [domF_nondiag hf hcd hl] at hd; cases hd
          obtain ⟨κ, hκ, hSource⟩ := diagonal_closed k xs q i hsD hf hcd hdiag hr hs huc.vec
          have hIter := Omega_iter_at_label_cut_relative k _ (hsD.coord i) (hcoordsR i) (hcoordsW i)
            hcd κ hκ hSource (n + 1)
          rw [closed_diagonal_fund_eq xs q i hf hcd hdiag (k + 3) n, UC_P_iff]
          refine ⟨VecUC_replace_min k xs hxl i hlow huc.vec hc0 _ hIter.1
            (fun _ _ _ _ w _ hwR hww hH => hIter.2 w hwR hww hH), ?_, UC_zero k⟩
          intro j
          rw [V.get0_set xs i _ j hil]
          split
          · exact UC_diagonal_iterates k _ (hsD.coord i) (hcoordsR i) (hcoordsW i) (huc.coord i) hcd
              κ hκ hSource (diagonal_topOK k xs q i hsD hf hcd hdiag hr hs huc.vec) (n + 1)
          · exact huc.coord j
    · have hdb : domF b = .omega := by rwa [domF_tail xs hb] at hd
      rw [fund_tail xs hb, UC_P_iff]
      exact ⟨huc.vec, huc.coord, UC_fund_omega k b hsD.tail (Recursive_P.1 hr).2.1
        (RecursiveWF_P.1 hs).2.1 huc.tail hdb n⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem virtual_of_Omega_closed [LargeCardinals.{u}] (k : Nat) (ys : V multi.T)
    (hysD : Dim (k + 3) (.P ys .Z))
    (hys : RecursiveWF (k + 3) (.P ys .Z)) (r : Nat) (hr0 : 0 < r) (hrk : r ≤ k + 1)
    (y : multi.T) (hy : RecursiveWF (k + 3) y) (hy0 : y ≠ .Z)
    (hΩ : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code y))) (convert (k + 3) (code y)) =
      true) :
    RecursiveWF (k + 3) (.P (V.set (upperVec ys r) r y) .Z) := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 ys j) := (RecursiveWF_P.1 hys).1
  have hyy := convert_ne_zero_of_ne (k := k) hy0
  have hyl := hysD.length
  have key : ∃ w, Term.isRT w = true ∧ Term.wf w = true ∧ Term.lt Term.bigOmega w = true ∧
      convert (k + 3) (code (.P (V.set (upperVec ys r) r y) .Z)) =
        .psi w (dropOne (convert (k + 3) (code y))) := by
    by_cases hrk' : r ≤ k
    · obtain ⟨a, ha, haw, _, _, _, heIns⟩ := upper_context k r hrk' ys hysD hys
      refine ⟨layerCut r a, layerCut_regular r a, layerCut_wf r a ha haw,
        layerCut_above_Omega r hr0 a, ?_⟩
      rw [heIns y hy0, step_layerCut r (by omega) a _ hyy]
    · have hrEq : r = k + 1 := by omega
      subst hrEq
      exact ⟨_, kumakuma.GeneralImageSharedTopPair.pairCut_regular _ _,
        kumakuma.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hcoords (k + 2)),
        kumakuma.GeneralImageSharedTopPair.pairCut_above_Omega (k + 1) (by omega) _,
        upper_image_top k ys hyl y hy0⟩
  obtain ⟨w, hwR, hww, hΩw, himg⟩ := key
  have hw := kumakuma.GeneralImageComparableCuts.H_bound_of_comparable_cuts Term.bigOmega w _
    (by decide +kernel) Term.wf_bigOmega hwR hww hy.wf (by simp [Term.le, hΩw])
    (by rw [show Term.predR Term.bigOmega = .zero from rfl]; exact kumakuma.OT2.zero_le _)
    hΩ
  exact label_virtual_recursiveWF k ys r (by omega) y hy hcoords w hwR hww himg
    (kumakuma.GeneralImageRelativePredecessor.H_drop_bound w _ hy.wf hw)

theorem topOK_nat [LargeCardinals.{u}] (k : Nat) (q : V multi.T) (hqD : Dim (k + 3) (.P q .Z))
    (hqW : RecursiveWF (k + 3) (.P q .Z)) (n : Nat) : TopOK k q (ofNatD (k + 3) n) := by
  intro ht0 m _ _ r hmr hrk
  rw [lift_rplc_eq_upper q m r hmr (by rw [hqD.length]; omega)]
  apply virtual_of_Omega_closed k q hqD hqW r (by omega) hrk _ (numeral_recursiveWF _ _ n) ht0
  rw [convert_numeral]
  exact H_nat_bound _ n

theorem UC_fund_one (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s) (huc : UC k s)
    (hd : domF s = .one) (t : multi.T) : UC k (T.fund s t) := by
  obtain ⟨a, ha⟩ := dom_one_succ s hsD hd
  rw [ha, kumakuma.SourceSuccessor.fund_succ]
  rw [ha] at huc
  exact UC_succ a huc

theorem UC_fund_nat [LargeCardinals.{u}] (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s) (n : Nat) :
    UC k (T.fund s (ofNatD (k + 3) n)) := by
  cases hd : domF s with
  | zero => rw [(domF_eq_zero_iff s).mp hd, fund_Z]; exact UC_zero k
  | one => exact UC_fund_one k s hsD huc hd _
  | omega => exact UC_fund_omega k s hsD hr hs huc hd n
  | Omega q =>
    obtain ⟨κ, hκ⟩ := Omega_label_cutFund k s hsD hr hs hd
    have hqD := Dim_Omega_label hsD hd
    have hqW := Omega_label_recursiveWF k s hs hd
    exact UC_fund_Omega k s hsD hr hs huc hd κ hκ _ (Dim_ofNatD _ _)
      (numeral_recursiveWF _ _ n) (UC_ofNat k n)
      (by rw [convert_numeral]; exact H_nat_bound _ n)
      (topOK_nat k q hqD hqW n)

theorem fund_nat_recursiveWF [LargeCardinals.{u}] (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s) (n : Nat) :
    RecursiveWF (k + 3) (T.fund s (ofNatD (k + 3) n)) := by
  cases hd : domF s with
  | zero => rw [(domF_eq_zero_iff s).mp hd, fund_Z]; exact recursive_zero _
  | one => exact fund_one_recursiveWF s _ hsD hs hd
  | omega => exact (ucTree_fund_invariant k (tree_of_UC k s hsD hr hs huc hd) hsD hr hs n).1
  | Omega q =>
    obtain ⟨κ, hκ⟩ := Omega_label_cutFund k s hsD hr hs hd
    exact (Omega_fund_at_label_cut_invariant k s hsD hr hs hd κ hκ _ (Dim_ofNatD _ _)
      (numeral_recursiveWF _ _ n)
      (by rw [convert_numeral]; exact H_nat_bound _ n)).1

theorem UC_LF (k : Nat) : ∀ n : Nat, UC k (towerD (k + 3) n)
  | 0 => UC_zero k
  | n + 1 => by
    rw [LF_step (k + 2) n, UC_P_iff]
    refine ⟨?_, ?_, UC_zero k⟩
    · intro j r hjr hrk hj0
      rw [get0_lastVec, ite_eq_right (by omega)] at hj0
      exact absurd rfl hj0
    · intro j
      rw [get0_lastVec]
      split
      · exact UC_LF k n
      · exact UC_zero k

theorem H_Omega_LF (k : Nat) : ∀ (n : Nat) (z : Term),
    z ∈ Term.H Term.bigOmega (convert (k + 3) (code (towerD (k + 3) n))) → z = .zero
  | 0, z, hz => by
    have hz' : z ∈ Term.H Term.bigOmega (convert (k + 3) (code .Z)) := hz
    rw [convert_Z, Term.H] at hz'; cases hz'
  | n + 1, z, hz => by
    have he : towerD (k + 3) (n + 1) = topNode k (towerD (k + 3) n) := by
      rw [LF_step (k + 2) n]; rfl
    rw [he] at hz
    rcases H_topNode_support k _ hz with h | h
    · exact h
    · exact H_Omega_LF k n z h

theorem UC_basis [LargeCardinals.{u}] (k n : Nat) :
    UC k (.P (lowVec (k + 2) (towerD (k + 3) n)) .Z) := by
  have hbase : RecursiveWF (k + 3) (.P (lowVec (k + 2) (towerD (k + 3) n)) .Z) :=
    basis_recursiveWF k n
  have hbD : Dim (k + 3) (.P (lowVec (k + 2) (towerD (k + 3) n)) .Z) :=
    DOT.dim (DOT.base_succ (k + 2) n)
  rw [UC_P_iff]
  refine ⟨?_, ?_, UC_zero k⟩
  · intro j r hjr hrk hj0
    rw [get0_lowVec] at hj0
    have hj : j = 0 := by
      by_cases hj : j = 0
      · exact hj
      · rw [ite_eq_right hj] at hj0; exact absurd rfl hj0
    rw [ite_eq_left hj] at hj0
    rw [lift_eq_upper_rplc _ j r (by rw [lowVec_length]; omega), get0_lowVec, ite_eq_left hj]
    apply virtual_of_Omega_closed k _ hbD hbase r (by omega) hrk _ (LF_recursiveWF k n) hj0
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    rw [H_Omega_LF k n z hz]
    exact (zero_lt_iff _).mpr (convert_ne_zero_of_ne hj0)
  · intro j
    rw [get0_lowVec]
    split
    · exact UC_LF k n
    · exact UC_zero k

theorem generated_invariant [LargeCardinals.{u}] (k : Nat) {lam : Nat} {s : multi.T}
    (hs : DOT lam s) : lam = k + 3 → RecursiveWF (k + 3) s ∧ UC k s := by
  induction hs with
  | base_0 n => intro e; omega
  | base_succ lam n =>
    intro e
    have hl : lam = k + 2 := by omega
    subst hl
    exact ⟨basis_recursiveWF k n, UC_basis k n⟩
  | step lam s hs n ih =>
    intro e
    subst e
    obtain ⟨hw, huc⟩ := ih rfl
    have hr := isOT_recursive hs
    have hsD := DOT.dim hs
    exact ⟨fund_nat_recursiveWF k s hsD hr hw huc n, UC_fund_nat k s hsD hr hw huc n⟩

theorem fundClosure_all [LargeCardinals.{u}] (k : Nat) : FundClosure k := by
  intro s hs _ n
  exact (generated_invariant k (DOT.step (k + 3) s hs n) rfl).1

theorem limitLowFundClosure_all [LargeCardinals.{u}] (k : Nat) : LimitLowFundClosure k :=
  (fundClosure_iff_limit_low k).mp (fundClosure_all k)

theorem global_certificate [LargeCardinals.{u}] : kumakuma.GeneralImageEmbedding.GlobalCertificate :=
  kumakuma.GeneralImageIndexSupport.global_certificate_of_limit_low limitLowFundClosure_all

end kumakuma.GeneralImageUniformMain

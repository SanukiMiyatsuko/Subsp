import Subsp.Support.Uniform

/-! Top-layer closure of diagonals, generation of `RecursiveWF ∧ UC` for all OT, and `global_certificate`. -/

namespace Support.GeneralImageUniformTop

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageLimitSupport Support.GeneralImageRelativePredecessor
open Support.GeneralImageContextBoundDiagonal Support.GeneralImageSharedLowerContext
open Support.GeneralImageSharedContext Support.GeneralImageRegularDiagonal
open Support.GeneralImageRegularLimit Support.GeneralImageHeadCuts Support.GeneralImageSharedTopPair
open Support.GeneralImageCofinalityBounds Support.GeneralImageComparableCuts
open Support.BinaryTranslation Support.TargetArithmetic Support.SourceFundOrder Support.SourceFundGap
open Support.SourceRecursiveDescending
open Support.GeneralImageUniformClosure Support.GeneralImageUniformContext
open Support.GeneralImageUniformPreservation

universe u

set_option maxRecDepth 10000

theorem predR_lt_psi [LargeCardinals.{u}] (v b : Term) (hw : Term.wf (.psi v b) = true) :
    Term.lt (Term.predR v) (.psi v b) = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  have hpred := (sem_of_wf.{u} hp.2.1).isR_pred hp.1
  rw [lt_iff_V hpred.1 hw, hpred.2.1]
  exact regPred_lt_Ψ _ _

theorem upperVec_succ {lam : Nat} (q : Vec (new.T lam) lam) (r : Nat) (hr : r + 1 < lam) :
    upperVec q ⟨r + 1, hr⟩ = (upperVec q ⟨r, by omega⟩).rplc ⟨r + 1, hr⟩ .Z := by
  apply vec_ext; intro l
  rw [vec_rplc_idx, upperVec_idx, upperVec_idx]
  by_cases hl : l.val = r + 1
  · simp [hl]
  · by_cases hlr : r + 1 < l.val
    · simp [hl, hlr, show r < l.val by omega]
    · simp [hl, hlr, show ¬r < l.val by omega]

theorem upperVec_le_succ {lam : Nat} (q : Vec (new.T lam) lam) (r : Nat) (hr : r + 1 < lam) :
    new.T.le (.P (upperVec q ⟨r + 1, hr⟩) .Z) (.P (upperVec q ⟨r, by omega⟩) .Z) := by
  rw [upperVec_succ q r hr]
  by_cases hz : q.idx ⟨r + 1, hr⟩ = .Z
  · apply Or.inr
    have he : (upperVec q ⟨r, by omega⟩).rplc ⟨r + 1, hr⟩ .Z = upperVec q ⟨r, by omega⟩ := by
      apply vec_ext; intro l
      rw [vec_rplc_idx]
      split
      · rename_i hl
        rw [upperVec_idx, ite_eq_left (by simp at hl ⊢; omega)]
        have he : l = ⟨r + 1, hr⟩ := Fin.ext hl
        rw [he, hz]
      · rfl
    rw [he]; exact new.T_refl _
  · apply Or.inl
    change new.compareT (.P _ .Z) (.P _ .Z) = .lt
    simp only [new.compareT]
    rw [compareVec_rplc_lt _ _ _ (by
      rw [upperVec_idx, ite_eq_left (by simp)]
      cases hq : q.idx ⟨r + 1, hr⟩ with
      | Z => exact absurd hq hz
      | P => rfl)]

theorem upperVec_mono {lam : Nat} (q : Vec (new.T lam) lam) (r : Nat) :
    ∀ (d : Nat) (h : r + d < lam),
      new.T.le (.P (upperVec q ⟨r + d, h⟩) .Z) (.P (upperVec q ⟨r, by omega⟩) .Z)
  | 0, _ => Or.inr (new.T_refl _)
  | d + 1, h => by
    have h1 : new.T.le (.P (upperVec q ⟨r + (d + 1), h⟩) .Z) (.P (upperVec q ⟨r + d, by omega⟩) .Z) :=
      upperVec_le_succ q (r + d) h
    have h2 := upperVec_mono q r d (by omega)
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact Or.inl (new.T_trans _ _ _ h1 h2)
      · rw [new.T_eq_sound _ _ h2] at h1; exact Or.inl h1
    · rw [new.T_eq_sound _ _ h1]; exact h2

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

theorem lift_rplc_eq_upper {lam : Nat} (q : Vec (new.T lam) lam) (m r : Fin lam) (hmr : m.val < r.val)
    (c : new.T lam) : lift (q.rplc m c) m r = (upperVec q r).rplc r c := by
  rw [lift_eq_upper_rplc, rplc_idx_eq]
  congr 1
  apply vec_ext; intro l
  rw [upperVec_idx, upperVec_idx]
  by_cases hl : r.val < l.val
  · simp only [hl, ↓reduceIte]; exact rplc_idx_ne q m l c (by omega)
  · simp only [hl, ↓reduceIte]

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
      rw [Support.OT2.H_succTerm]
      exact List.mem_append_right _ (List.mem_append_left _ hz)

theorem lift_self_of_low {lam : Nat} (xs : Vec (new.T lam) lam) (i : Fin lam)
    (hlow : ∀ j, j.val < i.val → xs.idx j = .Z) : lift xs i i = xs := by
  apply vec_ext; intro l
  rw [lift_idx]
  by_cases hl : i.val < l.val
  · simp [hl]
  · by_cases he : l.val = i.val
    · rw [Fin.ext he]; simp
    · simp only [hl, he, ↓reduceIte]; exact (hlow l (by omega)).symm

theorem not_lt_zero_source {lam : Nat} (a : new.T lam) : ¬new.T.lt a .Z := by
  intro h
  change new.compareT a .Z = .lt at h
  cases a <;> simp [new.compareT] at h

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
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hi0 : 0 < i.val) (hib : i.val ≤ k + 1)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hhigh : ∀ l : Fin (k + 3), i.val < l.val → xs.idx l = q.idx l)
    (hlt : new.T.lt (xs.idx i) (q.idx i)) : False := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hspec := Support.DimensionCut.minIdx_spec xs hm
  have hchild := hspec.1.symm
  have hlow := hspec.2.2
  have hcr : Recursive (xs.idx i) := by rw [Recursive] at hr; exact hr.1 i
  have hcw := hcoords i
  have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchild; cases hchild
  have hcy := convert_ne_zero_of_ne hc0
  have hdrop := Support.GeneralImageMiddleSums.Omega_image_drop k _ hcr hcw hchild
  have hqW := Omega_label_recursiveWF k _ hcw hchild
  have hqcoords : ∀ j, RecursiveWF (k + 3) (q.idx j) := by rw [RecursiveWF] at hqW; exact hqW.1
  have hqi0 : q.idx i ≠ .Z := by intro he; rw [he] at hlt; exact not_lt_zero_source _ hlt
  have hqy := convert_ne_zero_of_ne hqi0
  have hxsLift := lift_self_of_low xs i hlow

  have key : ∃ w, Term.isRT w = true ∧ Term.wf w = true ∧ Term.lt Term.bigOmega w = true ∧
      Term.allLt (Term.H w (convert (k + 3) (code (xs.idx i)))) (convert (k + 3) (code (xs.idx i))) = true ∧
      dropOne (convert (k + 3) (code (q.idx i))) ∈ Term.H w (convert (k + 3) (code (.P q .Z))) := by
    by_cases hik : i.val ≤ k
    · obtain ⟨a, ha, haw, _, heBase, heX, heIns⟩ := upper_context k i.val hik xs hs
      have hiEq : (⟨i.val, by omega⟩ : Fin (k + 3)) = i := Fin.ext rfl
      have hxsImg := lift_image_layer k i.val hi0 hik xs i hc0 a heIns
      rw [hiEq, hxsLift] at hxsImg
      have hp := (Term.wf_psi_iff _ _).mp (hxsImg ▸ hs.wf)
      have hzero : ∀ j, j.val < i.val + 1 → (upperVec xs ⟨i.val, by omega⟩).idx j = .Z :=
        fun j hj => upperVec_low xs _ j (by change j.val ≤ i.val; omega)
      have hsame : ∀ j, i.val < j.val → q.idx j = (upperVec xs ⟨i.val, by omega⟩).idx j :=
        fun j hj => by rw [upperVec_high xs _ j (by change i.val < j.val; exact hj)]; exact (hhigh j hj).symm
      have heQ := principal_shared_lower_image k i.val hik _ q hzero hsame a ha heBase
      rw [lower_succ, converted_coordinate q ⟨i.val, by omega⟩, hiEq,
        step_layerCut i.val (by omega) a _ hqy] at heQ
      refine ⟨layerCut i.val a, hp.1, hp.2.1, layerCut_above_Omega i.val hi0 a,
        by rw [← hdrop]; exact hp.2.2.2, ?_⟩
      have hqWf := heQ ▸ hqW.wf
      have hpsiW := lower_context_wf i.val _ _ (Or.inr ⟨rfl, by simp [layerCut, Term.fT]⟩) hqWf
      rw [heQ]
      exact H_lower_visible i.val _ hp.1 hp.2.1 i.val (Nat.le_refl _) _ _
        (Or.inr ⟨rfl, by simp [Term.fT]⟩) (by simp [Term.lt, Term.fT])
        (predR_lt_psi _ _ hpsiW) hqWf _ (psi_self_visible _ _ hpsiW)
    · have hiK : i.val = k + 1 := by omega
      have hiEq : i = ⟨k + 1, by omega⟩ := Fin.ext hiK
      have hxsImg := lift_image_top k xs i hc0
      rw [← hiEq, hxsLift] at hxsImg
      have hp := (Term.wf_psi_iff _ _).mp (hxsImg ▸ hs.wf)
      have htop : xs.idx ⟨k + 2, by omega⟩ = q.idx ⟨k + 2, by omega⟩ := hhigh _ (by simp; omega)
      have heQ := principal_top_image k q
      rw [← htop, ← hiEq] at heQ
      have htp : topPair (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))
          (convert (k + 3) (code (q.idx i))) =
          .psi (pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩))))
            (dropOne (convert (k + 3) (code (q.idx i)))) := by
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
  have hRel := Support.GeneralImageHigherDiagonal.Omega_label_relative_bound k _ hcr hcw hchild w _
    hwR hww hΩw hcw.wf hHc
  have hQ := (Term.allLt_iff _ _).mp hRel _ hvis
  have hcq := (convert_order k _ _ hcw (hqcoords i)).mp hlt
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

theorem succ_le_of_lt_source {lam : Nat} {x y : new.T lam} (h : new.T.lt x y) :
    new.T.le (Support.SourceSuccessor.succ x) y := by
  rcases new.T_total (Support.SourceSuccessor.succ x) y with hl | hl | he
  · exact Or.inl hl
  · have hle := (Support.SourceSuccessor.lt_succ_iff_le y x).mp hl
    rcases hle with hle | hle
    · have := new.T_trans _ _ _ h hle
      change new.compareT x x = .lt at this
      rw [new.T_refl] at this; cases this
    · rw [new.T_eq_sound _ _ hle] at h
      change new.compareT x x = .lt at h
      rw [new.T_refl] at h; cases h
  · rw [he]; exact Or.inr (new.T_refl _)

theorem label_virtual_recursiveWF (k : Nat) (q : Vec (new.T (k + 3)) (k + 3)) (r : Fin (k + 3))
    (c : new.T (k + 3)) (hc : RecursiveWF (k + 3) c)
    (hqcoords : ∀ j, RecursiveWF (k + 3) (q.idx j)) (wq : Term)
    (hwqR : Term.isRT wq = true) (hwqW : Term.wf wq = true)
    (himg : convert (k + 3) (code (.P ((upperVec q r).rplc r c) .Z)) =
      .psi wq (dropOne (convert (k + 3) (code c))))
    (hH : Term.allLt (Term.H wq (dropOne (convert (k + 3) (code c))))
      (dropOne (convert (k + 3) (code c))) = true) :
    RecursiveWF (k + 3) (.P ((upperVec q r).rplc r c) .Z) := by
  rw [RecursiveWF]
  refine ⟨fun j => ?_, recursive_zero _ _, ?_⟩
  · rw [vec_rplc_idx]
    split
    · exact hc
    · rw [upperVec_idx]; split
      · exact hqcoords j
      · exact recursive_zero _ _
  · change Term.wf (convert (k + 3) (code (.P ((upperVec q r).rplc r c) .Z))) = true
    rw [himg]
    exact (Term.wf_psi_iff _ _).mpr ⟨hwqR, hwqW, dropOne_wf hc.wf, hH⟩

theorem upper_image_top (k : Nat) (q : Vec (new.T (k + 3)) (k + 3)) (c : new.T (k + 3)) (hc : c ≠ .Z) :
    convert (k + 3) (code (.P ((upperVec q ⟨k + 1, by omega⟩).rplc ⟨k + 1, by omega⟩ c) .Z)) =
      .psi (pairCut (k + 1) (convert (k + 3) (code (q.idx ⟨k + 2, by omega⟩))))
        (dropOne (convert (k + 3) (code c))) := by
  let V := (upperVec q ⟨k + 1, by omega⟩).rplc ⟨k + 1, by omega⟩ c
  have hlow : ∀ j : Fin (k + 3), j.val < k + 1 → V.idx j = .Z := by
    intro j hj
    simp only [V]
    rw [rplc_idx_ne _ _ _ _ (by simp; omega), upperVec_low _ _ _ (by simp; omega)]
  have hV := lift_image_top k V ⟨k + 1, by omega⟩ (by simp only [V]; rw [rplc_idx_eq]; exact hc)
  rw [lift_self_of_low V ⟨k + 1, by omega⟩ hlow] at hV
  rw [hV]
  simp only [V]
  rw [rplc_idx_eq, rplc_idx_ne _ _ _ _ (by simp), upperVec_high _ _ _ (by simp)]

theorem topOK_same_layer [LargeCardinals.{u}] (k : Nat) (xs q : Vec (new.T (k + 3)) (k + 3))
    (i r p : Fin (k + 3)) (hrk : r.val ≤ k + 1) (hr0 : 0 < r.val) (hpr : r.val < p.val)
    (hp : new.compareT (xs.idx p) (q.idx p) = .lt)
    (hhigh : ∀ j : Fin (k + 3), p.val < j.val → xs.idx j = q.idx j)
    (hc0 : xs.idx i ≠ .Z) (hxsW : RecursiveWF (k + 3) (.P xs .Z)) (hqW : RecursiveWF (k + 3) (.P q .Z))
    (hvx : RecursiveWF (k + 3) (.P (lift xs i r) .Z)) :
    RecursiveWF (k + 3) (.P ((upperVec q r).rplc r (xs.idx i)) .Z) := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hxsW; exact hxsW.1
  have hqcoords : ∀ j, RecursiveWF (k + 3) (q.idx j) := by rw [RecursiveWF] at hqW; exact hqW.1
  have hcw := hcoords i
  by_cases hrk' : r.val ≤ k
  · obtain ⟨ax, hax, haxw, hbaseX, heBaseX, _, heInsX⟩ := upper_context k r.val hrk' xs hxsW
    obtain ⟨aq, haq, haqw, hbaseQ, heBaseQ, _, heInsQ⟩ := upper_context k r.val hrk' q hqW
    have hrEq : (⟨r.val, by omega⟩ : Fin (k + 3)) = r := Fin.ext rfl
    have hx := lift_image_layer k r.val hr0 hrk' xs i hc0 ax heInsX
    rw [hrEq] at hx
    have hq := heInsQ _ hc0
    rw [step_layerCut r.val (by omega) aq _ (convert_ne_zero_of_ne hc0), hrEq] at hq
    rw [hrEq] at heBaseX heBaseQ hbaseX hbaseQ
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hvx.wf)
    have hupper : new.T.le (.P (upperVec xs r) .Z) (.P (upperVec q r) .Z) := by
      apply Or.inl
      change new.compareT (.P _ .Z) (.P _ .Z) = .lt
      simp only [new.compareT]
      rw [compareVec_of_lt_at _ _ p (by rwa [upperVec_high _ _ _ hpr, upperVec_high _ _ _ hpr])
        (fun j hj => by rw [upperVec_high _ _ _ (by omega), upperVec_high _ _ _ (by omega)];
                        exact hhigh j hj)]
    have hle := uc_image_le_of_le k _ _ hbaseX hbaseQ hupper
    rw [heBaseX, heBaseQ] at hle
    obtain ⟨hcut, hpred⟩ := layerCut_comparable_of_erased_le r.val r.val (Nat.le_refl _) ax aq hax haq
      haxw haqw hle
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 (layerCut_regular r.val aq)
      (layerCut_wf r.val aq haq haqw) (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q r _ hcw hqcoords _ (layerCut_regular r.val aq)
      (layerCut_wf r.val aq haq haqw) hq hH
  · have hrK : r.val = k + 1 := by omega
    have hrEq : r = ⟨k + 1, by omega⟩ := Fin.ext hrK
    have hpK : p = ⟨k + 2, by omega⟩ := Fin.ext (by show p.val = k + 2; have := p.isLt; omega)
    rw [hpK] at hp
    rw [hrEq] at hvx ⊢
    have hx := lift_image_top k xs i hc0
    have hq := upper_image_top k q _ hc0
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hvx.wf)
    obtain ⟨hcut, hpred⟩ := Support.GeneralImageHighestContextDiagonal.pairCut_image_comparable k _ _
      (hcoords _) (hqcoords _) (Or.inl hp)
    have hqcut := Support.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hqcoords ⟨k + 2, by omega⟩)
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 (pairCut_regular _ _) hqcut
      (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q _ _ hcw hqcoords _ (pairCut_regular _ _) hqcut hq hH

theorem topNode_succ_image (k : Nat) (y : new.T (k + 3)) :
    convert (k + 3) (code (Support.GeneralImageLimitBranches.topNode k (Support.SourceSuccessor.succ y))) =
      pairCut (k + 1) (convert (k + 3) (code y)) := by
  have hs0 : convert (k + 3) (code (Support.SourceSuccessor.succ y)) ≠ .zero := by
    rw [convert_succ]; exact succTerm_ne_zero _
  rw [Support.GeneralImageLimitBranches.topNode, principal_top_image]
  have h2 : (lastVec (k + 2) (Support.SourceSuccessor.succ y)).idx ⟨k + 2, by omega⟩ =
      Support.SourceSuccessor.succ y := by rw [lastVec_idx, ite_eq_left rfl]
  have h1 : (lastVec (k + 2) (Support.SourceSuccessor.succ y)).idx ⟨k + 1, by omega⟩ = .Z := by
    rw [lastVec_idx, ite_eq_right (by simp)]
  have hz : convert (k + 3) (code (.Z : new.T (k + 3))) = .zero := by rw [code, convert]
  rw [h2, h1, hz]
  have htp : topPair (k + 1) (convert (k + 3) (code (Support.SourceSuccessor.succ y))) .zero =
      .inacc (k + 1) (dropOne (convert (k + 3) (code (Support.SourceSuccessor.succ y)))) := by
    simp [topPair, hs0]
  rw [htp, lower_keep (k + 1) _ _ (by simp) (fun l hl => by
    rw [converted_coordinate _ ⟨l, by omega⟩, lastVec_idx, ite_eq_right (by simp; omega), code, convert])]
  rw [convert_succ]
  by_cases hy : convert (k + 3) (code y) = .zero
  · rw [hy]; rfl
  · rw [Support.GeneralImageLimitSupport.drop_succ _ hy]; simp [pairCut, hy]

theorem topOK_higher [LargeCardinals.{u}] (k : Nat) (xs q : Vec (new.T (k + 3)) (k + 3))
    (i r p : Fin (k + 3)) (hr0 : 0 < r.val) (hri : r.val < i.val) (hib : i.val ≤ k + 1)
    (hip : i.val < p.val)
    (hp : new.compareT (xs.idx p) (q.idx p) = .lt)
    (hhigh : ∀ j : Fin (k + 3), p.val < j.val → xs.idx j = q.idx j)
    (hlow : ∀ j : Fin (k + 3), j.val < i.val → xs.idx j = .Z)
    (hc0 : xs.idx i ≠ .Z) (hxsW : RecursiveWF (k + 3) (.P xs .Z)) (hqW : RecursiveWF (k + 3) (.P q .Z)) :
    RecursiveWF (k + 3) (.P ((upperVec q r).rplc r (xs.idx i)) .Z) := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hxsW; exact hxsW.1
  have hqcoords : ∀ j, RecursiveWF (k + 3) (q.idx j) := by rw [RecursiveWF] at hqW; exact hqW.1
  have hcw := hcoords i
  have hcy := convert_ne_zero_of_ne hc0
  have hrk : r.val ≤ k := by omega
  have hrEq : (⟨r.val, by omega⟩ : Fin (k + 3)) = r := Fin.ext rfl
  obtain ⟨aqr, haqr, haqrw, hbaseQr, heBaseQr, _, heInsQr⟩ := upper_context k r.val hrk q hqW
  rw [hrEq] at hbaseQr heBaseQr heInsQr
  have hq := heInsQr _ hc0
  rw [step_layerCut r.val (by omega) aqr _ hcy] at hq
  have hxsLift := lift_self_of_low xs i hlow
  have hmono : ∀ (d : Fin (k + 3)), r.val ≤ d.val →
      new.T.le (.P (upperVec q d) .Z) (.P (upperVec q r) .Z) := by
    intro d hd
    have := upperVec_mono q r.val (d.val - r.val) (by omega)
    have hD : (⟨r.val + (d.val - r.val), by omega⟩ : Fin (k + 3)) = d := Fin.ext (by simp; omega)
    rwa [hD, hrEq] at this
  have hcutR : Term.isRT (layerCut r.val aqr) = true := layerCut_regular r.val aqr
  have hcutW : Term.wf (layerCut r.val aqr) = true := layerCut_wf r.val aqr haqr haqrw

  have hCof (h0 : aqr ≠ .zero) : Term.lt aqr (layerCut r.val aqr) = true := by
    have hfr := haqr.resolve_left h0
    simp only [layerCut, h0, ↓reduceIte]
    change Term.lt aqr (regular r.val aqr) = true
    rw [context_lt_regular hfr (above_principal hfr)]; simp [Term.le]
  have hPr (h0 : aqr ≠ .zero) : Term.predR (layerCut r.val aqr) = aqr := by
    simp only [layerCut, h0, ↓reduceIte]; exact predR_regular haqr h0 haqrw
  by_cases hik : i.val ≤ k
  · obtain ⟨ax, hax, haxw, hbaseX, heBaseX, _, heInsX⟩ := upper_context k i.val hik xs hxsW
    obtain ⟨aqi, haqi, haqiw, hbaseQi, heBaseQi, _, _⟩ := upper_context k i.val hik q hqW
    have hiEq : (⟨i.val, by omega⟩ : Fin (k + 3)) = i := Fin.ext rfl
    rw [hiEq] at hbaseX heBaseX hbaseQi heBaseQi
    have hx := lift_image_layer k i.val (by omega) hik xs i hc0 ax heInsX
    rw [hiEq, hxsLift] at hx
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hxsW.wf)
    have hstrict : new.T.lt (.P (upperVec xs i) .Z) (.P (upperVec q i) .Z) := by
      change new.compareT (.P _ .Z) (.P _ .Z) = .lt
      simp only [new.compareT]
      rw [compareVec_of_lt_at _ _ p (by rwa [upperVec_high _ _ _ hip, upperVec_high _ _ _ hip])
        (fun j hj => by rw [upperVec_high _ _ _ (by omega), upperVec_high _ _ _ (by omega)];
                        exact hhigh j hj)]
    have himg := (convert_order k _ _ hbaseX hbaseQi).mp hstrict
    rw [heBaseX, heBaseQi] at himg
    obtain ⟨hlt, haqi0⟩ := context_lt_of_image_lt hax haxw haqi haqiw himg
    have hle2 := uc_image_le_of_le k _ _ hbaseQi hbaseQr (hmono i (by omega))
    rw [heBaseQi, heBaseQr] at hle2
    have hle := context_le_of_image_le haqi haqiw haqr haqrw hle2
    have haqr0 : aqr ≠ .zero := by
      intro he; rw [he] at hle
      rcases (Term.le_iff_eq_or_lt _ _).mp hle with he' | hl
      · exact haqi0 he'
      · cases aqi <;> simp [Term.lt] at hl
    have hfi := haqi.resolve_left haqi0
    have hA : Term.lt (layerCut i.val ax) aqi = true :=
      layerCut_lt_of_context_lt i.val ax aqi
        (by rcases hax with h | h
            · exact Or.inl h
            · exact Or.inr ⟨above_principal h, by omega⟩) hfi hlt
    have hcutXW := layerCut_wf i.val ax hax haxw
    have hAle := term_lt_of_lt_of_le hcutXW haqiw haqrw hA hle
    have hcut : Term.le (layerCut i.val ax) (layerCut r.val aqr) = true := by
      have := lemma_6_1.{u}.2.1 _ _ _ hcutXW haqrw hcutW hAle (hCof haqr0)
      simp [Term.le, this]
    have hpred : Term.le (Term.predR (layerCut i.val ax)) (Term.predR (layerCut r.val aqr)) = true := by
      rw [hPr haqr0]
      by_cases hax0 : ax = .zero
      · simp only [layerCut, hax0, ↓reduceIte, Term.predR, Term.le]
        simp [(zero_lt_iff _).mpr haqr0]
      · have hPx : Term.predR (layerCut i.val ax) = ax := by
          simp only [layerCut, hax0, ↓reduceIte]; exact predR_regular hax hax0 haxw
        rw [hPx]
        have := term_lt_of_lt_of_le haxw haqiw haqrw hlt hle
        simp [Term.le, this]
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 hcutR hcutW
      (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q r _ hcw hqcoords _ hcutR hcutW hq hH
  · have hiK : i.val = k + 1 := by omega
    have hpK : p = ⟨k + 2, by omega⟩ := Fin.ext (by show p.val = k + 2; have := p.isLt; omega)
    rw [hpK] at hp
    have hiEq : i = ⟨k + 1, by omega⟩ := Fin.ext hiK
    have hx := lift_image_top k xs i hc0
    rw [← hiEq, hxsLift] at hx
    have hpx := (Term.wf_psi_iff _ _).mp (hx ▸ hxsW.wf)
    have hsl := succ_le_of_lt_source
      (show new.T.lt (xs.idx ⟨k + 2, by omega⟩) (q.idx ⟨k + 2, by omega⟩) from hp)
    have hsrc : new.T.le (Support.GeneralImageLimitBranches.topNode k
        (Support.SourceSuccessor.succ (xs.idx ⟨k + 2, by omega⟩))) (.P (upperVec q r) .Z) := by
      rcases hsl with hl | he
      · apply Or.inl
        change new.compareT (.P _ .Z) (.P _ .Z) = .lt
        simp only [new.compareT]
        rw [compareVec_of_lt_at _ _ ⟨k + 2, by omega⟩
          (by rw [lastVec_idx, ite_eq_left rfl, upperVec_high _ _ _ (by simp; omega)]; exact hl)
          (fun j hj => by have := j.isLt; simp at hj; omega)]
      · have heTop : lastVec (k + 2) (Support.SourceSuccessor.succ (xs.idx ⟨k + 2, by omega⟩)) =
            upperVec q ⟨k + 1, by omega⟩ := by
          apply vec_ext; intro l
          rw [lastVec_idx, upperVec_idx]
          by_cases hl : l.val = k + 2
          · rw [ite_eq_left hl, ite_eq_left (by simp; omega)]
            rw [new.T_eq_sound _ _ he, show l = ⟨k + 2, by omega⟩ from Fin.ext hl]
          · rw [ite_eq_right hl, ite_eq_right (by simp; omega)]
        change new.T.le (.P (lastVec (k + 2) _) .Z) _
        rw [heTop]
        exact hmono ⟨k + 1, by omega⟩ (by simp; omega)
    have hTopW := Support.GeneralImageLimitBranches.topNode_recursiveWF k _
      ((recursive_succ_iff _ _).mpr (hcoords ⟨k + 2, by omega⟩))
    have hle0 := uc_image_le_of_le k _ _ hTopW hbaseQr hsrc
    rw [topNode_succ_image, heBaseQr] at hle0
    have hcutX := Support.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hcoords ⟨k + 2, by omega⟩)
    have haqr0 : aqr ≠ .zero := by
      intro he
      rw [he, ite_eq_left rfl] at hle0
      have := (principal_le_one_iff (by simp [pairCut, Term.isPrin]) hcutX).mp hle0
      simp [pairCut, Term.one] at this
    rw [ite_eq_right haqr0] at hle0
    have hltCut : Term.lt (pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩))))
        (layerCut r.val aqr) = true := by
      rcases (Term.le_iff_eq_or_lt _ _).mp hle0 with he | hl
      · rw [he]; exact hCof haqr0
      · exact lemma_6_1.{u}.2.1 _ _ _ hcutX haqrw hcutW hl (hCof haqr0)
    have hcut : Term.le (pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩))))
        (layerCut r.val aqr) = true := by simp [Term.le, hltCut]
    have hpred : Term.le (Term.predR (pairCut (k + 1) (convert (k + 3) (code (xs.idx ⟨k + 2, by omega⟩)))))
        (Term.predR (layerCut r.val aqr)) = true := by
      rw [hPr haqr0]
      have hpl := predR_lt_self _ (pairCut_regular _ _) hcutX
      have hpw := ((sem_of_wf.{u} hcutX).isR_pred (pairCut_regular _ _)).1
      have := term_lt_of_lt_of_le hpw hcutX haqrw hpl hle0
      simp [Term.le, this]
    have hH := H_bound_of_comparable_cuts _ _ _ hpx.1 hpx.2.1 hcutR hcutW
      (dropOne_wf hcw.wf) hcut hpred hpx.2.2.2
    exact label_virtual_recursiveWF k q r _ hcw hqcoords _ hcutR hcutW hq hH

theorem diagonal_topOK [LargeCardinals.{u}] (k : Nat)
    (xs q : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hm : new.T.domVecMinIdx xs = some (i, .Omega q)) (hdiag : Vec.lt xs q)
    (hr : Recursive (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z)) (huc : VecUC k xs) :
    TopOK k q (xs.idx i) := by
  intro hc0 m hml hq r hmr hrk
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hspec := Support.DimensionCut.minIdx_spec xs hm
  have hchild := hspec.1.symm
  have hlow := hspec.2.2
  have hcw := hcoords i
  have hqW := Omega_label_recursiveWF k _ hcw hchild
  have hib := Support.GeneralImageClosedDiagonal.closed_diagonal_selector_bound k xs q i hm hdiag hr hs
  rw [lift_rplc_eq_upper q ⟨m, by omega⟩ r (by simpa using hmr)]

  have hneq : ∀ j : Fin (k + 3), xs.idx i ≠ q.idx j := by
    intro j he
    have hmass := Support.GeneralImageLabelClosure.Omega_label_mass_le (xs.idx i) hchild
    have hidx := mass_idx_lt q .Z j
    rw [he] at hmass
    omega
  by_cases hag : ∀ l : Fin (k + 3), r.val < l.val → xs.idx l = q.idx l
  · rcases Nat.lt_trichotomy i.val r.val with hir | hir | hir
    · have he : (upperVec q r).rplc r (xs.idx i) = lift xs i r := by
        rw [lift_eq_upper_rplc]
        congr 1
        apply vec_ext; intro l
        rw [upperVec_idx, upperVec_idx]
        by_cases hl : r.val < l.val
        · simp only [hl, ↓reduceIte]; exact (hag l hl).symm
        · simp only [hl, ↓reduceIte]
      rw [he]
      exact huc i r hir hrk hc0
    · have he : (upperVec q r).rplc r (xs.idx i) = xs := by
        apply vec_ext; intro l
        rw [vec_rplc_idx, upperVec_idx]
        by_cases hl : l.val = r.val
        · rw [ite_eq_left hl, show l = i from Fin.ext (by omega)]
        · rw [ite_eq_right hl]
          by_cases hlr : r.val < l.val
          · rw [ite_eq_left hlr]; exact (hag l hlr).symm
          · rw [ite_eq_right hlr]; exact (hlow l (by omega)).symm
      rw [he]; exact hs
    · exact False.elim (hneq i (hag i hir))
  · obtain ⟨p, hp, hhigh⟩ := compareVec_lt_witness xs q hdiag
    have hpr : r.val < p.val := by
      apply Classical.byContradiction; intro hpr
      apply hag
      intro l hl
      exact hhigh l (by omega)
    have hpi : i.val ≤ p.val := by
      apply Classical.byContradiction; intro hpi
      apply hneq i
      exact hhigh i (by omega)
    by_cases hir : i.val ≤ r.val
    · have hvx : RecursiveWF (k + 3) (.P (lift xs i r) .Z) := by
        rcases Nat.lt_or_eq_of_le hir with hlt | heq
        · exact huc i r hlt hrk hc0
        · rw [show r = i from Fin.ext heq.symm, lift_self_of_low xs i hlow]; exact hs
      exact topOK_same_layer k xs q i r p hrk (by omega) hpr hp hhigh hc0 hs hqW hvx
    · by_cases hpe : p.val = i.val
      · have hpI : p = i := Fin.ext hpe
        rw [hpI] at hp hhigh
        exact False.elim (higher_equal_context_false k xs q i hm (by omega) hib hr hs hhigh hp)
      · exact topOK_higher k xs q i r p (by omega) (by omega) hib (by omega) hp hhigh hlow hc0 hs hqW

end Support.GeneralImageUniformTop

namespace Support.GeneralImageUniformMain

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageCoefficients Support.SourceRecursiveDescending Support.SourceFundOrder
open Support.GeneralImageOmegaSpine Support.GeneralImageLabelCut Support.GeneralImageZeroFund
open Support.GeneralImageLabelClosure
open Support.GeneralImageUniformClosure Support.GeneralImageUniformContext
open Support.GeneralImageUniformDiagonal Support.GeneralImageUniformPreservation
open Support.GeneralImageUniformTop Support.BinaryTranslation Support.GeneralImageSharedContext

universe u

set_option maxRecDepth 10000

theorem topOK_transfer [LargeCardinals.{u}] (k : Nat) (q : Vec (new.T (k + 3)) (k + 3))
    (c t : new.T (k + 3)) (hc : TopOK k q c) (hc0 : c ≠ .Z) (ht : RecursiveWF (k + 3) t)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v (convert (k + 3) (code c))) (convert (k + 3) (code c)) = true →
      Term.allLt (Term.H v (convert (k + 3) (code t))) (convert (k + 3) (code t)) = true) :
    TopOK k q t := by
  intro ht0 m hml hq r hmr hrk
  have hold := hc hc0 m hml hq r hmr hrk
  rw [lift_rplc_eq_upper q ⟨m, by omega⟩ r (by simpa using hmr)] at hold ⊢
  exact virtual_replace k (upperVec q r) r (by omega) hrk (fun l hl => upperVec_low q r l (by omega))
    c t hc0 ht0 hold ht (fun w _ hwR hww hH => hrel w hwR hww hH)

theorem fund_successor_zero_eq {lam : Nat} (xs : Vec (new.T lam) lam) (h0 : 0 < lam)
    (hm : new.T.domVecMinIdx xs = some (⟨0, h0⟩, .one)) (t : new.T lam) :
    new.T.fund (.P xs .Z) t = new.T.mul (.P (xs.rplc ⟨0, h0⟩ (new.T.fund (xs.idx ⟨0, h0⟩) .Z)) .Z) t := by
  rw [new.T.fund]
  simp only [↓reduceIte, hm]
  rfl

theorem fund_minIdx_none_eq {lam : Nat} (xs : Vec (new.T lam) lam)
    (hm : new.T.domVecMinIdx xs = none) (t : new.T lam) : new.T.fund (.P xs .Z) t = .Z := by
  rw [new.T.fund]; simp only [↓reduceIte, hm]

theorem UC_ofNat (k : Nat) : ∀ n : Nat, UC k (new.T.ofNat (lam := k + 3) n)
  | 0 => UC_zero k
  | n + 1 => by
    change UC k (.P (Vec.ofFn (k + 3) (fun _ => .Z)) (new.T.ofNat n))
    rw [UC_P_iff]
    refine ⟨?_, ?_, UC_ofNat k n⟩
    · intro j r _ _ hj; rw [Vec.ofFn_idx] at hj; exact absurd rfl hj
    · intro j; rw [Vec.ofFn_idx]; exact UC_zero k

theorem UC_diagonal_iterates [LargeCardinals.{u}] (k : Nat) (c : new.T (k + 3))
    (hcr : Recursive c) (hcw : RecursiveWF (k + 3) c) (hcuc : UC k c)
    {q : Vec (new.T (k + 3)) (k + 3)} (hd : new.T.dom c = .Omega q)
    (κ : Term) (hκ : CutFund k (.P q .Z) κ)
    (hSource : Term.allLt (Term.H κ (convert (k + 3) (code c))) (convert (k + 3) (code c)) = true)
    (htop : TopOK k q c) :
    ∀ j : Nat, UC k (new.T.iter (new.T.fund c) (new.T.ofNat j)) := by
  have hc0 : c ≠ .Z := by intro he; rw [he, new.T.dom] at hd; cases hd
  intro j
  induction j with
  | zero => simp only [new.T.ofNat, new.T.iter]; exact UC_zero k
  | succ j ih =>
    rw [iter_ofNat_succ]
    have hIter := Omega_iter_at_label_cut_relative k c hcr hcw hd κ hκ hSource j
    exact UC_fund_Omega k c hcr hcw hcuc hd κ hκ _ hIter.1 ih
      (hIter.2 κ hκ.regular hκ.cutWf hSource)
      (topOK_transfer k q c _ htop hc0 hIter.1 hIter.2)

theorem UC_fund_zero [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s) :
    UC k (new.T.fund s .Z) := by
  have omegaCase (q : Vec (new.T (k + 3)) (k + 3)) (hd : new.T.dom s = .Omega q) :
      UC k (new.T.fund s .Z) := by
    obtain ⟨κ, hκ⟩ := Omega_label_cutFund k s hr hs hd
    exact UC_fund_Omega k s hr hs huc hd κ hκ .Z (recursive_zero _ _) (UC_zero k)
      (by simp only [code, convert, Term.H, Term.allLt, List.all_nil])
      (fun h => absurd rfl h)
  cases heS : s with
  | Z => rw [new.T.fund]; exact UC_zero k
  | P xs b =>
    rw [heS] at hr hs huc omegaCase
    have hcoordsR : ∀ j, Recursive (xs.idx j) := by rw [Recursive] at hr; exact hr.1
    have hcoordsW : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
    by_cases hb : b = .Z
    · subst b
      cases hm : new.T.domVecMinIdx xs with
      | none => rw [fund_minIdx_none_eq xs hm]; exact UC_zero k
      | some sel =>
        obtain ⟨i, d⟩ := sel
        have hspec := Support.DimensionCut.minIdx_spec xs hm
        have hchild := hspec.1.symm
        have hlow := hspec.2.2
        cases d with
        | zero => exact False.elim (hspec.2.1 rfl)
        | one =>
          by_cases hi0 : i.val = 0
          · have heI : i = ⟨0, by omega⟩ := Fin.ext hi0
            rw [heI] at hm
            rw [fund_successor_zero_eq xs (by omega) hm]
            exact UC_zero k
          · exact omegaCase xs (by simp only [new.T.dom, ↓reduceIte, hm, hi0])
        | Omega q =>
          by_cases hdiag : Vec.lt xs q
          · have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchild; cases hchild
            have hf : new.T.fund (.P xs .Z) .Z = .P (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z := by
              simp only [new.T.fund, ↓reduceIte, hm, hdiag, GetElem.getElem, new.T.iter]
            rw [hf, UC_P_iff]
            refine ⟨VecUC_replace_zero_fund k xs i hlow huc.vec hc0 (hcoordsR i) (hcoordsW i), ?_, UC_zero k⟩
            intro j
            rw [vec_rplc_idx]
            split
            · rename_i hji
              have heJ : j = i := Fin.ext hji
              subst heJ
              obtain ⟨κ, hκ⟩ := Omega_label_cutFund k _ (hcoordsR j) (hcoordsW j) hchild
              exact UC_fund_Omega k _ (hcoordsR j) (hcoordsW j) (huc.coord j) hchild κ hκ .Z
                (recursive_zero _ _) (UC_zero k)
                (by simp only [code, convert, Term.H, Term.allLt, List.all_nil]) (fun h => absurd rfl h)
            · exact huc.coord j
          · exact omegaCase q (by simp only [new.T.dom, ↓reduceIte, hm, hdiag])
        | omega =>
          have hc0 : xs.idx i ≠ .Z := by intro he; rw [he, new.T.dom] at hchild; cases hchild
          rw [fund_omega_child_eq xs i hm, UC_P_iff]
          refine ⟨VecUC_replace_zero_fund k xs i hlow huc.vec hc0 (hcoordsR i) (hcoordsW i), ?_, UC_zero k⟩
          intro j
          rw [vec_rplc_idx]
          split
          · rename_i hji
            have heJ : j = i := Fin.ext hji
            subst heJ
            exact UC_fund_zero k (xs.idx j) (hcoordsR j) (hcoordsW j) (huc.coord j)
          · exact huc.coord j
    · have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      rw [fund_tail_eq xs b .Z hb, UC_P_iff]
      exact ⟨huc.vec, huc.coord, UC_fund_zero k b hbr hbw huc.tail⟩
termination_by new.T.size s
decreasing_by
  all_goals rw [heS]
  all_goals first
    | exact new.T.idx_size_lt_P _ _ _
    | exact new.T.add_size_lt_P _ _

theorem UC_fund_omega [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s)
    (hd : new.T.dom s = .omega) (n : Nat) : UC k (new.T.fund s (new.T.ofNat n)) := by
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
        have hc0 : xs.idx i ≠ .Z := by
          intro he; apply hspec.2.1; rw [hspec.1, he, new.T.dom]
        cases d with
        | zero => exact False.elim (hspec.2.1 rfl)
        | one =>
          by_cases hi0 : i.val = 0
          · have heI : i = ⟨0, by omega⟩ := Fin.ext hi0
            rw [heI] at hm hc0
            rw [fund_successor_zero_eq xs (by omega) hm]
            apply UC_mul
            rw [UC_P_iff]
            refine ⟨VecUC_replace_zero_fund k xs _ (fun j hj => absurd hj (by simp)) huc.vec hc0
              (hcoordsR _) (hcoordsW _), ?_, UC_zero k⟩
            intro j
            rw [vec_rplc_idx]
            split
            · exact UC_fund_zero k _ (hcoordsR _) (hcoordsW _) (huc.coord _)
            · exact huc.coord j
          · simp only [new.T.dom, ↓reduceIte, hm, hi0] at hd; cases hd
        | omega =>
          have htree := tree_of_UC k (xs.idx i) (hcoordsR i) (hcoordsW i) (huc.coord i) hchild
          have hInv := ucTree_fund_invariant k htree (hcoordsR i) (hcoordsW i) n
          rw [fund_omega_child_eq xs i hm, UC_P_iff]
          refine ⟨VecUC_replace_min k xs i hlow huc.vec hc0 _ hInv.1
            (fun _ _ _ _ w _ hwR hww hH => hInv.2.2 w hwR hww hH), ?_, UC_zero k⟩
          intro j
          rw [vec_rplc_idx]
          split
          · rename_i hji
            have heJ : j = i := Fin.ext hji
            subst heJ
            exact UC_fund_omega k (xs.idx j) (hcoordsR j) (hcoordsW j) (huc.coord j) hchild n
          · exact huc.coord j
        | Omega q =>
          have hdiag : Vec.lt xs q := by
            by_cases hl : Vec.lt xs q
            · exact hl
            · simp only [new.T.dom, ↓reduceIte, hm, hl] at hd; cases hd
          obtain ⟨κ, hκ, hSource⟩ := diagonal_closed k xs q i hm hdiag hr hs huc.vec
          have hIter := Omega_iter_at_label_cut_relative k _ (hcoordsR i) (hcoordsW i) hchild κ hκ
            hSource (n + 1)
          rw [Support.GeneralImageClosedDiagonal.closed_diagonal_fund_eq k xs q i hm hdiag n, UC_P_iff]
          refine ⟨VecUC_replace_min k xs i hlow huc.vec hc0 _ hIter.1
            (fun _ _ _ _ w _ hwR hww hH => hIter.2 w hwR hww hH), ?_, UC_zero k⟩
          intro j
          rw [vec_rplc_idx]
          split
          · rename_i hji
            have heJ : j = i := Fin.ext hji
            subst heJ
            exact UC_diagonal_iterates k _ (hcoordsR j) (hcoordsW j) (huc.coord j) hchild κ hκ hSource
              (diagonal_topOK k xs q j hm hdiag hr hs huc.vec) (n + 1)
          · exact huc.coord j
    · have hdb : new.T.dom b = .omega := by rwa [new.T.dom, ite_eq_right hb] at hd
      have hbr : Recursive b := by rw [Recursive] at hr; exact hr.2.1
      have hbw : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
      rw [fund_tail_eq xs b _ hb, UC_P_iff]
      exact ⟨huc.vec, huc.coord, UC_fund_omega k b hbr hbw huc.tail hdb n⟩
termination_by new.T.size s
decreasing_by
  all_goals rw [heS]
  all_goals first
    | exact new.T.idx_size_lt_P _ _ _
    | exact new.T.add_size_lt_P _ _

theorem virtual_of_Omega_closed [LargeCardinals.{u}] (k : Nat) (ys : Vec (new.T (k + 3)) (k + 3))
    (hys : RecursiveWF (k + 3) (.P ys .Z)) (r : Fin (k + 3)) (hr0 : 0 < r.val) (hrk : r.val ≤ k + 1)
    (y : new.T (k + 3)) (hy : RecursiveWF (k + 3) y) (hy0 : y ≠ .Z)
    (hΩ : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code y))) (convert (k + 3) (code y)) = true) :
    RecursiveWF (k + 3) (.P ((upperVec ys r).rplc r y) .Z) := by
  have hcoords : ∀ j, RecursiveWF (k + 3) (ys.idx j) := by rw [RecursiveWF] at hys; exact hys.1
  have hyy := convert_ne_zero_of_ne hy0
  have key : ∃ w, Term.isRT w = true ∧ Term.wf w = true ∧ Term.lt Term.bigOmega w = true ∧
      convert (k + 3) (code (.P ((upperVec ys r).rplc r y) .Z)) =
        .psi w (dropOne (convert (k + 3) (code y))) := by
    by_cases hrk' : r.val ≤ k
    · obtain ⟨a, ha, haw, _, _, _, heIns⟩ := upper_context k r.val hrk' ys hys
      have hrEq : (⟨r.val, by omega⟩ : Fin (k + 3)) = r := Fin.ext rfl
      rw [hrEq] at heIns
      refine ⟨layerCut r.val a, layerCut_regular r.val a, layerCut_wf r.val a ha haw,
        layerCut_above_Omega r.val hr0 a, ?_⟩
      rw [heIns y hy0, step_layerCut r.val (by omega) a _ hyy]
    · have hrEq : r = ⟨k + 1, by omega⟩ := Fin.ext (by show r.val = k + 1; omega)
      rw [hrEq]
      exact ⟨_, Support.GeneralImageSharedTopPair.pairCut_regular _ _,
        Support.GeneralImageChangingMiddle.pairCut_convert_wf k _ (hcoords ⟨k + 2, by omega⟩),
        Support.GeneralImageSharedTopPair.pairCut_above_Omega (k + 1) (by omega) _,
        upper_image_top k ys y hy0⟩
  obtain ⟨w, hwR, hww, hΩw, himg⟩ := key
  have hw := Support.GeneralImageComparableCuts.H_bound_of_comparable_cuts Term.bigOmega w _
    (by decide +kernel) Term.wf_bigOmega hwR hww hy.wf (by simp [Term.le, hΩw])
    (by rw [show Term.predR Term.bigOmega = .zero from rfl]; exact Support.OT2.zero_le _)
    hΩ
  exact label_virtual_recursiveWF k ys r y hy hcoords w hwR hww himg
    (Support.GeneralImageRelativePredecessor.H_drop_bound w _ hy.wf hw)

theorem topOK_nat [LargeCardinals.{u}] (k : Nat) (q : Vec (new.T (k + 3)) (k + 3))
    (hqW : RecursiveWF (k + 3) (.P q .Z)) (n : Nat) : TopOK k q (new.T.ofNat n) := by
  intro ht0 m hml _ r hmr hrk
  rw [lift_rplc_eq_upper q ⟨m, by omega⟩ r (by simpa using hmr)]
  apply virtual_of_Omega_closed k q hqW r (by omega) hrk _
    (Support.GeneralImageCountableRecursion.numeral_recursiveWF _ _ n) ht0
  rw [Support.GeneralImageCountableRecursion.convert_numeral]
  exact Support.GeneralImageLimitBranches.H_nat_bound _ n

theorem UC_fund_one (k : Nat) (s : new.T (k + 3)) (huc : UC k s) (hd : new.T.dom s = .one)
    (t : new.T (k + 3)) : UC k (new.T.fund s t) := by
  obtain ⟨a, ha⟩ := dom_one_succ s hd
  rw [ha, Support.SourceSuccessor.fund_succ]
  rw [ha] at huc
  exact UC_succ a huc

theorem UC_fund_nat [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s) (n : Nat) :
    UC k (new.T.fund s (new.T.ofNat n)) := by
  cases hd : new.T.dom s with
  | zero => rw [(Support.DimensionCut.dom_eq_zero_iff s).mp hd, new.T.fund]; exact UC_zero k
  | one => exact UC_fund_one k s huc hd _
  | omega => exact UC_fund_omega k s hr hs huc hd n
  | Omega q =>
    obtain ⟨κ, hκ⟩ := Omega_label_cutFund k s hr hs hd
    have hqW := Support.GeneralImageCofinalityBounds.Omega_label_recursiveWF k s hs hd
    exact UC_fund_Omega k s hr hs huc hd κ hκ _
      (Support.GeneralImageCountableRecursion.numeral_recursiveWF _ _ n) (UC_ofNat k n)
      (by rw [Support.GeneralImageCountableRecursion.convert_numeral];
          exact Support.GeneralImageLimitBranches.H_nat_bound _ n)
      (topOK_nat k q hqW n)

theorem fund_nat_recursiveWF [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hr : Recursive s) (hs : RecursiveWF (k + 3) s) (huc : UC k s) (n : Nat) :
    RecursiveWF (k + 3) (new.T.fund s (new.T.ofNat n)) := by
  cases hd : new.T.dom s with
  | zero => rw [(Support.DimensionCut.dom_eq_zero_iff s).mp hd, new.T.fund]; exact recursive_zero _ _
  | one => exact fund_one_recursiveWF s _ hs hd
  | omega => exact (ucTree_fund_invariant k (tree_of_UC k s hr hs huc hd) hr hs n).1
  | Omega q =>
    obtain ⟨κ, hκ⟩ := Omega_label_cutFund k s hr hs hd
    exact (Omega_fund_at_label_cut_invariant k s hr hs hd κ hκ _
      (Support.GeneralImageCountableRecursion.numeral_recursiveWF _ _ n)
      (by rw [Support.GeneralImageCountableRecursion.convert_numeral];
          exact Support.GeneralImageLimitBranches.H_nat_bound _ n)).1

theorem UC_LF (k : Nat) : ∀ n : Nat, UC k (new.T.LF (k + 3) n)
  | 0 => by rw [new.T.LF]; exact UC_zero k
  | n + 1 => by
    rw [LF_step (k + 2) n, UC_P_iff]
    refine ⟨?_, ?_, UC_zero k⟩
    · intro j r hjr hrk hj0
      rw [lastVec_idx, ite_eq_right (by omega)] at hj0
      exact absurd rfl hj0
    · intro j
      rw [lastVec_idx]
      split
      · exact UC_LF k n
      · exact UC_zero k

theorem H_Omega_LF (k : Nat) : ∀ (n : Nat) (z : Term),
    z ∈ Term.H Term.bigOmega (convert (k + 3) (code (new.T.LF (k + 3) n))) → z = .zero
  | 0, z, hz => by
    rw [new.T.LF] at hz
    simp only [code, convert, Term.H] at hz
    cases hz
  | n + 1, z, hz => by
    have he : new.T.LF (k + 3) (n + 1) = Support.GeneralImageLimitBranches.topNode k (new.T.LF (k + 3) n) := by
      rw [LF_step (k + 2) n]; rfl
    rw [he] at hz
    rcases Support.GeneralImageLimitBranches.H_topNode_support k _ hz with h | h
    · exact h
    · exact H_Omega_LF k n z h

theorem UC_basis [LargeCardinals.{u}] (k n : Nat) :
    UC k (.P (lowVec (k + 2) (new.T.LF (k + 3) n)) .Z) := by
  have hbase : RecursiveWF (k + 3) (.P (lowVec (k + 2) (new.T.LF (k + 3) n)) .Z) := by
    simpa only [Support.GeneralImageEmbedding.basis, Support.OTQuotient.lowerBase]
      using basis_recursiveWF k n
  rw [UC_P_iff]
  refine ⟨?_, ?_, UC_zero k⟩
  · intro j r hjr hrk hj0
    rw [lowVec_idx] at hj0
    have hj : j.val = 0 := by
      by_cases hj : j.val = 0
      · exact hj
      · rw [ite_eq_right hj] at hj0; exact absurd rfl hj0
    rw [ite_eq_left hj] at hj0
    rw [lift_eq_upper_rplc, lowVec_idx, ite_eq_left hj]
    apply virtual_of_Omega_closed k _ hbase r (by omega) hrk _ (LF_recursiveWF k n) hj0
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    rw [H_Omega_LF k n z hz]
    exact (Support.TargetArithmetic.zero_lt_iff _).mpr (convert_ne_zero_of_ne hj0)
  · intro j
    rw [lowVec_idx]
    split
    · exact UC_LF k n
    · exact UC_zero k

theorem generated_invariant [LargeCardinals.{u}] (k : Nat) {lam : Nat} {s : new.T lam}
    (hs : new.T.isOT lam s) :
    ∀ e : lam = k + 3, RecursiveWF (k + 3) (e ▸ s) ∧ UC k (e ▸ s) := by
  induction hs with
  | base_0 n => intro e; omega
  | base_succ lam n =>
    intro e
    have hl : lam = k + 2 := by omega
    subst lam
    cases e
    refine ⟨?_, ?_⟩
    · simpa only [Support.GeneralImageEmbedding.basis, Support.OTQuotient.lowerBase,
        lowVec] using basis_recursiveWF k n
    · simpa only [lowVec] using UC_basis k n
  | step lam s hs n ih =>
    intro e
    subst e
    obtain ⟨hw, huc⟩ := ih rfl
    have hr := isOT_recursive hs
    exact ⟨fund_nat_recursiveWF k s hr hw huc n, UC_fund_nat k s hr hw huc n⟩

theorem fundClosure_all [LargeCardinals.{u}] (k : Nat) : FundClosure k := by
  intro s hs _ n
  exact (generated_invariant k (new.T.isOT.step (k + 3) s hs n) rfl).1

theorem limitLowFundClosure_all [LargeCardinals.{u}] (k : Nat) : LimitLowFundClosure k :=
  (fundClosure_iff_limit_low k).mp (fundClosure_all k)

theorem global_certificate [LargeCardinals.{u}] : Support.GeneralImageEmbedding.GlobalCertificate :=
  Support.GeneralImageIndexSupport.global_certificate_of_limit_low limitLowFundClosure_all

end Support.GeneralImageUniformMain

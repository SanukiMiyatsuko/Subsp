import Subsp.Buchholz.Rank1
import Subsp.multi.Lex

/-! The order isomorphism between the ordinal terms of a fundamental-sequence system on
`multi.T` and a segment of Buchholz normal forms, assembled from the separate facts proved
for each system: an invariant containing all ordinal terms, a strictly monotone translation,
surjectivity of the translation, and cofinality of the fundamental sequences. -/

theorem MultiAssembly.order_iso (S : multi.FundSys)
    (Inv : multi.T → Prop) (tr : multi.T → T) (bound : T)
    (hbase : ∀ n, Inv (S.base n))
    (hfund : ∀ s, Inv s → ∀ n, Inv (S.fund s (multi.T.ofNat n)))
    (hnorm : ∀ s, Inv s → Inv (multi.T.norm s))
    (htrn : ∀ s, tr (multi.T.norm s) = tr s)
    (htr : ∀ s, Inv s → T.isNF1 (tr s) ∧ tr s < bound)
    (hmono : ∀ s t, Inv s → Inv t → s < t → tr s < tr t)
    (hlt : ∀ s n, s ≠ multi.T.Z → S.fund s (multi.T.ofNat n) < s)
    (hcof : ∀ a b, Inv a → Inv b → b < a → ∃ n, b ≤ S.fund a (multi.T.ofNat n))
    (hsurj : ∀ u, T.isNF1 u → u < bound → ∃ s, Inv s ∧ tr s = u)
    (hcov : ∀ s, Inv s → ∃ n, s ≤ S.base n) :
    ∃ f : @multi.FundSys.NOT S → { u : T // T.isNF1 u ∧ u < bound },
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  -- every ordinal term satisfies the invariant
  have hInv : ∀ a : multi.NT, S.NIsOT a → Inv a.1 := by
    intro a ha
    induction ha with
    | base n => exact hnorm _ (hbase n)
    | step s _ n ih =>
      show Inv (multi.T.norm (S.fund s.1 (multi.T.rep (multi.T.ofNat n)).1))
      rw [multi.T.rep_ofNat]
      exact hnorm _ (hfund _ ih n)
  -- the translation reflects the order and is injective on normal terms
  have hreflect : ∀ s t : multi.NT, Inv s.1 → Inv t.1 → tr s.1 < tr t.1 → s < t := by
    intro s t hs ht h
    rcases multi.NT.lt_trichotomy s t with hst | rfl | hts
    · exact hst
    · exact absurd h (lt_irrefl_thm _)
    · exact absurd h (lt_asymm_thm (hmono _ _ ht hs hts))
  have hinj : ∀ s t : multi.NT, Inv s.1 → Inv t.1 → tr s.1 = tr t.1 → s = t := by
    intro s t hs ht h
    rcases multi.NT.lt_trichotomy s t with hst | heq | hts
    · have := hmono _ _ hs ht hst; rw [h] at this; exact absurd this (lt_irrefl_thm _)
    · exact heq
    · have := hmono _ _ ht hs hts; rw [h] at this; exact absurd this (lt_irrefl_thm _)
  -- downward closure of the ordinal terms
  have hwf : WellFounded (fun a b : { x : multi.NT // S.NIsOT x } => a.1 < b.1) :=
    Subrelation.wf (fun {a b} h => hmono _ _ (hInv _ a.2) (hInv _ b.2) h)
      (InvImage.wf (fun a : { x : multi.NT // S.NIsOT x } =>
        (⟨tr a.1.1, (htr _ (hInv _ a.2)).1⟩ : T.NF1)) T.well_founded_NF1)
  have hdown : ∀ a : { x : multi.NT // S.NIsOT x }, ∀ b : multi.NT, Inv b.1 → b.1 ≤ a.1.1 →
      S.NIsOT b := by
    intro a
    induction a using hwf.induction with
    | h a ih =>
      intro b hb hba
      rcases hba with hba | heq
      · obtain ⟨n, hn⟩ := hcof a.1.1 b.1 (hInv _ a.2) hb hba
        have hc : S.NIsOT (S.ntFund a.1 (multi.T.rep (multi.T.ofNat n))) := .step _ a.2 n
        have hcval : (S.ntFund a.1 (multi.T.rep (multi.T.ofNat n))).1 =
            multi.T.norm (S.fund a.1.1 (multi.T.ofNat n)) := by
          show multi.T.norm (S.fund a.1.1 (multi.T.rep (multi.T.ofNat n)).1) = _
          rw [multi.T.rep_ofNat]
        have hane : a.1.1 ≠ multi.T.Z := by
          intro h; rw [h] at hba; exact multi.T.not_lt_Z _ hba
        have hclt : S.ntFund a.1 (multi.T.rep (multi.T.ofNat n)) < a.1 := by
          show (S.ntFund a.1 (multi.T.rep (multi.T.ofNat n))).1 < a.1.1
          rw [hcval]
          have h1 := (multi.T.lt_norm_iff _ _).1 (hlt a.1.1 n hane)
          rwa [a.1.2] at h1
        apply ih ⟨_, hc⟩ hclt b hb
        show b.1 ≤ (S.ntFund a.1 (multi.T.rep (multi.T.ofNat n))).1
        rw [hcval]
        have h1 := (multi.T.le_norm_iff _ _).1 hn
        rwa [b.2] at h1
      · have : b = a.1 := (multi.NT.compare_eq_iff b a.1).1 heq
        rw [this]; exact a.2
  refine ⟨fun s => ⟨tr s.1.1, htr _ (hInv _ s.2)⟩, ?_, ?_, ?_⟩
  · intro s t h
    have h' : tr s.1.1 = tr t.1.1 := congrArg Subtype.val h
    exact Subtype.ext (hinj _ _ (hInv _ s.2) (hInv _ t.2) h')
  · intro u
    obtain ⟨s0, hs0, htr0⟩ := hsurj u.1 u.2.1 u.2.2
    let b : multi.NT := multi.T.rep s0
    have hb : Inv b.1 := hnorm _ hs0
    obtain ⟨n, hn⟩ := hcov _ hb
    have hbase' : S.NIsOT (multi.T.rep (S.base n)) := .base n
    have hle : b.1 ≤ (multi.T.rep (S.base n)).1 := by
      have h1 := (multi.T.le_norm_iff _ _).1 hn
      rw [b.2] at h1; exact h1
    refine ⟨⟨b, hdown ⟨_, hbase'⟩ b hb hle⟩, Subtype.ext ?_⟩
    show tr (multi.T.norm s0) = u.1
    rw [htrn, htr0]
  · intro s t
    constructor
    · exact hmono _ _ (hInv _ s.2) (hInv _ t.2)
    · exact hreflect s.1 t.1 (hInv _ s.2) (hInv _ t.2)

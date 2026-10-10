import Subsp.multi.kuma.Order

/-! `RecursiveWF`, the wf invariant of images, and source subterm/fund gap bounds (the `multi`
version of `Subsp/Support/WF.lean`). -/

namespace kumakuma.GeneralImageWFInvariant

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource kumakuma.DimensionCut
open kumakuma.GeneralImageEmbedding kumakuma.GeneralImageRawOrder

theorem recursive_zero (d : Nat) : RecursiveWF d .Z := RecursiveWF_Z d

theorem code_ofNatD_one (lam : Nat) : code (ofNatD lam 1) = UserImage.oneCode := by
  rw [FiniteCorrespondence.code_ofNatD]; rfl

theorem fixed_LF_wf (k n : Nat) :
    Term.wf (DimensionImage.convert (k + 3) (code (towerD (k + 3) n))) = true := by
  match n with
  | 0 =>
    show Term.wf (DimensionImage.convert (k + 3) (code .Z)) = true
    rw [convert_Z]; rfl
  | 1 =>
    rw [LF_one, code_ofNatD_one, DimensionImage.convert_one]
    exact Term.wf_one
  | n + 2 => rw [fixed_LF_value]; exact tower_wf k (n + 1)

theorem LF_recursiveWF (k n : Nat) : RecursiveWF (k + 3) (towerD (k + 3) n) := by
  induction n with
  | zero => exact recursive_zero _
  | succ n ih =>
    have h := fixed_LF_wf k (n + 1)
    rw [LF_step (k + 2) n] at h ⊢
    refine RecursiveWF_P.2 ⟨?_, recursive_zero _, h⟩
    intro i
    rw [get0_lastVec]
    split
    · exact ih
    · exact recursive_zero _

theorem fixed_basis_wf (k n : Nat) :
    Term.wf (DimensionImage.convert (k + 3) (code (basis k n).2.val)) = true := by
  show Term.wf (DimensionImage.convert (k + 3)
    (code (.P (lowVec (k + 2) (towerD (k + 3) n)) .Z))) = true
  rw [code_P, trim_codes_lowVec, code_Z]
  match n with
  | 0 =>
    show Term.wf (DimensionImage.convert (k + 3) (.p (trim [code .Z]) .zero)) = true
    rw [code_Z]
    show Term.wf (DimensionImage.convert (k + 3) UserImage.oneCode) = true
    rw [DimensionImage.convert_one]
    exact Term.wf_one
  | 1 =>
    rw [LF_one, code_ofNatD_one]
    show Term.wf (DimensionImage.convert (k + 3) (.p [UserImage.oneCode] .zero)) = true
    simp only [DimensionImage.convert, DimensionImage.arguments,
      DimensionImage.principal_singleton, DimensionImage.convert_one, OT2.assemble, ↓reduceIte]
    decide +kernel
  | n + 2 =>
    have hc : trim [code (towerD (k + 3) (n + 2))] = [code (towerD (k + 3) (n + 2))] := by
      cases he : code (towerD (k + 3) (n + 2)) with
      | zero => exact False.elim (LF_positive (k + 2) (n + 1) ((code_eq_zero_iff _).1 he))
      | p xs b => rfl
    rw [hc]
    simp only [DimensionImage.convert, DimensionImage.arguments,
      DimensionImage.principal_singleton, fixed_LF_value, OT2.assemble, ↓reduceIte]
    exact psi_tower_wf k (n + 1)

theorem basis_recursiveWF (k n : Nat) : RecursiveWF (k + 3) (basis k n).2.val := by
  show RecursiveWF (k + 3) (.P (lowVec (k + 2) (towerD (k + 3) n)) .Z)
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, fixed_basis_wf k n⟩
  intro i
  rw [get0_lowVec]
  split
  · exact LF_recursiveWF k n
  · exact recursive_zero _

theorem assemble_succ (p t : Term) (hp : Term.isPrin p = true) :
    OT2.assemble p (kumakuma.BinaryTranslation.succTerm t) =
      kumakuma.BinaryTranslation.succTerm (OT2.assemble p t) := by
  unfold OT2.assemble
  rw [ite_eq_right (kumakuma.TargetArithmetic.succTerm_ne_zero t)]
  by_cases ht : t = .zero
  · subst t
    simp only [↓reduceIte, kumakuma.BinaryTranslation.succTerm]
    cases p with
    | zero | add => cases hp
    | inacc | psi => rfl
  · rw [ite_eq_right ht]
    rfl

theorem convert_succ (d lam : Nat) : ∀ s : multi.T,
    DimensionImage.convert d (code (SourceSuccessor.succ lam s)) =
      kumakuma.BinaryTranslation.succTerm (DimensionImage.convert d (code s))
  | .Z => by
    show DimensionImage.convert d (code (ofNatD lam 1)) = _
    rw [code_ofNatD_one, DimensionImage.convert_one, convert_Z]
    rfl
  | .P xs b => by
    show DimensionImage.convert d (code (.P xs (SourceSuccessor.succ lam b))) = _
    rw [convert_P, convert_P, convert_succ d lam b]
    exact assemble_succ _ _ (principal_isPrin _ _)

theorem recursive_head {d : Nat} (s : multi.T) (hs : RecursiveWF d s) :
    RecursiveWF d (T.hd s) := by
  cases s with
  | Z => exact hs
  | P xs b =>
    have hs' := RecursiveWF_P.1 hs
    show RecursiveWF d (.P xs .Z)
    refine RecursiveWF_P.2 ⟨hs'.1, recursive_zero _, ?_⟩
    have hw := hs'.2.2
    rw [convert_P] at hw
    rw [convert_P, convert_Z]
    simp only [OT2.assemble, ↓reduceIte]
    exact assemble_wf_left hw

theorem assemble_wf_of_succ {p t : Term} (hp : Term.isPrin p = true)
    (ht : Term.wf t = true)
    (h : Term.wf (OT2.assemble p (kumakuma.BinaryTranslation.succTerm t)) = true) :
    Term.wf (OT2.assemble p t) = true := by
  have hwp := assemble_wf_left h
  by_cases hz : t = .zero
  · subst t
    simpa only [OT2.assemble, ↓reduceIte] using hwp
  · unfold OT2.assemble at h ⊢
    rw [ite_eq_right (kumakuma.TargetArithmetic.succTerm_ne_zero t)] at h
    rw [ite_eq_right hz]
    have hh := ((Term.wf_add_iff _ _).mp h).2.2.2.2
    rw [kumakuma.TargetArithmetic.head_succTerm hz] at hh
    exact (Term.wf_add_iff _ _).mpr ⟨hp, hwp, ht, hz, hh⟩

theorem ofNat_one_recursiveWF (d lam : Nat) : RecursiveWF d (ofNatD lam 1) := by
  refine RecursiveWF_P.2 ⟨fun i => ?_, recursive_zero _, ?_⟩
  · rw [get0_zeros]; exact recursive_zero _
  · show Term.wf (DimensionImage.convert d (code (ofNatD lam 1))) = true
    rw [code_ofNatD_one, DimensionImage.convert_one]
    exact Term.wf_one

theorem recursive_succ_iff (d lam : Nat) : ∀ s : multi.T,
    RecursiveWF d (SourceSuccessor.succ lam s) ↔ RecursiveWF d s
  | .Z => ⟨fun _ => recursive_zero _, fun _ => ofNat_one_recursiveWF d lam⟩
  | .P xs b => by
    show RecursiveWF d (.P xs (SourceSuccessor.succ lam b)) ↔ RecursiveWF d (.P xs b)
    constructor
    · intro hs
      have hw := hs.wf
      have hs' := RecursiveWF_P.1 hs
      have hb := ((recursive_succ_iff d lam b).mp hs'.2.1).wf
      refine RecursiveWF_P.2 ⟨hs'.1, (recursive_succ_iff d lam b).mp hs'.2.1, ?_⟩
      rw [convert_P, convert_succ] at hw
      rw [convert_P]
      exact assemble_wf_of_succ (principal_isPrin _ _) hb hw
    · intro hs
      have hw := hs.wf
      have hs' := RecursiveWF_P.1 hs
      refine RecursiveWF_P.2 ⟨hs'.1, (recursive_succ_iff d lam b).mpr hs'.2.1, ?_⟩
      rw [show (multi.T.P xs (SourceSuccessor.succ lam b)) = SourceSuccessor.succ lam (.P xs b)
        from rfl, convert_succ]
      exact kumakuma.TargetArithmetic.succTerm_wf hw

theorem dom_one_succ {lam : Nat} : ∀ s : multi.T, Dim lam s → domF s = .one →
    ∃ a, s = SourceSuccessor.succ lam a
  | .Z, _, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, hD, hd => by
    by_cases hb : b = .Z
    · subst hb
      have hz := dom_one_principal hd
      refine ⟨.Z, ?_⟩
      show multi.T.P xs .Z = multi.T.P (zeros lam) .Z
      congr 1
      exact V.eq_of_get0 _ _ (by rw [hD.length, zeros_length]) (fun i => by rw [hz, get0_zeros])
    · rw [domF_tail xs hb] at hd
      obtain ⟨a, ha⟩ := dom_one_succ b hD.tail hd
      exact ⟨.P xs a, by rw [ha]; rfl⟩

theorem fund_one_recursiveWF {d lam : Nat} (s t : multi.T) (hsD : Dim lam s)
    (hs : RecursiveWF d s) (hd : domF s = .one) : RecursiveWF d (T.fund s t) := by
  obtain ⟨a, ha⟩ := dom_one_succ s hsD hd
  rw [ha, SourceSuccessor.fund_succ]
  rw [ha] at hs
  exact (recursive_succ_iff d lam a).mp hs

theorem assemble_head (p t : Term) (hp : Term.isPrin p = true) :
    Term.head (OT2.assemble p t) = p := by
  unfold OT2.assemble
  split
  · cases p with
    | zero | add => cases hp
    | inacc | psi => rfl
  · rfl

theorem convert_head (d : Nat) (s : multi.T) :
    Term.head (DimensionImage.convert d (code s)) =
      DimensionImage.convert d (code (T.hd s)) := by
  cases s with
  | Z =>
    show Term.head (DimensionImage.convert d (code .Z)) = DimensionImage.convert d (code .Z)
    rw [convert_Z]; rfl
  | P xs b =>
    show _ = DimensionImage.convert d (code (.P xs .Z))
    rw [convert_P, convert_P, convert_Z, assemble_head _ _ (principal_isPrin _ _)]
    simp only [OT2.assemble, ↓reduceIte]

theorem Dim_hd {d : Nat} {s : multi.T} (h : Dim d s) : Dim d (T.hd s) := by
  cases s with
  | Z => exact h
  | P xs b => exact Dim_P h.length h.coord (Dim_Z d)

theorem image_le_of_le (k : Nat) (s t : multi.T)
    (hsD : Dim (k + 3) s) (htD : Dim (k + 3) t)
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t) (h : s ≤ t) :
    Term.le (DimensionImage.convert (k + 3) (code s))
      (DimensionImage.convert (k + 3) (code t)) = true := by
  apply (Term.le_iff_eq_or_lt _ _).mpr
  rcases h with h | h
  · exact Or.inr ((convert_order k s t hsD htD hs ht).mp h)
  · exact Or.inl (congrArg (fun a => DimensionImage.convert (k + 3) (code a))
      (eq_of_compare_eq hsD htD h))

theorem replace_tail_recursiveWF (k : Nat)
    (xs : V multi.T) (b c : multi.T) (hsD : Dim (k + 3) (.P xs b)) (hcD : Dim (k + 3) c)
    (hs : RecursiveWF (k + 3) (.P xs b)) (hc : RecursiveWF (k + 3) c)
    (hb : b ≠ .Z) (hcb : c < b) : RecursiveWF (k + 3) (.P xs c) := by
  have hpwf := principal_wf hs
  have hs' := RecursiveWF_P.1 hs
  refine RecursiveWF_P.2 ⟨hs'.1, hc, ?_⟩
  by_cases hz : c = .Z
  · subst c
    rw [convert_P, convert_Z]
    simpa only [OT2.assemble, ↓reduceIte] using hpwf
  · have hbnz : DimensionImage.convert (k + 3) (code b) ≠ .zero := by
      intro h
      exact hb ((code_eq_zero_iff _).1 ((fixed_convert_zero_iff _ _).mp h))
    have hcnz : DimensionImage.convert (k + 3) (code c) ≠ .zero := by
      intro h
      exact hz ((code_eq_zero_iff _).1 ((fixed_convert_zero_iff _ _).mp h))
    have hw := hs'.2.2
    rw [convert_P, OT2.assemble, ite_eq_right hbnz] at hw
    have hbound := ((Term.wf_add_iff _ _).mp hw).2.2.2.2
    have hh := image_le_of_le k (T.hd c) (T.hd b) (Dim_hd hcD) (Dim_hd hsD.tail)
      (recursive_head c hc) (recursive_head b hs'.2.1) (T.hd_mono hcb)
    rw [← convert_head, ← convert_head] at hh
    have hnew := Term.le_trans (wf_head hc.wf) (wf_head hs'.2.1.wf) hpwf hh hbound
    rw [convert_P, OT2.assemble, ite_eq_right hcnz]
    exact (Term.wf_add_iff _ _).mpr ⟨principal_isPrin _ _, hpwf, hc.wf, hcnz, hnew⟩

theorem fund_nonzero_tail_recursiveWF (k : Nat)
    (xs : V multi.T) (b t : multi.T) (hsD : Dim (k + 3) (.P xs b)) (htD : Dim (k + 3) t)
    (hs : RecursiveWF (k + 3) (.P xs b)) (hb : b ≠ .Z)
    (hc : RecursiveWF (k + 3) (T.fund b t)) :
    RecursiveWF (k + 3) (T.fund (.P xs b) t) := by
  rw [fund_tail xs hb]
  exact replace_tail_recursiveWF k xs b _ hsD (Dim_fund b t hsD.tail htD) hs hc hb
    (SourceFundOrder.fund_lt b t hb)

theorem H_size_lt (u t : Term) {z : Term} (hz : z ∈ Term.H u t) :
    Term.size z < Term.size t := by
  induction t with
  | zero => cases hz
  | add a b iha ihb =>
    rw [Term.H] at hz
    rcases List.mem_append.mp hz with hz | hz
    · have h := iha hz
      simp only [Term.size]; omega
    · have h := ihb hz
      simp only [Term.size]; omega
  | inacc n b ih =>
    rw [Term.H] at hz
    rcases List.mem_append.mp hz with hz | hz
    · split at hz
      · cases hz
      · unfold Term.hOne at hz
        split at hz
        · cases hz
        · split at hz
          · cases hz
          · have he := List.mem_singleton.mp hz
            subst z
            simp only [Term.size]
            have := Term.size_pos b
            omega
    · have h := ih hz
      simp only [Term.size]; omega
  | psi v b ihv ihb =>
    rw [Term.H] at hz
    split at hz
    · cases hz
    · split at hz
      · have h := ihv hz
        simp only [Term.size]; have := Term.size_pos b; omega
      · rcases List.mem_cons.mp hz with rfl | hz
        · simp only [Term.size]; have := Term.size_pos v; omega
        · rcases List.mem_append.mp hz with hz | hz
          · have h := ihb hz
            simp only [Term.size]; have := Term.size_pos v; omega
          · have h := ihv hz
            simp only [Term.size]; have := Term.size_pos b; omega

theorem psi_omega_wf_of_succ {a : Term} (ha : Term.wf a = true)
    (h : Term.wf (.psi Term.bigOmega (kumakuma.BinaryTranslation.succTerm a)) = true) :
    Term.wf (.psi Term.bigOmega a) = true := by
  apply (Term.wf_psi_iff _ _).mpr
  refine ⟨by decide +kernel, Term.wf_bigOmega, ha, ?_⟩
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  have hzw := kumakuma.GeneralImageCoefficients.H_coefficient_wf Term.bigOmega a ha hz
  have hzs : z ∈ Term.H Term.bigOmega (kumakuma.BinaryTranslation.succTerm a) := by
    rw [kumakuma.OT2.H_succTerm]
    exact List.mem_append_left _ hz
  have hlt := (Term.allLt_iff _ _).mp ((Term.wf_psi_iff _ _).mp h).2.2.2 z hzs
  rw [kumakuma.TargetArithmetic.lt_succTerm_eq_le hzw ha] at hlt
  rcases (Term.le_iff_eq_or_lt _ _).mp hlt with he | he
  · have hn := H_size_lt Term.bigOmega a hz
    rw [he] at hn
    exact False.elim (Nat.lt_irrefl _ hn)
  · exact he

theorem convert_low_principal (d m : Nat) (a : multi.T) :
    DimensionImage.convert d (code (.P (lowVec m a) .Z)) =
      .psi Term.bigOmega (DimensionImage.convert d (code a)) := by
  rw [code_P, trim_codes_lowVec, code_Z]
  cases he : code a with
  | zero =>
    simp only [trim, Code.isZero, ↓reduceIte, DimensionImage.convert,
      DimensionImage.arguments, DimensionImage.principal_nil, OT2.assemble, Term.one]
  | p xs b =>
    simp [trim, Code.isZero, DimensionImage.convert,
      DimensionImage.arguments, DimensionImage.principal_singleton, OT2.assemble]

theorem low_principal_recursiveWF_iff (d m : Nat) (a : multi.T) :
    RecursiveWF d (.P (lowVec m a) .Z) ↔
      RecursiveWF d a ∧ Term.allLt
        (Term.H Term.bigOmega (DimensionImage.convert d (code a)))
        (DimensionImage.convert d (code a)) = true := by
  constructor
  · intro hs
    have hs' := RecursiveWF_P.1 hs
    have ha := hs'.1 0
    rw [get0_lowVec, ite_eq_left rfl] at ha
    have hw := hs'.2.2
    rw [convert_low_principal] at hw
    exact ⟨ha, ((Term.wf_psi_iff _ _).mp hw).2.2.2⟩
  · rintro ⟨ha, hH⟩
    refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
    · intro i
      rw [get0_lowVec]
      split
      · exact ha
      · exact recursive_zero _
    · rw [convert_low_principal]
      exact (Term.wf_psi_iff _ _).mpr ⟨by decide +kernel, Term.wf_bigOmega, ha.wf, hH⟩

theorem low_principal_succ_predecessor (k : Nat) (a : multi.T)
    (hs : RecursiveWF (k + 3) (.P (lowVec (k + 2) (SourceSuccessor.succ (k + 3) a)) .Z)) :
    RecursiveWF (k + 3) (.P (lowVec (k + 2) a) .Z) := by
  have hs' := RecursiveWF_P.1 hs
  have ha := hs'.1 0
  rw [get0_lowVec, ite_eq_left rfl] at ha
  have hw := hs'.2.2
  rw [convert_low_principal, convert_succ] at hw
  have har := (recursive_succ_iff (k + 3) (k + 3) a).mp ha
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
  · intro i
    rw [get0_lowVec]
    split
    · exact har
    · exact recursive_zero _
  · rw [convert_low_principal]
    exact psi_omega_wf_of_succ har.wf hw

theorem mul_principal_recursiveWF {d : Nat} (xs : V multi.T)
    (hs : RecursiveWF d (.P xs .Z)) : ∀ t : multi.T,
    RecursiveWF d (multi.T.mul (.P xs .Z) t)
  | .Z => recursive_zero _
  | .P ys b => by
    show RecursiveWF d (.P xs (multi.T.mul (.P xs .Z) b))
    have hc := mul_principal_recursiveWF xs hs b
    have hpwf := principal_wf hs
    have hs' := RecursiveWF_P.1 hs
    refine RecursiveWF_P.2 ⟨hs'.1, hc, ?_⟩
    rw [convert_P, OT2.assemble]
    split
    · exact hpwf
    · rename_i hn
      apply (Term.wf_add_iff _ _).mpr
      refine ⟨principal_isPrin _ _, hpwf, hc.wf, hn, ?_⟩
      cases b with
      | Z => exact absurd (convert_Z d) hn
      | P us c =>
        show Term.le (Term.head (DimensionImage.convert d
          (code (.P xs (multi.T.mul (.P xs .Z) c))))) _ = true
        rw [convert_P, assemble_head _ _ (principal_isPrin _ _)]
        exact (Term.le_iff_eq_or_lt _ _).mpr (Or.inl rfl)

theorem fund_low_successor_recursiveWF (k : Nat)
    (a t : multi.T) (haD : Dim (k + 3) a) (hd : domF a = .one)
    (hs : RecursiveWF (k + 3) (.P (lowVec (k + 2) a) .Z)) :
    RecursiveWF (k + 3) (T.fund (.P (lowVec (k + 2) a) .Z) t) := by
  obtain ⟨b, hb⟩ := dom_one_succ a haD hd
  have hp : RecursiveWF (k + 3) (.P (lowVec (k + 2) b) .Z) := by
    rw [hb] at hs
    exact low_principal_succ_predecessor k b hs
  have ha : a ≠ .Z := by intro h; rw [h, domF_Z] at hd; cases hd
  have hg : V.get0 (lowVec (k + 2) a) 0 = a := by rw [get0_lowVec, ite_eq_left rfl]
  rw [fund_one_zero (fnz_lowVec ha) (by rw [hg]; exact hd), hg, lowVec_set_zero, hb,
    SourceSuccessor.fund_succ]
  exact mul_principal_recursiveWF _ hp t

theorem fund_low_zero_recursiveWF (d m : Nat) (t : multi.T) :
    RecursiveWF d (T.fund (.P (lowVec m .Z) .Z) t) := by
  rw [fund_none (fnz_lowVec_Z m)]
  exact recursive_zero _

theorem fund_low_omega (m : Nat) (a t : multi.T) (hd : domF a = .omega) :
    T.fund (.P (lowVec m a) .Z) t = .P (lowVec m (T.fund a t)) .Z := by
  have ha : a ≠ .Z := by intro h; rw [h, domF_Z] at hd; cases hd
  have hg : V.get0 (lowVec m a) 0 = a := by rw [get0_lowVec, ite_eq_left rfl]
  rw [fund_omega (fnz_lowVec ha) (by rw [hg]; exact hd), hg, lowVec_set_zero]

theorem fund_low_Omega (m : Nat) (a t : multi.T) (v : V multi.T) (hd : domF a = .Omega v) :
    T.fund (.P (lowVec m a) .Z) t =
      .P (lowVec m (T.fund a (multi.T.iter (T.fund a) t))) .Z := by
  have ha : a ≠ .Z := by intro h; rw [h, domF_Z] at hd; cases hd
  have hg : V.get0 (lowVec m a) 0 = a := by rw [get0_lowVec, ite_eq_left rfl]
  obtain ⟨i, hi, hm, _⟩ := SourceFundOrder.domOmega_regular a hd
  have hv : lowVec m a < v := SourceFundOrder.lowVec_below_regular a v i hi hm
  rw [fund_diag (fnz_lowVec ha) (by rw [hg]; exact hd) hv, hg, lowVec_set_zero]

def FundClosure (k : Nat) : Prop :=
  ∀ (s : multi.T), DOT (k + 3) s → RecursiveWF (k + 3) s →
    ∀ n, RecursiveWF (k + 3) (T.fund s (ofNatD (k + 3) n))

def PrincipalFundClosure (k : Nat) : Prop :=
  ∀ xs : V multi.T, DOT (k + 3) (.P xs .Z) →
    RecursiveWF (k + 3) (.P xs .Z) →
    ∀ n, RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n))

theorem fundClosure_iff_principal (k : Nat) :
    FundClosure k ↔ PrincipalFundClosure k := by
  constructor
  · intro h xs ho hw n
    exact h _ ho hw n
  · intro h
    intro s ho hw n
    induction hs : s.size using Nat.strongRecOn generalizing s with
    | ind size ih =>
      cases s with
      | Z => rw [fund_Z]; exact recursive_zero _
      | P xs b =>
        by_cases hb : b = .Z
        · subst b
          exact h xs ho hw n
        · have hbo : DOT (k + 3) b := SourceSummands.tail_isOT ho
          have hc := ih b.size (by rw [← hs]; exact multi.T.size_lt_P_right _ _)
            b hbo (RecursiveWF_P.1 hw).2.1 rfl
          exact fund_nonzero_tail_recursiveWF k xs b _ ho.dim (Dim_ofNatD _ _) hw hb hc

def LimitLowFundClosure (k : Nat) : Prop :=
  ∀ a : multi.T, DOT (k + 3) (.P (lowVec (k + 2) a) .Z) →
    RecursiveWF (k + 3) (.P (lowVec (k + 2) a) .Z) →
    (domF a = .omega ∨ ∃ v, domF a = .Omega v) →
    ∀ n, RecursiveWF (k + 3) (T.fund (.P (lowVec (k + 2) a) .Z) (ofNatD (k + 3) n))

theorem principalFundClosure_iff_limit_low (k : Nat) :
    PrincipalFundClosure k ↔ LimitLowFundClosure k := by
  constructor
  · intro h a ho hw _ n
    exact h _ ho hw n
  · intro h xs ho hw n
    have houter := CountableSource.isOT_outer ho
    cases houter with
    | cons a _ _ =>
      have haD : Dim (k + 3) a := by
        have := ho.dim.coord 0
        rwa [get0_lowVec, ite_eq_left rfl] at this
      cases hd : domF a with
      | zero =>
        have ha := (domF_eq_zero_iff a).mp hd
        rw [ha]
        exact fund_low_zero_recursiveWF _ _ _
      | one => exact fund_low_successor_recursiveWF k a _ haD hd hw
      | omega => exact h a ho hw (Or.inl hd) n
      | Omega v => exact h a ho hw (Or.inr ⟨v, hd⟩) n

theorem fundClosure_iff_limit_low (k : Nat) :
    FundClosure k ↔ LimitLowFundClosure k :=
  (fundClosure_iff_principal k).trans (principalFundClosure_iff_limit_low k)

theorem generated_recursiveWF_aux (k : Nat) (hc : FundClosure k)
    {lam : Nat} {s : multi.T} (hs : DOT lam s) :
    lam = k + 3 → RecursiveWF (k + 3) s := by
  induction hs with
  | base_0 n => intro e; omega_c
  | base_succ lam n =>
    intro e
    obtain rfl : lam = k + 2 := by omega_c
    exact basis_recursiveWF k n
  | step lam s hs n ih =>
    intro e
    subst e
    exact hc s hs (ih rfl) n

theorem original_recursiveWF_of_closure (k : Nat) (hc : FundClosure k)
    (s : multi.T) (hs : DOT (k + 3) s) : RecursiveWF (k + 3) s :=
  generated_recursiveWF_aux k hc hs rfl

theorem original_wf_of_closure (k : Nat) (hc : FundClosure k)
    (s : multi.T) (hs : DOT (k + 3) s) :
    Term.wf (DimensionImage.convert (k + 3) (code s)) = true :=
  (original_recursiveWF_of_closure k hc s hs).wf

theorem original_order_of_closure (k : Nat) (hc : FundClosure k)
    (s t : multi.T) (hs : DOT (k + 3) s) (ht : DOT (k + 3) t) :
    s < t ↔ Term.lt (DimensionImage.convert (k + 3) (code s))
      (DimensionImage.convert (k + 3) (code t)) = true :=
  convert_order k s t hs.dim ht.dim (original_recursiveWF_of_closure k hc s hs)
    (original_recursiveWF_of_closure k hc t ht)

end kumakuma.GeneralImageWFInvariant

namespace kumakuma.GeneralImageIndexSupport

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CodeReification
open kumakuma.BinaryTranslation kumakuma.TargetIndexCuts kumakuma.DimensionImage
open kumakuma.GeneralImageTopPair kumakuma.GeneralImageLayerOrder
open kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageRawOrder

theorem indices_drop_iff {k : Nat} (hk : 0 < k) (t : Term) :
    IndicesBelow k (dropOne t) ↔ IndicesBelow k t := by
  cases t with
  | zero | inacc => rfl
  | add a b =>
    simp only [dropOne]
    split
    · rename_i ha
      rw [ha]
      simp only [IndicesBelow]
      exact ⟨fun h => ⟨indices_one hk, h⟩, fun h => h.2⟩
    · rfl
  | psi v b =>
    simp only [dropOne]
    split
    · rename_i ht
      rw [ht]
      exact ⟨fun _ => indices_one hk, fun _ => trivial⟩
    · rfl

theorem indices_succ_iff {k : Nat} (hk : 0 < k) (t : Term) :
    IndicesBelow k (succTerm t) ↔ IndicesBelow k t := by
  induction t with
  | zero => exact ⟨fun _ => trivial, fun _ => indices_one hk⟩
  | add a b _ ih => simp only [succTerm, IndicesBelow, ih]
  | inacc n b | psi v b =>
    simp only [succTerm, IndicesBelow]
    exact ⟨fun h => h.1, fun h => ⟨h, indices_one hk⟩⟩

theorem step_indices {k : Nat} (hk : 0 < k) (n : Nat) (a c : Term)
    (h : IndicesBelow k (step n a c)) : IndicesBelow k a ∧ IndicesBelow k c := by
  unfold step at h
  by_cases ha : a = .zero
  · subst a
    simp only [↓reduceIte] at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h
      exact ⟨trivial, h.2⟩
    · rw [ite_eq_right hn] at h
      by_cases hc : c = .zero
      · subst c; exact ⟨trivial, trivial⟩
      · rw [ite_eq_right hc] at h
        exact ⟨trivial, (indices_drop_iff hk c).mp h.2⟩
  · rw [ite_eq_right ha] at h
    by_cases hc : c = .zero
    · subst c
      simp only [↓reduceIte] at h
      exact ⟨h, trivial⟩
    · rw [ite_eq_right hc] at h
      exact ⟨(indices_succ_iff hk a).mp h.1.2,
        (indices_drop_iff hk c).mp h.2⟩

theorem lower_indices {k : Nat} (hk : 0 < k) (j : Nat) (xs : List Term) (a : Term)
    (h : IndicesBelow k (lower j xs a)) :
    IndicesBelow k a ∧ ∀ i, i < j → IndicesBelow k (xs[i]?.getD .zero) := by
  induction j generalizing a with
  | zero => exact ⟨h, fun i hi => False.elim (by omega)⟩
  | succ j ih =>
    rw [lower_succ] at h
    obtain ⟨hs, hx⟩ := ih _ h
    obtain ⟨ha, hc⟩ := step_indices hk j _ _ hs
    refine ⟨ha, ?_⟩
    intro i hi
    by_cases hij : i < j
    · exact hx i hij
    · have he : i = j := by omega
      simpa only [he] using hc

theorem topPair_indices {k : Nat} (hk : 0 < k) (n : Nat) (a b : Term)
    (h : IndicesBelow k (topPair n a b)) : IndicesBelow k a ∧ IndicesBelow k b := by
  unfold topPair at h
  by_cases hb : b = .zero
  · subst b
    simp only [↓reduceIte] at h
    by_cases ha : a = .zero
    · subst a; exact ⟨trivial, trivial⟩
    · rw [ite_eq_right ha] at h
      exact ⟨(indices_drop_iff hk a).mp h.2, trivial⟩
  · rw [ite_eq_right hb] at h
    refine ⟨?_, (indices_drop_iff hk b).mp h.2⟩
    by_cases ha : a = .zero
    · subst a; trivial
    · rw [ite_eq_right ha] at h
      exact (indices_drop_iff hk a).mp ((indices_succ_iff hk (dropOne a)).mp h.1.2)

theorem topPair_zero_of_indices {k n : Nat} (hn : k ≤ n) (a b : Term)
    (h : IndicesBelow k (topPair n a b)) : a = .zero ∧ b = .zero := by
  unfold topPair at h
  by_cases hb : b = .zero
  · rw [ite_eq_left hb] at h
    refine ⟨?_, hb⟩
    by_cases ha : a = .zero
    · exact ha
    · rw [ite_eq_right ha] at h
      have := h.1
      omega
  · rw [ite_eq_right hb] at h
    have := h.1.1
    omega

theorem principal_indices {cut : Nat} (hc : 0 < cut) (k : Nat) (xs : List Term)
    (h : IndicesBelow cut (principal (k + 3) xs)) :
    (∀ i, i < k + 3 → IndicesBelow cut (xs[i]?.getD .zero)) ∧
      (cut ≤ k + 1 → xs[k + 2]?.getD .zero = .zero) := by
  rw [principal_as_layers] at h
  obtain ⟨ht, hl⟩ := lower_indices hc (k + 1) xs _ h
  obtain ⟨hh, hm⟩ := topPair_indices hc (k + 1) _ _ ht
  refine ⟨?_, fun hcut => (topPair_zero_of_indices hcut _ _ ht).1⟩
  intro i hi
  by_cases hil : i < k + 1
  · exact hl i hil
  · by_cases him : i = k + 1
    · simpa only [him] using hm
    · have he : i = k + 2 := by omega
      simpa only [he] using hh

theorem assemble_indices {k : Nat} (a b : Term)
    (h : IndicesBelow k (OT2.assemble a b)) : IndicesBelow k a ∧ IndicesBelow k b := by
  unfold OT2.assemble at h
  by_cases hb : b = .zero
  · subst b
    simp only [↓reduceIte] at h
    exact ⟨h, trivial⟩
  · rw [ite_eq_right hb] at h
    exact h

theorem argsWidth_coordinates (xs : V multi.T) (n : Nat)
    (h : ∀ i, width (code (V.get0 xs i)) ≤ n) : argsWidth (codes xs) ≤ n := by
  induction xs with
  | emp => rw [codes_emp, argsWidth]; exact Nat.zero_le _
  | snoc x xs ih =>
    rw [codes_snoc, argsWidth_append, argsWidth_singleton]
    refine Nat.max_le.2 ⟨ih (fun i => ?_), ?_⟩
    · by_cases hi : i < xs.length
      · have := h i; rwa [V.get0_snoc_low x xs i hi] at this
      · rw [V.get0_ge xs i (Nat.le_of_not_lt hi), code_Z, width]; exact Nat.zero_le _
    · have := h xs.length; rwa [V.get0_snoc_top] at this

theorem width_of_indices (k : Nat) : ∀ (s : multi.T), Dim (k + 3) s →
    IndicesBelow (k + 1) (convert (k + 3) (code s)) → width (code s) ≤ k + 2
  | .Z, _, _ => by rw [code_Z, width]; omega
  | .P xs b, hsD, h => by
    rw [convert_P] at h
    obtain ⟨hp, hb⟩ := assemble_indices _ _ h
    obtain ⟨hc, hz⟩ := principal_indices (by omega : 0 < k + 1) k _ hp
    have hi : ∀ i, i < k + 3 →
        IndicesBelow (k + 1) (convert (k + 3) (code (V.get0 xs i))) := by
      intro i hik
      have := hc i hik
      rwa [converted_coordinate] at this
    have hlast : V.get0 xs (k + 2) = .Z := by
      have he := hz (Nat.le_refl _)
      rw [converted_coordinate] at he
      exact (code_eq_zero_iff _).1 ((kumakuma.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he)
    have hlen : (trim (codes xs)).length ≤ k + 2 := by
      have hl := hsD.length
      cases xs with
      | emp => rw [codes_emp]; exact Nat.zero_le _
      | snoc x xs' =>
        have hl' : xs'.length = k + 2 := by simp only [V.length] at hl; omega
        have hx : x = .Z := by
          have := hlast
          rw [← hl', V.get0_snoc_top] at this
          exact this
        subst hx
        rw [codes_snoc, code_Z, trim_append_zero]
        exact Nat.le_trans (trim_length_le _) (Nat.le_of_eq (by rw [codes_length, hl']))
    have hargs := argsWidth_coordinates xs (k + 2) (fun i => by
      by_cases hik : i < k + 3
      · exact width_of_indices k _ (hsD.coord i) (hi i hik)
      · rw [V.get0_ge xs i (by rw [hsD.length]; omega), code_Z, width]; exact Nat.zero_le _)
    rw [code_P, width]
    exact Nat.max_le.mpr ⟨hlen, Nat.max_le.mpr
      ⟨Nat.le_trans (argsWidth_trim_le _) hargs, width_of_indices k b hsD.tail hb⟩⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem class_not_lower_indices (k : Nat) (q : Classes)
    (hd : kumakuma.GeneralImageEmbedding.ambient (representative q) = k + 4) :
    ¬ IndicesBelow (k + 2) (kumakuma.GeneralImageEmbedding.classConversion q) := by
  intro h
  obtain ⟨s, he⟩ := kumakuma.GeneralImageEmbedding.exists_fixedWitness (k + 4) q
    (by rw [← hd]; exact Nat.le_max_right 3 _)
  rw [kumakuma.GeneralImageEmbedding.class_fixed_value (k + 4) q hd s he] at h
  have hw := width_of_indices (k + 1) s.val s.property.dim h
  rw [he] at hw
  unfold kumakuma.GeneralImageEmbedding.ambient at hd
  omega

theorem source_lt_of_ambient_lt (q r : Classes)
    (hd : kumakuma.GeneralImageEmbedding.ambient (representative q) <
      kumakuma.GeneralImageEmbedding.ambient (representative r)) : ClassLT q r := by
  let k := kumakuma.GeneralImageEmbedding.ambient (representative r) - 2
  have hr3 := Nat.le_max_left 3 (width (representative r))
  have hq3 := Nat.le_max_left 3 (width (representative q))
  have hrw : width (representative r) = k + 2 := by
    unfold kumakuma.GeneralImageEmbedding.ambient at hd
    dsimp [k]
    unfold kumakuma.GeneralImageEmbedding.ambient
    omega_c
  have hqw : width (representative q) ≤ k + 1 := by
    have h := Nat.le_max_right 3 (width (representative q))
    change width (representative q) ≤ kumakuma.GeneralImageEmbedding.ambient (representative q) at h
    dsimp [k]
    unfold kumakuma.GeneralImageEmbedding.ambient at hd
    omega_c
  have hq : HasDimensionWitness (k + 1) q := by
    exact (hasDimensionWitness_iff _ _).mpr hqw
  have hqb := kumakuma.DimensionCut.dimension_witness_below_boundary hq
  rcases classLT_total (kumakuma.DimensionCut.boundaryClass k) r with hl | hl | he
  · exact classLT_trans hqb hl
  · have hr := (kumakuma.DimensionCut.dimension_witness_iff_below_boundary k r).mpr hl
    have hw := (hasDimensionWitness_iff r (k + 1)).mp hr
    rw [hrw] at hw
    omega_c
  · simpa only [he] using hqb

theorem target_lt_of_ambient_lt (q r : Classes)
    (hd : kumakuma.GeneralImageEmbedding.ambient (representative q) <
      kumakuma.GeneralImageEmbedding.ambient (representative r))
    (hq : Term.wf (kumakuma.GeneralImageEmbedding.classConversion q) = true)
    (hr : Term.wf (kumakuma.GeneralImageEmbedding.classConversion r) = true) :
    Term.lt (kumakuma.GeneralImageEmbedding.classConversion q)
      (kumakuma.GeneralImageEmbedding.classConversion r) = true := by
  have hq3 := Nat.le_max_left 3 (width (representative q))
  change 3 ≤ kumakuma.GeneralImageEmbedding.ambient (representative q) at hq3
  have hr4 : 4 ≤ kumakuma.GeneralImageEmbedding.ambient (representative r) := by omega
  let k := kumakuma.GeneralImageEmbedding.ambient (representative r) - 4
  have hdim : kumakuma.GeneralImageEmbedding.ambient (representative r) = k + 4 := by dsimp [k]; omega
  have hnot := class_not_lower_indices k r hdim
  have hidx : IndicesBelow (k + 2) (kumakuma.GeneralImageEmbedding.classConversion q) := by
    apply (kumakuma.GeneralImageEmbedding.indices_convert (representative q)).mono
    omega
  rcases Term.lt_trichotomy hq hr with hl | he | hl
  · exact hl
  · exact False.elim (hnot (he ▸ hidx))
  · exact False.elim (hnot (indicesBelow_initial (by omega : 0 < k + 2)
      ⟨_, hr, kumakuma.GeneralImageEmbedding.class_below r⟩
      ⟨_, hq, kumakuma.GeneralImageEmbedding.class_below q⟩ hl hidx))

theorem different_ambient_order (q r : Classes)
    (hd : kumakuma.GeneralImageEmbedding.ambient (representative q) <
      kumakuma.GeneralImageEmbedding.ambient (representative r))
    (hq : Term.wf (kumakuma.GeneralImageEmbedding.classConversion q) = true)
    (hr : Term.wf (kumakuma.GeneralImageEmbedding.classConversion r) = true) :
    ClassLT q r ↔ Term.lt (kumakuma.GeneralImageEmbedding.classConversion q)
      (kumakuma.GeneralImageEmbedding.classConversion r) = true :=
  ⟨fun _ => target_lt_of_ambient_lt q r hd hq hr, fun _ => source_lt_of_ambient_lt q r hd⟩

theorem global_certificate_of_fundClosure
    (hc : ∀ k, kumakuma.GeneralImageWFInvariant.FundClosure k) :
    kumakuma.GeneralImageEmbedding.GlobalCertificate := by
  have hw : ∀ q : Classes,
      Term.wf (kumakuma.GeneralImageEmbedding.classConversion q) = true := by
    apply kumakuma.GeneralImageEmbedding.global_wf_of_fixed
    intro d hd s
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
    have he : d = k + 3 := by omega
    clear hk
    subst d
    exact kumakuma.GeneralImageWFInvariant.original_wf_of_closure k (hc k) s.val s.property
  refine ⟨hw, ?_⟩
  intro q r
  by_cases he : kumakuma.GeneralImageEmbedding.ambient (representative q) =
      kumakuma.GeneralImageEmbedding.ambient (representative r)
  · have hd : 3 ≤ kumakuma.GeneralImageEmbedding.ambient (representative q) := Nat.le_max_left 3 _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
    have hdq : kumakuma.GeneralImageEmbedding.ambient (representative q) = k + 3 := by omega
    exact kumakuma.GeneralImageEmbedding.same_ambient_order_of_fixed (k + 3) q r hdq (he.symm.trans hdq)
      (fun s t => kumakuma.GeneralImageWFInvariant.original_order_of_closure k (hc k)
        s.val t.val s.property t.property)
  · rcases Nat.lt_or_gt_of_ne he with hd | hd
    · exact different_ambient_order q r hd (hw q) (hw r)
    · have hs := source_lt_of_ambient_lt r q hd
      have ht := target_lt_of_ambient_lt r q hd (hw r) (hw q)
      constructor
      · intro h
        exact False.elim (classLT_irrefl q (classLT_trans h hs))
      · intro h
        have hf := Term.not_lt_of_lt ht
        rw [h] at hf
        cases hf

theorem global_certificate_of_limit_low
    (hc : ∀ k, kumakuma.GeneralImageWFInvariant.LimitLowFundClosure k) :
    kumakuma.GeneralImageEmbedding.GlobalCertificate :=
  global_certificate_of_fundClosure
    (fun k => (kumakuma.GeneralImageWFInvariant.fundClosure_iff_limit_low k).mpr (hc k))

end kumakuma.GeneralImageIndexSupport

namespace kumakuma.GeneralImageLimitBranches

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.CountableSource
open kumakuma.GeneralImageEmbedding kumakuma.GeneralImageRawOrder
open kumakuma.GeneralImageWFInvariant kumakuma.BinaryTranslation
open kumakuma.DimensionCut kumakuma.TargetArithmetic

theorem H_mul_principal_support (d : Nat) (xs : V multi.T) (lam : Nat) (u : Term) :
    ∀ (n : Nat) {z : Term}, z ∈ Term.H u (DimensionImage.convert d
      (code (multi.T.mul (.P xs .Z) (ofNatD lam n)))) →
    z ∈ Term.H u (DimensionImage.convert d (code (.P xs .Z)))
  | 0, z, hz => by
    have : multi.T.mul (.P xs .Z) (ofNatD lam 0) = .Z := rfl
    rw [this, convert_Z, Term.H] at hz; cases hz
  | n + 1, z, hz => by
    have he : multi.T.mul (.P xs .Z) (ofNatD lam (n + 1)) =
        .P xs (multi.T.mul (.P xs .Z) (ofNatD lam n)) := rfl
    rw [he, convert_P] at hz
    rcases kumakuma.GeneralImageCoefficients.H_assemble_support u _ _ hz with hz | hz
    · rw [convert_P, convert_Z]
      simpa only [OT2.assemble, ↓reduceIte] using hz
    · exact H_mul_principal_support d xs lam u n hz

theorem H_subset_omega (u t : Term) (ht : Term.wf t = true) {z : Term}
    (hz : z ∈ Term.H u t) : z ∈ Term.H Term.bigOmega t := by
  induction t with
  | zero => cases hz
  | add a b iha ihb =>
    have hw := (Term.wf_add_iff _ _).mp ht
    rw [Term.H] at hz ⊢
    rcases List.mem_append.mp hz with hz | hz
    · exact List.mem_append_left _ (iha hw.2.1 hz)
    · exact List.mem_append_right _ (ihb hw.2.2.1 hz)
  | inacc n b ih =>
    rcases kumakuma.GeneralImageCoefficients.H_inacc_support n b hz with rfl | hz
    · rw [Term.H]
      by_cases hn : n = 0
      · subst n
        rw [Term.H] at hz
        simp only [↓reduceIte, List.nil_append] at hz
        exact ih ((Term.wf_inacc_iff _ _).mp ht).1 hz
      · simp [hn, Term.hOne, Term.bigOmega, Term.predR, Term.le, Term.one, Term.lt]
    · rw [Term.H]
      exact List.mem_append_right _ (ih ((Term.wf_inacc_iff _ _).mp ht).1 hz)
  | psi v b ihv ihb =>
    have hw := (Term.wf_psi_iff _ _).mp ht
    have he : Term.H Term.bigOmega (.psi v b) = b ::
        (Term.H Term.bigOmega b ++ Term.H Term.bigOmega v) := by
      cases v with
      | zero | add | psi => cases hw.1
      | inacc n c =>
        simp [Term.H, Term.bigOmega, Term.predR, Term.le, Term.lt,
          kumakuma.CountableTarget.lt_zero]
    rw [he]
    rcases kumakuma.GeneralImageCoefficients.H_psi_support hz with rfl | hz | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihb hw.2.2.1 hz))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihv hw.2.1 hz))

theorem H_nat_support (u : Term) (n : Nat) {z : Term}
    (hz : z ∈ Term.H u (kumakuma.FiniteCorrespondence.natTerm n)) : z = .zero := by
  induction n with
  | zero => cases hz
  | succ n ih =>
    cases n with
    | zero => exact kumakuma.GeneralImageCoefficients.H_one_mem hz
    | succ n =>
      rw [kumakuma.FiniteCorrespondence.natTerm, Term.H] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact kumakuma.GeneralImageCoefficients.H_one_mem hz
      · exact ih hz

theorem H_nat_bound (u : Term) (n : Nat) :
    Term.allLt (Term.H u (kumakuma.FiniteCorrespondence.natTerm n))
      (kumakuma.FiniteCorrespondence.natTerm n) = true := by
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  rw [H_nat_support u n hz]
  cases n with
  | zero => cases hz
  | succ n => cases n <;> simp [kumakuma.FiniteCorrespondence.natTerm, Term.lt, Term.one]

theorem H_drop_bound_of_omega (u t : Term) (ht : Term.wf t = true)
    (hH : Term.allLt (Term.H Term.bigOmega t) t = true) :
    Term.allLt (Term.H u (dropOne t)) (dropOne t) = true := by
  by_cases hh : Term.head t = Term.one
  · obtain ⟨n, rfl⟩ := head_one_nat ht hh
    rw [dropOne_nat]
    exact H_nat_bound u n
  · rw [dropOne_of_head_ne hh]
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    exact (Term.allLt_iff _ _).mp hH z (H_subset_omega u t ht hz)

def topNode (k : Nat) (a : multi.T) : multi.T := .P (lastVec (k + 2) a) .Z

theorem topNode_zero (k : Nat) : topNode k .Z = ofNatD (k + 3) 1 := rfl

theorem Dim_topNode {k : Nat} {a : multi.T} (ha : Dim (k + 3) a) : Dim (k + 3) (topNode k a) := by
  refine Dim_P (lastVec_length _ _) (fun i => ?_) (Dim_Z _)
  rw [get0_lastVec]
  split
  · exact ha
  · exact Dim_Z _

theorem convert_topNode (k : Nat) (a : multi.T) (ha : a ≠ .Z) :
    DimensionImage.convert (k + 3) (code (topNode k a)) =
      .inacc (k + 1) (dropOne (DimensionImage.convert (k + 3) (code a))) := by
  have hc : code a ≠ .zero := fun h => ha ((code_eq_zero_iff _).1 h)
  rw [topNode, code_lastVec_principal, trim_before_nonzero _ _ hc]
  simp only [DimensionImage.convert, DimensionImage.arguments_append,
    DimensionImage.arguments_zeros, DimensionImage.arguments]
  have hn : DimensionImage.convert (k + 3) (code a) ≠ .zero := by
    intro h
    exact hc ((fixed_convert_zero_iff _ _).mp h)
  rw [principal_top_term k _ hn]
  rfl

theorem topNode_recursiveWF (k : Nat) (a : multi.T)
    (ha : RecursiveWF (k + 3) a) : RecursiveWF (k + 3) (topNode k a) := by
  by_cases hz : a = .Z
  · subst a
    rw [topNode_zero]
    exact ofNat_one_recursiveWF _ _
  · refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
    · intro i
      rw [get0_lastVec]
      split
      · exact ha
      · exact recursive_zero _
    · show Term.wf (DimensionImage.convert (k + 3) (code (topNode k a))) = true
      rw [convert_topNode k a hz]
      apply (Term.wf_inacc_iff _ _).mpr
      refine ⟨dropOne_wf ha.wf, ?_⟩
      have hi := DimensionImage.indices_drop
        (DimensionImage.indices_convert (k + 3) (by omega) (code a))
      have hf := kumakuma.TargetIndexCuts.IndicesBelow.fT_lt (by omega : 0 < k + 2) hi
      exact Nat.le_of_lt_succ hf

theorem H_topNode_support (k : Nat) (a : multi.T) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega (DimensionImage.convert (k + 3) (code (topNode k a)))) :
    z = .zero ∨ z ∈ Term.H Term.bigOmega (DimensionImage.convert (k + 3) (code a)) := by
  by_cases hn : a = .Z
  · subst a
    rw [topNode_zero, code_ofNatD_one, DimensionImage.convert_one] at hz
    exact Or.inl (kumakuma.GeneralImageCoefficients.H_one_mem hz)
  · rw [convert_topNode k a hn] at hz
    rcases kumakuma.GeneralImageCoefficients.H_inacc_support _ _ hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (kumakuma.OT2.mem_H_dropOne hz)

end kumakuma.GeneralImageLimitBranches

namespace kumakuma.SourceRecursiveDescending

open multi OTQuotient SourceDescending

def Recursive : multi.T → Prop
  | .Z => True
  | .P xs b => (∀ i, Recursive (V.get0 xs i)) ∧ Recursive b ∧ Descending (.P xs b)
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem recursive_zero : Recursive .Z := by rw [Recursive]; trivial

theorem Recursive_P {xs : V multi.T} {b : multi.T} :
    Recursive (.P xs b) ↔ (∀ i, Recursive (V.get0 xs i)) ∧ Recursive b ∧ Descending (.P xs b) := by
  rw [Recursive]

theorem coordinates_set (xs : V multi.T) (i : Nat) (s : multi.T)
    (hx : ∀ j, Recursive (V.get0 xs j)) (hs : Recursive s) :
    ∀ j, Recursive (V.get0 (V.set xs i s) j) := by
  intro j
  by_cases hi : i < xs.length
  · rw [V.get0_set xs i s j hi]
    split
    · exact hs
    · exact hx j
  · rw [set_of_ge xs i s (Nat.le_of_not_lt hi)]
    exact hx j

theorem principal (xs : V multi.T) (hx : ∀ i, Recursive (V.get0 xs i)) :
    Recursive (.P xs .Z) :=
  Recursive_P.2 ⟨hx, recursive_zero, principal_descending xs⟩

theorem mul_principal (xs : V multi.T) (hx : ∀ i, Recursive (V.get0 xs i)) :
    ∀ t : multi.T, Recursive (multi.T.mul (.P xs .Z) t)
  | .Z => recursive_zero
  | .P ys b => by
    show Recursive (.P xs (multi.T.mul (.P xs .Z) b))
    exact Recursive_P.2 ⟨hx, mul_principal xs hx b, mul_principal_descending xs (.P ys b)⟩

theorem iter_recursive (F : multi.T → multi.T)
    (hf : ∀ s, Recursive s → Recursive (F s)) : ∀ t : multi.T, Recursive t →
    Recursive (multi.T.iter F t)
  | .Z, _ => recursive_zero
  | .P ys b, ht => by
    show Recursive (F (multi.T.iter F b))
    exact hf _ (iter_recursive F hf b (Recursive_P.1 ht).2.1)

theorem fund_recursive : ∀ (s t : multi.T), Recursive s → Recursive t → Recursive (T.fund s t)
  | .Z, _, _, _ => by rw [fund_Z]; exact recursive_zero
  | .P xs b, t, hs, ht => by
    have hs' := Recursive_P.1 hs
    have hx := hs'.1
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf]; exact recursive_zero
      · have hrec : ∀ a, Recursive a → Recursive (T.fund (V.get0 xs i) a) :=
          fun a ha => fund_recursive (V.get0 xs i) a (hx i) ha
        cases hd : domF (V.get0 xs i) with
        | zero => rw [fund_zero hf hd]; exact principal _ (coordinates_set xs i _ hx (hrec t ht))
        | omega => rw [fund_omega hf hd]; exact principal _ (coordinates_set xs i _ hx (hrec t ht))
        | Omega v =>
          by_cases hv : xs < v
          · rw [fund_diag hf hd hv]
            exact principal _ (coordinates_set xs i _ hx (hrec _ (iter_recursive _ hrec t ht)))
          · rw [fund_nondiag hf hd hv]
            exact principal _ (coordinates_set xs i _ hx (hrec t ht))
        | one =>
          cases i with
          | zero =>
            rw [fund_one_zero hf hd]
            exact mul_principal _ (coordinates_set xs 0 _ hx (hrec .Z recursive_zero)) t
          | succ m =>
            rw [fund_one_succ hf hd]
            exact principal _ (coordinates_set _ m t
              (coordinates_set xs (m + 1) _ hx (hrec .Z recursive_zero)) ht)
    · have hd := fund_descending (.P xs b) t hs'.2.2
      rw [fund_tail xs hb] at hd ⊢
      exact Recursive_P.2 ⟨hx, fund_recursive b t hs'.2.1 ht, hd⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem ofNat_recursive (lam n : Nat) : Recursive (ofNatD lam n) := by
  induction n with
  | zero => exact recursive_zero
  | succ n ih =>
    show Recursive (.P (zeros lam) (ofNatD lam n))
    refine Recursive_P.2 ⟨fun i => ?_, ih, ofNat_descending lam (n + 1)⟩
    rw [get0_zeros]; exact recursive_zero

theorem LF_recursive (lam n : Nat) : Recursive (towerD lam n) := by
  induction n with
  | zero => exact recursive_zero
  | succ n ih =>
    cases lam with
    | zero =>
      rw [← FiniteCorrespondence.ofNatD_zero_eq_tower]
      exact ofNat_recursive 0 (n + 1)
    | succ k =>
      rw [LF_step]
      apply principal
      intro i
      rw [get0_lastVec]
      split
      · exact ih
      · exact recursive_zero

theorem isOT_recursive {lam : Nat} {s : multi.T} (hs : DOT lam s) : Recursive s := by
  induction hs with
  | base_0 n => exact LF_recursive 0 n
  | base_succ k n =>
    apply principal
    intro i
    show Recursive (V.get0 (CountableSource.lowVec k (towerD (k + 1) n)) i)
    rw [CountableSource.get0_lowVec]
    split
    · exact LF_recursive (k + 1) n
    · exact recursive_zero
  | step lam s hs n ih => exact fund_recursive s _ ih (ofNat_recursive lam n)

theorem domain_principal_le_head (s : multi.T) (hs : Recursive s) {v : V multi.T}
    (hd : domF s = .Omega v) : multi.T.P v .Z ≤ T.hd s := by
  have hp := SourceFundOrder.OmegaLabelPath.of_domain s hd
  clear hd
  induction hp with
  | regular => exact T.le_refl _
  | inherit xs i hf hdq hnd =>
    rcases V.not_lt.1 hnd with h | h
    · exact Or.inl (T.P_lt_P_of_vlt _ _ h)
    · exact Or.inr ((T.P_eqv_iff _ _ _ _).2 ⟨h, compareT_ZZ⟩)
  | tail xs b hb _ ih => exact T.le_trans (ih (Recursive_P.1 hs).2.1) (Recursive_P.1 hs).2.2.2

theorem diagonal_principal_lt_argument (xs : V multi.T)
    (a : multi.T) (ha : Recursive a) {v : V multi.T}
    (hd : domF a = .Omega v) (hv : xs < v) : multi.T.P xs .Z < a := by
  have hhead := T.le_trans (domain_principal_le_head a ha hd) (T.hd_le_self a)
  exact T.lt_of_lt_of_le (T.P_lt_P_of_vlt _ _ hv) hhead

end kumakuma.SourceRecursiveDescending

namespace kumakuma.SourceFundGap

open multi OTQuotient DimensionCut SourceFundOrder

mutual
  def mass : multi.T → Nat
    | .Z => 0
    | .P xs b => 1 + vectorMass xs + mass b

  def vectorMass : V multi.T → Nat
    | .emp => 0
    | .snoc x xs => vectorMass xs + mass x
end

theorem mass_Z : mass .Z = 0 := by rw [mass]

theorem mass_P (xs : V multi.T) (b : multi.T) : mass (.P xs b) = 1 + vectorMass xs + mass b := by
  rw [mass]

theorem vectorMass_emp : vectorMass (.emp : V multi.T) = 0 := by rw [vectorMass]

theorem vectorMass_snoc (x : multi.T) (xs : V multi.T) :
    vectorMass (.snoc x xs) = vectorMass xs + mass x := by rw [vectorMass]

/-- Sum of the masses of `f 0, …, f (n - 1)`. -/
def msum (f : Nat → multi.T) : Nat → Nat
  | 0 => 0
  | n + 1 => msum f n + mass (f n)

theorem msum_congr {f g : Nat → multi.T} :
    ∀ n, (∀ j, j < n → mass (f j) = mass (g j)) → msum f n = msum g n
  | 0, _ => rfl
  | n + 1, h => by
    show msum f n + mass (f n) = msum g n + mass (g n)
    rw [msum_congr n (fun j hj => h j (by omega)), h n (by omega)]

theorem msum_eq_zero (f : Nat → multi.T) : ∀ n, (∀ j, j < n → f j = .Z) → msum f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    show msum f n + mass (f n) = 0
    rw [msum_eq_zero f n (fun j hj => h j (by omega)), h n (by omega), mass_Z]

theorem msum_add (f : Nat → multi.T) (a : Nat) :
    ∀ b, msum f (a + b) = msum f a + msum (fun j => f (a + j)) b
  | 0 => rfl
  | b + 1 => by
    show msum f (a + b) + mass (f (a + b)) = msum f a + (msum (fun j => f (a + j)) b + mass (f (a + b)))
    rw [msum_add f a b]; omega

theorem msum_zero_tail (f : Nat → multi.T) (n : Nat) (h : ∀ j, n ≤ j → f j = .Z) :
    ∀ m, n ≤ m → msum f m = msum f n := by
  intro m hm
  obtain ⟨r, rfl⟩ : ∃ r, m = n + r := ⟨m - n, by omega⟩
  rw [msum_add, msum_eq_zero _ r (fun j _ => h (n + j) (by omega)), Nat.add_zero]

theorem vectorMass_eq_msum (v : V multi.T) : vectorMass v = msum (V.get0 v) v.length := by
  induction v with
  | emp => rfl
  | snoc x xs ih =>
    rw [vectorMass_snoc, ih]
    show _ = msum (V.get0 (.snoc x xs)) xs.length + mass (V.get0 (.snoc x xs) xs.length)
    rw [V.get0_snoc_top]
    congr 1
    exact msum_congr _ (fun j hj => by rw [V.get0_snoc_low x xs j hj])

theorem vectorMass_eq_msum_of (v : V multi.T) (N : Nat) (hN : v.length ≤ N) :
    vectorMass v = msum (V.get0 v) N := by
  rw [vectorMass_eq_msum, msum_zero_tail _ v.length (fun j hj => V.get0_ge v j hj) N hN]

theorem vectorMass_get0_le (xs : V multi.T) (i : Nat) : mass (V.get0 xs i) ≤ vectorMass xs := by
  induction xs with
  | emp => show mass .Z ≤ _; rw [mass_Z]; exact Nat.zero_le _
  | snoc x xs ih =>
    rw [vectorMass_snoc]
    show mass (if i = xs.length then x else V.get0 xs i) ≤ _
    by_cases hi : i = xs.length
    · rw [ite_eq_left hi]; omega
    · rw [ite_eq_right hi]; have := ih; omega

theorem mass_idx_lt (xs : V multi.T) (b : multi.T) (i : Nat) :
    mass (V.get0 xs i) < mass (.P xs b) := by
  have hi := vectorMass_get0_le xs i
  rw [mass_P]
  omega

theorem vectorMass_pair_le (xs : V multi.T) (i j : Nat) (hij : i ≠ j) :
    mass (V.get0 xs i) + mass (V.get0 xs j) ≤ vectorMass xs := by
  induction xs with
  | emp => show mass .Z + mass .Z ≤ _; rw [mass_Z, vectorMass_emp]; exact Nat.le_refl _
  | snoc x xs ih =>
    rw [vectorMass_snoc]
    show mass (if i = xs.length then x else V.get0 xs i) +
      mass (if j = xs.length then x else V.get0 xs j) ≤ _
    by_cases hi : i = xs.length
    · rw [ite_eq_left hi, ite_eq_right (by omega)]
      have := vectorMass_get0_le xs j; omega
    · rw [ite_eq_right hi]
      by_cases hj : j = xs.length
      · rw [ite_eq_left hj]
        have := vectorMass_get0_le xs i; omega
      · rw [ite_eq_right hj]; have := ih; omega

theorem mass_tail_lt (xs : V multi.T) (b : multi.T) : mass b < mass (.P xs b) := by
  rw [mass_P]; omega

theorem vectorMass_set (xs : V multi.T) (i : Nat) (hi : i < xs.length) (a : multi.T) :
    vectorMass (V.set xs i a) + mass (V.get0 xs i) = vectorMass xs + mass a := by
  induction xs with
  | emp => simp [V.length] at hi
  | snoc x xs ih =>
    simp only [V.length] at hi
    by_cases h : i = xs.length
    · subst h
      rw [show V.set (.snoc x xs) xs.length a = .snoc a xs by simp [V.set],
        V.get0_snoc_top, vectorMass_snoc, vectorMass_snoc]
      omega
    · rw [show V.set (.snoc x xs) i a = .snoc x (V.set xs i a) by simp [V.set, h],
        V.get0_snoc_low x xs i (by omega), vectorMass_snoc, vectorMass_snoc]
      have := ih (by omega)
      omega

theorem vectorMass_eq_zero (xs : V multi.T) (hz : ∀ i, V.get0 xs i = .Z) : vectorMass xs = 0 := by
  rw [vectorMass_eq_msum]
  exact msum_eq_zero _ _ (fun j _ => hz j)

theorem mass_norm : ∀ s : multi.T, mass (multi.T.norm s) = mass s
  | .Z => by rw [multi.T.norm]
  | .P v a => by
    rw [multi.T.norm_P, mass_P, mass_P, mass_norm a]
    have hl : (V.norm v).length ≤ v.length := by
      rw [multi.V.norm_eq, multi.V.length_mapNorm]; exact multi.V.length_trim_le v
    have hv : vectorMass (V.norm v) = vectorMass v := by
      rw [vectorMass_eq_msum_of (V.norm v) v.length hl, vectorMass_eq_msum v]
      exact msum_congr _ (fun j _ => by rw [multi.V.get0_norm, mass_norm])
    rw [hv]
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem mass_congr {x y : multi.T} (h : compareT x y = .eq) : mass x = mass y := by
  rw [← mass_norm x, ← mass_norm y, (compareT_eq_iff x y).1 h]

theorem vectorMass_congr {v w : V multi.T} (h : compareV v w = .eq) :
    vectorMass v = vectorMass w := by
  have hm := mass_congr (x := .P v .Z) (y := .P w .Z) ((T.P_eqv_iff _ _ _ _).2 ⟨h, compareT_ZZ⟩)
  rw [mass_P, mass_P] at hm
  omega

theorem mass_positive {s : multi.T} (hs : s ≠ .Z) : 0 < mass s := by
  cases s with
  | Z => exact absurd rfl hs
  | P xs b => rw [mass_P]; omega

/-! ### Successors in arbitrary dimension -/

theorem add_one_ne_zero (w : V multi.T) (c : multi.T) : c + .P w .Z ≠ .Z := by
  cases c <;> intro h <;> cases h

theorem fund_add_one {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) :
    ∀ (c t : multi.T), T.fund (c + .P w .Z) t = c
  | .Z, t => fund_none (fnz_eq_none hw) t
  | .P xs b, t => by
    show T.fund (.P xs (b + .P w .Z)) t = .P xs b
    rw [fund_tail xs (add_one_ne_zero w b), fund_add_one hw b t]

theorem lt_add_one_iff {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) :
    ∀ z c : multi.T, z < c + .P w .Z ↔ z ≤ c
  | z, .Z => by
    show z < .P w .Z ↔ z ≤ .Z
    rw [lt_one_iff hw]
    constructor
    · rintro rfl; exact T.le_refl _
    · rintro (h | h)
      · exact absurd h (T.not_lt_Z _)
      · exact T.eqv_Z_iff.1 h
  | .Z, .P ys b => ⟨fun _ => T.Z_le _, fun _ => T.Z_lt_P _ _⟩
  | .P xs a, .P ys b => by
    show multi.T.P xs a < .P ys (b + .P w .Z) ↔ multi.T.P xs a ≤ .P ys b
    rw [T.P_lt_P_iff, T.P_le_P_iff, lt_add_one_iff hw a b]

theorem mass_add_one {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) :
    ∀ c : multi.T, mass (c + .P w .Z) = mass c + 1
  | .Z => by
    show mass (.P w .Z) = mass .Z + 1
    rw [mass_P, mass_Z, vectorMass_eq_zero w hw]
  | .P xs b => by
    show mass (.P xs (b + .P w .Z)) = mass (.P xs b) + 1
    rw [mass_P, mass_P, mass_add_one hw b]
    omega

theorem dom_one_decomp : ∀ a : multi.T, domF a = .one →
    ∃ c w, (∀ i, V.get0 w i = .Z) ∧ a = c + .P w .Z
  | .Z, hd => by rw [domF_Z] at hd; cases hd
  | .P xs b, hd => by
    by_cases hb : b = .Z
    · subst hb
      exact ⟨.Z, xs, dom_one_principal hd, rfl⟩
    · rw [domF_tail xs hb] at hd
      obtain ⟨c, w, hw, rfl⟩ := dom_one_decomp b hd
      exact ⟨.P xs c, w, hw, rfl⟩

theorem mass_succ (lam : Nat) (s : multi.T) : mass (SourceSuccessor.succ lam s) = mass s + 1 :=
  mass_add_one (w := zeros lam) (get0_zeros lam) s

theorem mass_fund_one (s t : multi.T) (hd : domF s = .one) : mass (T.fund s t) + 1 = mass s := by
  obtain ⟨c, w, hw, rfl⟩ := dom_one_decomp s hd
  rw [fund_add_one hw, mass_add_one hw]

theorem source_le_antisymm {a b : multi.T} (hab : a ≤ b) (hba : b ≤ a) : compareT a b = .eq :=
  (compareT_eq_iff a b).2 (T.le_antisymm hab hba)

/-! ### Intervals below a principal term -/

theorem vlt_irrefl_of_le_lt {a b : V multi.T} (hab : a ≤ b) (hba : b < a) : False := by
  rcases hab with h | h
  · exact V.lt_irrefl _ (V.lt_trans h hba)
  · exact V.lt_irrefl _ (V.lt_of_lt_of_eqv hba h)

theorem vector_interval (xs lo ys : V multi.T) (i : Nat)
    (hz : ∀ j, j < i → V.get0 xs j = .Z)
    (hh : ∀ j, i < j → V.get0 lo j = V.get0 xs j)
    (hlo : lo ≤ ys) (hhi : ys < xs) :
    V.get0 lo i ≤ V.get0 ys i ∧ V.get0 ys i < V.get0 xs i ∧
      vectorMass xs - mass (V.get0 xs i) + mass (V.get0 ys i) ≤ vectorMass ys := by
  obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot ys xs).1 hhi
  have hpi : i ≤ p := pivot_above_zero hz hp
  have hp_eq : p = i := by
    apply Nat.le_antisymm _ hpi
    apply Nat.le_of_not_lt
    intro hip
    apply vlt_irrefl_of_le_lt hlo
    apply V.lt_of_pivot p
    · intro j hj
      rw [hh j (by omega)]
      exact habove j hj
    · rw [hh p hip]; exact hp
  subst hp_eq
  refine ⟨?_, hp, ?_⟩
  · rcases T.le_total (V.get0 lo p) (V.get0 ys p) with h | h
    · exact h
    · rcases h with h | h
      · exfalso
        apply vlt_irrefl_of_le_lt hlo
        apply V.lt_of_pivot p
        · intro j hj
          rw [hh j hj]
          exact habove j hj
        · exact h
      · exact T.le_of_eqv (T.eqv_symm h)
  · have hpx : p < xs.length := by
      apply Nat.lt_of_not_le
      intro hle
      rw [V.get0_ge xs p hle] at hp
      exact T.not_lt_Z _ hp
    let N := xs.length + ys.length
    obtain ⟨r, hr⟩ : ∃ r, N = (p + 1) + r := ⟨N - (p + 1), by omega⟩
    have hx := vectorMass_eq_msum_of xs N (by omega)
    have hy := vectorMass_eq_msum_of ys N (by omega)
    rw [hr, msum_add] at hx hy
    have hx0 : msum (V.get0 xs) (p + 1) = mass (V.get0 xs p) := by
      show msum (V.get0 xs) p + mass (V.get0 xs p) = _
      rw [msum_eq_zero _ p hz, Nat.zero_add]
    have hy0 : mass (V.get0 ys p) ≤ msum (V.get0 ys) (p + 1) := by
      show _ ≤ msum (V.get0 ys) p + mass (V.get0 ys p)
      omega
    have htop : msum (fun j => V.get0 xs (p + 1 + j)) r = msum (fun j => V.get0 ys (p + 1 + j)) r :=
      msum_congr _ (fun j _ => (mass_congr (habove (p + 1 + j) (by omega))).symm)
    omega

theorem principal_interval_mass (xs lo : V multi.T) (b w : multi.T) (i g : Nat)
    (hz : ∀ j, j < i → V.get0 xs j = .Z)
    (hh : ∀ j, i < j → V.get0 lo j = V.get0 xs j)
    (hgap : ∀ z, V.get0 lo i ≤ z → z < V.get0 xs i → g ≤ mass z)
    (hlo : multi.T.P lo b ≤ w) (hhi : w < .P xs .Z) :
    1 + (vectorMass xs - mass (V.get0 xs i)) + g ≤ mass w := by
  cases w with
  | Z =>
    rcases hlo with hlo | hlo
    · exact absurd hlo (T.not_lt_Z _)
    · rw [compareT_PZ] at hlo; cases hlo
  | P ys c =>
    have hlv : lo ≤ ys := by
      rcases (T.P_le_P_iff lo ys b c).1 hlo with h | ⟨h, _⟩
      · exact Or.inl h
      · exact Or.inr h
    have hv := vector_interval xs lo ys i hz hh hlv (vlt_of_P_lt hhi)
    have hg := hgap (V.get0 ys i) hv.1 hv.2.1
    rw [mass_P]
    omega

theorem tail_interval (xs : V multi.T) (b c w : multi.T)
    (hlo : multi.T.P xs c ≤ w) (hhi : w < .P xs b) :
    ∃ ys r, w = .P ys r ∧ compareV ys xs = .eq ∧ c ≤ r ∧ r < b := by
  cases w with
  | Z =>
    rcases hlo with hlo | hlo
    · exact absurd hlo (T.not_lt_Z _)
    · rw [compareT_PZ] at hlo; cases hlo
  | P ys r =>
    refine ⟨ys, r, rfl, ?_⟩
    rcases (T.P_le_P_iff xs ys c r).1 hlo with h1 | ⟨h1, hcr⟩
    · rcases (T.P_lt_P_iff ys xs r b).1 hhi with h2 | ⟨h2, _⟩
      · exact absurd (V.lt_trans h1 h2) (V.lt_irrefl _)
      · exact absurd (V.lt_of_lt_of_eqv h1 h2) (V.lt_irrefl _)
    · rcases (T.P_lt_P_iff ys xs r b).1 hhi with h2 | ⟨h2, hrb⟩
      · exact absurd (V.lt_of_eqv_of_lt h1 h2) (V.lt_irrefl _)
      · exact ⟨h2, hcr, hrb⟩

theorem mass_gap_one_coordinate (a z : multi.T) (ha : domF a = .one)
    (hlo : T.fund a .Z ≤ z) (hhi : z < a) : mass a - 1 ≤ mass z := by
  obtain ⟨c, w, hw, rfl⟩ := dom_one_decomp a ha
  rw [fund_add_one hw] at hlo
  have hz := (lt_add_one_iff hw z c).1 hhi
  have he := source_le_antisymm hlo hz
  rw [mass_add_one hw, mass_congr he]
  omega

theorem principal_step_gap (xs lo : V multi.T) (b w : multi.T) (i : Nat)
    (hz : ∀ j, j < i → V.get0 xs j = .Z) (hn : V.get0 xs i ≠ .Z)
    (hh : ∀ j, i < j → V.get0 lo j = V.get0 xs j)
    (hg : ∀ z, V.get0 lo i ≤ z → z < V.get0 xs i → mass (V.get0 xs i) - 1 ≤ mass z)
    (hlo : multi.T.P lo b ≤ w) (hhi : w < .P xs .Z) :
    mass (.P xs .Z) - 1 ≤ mass w := by
  have h := principal_interval_mass xs lo b w i (mass (V.get0 xs i) - 1) hz hh hg hlo hhi
  have hi := vectorMass_get0_le xs i
  have hp := mass_positive hn
  rw [mass_P, mass_Z]
  omega

theorem gap_mass : ∀ (s t w : multi.T), (domF s = .omega ∨ ∃ v, domF s = .Omega v) →
    (domF s = .omega → t ≠ .Z) → T.fund s t ≤ w → w < s → mass s - 1 ≤ mass w
  | .Z, _, _, hd, _, _, _ => by
    rw [domF_Z] at hd; rcases hd with hd | ⟨v, hd⟩ <;> cases hd
  | .P xs b, t, w, hd, ht, hlo, hhi => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; rcases hd with hd | ⟨v, hd⟩ <;> cases hd
      · obtain ⟨hn, hz⟩ := V.fnz_some_spec xs i hf
        have hil := fnz_lt_length hf
        have hset : ∀ y j, i < j → V.get0 (V.set xs i y) j = V.get0 xs j :=
          fun y j hj => V.get0_set_ne xs i y j (Nat.ne_of_gt hj)
        have hseti : ∀ y, V.get0 (V.set xs i y) i = y := fun y => V.get0_set_same xs i y hil
        cases hc : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hc) hn
        | omega =>
          have hdom := domF_omega hf hc
          rw [fund_omega hf hc] at hlo
          apply principal_step_gap xs _ .Z w i hz hn (hset _) ?_ hlo hhi
          intro z hz1 hz2
          rw [hseti] at hz1
          exact gap_mass _ t z (Or.inl hc) (fun _ => ht hdom) hz1 hz2
        | Omega v =>
          by_cases hv : xs < v
          · rw [fund_diag hf hc hv] at hlo
            apply principal_step_gap xs _ .Z w i hz hn (hset _) ?_ hlo hhi
            intro z hz1 hz2
            rw [hseti] at hz1
            exact gap_mass _ _ z (Or.inr ⟨v, hc⟩) (by intro h; rw [hc] at h; cases h) hz1 hz2
          · rw [fund_nondiag hf hc hv] at hlo
            apply principal_step_gap xs _ .Z w i hz hn (hset _) ?_ hlo hhi
            intro z hz1 hz2
            rw [hseti] at hz1
            exact gap_mass _ t z (Or.inr ⟨v, hc⟩) (by intro h; rw [hc] at h; cases h) hz1 hz2
        | one =>
          cases i with
          | zero =>
            have hdom := domF_one_zero hf hc
            have htn := ht hdom
            cases t with
            | Z => exact absurd rfl htn
            | P us c =>
              rw [fund_one_zero hf hc] at hlo
              have hlo' : multi.T.P (V.set xs 0 (T.fund (V.get0 xs 0) .Z))
                  (multi.T.mul (.P (V.set xs 0 (T.fund (V.get0 xs 0) .Z)) .Z) c) ≤ w := hlo
              apply principal_step_gap xs _ _ w 0 hz hn (hset _) ?_ hlo' hhi
              intro z hz1 hz2
              rw [hseti] at hz1
              exact mass_gap_one_coordinate _ _ hc hz1 hz2
          | succ m =>
            rw [fund_one_succ hf hc] at hlo
            apply principal_step_gap xs _ .Z w (m + 1) hz hn ?_ ?_ hlo hhi
            · intro j hj
              rw [V.get0_set_ne _ m t j (by omega), hset _ j hj]
            · intro z hz1 hz2
              rw [V.get0_set_ne _ m t (m + 1) (by omega), hseti] at hz1
              exact mass_gap_one_coordinate _ _ hc hz1 hz2
    · rw [fund_tail xs hb] at hlo
      rw [domF_tail xs hb] at hd ht
      obtain ⟨ys, r, rfl, hys, hl, hh⟩ := tail_interval xs b (T.fund b t) w hlo hhi
      have hg := gap_mass b t r hd ht hl hh
      have hp := mass_positive hb
      rw [mass_P, mass_P, vectorMass_congr hys]
      omega
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

def zeroGap (s : multi.T) : Nat :=
  match s with
  | .Z => 0
  | .P xs b =>
    if b = .Z then
      match V.fnz xs with
      | none => 0
      | some i =>
        match domF (V.get0 xs i) with
        | .zero => 0
        | .one => if i = 0 then 0 else vectorMass xs
        | .omega => 1 + (vectorMass xs - mass (V.get0 xs i)) + zeroGap (V.get0 xs i)
        | .Omega _ => vectorMass xs
    else 1 + vectorMass xs + zeroGap b
termination_by s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem zeroGap_Z : zeroGap .Z = 0 := by rw [zeroGap]

theorem zeroGap_tail (xs : V multi.T) {b : multi.T} (hb : b ≠ .Z) :
    zeroGap (.P xs b) = 1 + vectorMass xs + zeroGap b := by
  rw [zeroGap, ite_eq_right hb]

theorem zeroGap_none {xs : V multi.T} (h : V.fnz xs = none) : zeroGap (.P xs .Z) = 0 := by
  rw [zeroGap, ite_eq_left rfl, h]

theorem zeroGap_omega {xs : V multi.T} {i : Nat} (h : V.fnz xs = some i)
    (hd : domF (V.get0 xs i) = .omega) :
    zeroGap (.P xs .Z) = 1 + (vectorMass xs - mass (V.get0 xs i)) + zeroGap (V.get0 xs i) := by
  rw [zeroGap, ite_eq_left rfl, h]; simp only [hd]

theorem zeroGap_Omega_case {xs : V multi.T} {i : Nat} {v : V multi.T} (h : V.fnz xs = some i)
    (hd : domF (V.get0 xs i) = .Omega v) : zeroGap (.P xs .Z) = vectorMass xs := by
  rw [zeroGap, ite_eq_left rfl, h]; simp only [hd]

theorem zeroGap_one_zero {xs : V multi.T} (h : V.fnz xs = some 0)
    (hd : domF (V.get0 xs 0) = .one) : zeroGap (.P xs .Z) = 0 := by
  rw [zeroGap, ite_eq_left rfl, h]; simp only [hd, ↓reduceIte]

theorem zeroGap_one_succ {xs : V multi.T} {m : Nat} (h : V.fnz xs = some (m + 1))
    (hd : domF (V.get0 xs (m + 1)) = .one) : zeroGap (.P xs .Z) = vectorMass xs := by
  rw [zeroGap, ite_eq_left rfl, h]; simp only [hd, Nat.add_one_ne_zero, ↓reduceIte]

theorem gap_zero : ∀ (s w : multi.T), T.fund s .Z ≤ w → w < s → zeroGap s ≤ mass w
  | .Z, w, _, hhi => absurd hhi (T.not_lt_Z _)
  | .P xs b, w, hlo, hhi => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [zeroGap_none hf]; exact Nat.zero_le _
      · obtain ⟨hn, hz⟩ := V.fnz_some_spec xs i hf
        have hil := fnz_lt_length hf
        have hset : ∀ y j, i < j → V.get0 (V.set xs i y) j = V.get0 xs j :=
          fun y j hj => V.get0_set_ne xs i y j (Nat.ne_of_gt hj)
        have hseti : ∀ y, V.get0 (V.set xs i y) i = y := fun y => V.get0_set_same xs i y hil
        cases hc : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hc) hn
        | omega =>
          rw [zeroGap_omega hf hc]
          rw [fund_omega hf hc] at hlo
          apply principal_interval_mass xs _ .Z w i (zeroGap (V.get0 xs i)) hz (hset _) ?_ hlo hhi
          intro z hz1 hz2
          rw [hseti] at hz1
          exact gap_zero _ z hz1 hz2
        | Omega v =>
          rw [zeroGap_Omega_case hf hc]
          have hg : mass (.P xs .Z) - 1 ≤ mass w := by
            by_cases hv : xs < v
            · rw [fund_diag hf hc hv] at hlo
              apply principal_step_gap xs _ .Z w i hz hn (hset _) ?_ hlo hhi
              intro z hz1 hz2
              rw [hseti] at hz1
              exact gap_mass _ _ z (Or.inr ⟨v, hc⟩) (by intro h; rw [hc] at h; cases h) hz1 hz2
            · rw [fund_nondiag hf hc hv] at hlo
              apply principal_step_gap xs _ .Z w i hz hn (hset _) ?_ hlo hhi
              intro z hz1 hz2
              rw [hseti] at hz1
              exact gap_mass _ .Z z (Or.inr ⟨v, hc⟩) (by intro h; rw [hc] at h; cases h) hz1 hz2
          rw [mass_P, mass_Z] at hg
          omega
        | one =>
          cases i with
          | zero => rw [zeroGap_one_zero hf hc]; exact Nat.zero_le _
          | succ m =>
            rw [zeroGap_one_succ hf hc]
            rw [fund_one_succ hf hc] at hlo
            have hg : mass (.P xs .Z) - 1 ≤ mass w := by
              apply principal_step_gap xs _ .Z w (m + 1) hz hn ?_ ?_ hlo hhi
              · intro j hj
                rw [V.get0_set_ne _ m .Z j (by omega), hset _ j hj]
              · intro z hz1 hz2
                rw [V.get0_set_ne _ m .Z (m + 1) (by omega), hseti] at hz1
                exact mass_gap_one_coordinate _ _ hc hz1 hz2
            rw [mass_P, mass_Z] at hg
            omega
    · rw [zeroGap_tail xs hb]
      rw [fund_tail xs hb] at hlo
      obtain ⟨ys, r, rfl, hys, hl, hh⟩ := tail_interval xs b (T.fund b .Z) w hlo hhi
      have hg := gap_zero b r hl hh
      rw [mass_P, vectorMass_congr hys]
      omega
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

def gap (s t : multi.T) : Nat :=
  if t = .Z then zeroGap s else mass s - 1

theorem gap_all (s t w : multi.T) (hlo : T.fund s t ≤ w) (hhi : w < s) : gap s t ≤ mass w := by
  by_cases ht : t = .Z
  · subst t
    rw [gap, ite_eq_left rfl]
    exact gap_zero s w hlo hhi
  · rw [gap, ite_eq_right ht]
    cases hd : domF s with
    | zero =>
      rw [(domF_eq_zero_iff s).mp hd] at hhi
      exact absurd hhi (T.not_lt_Z _)
    | one =>
      rw [SourceFundOrder.dom_one_fund_constant s hd t .Z] at hlo
      exact mass_gap_one_coordinate s w hd hlo hhi
    | omega => exact gap_mass s t w (Or.inl hd) (fun _ => ht) hlo hhi
    | Omega v => exact gap_mass s t w (Or.inr ⟨v, hd⟩) (by intro h; rw [hd] at h; cases h) hlo hhi

theorem small_lt_fund_all (s t z : multi.T) (hz : z < s) (hm : mass z < gap s t) :
    z < T.fund s t := by
  rcases T.lt_trichotomy z (T.fund s t) with h | h | h
  · exact h
  · exact absurd (gap_all s t z (Or.inr ((compareT_eq_iff _ _).2 h.symm)) hz) (Nat.not_le_of_lt hm)
  · exact absurd (gap_all s t z (Or.inl h) hz) (Nat.not_le_of_lt hm)

theorem zeroGap_le_mass : ∀ s : multi.T, zeroGap s ≤ mass s - 1
  | .Z => by rw [zeroGap_Z, mass_Z]; exact Nat.zero_le _
  | .P xs b => by
    by_cases hb : b = .Z
    · subst hb
      rw [mass_P, mass_Z]
      rcases hf : V.fnz xs with _ | i
      · rw [zeroGap_none hf]; exact Nat.zero_le _
      · cases hc : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hc) (V.fnz_some_spec xs i hf).1
        | one =>
          cases i with
          | zero => rw [zeroGap_one_zero hf hc]; exact Nat.zero_le _
          | succ m => rw [zeroGap_one_succ hf hc]; omega
        | Omega v => rw [zeroGap_Omega_case hf hc]; omega
        | omega =>
          rw [zeroGap_omega hf hc]
          have hn := (V.fnz_some_spec xs i hf).1
          have hi := vectorMass_get0_le xs i
          have hp := mass_positive hn
          have hg := zeroGap_le_mass (V.get0 xs i)
          omega
    · rw [zeroGap_tail xs hb, mass_P]
      have hp := mass_positive hb
      have hg := zeroGap_le_mass b
      omega
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem zeroGap_Omega (s : multi.T) (v : V multi.T) (hd : domF s = .Omega v) :
    zeroGap s + 1 = mass s := by
  have hp := SourceFundOrder.OmegaLabelPath.of_domain s hd
  clear hd
  induction hp with
  | regular m hf hc => rw [zeroGap_one_succ hf hc, mass_P, mass_Z]; omega
  | inherit xs i hf hdq => rw [zeroGap_Omega_case hf hdq, mass_P, mass_Z]; omega
  | tail xs b hb _ ih => rw [zeroGap_tail xs hb, mass_P]; omega

theorem gap_nonzero (s t : multi.T) (ht : t ≠ .Z) : gap s t = mass s - 1 := by
  rw [gap, ite_eq_right ht]

theorem gap_Omega (s t : multi.T) (v : V multi.T) (hd : domF s = .Omega v) :
    gap s t = mass s - 1 := by
  by_cases ht : t = .Z
  · rw [gap, ite_eq_left ht]
    have hg := zeroGap_Omega s v hd
    omega
  · exact gap_nonzero s t ht

theorem mass_fund_zero_le : ∀ s : multi.T, mass (T.fund s .Z) ≤ zeroGap s
  | .Z => by rw [fund_Z, mass_Z]; exact Nat.zero_le _
  | .P xs b => by
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf, zeroGap_none hf, mass_Z]; exact Nat.le_refl _
      · obtain ⟨hn, hz⟩ := V.fnz_some_spec xs i hf
        have hil := fnz_lt_length hf
        have hr := vectorMass_set xs i hil (T.fund (V.get0 xs i) .Z)
        have hi := vectorMass_get0_le xs i
        have hg := mass_fund_zero_le (V.get0 xs i)
        cases hc : domF (V.get0 xs i) with
        | zero => exact absurd ((domF_eq_zero_iff _).1 hc) hn
        | omega =>
          rw [fund_omega hf hc, zeroGap_omega hf hc, mass_P, mass_Z]
          omega
        | Omega ys =>
          have hgO := zeroGap_Omega (V.get0 xs i) ys hc
          rw [zeroGap_Omega_case hf hc]
          by_cases hv : xs < ys
          · rw [fund_diag hf hc hv]
            show mass (.P (V.set xs i (T.fund (V.get0 xs i) .Z)) .Z) ≤ _
            rw [mass_P, mass_Z]
            omega
          · rw [fund_nondiag hf hc hv, mass_P, mass_Z]
            omega
        | one =>
          have hg1 := mass_fund_one (V.get0 xs i) .Z hc
          cases i with
          | zero =>
            rw [fund_one_zero hf hc, zeroGap_one_zero hf hc]
            show mass .Z ≤ 0
            rw [mass_Z]; exact Nat.le_refl _
          | succ m =>
            rw [fund_one_succ hf hc, zeroGap_one_succ hf hc]
            have hl : V.get0 xs m = .Z := hz m (by omega)
            have hp : V.get0 (V.set xs (m + 1) (T.fund (V.get0 xs (m + 1)) .Z)) m = .Z := by
              rw [V.get0_set_ne _ _ _ m (by omega), hl]
            have hr2 := vectorMass_set (V.set xs (m + 1) (T.fund (V.get0 xs (m + 1)) .Z)) m
              (by rw [V.length_set]; omega) .Z
            rw [hp, mass_Z] at hr2
            rw [mass_P, mass_Z]
            omega
    · rw [fund_tail xs hb, zeroGap_tail xs hb, mass_P]
      have hg := mass_fund_zero_le b
      omega
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

end kumakuma.SourceFundGap

namespace kumakuma.SourceCoefficientGap

open multi OTQuotient SourceFundGap
open GeneralImageCoefficients

theorem mass_lt_of_subterm {a s : multi.T} (h : Subterm a s) : mass a < mass s := by
  induction h with
  | coordinate => exact mass_idx_lt _ _ _
  | tail => exact mass_tail_lt _ _
  | trans _ _ ha hb => exact Nat.lt_trans ha hb

/-- A subterm of `xs ⊕ b` is no heavier than a coordinate of `xs` or than `b`. -/
theorem mass_le_of_subterm_P {a : multi.T} {xs : V multi.T} {b : multi.T}
    (h : Subterm a (.P xs b)) : (∃ j, mass a ≤ mass (V.get0 xs j)) ∨ mass a ≤ mass b := by
  suffices ∀ {s}, Subterm a s → s = .P xs b →
      (∃ j, mass a ≤ mass (V.get0 xs j)) ∨ mass a ≤ mass b from this h rfl
  clear h
  intro s h
  induction h with
  | coordinate _ _ i => intro he; cases he; exact .inl ⟨i, Nat.le_refl _⟩
  | tail => intro he; cases he; exact .inr (Nat.le_refl _)
  | trans hab _ _ ih =>
    have := mass_lt_of_subterm hab
    intro he
    exact (ih he).imp (fun ⟨j, hj⟩ => ⟨j, Nat.le_trans (Nat.le_of_lt this) hj⟩)
      (Nat.le_trans (Nat.le_of_lt this))

theorem principal_subterm_mass {xs : V multi.T} {i j : Nat} (hij : i ≠ j)
    (hi : V.get0 xs i ≠ .Z) (hj : V.get0 xs j ≠ .Z) {a : multi.T} (ha : Subterm a (.P xs .Z)) :
    mass a < mass (.P xs .Z) - 1 := by
  have := mass_positive hi; have := mass_positive hj; have := vectorMass_pair_le xs i j hij
  rw [mass_P, mass_Z]
  rcases mass_le_of_subterm_P ha with ⟨l, hl⟩ | hl
  · by_cases e : l = i
    · subst e; omega
    · have := vectorMass_pair_le xs l i e; omega
  · rw [mass_Z] at hl; omega

theorem sum_subterm_mass {xs : V multi.T} {b : multi.T} (hb : b ≠ .Z) (hx : 0 < vectorMass xs)
    {a : multi.T} (ha : Subterm a (.P xs b)) : mass a < mass (.P xs b) - 1 := by
  have := mass_positive hb
  rw [mass_P]
  rcases mass_le_of_subterm_P ha with ⟨l, hl⟩ | hl
  · have := vectorMass_get0_le xs l; omega
  · omega

end kumakuma.SourceCoefficientGap

namespace kumakuma.GeneralImageLimitSupport

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageCoefficients kumakuma.TargetArithmetic kumakuma.BinaryTranslation
open kumakuma.DimensionCut kumakuma.GeneralImageLimitBranches
open kumakuma.CountableSource
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair

theorem convert_principal (d : Nat) (xs : V multi.T) :
    convert d (code (.P xs .Z)) = principal d (arguments d (trim (codes xs))) := by
  rw [convert_P, convert_Z]
  simp only [kumakuma.OT2.assemble, ↓reduceIte]

theorem principal_image_ne_one (k : Nat)
    (xs : V multi.T) (i : Nat) (hsD : Dim (k + 3) (.P xs .Z))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (hn : V.get0 xs i ≠ .Z) :
    convert (k + 3) (code (.P xs .Z)) ≠ Term.one := by
  intro he
  have ho : RecursiveWF (k + 3) (ofNatD (k + 3) 1) := ofNat_one_recursiveWF _ _
  have hone : convert (k + 3) (code (ofNatD (k + 3) 1)) = Term.one := by
    rw [code_ofNatD_one, DimensionImage.convert_one]
  have heq := convert_injective k (.P xs .Z) (ofNatD (k + 3) 1) hsD (Dim_ofNatD _ _) hs ho
    (he.trans hone.symm)
  have hx : xs = zeros (k + 3) := by injection heq
  apply hn
  rw [hx, get0_zeros]

theorem lt_inacc_drop (n : Nat) (a : Term)
    (ha : Term.wf a = true) (hi : Term.wf (.inacc n (dropOne a)) = true) :
    Term.lt a (.inacc n (dropOne a)) = true := by
  by_cases hh : Term.head a = Term.one
  · obtain ⟨m, he⟩ := head_one_nat ha hh
    rw [he]
    simpa only [he] using
      nat_lt_of_head_ne hi (by intro h; cases h) (by intro h; cases h) (m + 1)
  · rw [dropOne_of_head_ne hh] at hi ⊢
    exact OCF.Jaeger.Term.lt_inacc_self hi

theorem no_diagonal_highest (k : Nat)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hr : kumakuma.SourceRecursiveDescending.Recursive (V.get0 xs (k + 2)))
    {v : V multi.T} (hf : V.fnz xs = some (k + 2))
    (hd : domF (V.get0 xs (k + 2)) = .Omega v) : ¬ xs < v := by
  intro hv
  have hn : V.get0 xs (k + 2) ≠ .Z := (V.fnz_some_spec xs _ hf).1
  have hx : xs = lastVec (k + 2) (V.get0 xs (k + 2)) := by
    apply V.eq_of_get0 _ _ (by rw [hsD.length, lastVec_length])
    intro j
    rw [get0_lastVec]
    by_cases hj : j = k + 2
    · rw [ite_eq_left hj, hj]
    · rw [ite_eq_right hj]
      by_cases hjl : j < k + 2
      · exact (V.fnz_some_spec xs _ hf).2 j hjl
      · exact V.get0_ge xs j (by rw [hsD.length]; omega)
  have he : convert (k + 3) (code (.P xs .Z)) =
      .inacc (k + 1) (dropOne (convert (k + 3) (code (V.get0 xs (k + 2))))) := by
    have ht := convert_topNode k (V.get0 xs (k + 2)) hn
    rw [topNode, ← hx] at ht
    exact ht
  have ha : RecursiveWF (k + 3) (V.get0 xs (k + 2)) := (RecursiveWF_P.1 hs).1 _
  have hlt := (convert_order k (.P xs .Z) (V.get0 xs (k + 2)) hsD (hsD.coord _) hs ha).mp
    (kumakuma.SourceRecursiveDescending.diagonal_principal_lt_argument xs _ hr hd hv)
  have hrev : Term.lt (convert (k + 3) (code (V.get0 xs (k + 2))))
      (convert (k + 3) (code (.P xs .Z))) = true := by
    rw [he]
    exact lt_inacc_drop _ _ ha.wf (he ▸ hs.wf)
  have hf' := OCF.Jaeger.Term.not_lt_of_lt hlt
  rw [hf'] at hrev
  cases hrev

theorem drop_succ (a : Term) (ha : a ≠ .zero) :
    dropOne (succTerm a) = succTerm (dropOne a) := by
  cases a with
  | zero => exact False.elim (ha rfl)
  | add a b => by_cases he : a = Term.one <;> simp [succTerm, dropOne, he]
  | inacc n b => simp [succTerm, dropOne, Term.one]
  | psi v b =>
    by_cases he : Term.psi v b = Term.one
    · rw [he]; simp [succTerm, dropOne, Term.one, Term.bigOmega]
    · simp [succTerm, dropOne, he]

theorem psi_wf_of_succ (v a : Term) (ha : Term.wf a = true)
    (hw : Term.wf (.psi v (succTerm a)) = true) : Term.wf (.psi v a) = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  apply (Term.wf_psi_iff _ _).mpr
  refine ⟨hp.1, hp.2.1, ha, ?_⟩
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  have hzw := H_coefficient_wf v a ha hz
  have hz' : z ∈ Term.H v (succTerm a) := by
    rw [kumakuma.OT2.H_succTerm]; exact List.mem_append_left _ hz
  have hlt := (Term.allLt_iff _ _).mp hp.2.2.2 z hz'
  rw [lt_succTerm_eq_le hzw ha] at hlt
  rcases (Term.le_iff_eq_or_lt _ _).mp hlt with he | he
  · have hn := H_size_lt v a hz
    rw [he] at hn
    exact False.elim (Nat.lt_irrefl _ hn)
  · exact he

theorem step_successor_predecessor (n : Nat) (a c : Term)
    (ha : Above n a) (hc : Term.wf c = true)
    (hw : Term.wf (step n a (succTerm c)) = true) : Term.wf (step n a c) = true := by
  by_cases hc0 : c = .zero
  · subst c
    by_cases ha0 : a = .zero
    · subst a
      by_cases hn : n = 0
      · subst n; rfl
      · simp only [step, ↓reduceIte, hn, Term.wf]
    · rw [step, ite_eq_right ha0, ite_eq_left rfl]
      exact step_context_wf ha hw
  · have hdrop := drop_succ c hc0
    have hd := dropOne_wf hc
    by_cases ha0 : a = .zero
    · subst a
      by_cases hn : n = 0
      · subst n
        simpa only [step, ↓reduceIte] using psi_wf_of_succ Term.bigOmega c hc
          (by simpa only [step, ↓reduceIte] using hw)
      · simp only [step, ↓reduceIte, hn, hc0, succTerm_ne_zero, hdrop] at hw ⊢
        exact psi_wf_of_succ (.inacc n .zero) (dropOne c) hd hw
    · simp only [step, ha0, hc0, succTerm_ne_zero, hdrop, ↓reduceIte] at hw ⊢
      exact psi_wf_of_succ (regular n a) (dropOne c) hd hw

theorem zero_step_predecessor (a c : Term) (ha : Above 0 a) (hc : Term.wf c = true)
    (hw : Term.wf (step 0 a (succTerm c)) = true) :
    Term.wf (step 0 a c) = true ∧
      ∀ z, z ∈ Term.H Term.bigOmega (step 0 a c) →
        z = c ∨ z = dropOne c ∨ z ∈ Term.H Term.bigOmega (step 0 a (succTerm c)) := by
  by_cases ha0 : a = .zero
  · subst a
    simp only [step, ↓reduceIte] at hw ⊢
    refine ⟨psi_wf_of_succ _ _ hc hw, ?_⟩
    intro z hz
    change z ∈ Term.H Term.bigOmega (.psi (.inacc 0 .zero) c) at hz
    rw [H_omega_psi_inacc] at hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact Or.inl rfl
    · apply Or.inr; apply Or.inr
      change z ∈ Term.H Term.bigOmega (.psi (.inacc 0 .zero) (succTerm c))
      rw [H_omega_psi_inacc]
      apply List.mem_cons_of_mem
      rcases List.mem_append.mp hz with hz | hz
      · apply List.mem_append_left
        rw [kumakuma.OT2.H_succTerm]
        exact List.mem_append_left _ hz
      · exact List.mem_append_right _ hz
  · by_cases hc0 : c = .zero
    · subst c
      refine ⟨?_, ?_⟩
      · simpa only [step, ha0, ↓reduceIte] using step_context_wf ha hw
      · intro z hz
        apply Or.inr; apply Or.inr
        apply H_omega_step_context
        simpa only [step, ha0, ↓reduceIte] using hz
    · have he := drop_succ c hc0
      simp only [step, ha0, hc0, succTerm_ne_zero, ↓reduceIte, he] at hw ⊢
      refine ⟨psi_wf_of_succ _ _ (dropOne_wf hc) hw, ?_⟩
      intro z hz
      rw [regular, H_omega_psi_inacc] at hz ⊢
      rcases List.mem_cons.mp hz with rfl | hz
      · exact Or.inr (Or.inl rfl)
      · apply Or.inr; apply Or.inr
        apply List.mem_cons_of_mem
        rcases List.mem_append.mp hz with hz | hz
        · apply List.mem_append_left
          rw [kumakuma.OT2.H_succTerm]
          exact List.mem_append_left _ hz
        · exact List.mem_append_right _ hz

theorem lower_zero_predecessor (j : Nat) (hj : 0 < j) (xs ys : List Term) (a c : Term)
    (ha : Context j a) (hc : Term.wf c = true)
    (hx : xs[0]?.getD .zero = succTerm c) (hy : ys[0]?.getD .zero = c)
    (he : ∀ i, 0 < i → i < j → xs[i]?.getD .zero = ys[i]?.getD .zero)
    (hw : Term.wf (lower j xs a) = true) :
    Term.wf (lower j ys a) = true ∧
      ∀ z, z ∈ Term.H Term.bigOmega (lower j ys a) →
        z = c ∨ z = dropOne c ∨ z ∈ Term.H Term.bigOmega (lower j xs a) := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero =>
      simp only [lower, hx, hy] at hw ⊢
      exact zero_step_predecessor a c (context_above ha) hc hw
    | succ j =>
      rw [lower_succ] at hw ⊢
      have hxy := he (j + 1) (by omega) (by omega)
      rw [← hxy]
      exact ih (by omega) _ (step_shape _ (context_above ha))
        (fun i hi hij => he i hi (by omega)) hw

theorem zero_coordinate_predecessor (k : Nat) (xs : V multi.T) (b : multi.T)
    (hsD : Dim (k + 3) (.P xs .Z))
    (hx : V.get0 xs 0 = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    RecursiveWF (k + 3) (.P (V.set xs 0 b) .Z) ∧
      ∀ z, z ∈ Term.H Term.bigOmega
        (convert (k + 3) (code (.P (V.set xs 0 b) .Z))) →
        z = convert (k + 3) (code b) ∨ z = dropOne (convert (k + 3) (code b)) ∨
          z ∈ Term.H Term.bigOmega (convert (k + 3) (code (.P xs .Z))) := by
  have hl0 : 0 < xs.length := by rw [hsD.length]; omega
  let ys := V.set xs 0 b
  let us := arguments (k + 3) (trim (codes xs))
  let vs := arguments (k + 3) (trim (codes ys))
  have hs' := RecursiveWF_P.1 hs
  have hb : RecursiveWF (k + 3) b := by
    have := hs'.1 0
    rw [hx] at this
    exact (recursive_succ_iff _ _ _).mp this
  have he : ∀ i, 0 < i → i < k + 3 → us[i]?.getD .zero = vs[i]?.getD .zero := by
    intro i hi _
    show (arguments (k + 3) (trim (codes xs)))[i]?.getD .zero =
      (arguments (k + 3) (trim (codes (V.set xs 0 b))))[i]?.getD .zero
    rw [converted_coordinate xs i, converted_coordinate (V.set xs 0 b) i,
      V.get0_set_ne xs 0 b i (by omega)]
  have htop : topPair (k + 1) (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero) =
      topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero) := by
    rw [he (k + 2) (by omega) (by omega), he (k + 1) (by omega) (by omega)]
  have hctx : Context (k + 1)
      (topPair (k + 1) (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero)) := by
    rcases topPair_shape (k + 1) _ _ with h | ⟨h, hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, Nat.le_of_eq hf.symm⟩
  have h0 : us[0]?.getD .zero = succTerm (convert (k + 3) (code b)) := by
    show (arguments (k + 3) (trim (codes xs)))[0]?.getD .zero = _
    rw [converted_coordinate xs 0, hx, convert_succ]
  have h0' : vs[0]?.getD .zero = convert (k + 3) (code b) := by
    show (arguments (k + 3) (trim (codes (V.set xs 0 b))))[0]?.getD .zero = _
    rw [converted_coordinate (V.set xs 0 b) 0, V.get0_set_same xs 0 b hl0]
  have hw := hs.wf
  rw [convert_principal, principal_as_layers] at hw
  have hp := lower_zero_predecessor (k + 1) (by omega) us vs _ _ hctx hb.wf h0 h0'
    (fun i hi hik => he i hi (by omega)) hw
  have hnew : RecursiveWF (k + 3) (.P ys .Z) := by
    refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
    · intro i
      show RecursiveWF (k + 3) (V.get0 (V.set xs 0 b) i)
      rw [V.get0_set xs 0 b i hl0]
      split
      · exact hb
      · exact hs'.1 i
    · show Term.wf (convert (k + 3) (code (.P (V.set xs 0 b) .Z))) = true
      rw [convert_principal, principal_as_layers]
      show Term.wf (lower (k + 1) vs
        (topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero))) = true
      rw [← htop]
      exact hp.1
  refine ⟨hnew, ?_⟩
  intro z hz
  rw [convert_principal, principal_as_layers] at hz
  change z ∈ Term.H Term.bigOmega (lower (k + 1) vs
    (topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero))) at hz
  rw [← htop] at hz
  have hpz := hp.2 z hz
  rw [convert_principal, principal_as_layers]
  exact hpz

theorem fund_zero_coordinate_successor (k : Nat) (xs : V multi.T)
    (b t : multi.T)
    (hx : V.get0 xs 0 = kumakuma.SourceSuccessor.succ (k + 3) b) :
    T.fund (.P xs .Z) t = multi.T.mul (.P (V.set xs 0 b) .Z) t := by
  have hd : domF (V.get0 xs 0) = .one := by rw [hx, kumakuma.SourceSuccessor.dom_succ]
  have hf : V.fnz xs = some 0 :=
    fnz_eq_some (by rw [hx]; exact kumakuma.SourceSuccessor.succ_ne_zero _ _)
      (fun j hj => absurd hj (Nat.not_lt_zero j))
  rw [fund_one_zero hf hd, hx, kumakuma.SourceSuccessor.fund_succ]

theorem undrop_lt_principal (a p : Term) (ha : Term.wf a = true)
    (hp : Term.wf p = true) (hprin : Term.isPrin p = true) (hne : p ≠ Term.one)
    (hlt : Term.lt (dropOne a) p = true) : Term.lt a p = true := by
  by_cases hh : Term.head a = Term.one
  · obtain ⟨n, he⟩ := head_one_nat ha hh
    rw [he]
    have hz : p ≠ .zero := by intro h; rw [h] at hprin; cases hprin
    have hh' : Term.head p ≠ Term.one := by
      cases p with
      | zero | add => cases hprin
      | inacc | psi => exact hne
    exact nat_lt_of_head_ne hp hz hh' (n + 1)
  · rwa [dropOne_of_head_ne hh] at hlt

end kumakuma.GeneralImageLimitSupport

namespace kumakuma.SourceSubtermBounds

open multi OTQuotient DimensionCut SourceFundOrder
open GeneralImageCoefficients SourceRecursiveDescending

theorem last_coordinate_lt {m : Nat} : ∀ (xs : V multi.T) (b : multi.T),
    Dim (m + 1) (.P xs b) → V.get0 xs m < .P xs b
  | xs, b, hD => by
    cases he : V.get0 xs m with
    | Z => exact T.Z_lt_P _ _
    | P ys c =>
      have hc : Dim (m + 1) (.P ys c) := he ▸ hD.coord m
      have hh := last_coordinate_lt ys c hc
      apply T.P_lt_P_of_vlt
      apply V.lt_of_pivot m
      · intro j hj
        rw [V.get0_ge ys j (by rw [hc.length]; omega), V.get0_ge xs j (by rw [hD.length]; omega)]
        exact compareT_ZZ
      · rw [he]; exact hh
termination_by xs b => (multi.T.P xs b).size
decreasing_by
  have h := multi.T.size_get0_lt_P xs m b
  rw [he] at h
  exact h

theorem descending_tail_lt : ∀ (xs : V multi.T) (b : multi.T),
    SourceDescending.Descending (.P xs b) → b < .P xs b
  | _, .Z, _ => T.Z_lt_P _ _
  | xs, .P ys c, hs => by
    have hb := hs.1
    rcases hs.2 with hh | hh
    · exact T.P_lt_P_of_vlt _ _ (vlt_of_P_lt hh)
    · have hv : compareV ys xs = .eq := ((T.P_eqv_iff _ _ _ _).1 hh).1
      exact T.P_lt_P_of_eqv hv (descending_tail_lt ys c hb)
termination_by _ b => b.size
decreasing_by exact multi.T.size_lt_P_right _ _

def TreeBelow (bound : multi.T) : multi.T → Prop
  | .Z => multi.T.Z < bound
  | .P xs b => multi.T.P xs b < bound ∧ (∀ i, TreeBelow bound (V.get0 xs i)) ∧ TreeBelow bound b
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

def ChildrenBelow (bound : multi.T) : multi.T → Prop
  | .Z => True
  | .P xs b => (∀ i, TreeBelow bound (V.get0 xs i)) ∧ TreeBelow bound b

theorem TreeBelow_P {bound : multi.T} {xs : V multi.T} {b : multi.T} :
    TreeBelow bound (.P xs b) ↔
      multi.T.P xs b < bound ∧ (∀ i, TreeBelow bound (V.get0 xs i)) ∧ TreeBelow bound b := by
  rw [TreeBelow]

theorem TreeBelow_Z {bound : multi.T} : TreeBelow bound .Z ↔ multi.T.Z < bound := by
  rw [TreeBelow]

theorem TreeBelow.root_lt {bound s : multi.T} (hs : TreeBelow bound s) : s < bound := by
  cases s with
  | Z => exact TreeBelow_Z.1 hs
  | P => exact (TreeBelow_P.1 hs).1

theorem TreeBelow.children {bound s : multi.T} (hs : TreeBelow bound s) : ChildrenBelow bound s := by
  cases s with
  | Z => trivial
  | P => exact (TreeBelow_P.1 hs).2

theorem treeBelow_iff (bound s : multi.T) :
    TreeBelow bound s ↔ s < bound ∧ ChildrenBelow bound s := by
  cases s with
  | Z => rw [TreeBelow_Z]; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  | P xs b => rw [TreeBelow_P]; rfl

theorem Subterm.treeBelow {a s bound : multi.T} (h : Subterm a s)
    (hs : TreeBelow bound s) : TreeBelow bound a := by
  induction h with
  | coordinate xs b i => exact (TreeBelow_P.1 hs).2.1 i
  | tail xs b => exact (TreeBelow_P.1 hs).2.2
  | trans _ _ ha hb => exact ha (hb hs)

theorem ChildrenBelow.subterm {s bound : multi.T} (hs : ChildrenBelow bound s)
    {a : multi.T} (h : Subterm a s) : TreeBelow bound a := by
  induction h with
  | coordinate xs b i => exact hs.1 i
  | tail xs b => exact hs.2
  | trans _ _ ha hb => exact ha (hb hs).children

theorem treeBelow_of_subterms (bound : multi.T) : ∀ (s : multi.T), s < bound →
    (∀ a, Subterm a s → a < bound) → TreeBelow bound s
  | .Z, hr, _ => TreeBelow_Z.2 hr
  | .P xs b, hr, hs => by
    refine TreeBelow_P.2 ⟨hr, ?_, ?_⟩
    · intro i
      exact treeBelow_of_subterms bound (V.get0 xs i) (hs _ (Subterm.coordinate xs b i))
        (fun a ha => hs a (Subterm.trans ha (Subterm.coordinate xs b i)))
    · exact treeBelow_of_subterms bound b (hs _ (Subterm.tail xs b))
        (fun a ha => hs a (Subterm.trans ha (Subterm.tail xs b)))
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem childrenBelow_iff (bound s : multi.T) :
    ChildrenBelow bound s ↔ ∀ a, Subterm a s → a < bound := by
  constructor
  · intro hs a ha; exact (hs.subterm ha).root_lt
  · intro hs
    cases s with
    | Z => trivial
    | P xs b =>
      refine ⟨?_, ?_⟩
      · intro i
        exact treeBelow_of_subterms bound (V.get0 xs i) (hs _ (Subterm.coordinate xs b i))
          (fun a ha => hs a (Subterm.trans ha (Subterm.coordinate xs b i)))
      · exact treeBelow_of_subterms bound b (hs _ (Subterm.tail xs b))
          (fun a ha => hs a (Subterm.trans ha (Subterm.tail xs b)))

theorem treeBelow_set (xs : V multi.T) (i : Nat) (a bound : multi.T)
    (hx : ∀ j, TreeBelow bound (V.get0 xs j)) (ha : TreeBelow bound a) :
    ∀ j, TreeBelow bound (V.get0 (V.set xs i a) j) := by
  intro j
  by_cases hi : i < xs.length
  · rw [V.get0_set xs i a j hi]
    split
    · exact ha
    · exact hx j
  · rw [set_of_ge xs i a (Nat.le_of_not_lt hi)]
    exact hx j

theorem TreeBelow.zero {bound s : multi.T} (hs : TreeBelow bound s) : TreeBelow bound .Z := by
  apply TreeBelow_Z.2
  cases bound with
  | Z => exact absurd hs.root_lt (T.not_lt_Z _)
  | P => exact T.Z_lt_P _ _

theorem fund_zero_bounds : ∀ (s bound : multi.T),
    (ChildrenBelow bound s → ChildrenBelow bound (T.fund s .Z)) ∧
      (TreeBelow bound s → TreeBelow bound (T.fund s .Z))
  | s, bound => by
    have hchildren : ChildrenBelow bound s → ChildrenBelow bound (T.fund s .Z) := by
      cases s with
      | Z => rw [fund_Z]; exact id
      | P xs b =>
        intro hs
        have hf : ∀ i, TreeBelow bound (T.fund (V.get0 xs i) .Z) :=
          fun i => (fund_zero_bounds (V.get0 xs i) bound).2 (hs.1 i)
        by_cases hb : b = .Z
        · subst hb
          rcases hfz : V.fnz xs with _ | i
          · rw [fund_none hfz]; trivial
          · cases hd : domF (V.get0 xs i) with
            | zero =>
              rw [fund_zero hfz hd]
              exact ⟨treeBelow_set xs i _ bound hs.1 (hf i), hs.2⟩
            | omega =>
              rw [fund_omega hfz hd]
              exact ⟨treeBelow_set xs i _ bound hs.1 (hf i), hs.2⟩
            | Omega v =>
              by_cases hv : xs < v
              · rw [fund_diag hfz hd hv]
                exact ⟨treeBelow_set xs i _ bound hs.1 (hf i), hs.2⟩
              · rw [fund_nondiag hfz hd hv]
                exact ⟨treeBelow_set xs i _ bound hs.1 (hf i), hs.2⟩
            | one =>
              cases i with
              | zero => rw [fund_one_zero hfz hd]; trivial
              | succ m =>
                rw [fund_one_succ hfz hd]
                exact ⟨treeBelow_set _ m .Z bound
                  (treeBelow_set xs (m + 1) _ bound hs.1 (hf (m + 1))) hs.2, hs.2⟩
        · rw [fund_tail xs hb]
          exact ⟨hs.1, (fund_zero_bounds b bound).2 hs.2⟩
    refine ⟨hchildren, ?_⟩
    intro hs
    apply (treeBelow_iff _ _).mpr
    refine ⟨?_, hchildren hs.children⟩
    cases s with
    | Z => rw [fund_Z]; exact hs.root_lt
    | P xs b => exact T.lt_trans (fund_lt (.P xs b) .Z (by intro he; cases he)) hs.root_lt
termination_by s _ => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem TreeBelow.fund_zero {s bound : multi.T} (hs : TreeBelow bound s) :
    TreeBelow bound (T.fund s .Z) := (fund_zero_bounds s bound).2 hs

theorem ChildrenBelow.fund_zero {s bound : multi.T} (hs : ChildrenBelow bound s) :
    ChildrenBelow bound (T.fund s .Z) := (fund_zero_bounds s bound).1 hs

theorem treeBelow_iter (F : multi.T → multi.T) (bound : multi.T)
    (hz : TreeBelow bound .Z)
    (hf : ∀ a, TreeBelow bound a → TreeBelow bound (F a)) :
    ∀ t : multi.T, TreeBelow bound (multi.T.iter F t)
  | .Z => hz
  | .P _ b => hf _ (treeBelow_iter F bound hz hf b)

theorem treeBelow_mul_principal (xs : V multi.T) (bound : multi.T)
    (hx : ∀ i, TreeBelow bound (V.get0 xs i)) (hz : TreeBelow bound .Z)
    (hr : ∀ a, a ≠ .Z → multi.T.mul (.P xs .Z) a < bound) :
    ∀ t : multi.T, TreeBelow bound (multi.T.mul (.P xs .Z) t)
  | .Z => hz
  | .P ys b => by
    show TreeBelow bound (.P xs (multi.T.mul (.P xs .Z) b))
    exact TreeBelow_P.2 ⟨hr (.P ys b) (by intro he; cases he), hx,
      treeBelow_mul_principal xs bound hx hz hr b⟩

theorem fund_bounds : ∀ (s bound : multi.T),
    (∀ t, ChildrenBelow bound s → s ≤ bound → TreeBelow bound t →
      ChildrenBelow bound (T.fund s t)) ∧
    (∀ t, TreeBelow bound s → TreeBelow bound t → TreeBelow bound (T.fund s t))
  | s, bound => by
    have hchildren : ∀ t, ChildrenBelow bound s → s ≤ bound → TreeBelow bound t →
        ChildrenBelow bound (T.fund s t) := by
      cases s with
      | Z => intro t _ _ _; rw [fund_Z]; trivial
      | P xs b =>
        intro t hs hl ht
        have lift : ∀ a, a < .P xs b → a < bound := fun a ha => T.lt_of_lt_of_le ha hl
        have hf : ∀ i a, TreeBelow bound a → TreeBelow bound (T.fund (V.get0 xs i) a) :=
          fun i a ha => (fund_bounds (V.get0 xs i) bound).2 a (hs.1 i) ha
        by_cases hb : b = .Z
        · subst hb
          rcases hfz : V.fnz xs with _ | i
          · rw [fund_none hfz]; trivial
          · cases hd : domF (V.get0 xs i) with
            | zero =>
              rw [fund_zero hfz hd]
              exact ⟨treeBelow_set xs i _ bound hs.1 (hf i t ht), hs.2⟩
            | omega =>
              rw [fund_omega hfz hd]
              exact ⟨treeBelow_set xs i _ bound hs.1 (hf i t ht), hs.2⟩
            | Omega v =>
              by_cases hv : xs < v
              · rw [fund_diag hfz hd hv]
                exact ⟨treeBelow_set xs i _ bound hs.1
                  (hf i _ (treeBelow_iter (T.fund (V.get0 xs i)) bound ht.zero (hf i) t)), hs.2⟩
              · rw [fund_nondiag hfz hd hv]
                exact ⟨treeBelow_set xs i _ bound hs.1 (hf i t ht), hs.2⟩
            | one =>
              cases i with
              | zero =>
                have hx := treeBelow_set xs 0 _ bound hs.1 (hf 0 .Z ht.zero)
                apply TreeBelow.children
                rw [fund_one_zero hfz hd]
                apply treeBelow_mul_principal _ bound hx ht.zero
                intro a ha
                apply lift
                have hh := fund_lt (.P xs .Z) a (by intro he; cases he)
                rwa [fund_one_zero hfz hd] at hh
              | succ m =>
                rw [fund_one_succ hfz hd]
                exact ⟨treeBelow_set _ m t bound
                  (treeBelow_set xs (m + 1) _ bound hs.1 (hf (m + 1) .Z ht.zero)) ht, hs.2⟩
        · rw [fund_tail xs hb]
          exact ⟨hs.1, (fund_bounds b bound).2 t hs.2 ht⟩
    refine ⟨hchildren, ?_⟩
    intro t hs ht
    apply (treeBelow_iff _ _).mpr
    refine ⟨?_, hchildren t hs.children (Or.inl hs.root_lt) ht⟩
    cases s with
    | Z => rw [fund_Z]; exact hs.root_lt
    | P xs b => exact T.lt_trans (fund_lt (.P xs b) t (by intro he; cases he)) hs.root_lt
termination_by s _ => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem TreeBelow.fund {s t bound : multi.T} (hs : TreeBelow bound s)
    (ht : TreeBelow bound t) : TreeBelow bound (T.fund s t) := (fund_bounds s bound).2 t hs ht

theorem no_diagonal_of_subterms (xs : V multi.T) (i : Nat)
    (hr : Recursive (V.get0 xs i)) {v : V multi.T} (hd : domF (V.get0 xs i) = .Omega v)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z) : ¬ xs < v := by
  intro hv
  have h1 := diagonal_principal_lt_argument xs (V.get0 xs i) hr hd hv
  have h2 := hs _ (Subterm.coordinate xs .Z i)
  exact T.lt_irrefl _ (T.lt_trans h1 h2)

theorem omega_selector_of_subterms (xs : V multi.T)
    (hr : Recursive (.P xs .Z))
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z)
    (hd : domF (.P xs .Z) = .omega) :
    (V.fnz xs = some 0 ∧ domF (V.get0 xs 0) = .one) ∨
      ∃ i, V.fnz xs = some i ∧ domF (V.get0 xs i) = .omega := by
  have hr' := Recursive_P.1 hr
  rcases hf : V.fnz xs with _ | i
  · rw [domF_none hf] at hd; cases hd
  · cases hc : domF (V.get0 xs i) with
    | zero => exact absurd ((domF_eq_zero_iff _).1 hc) (V.fnz_some_spec xs i hf).1
    | one =>
      cases i with
      | zero => exact Or.inl ⟨rfl, hc⟩
      | succ m => rw [domF_one_succ hf hc] at hd; cases hd
    | omega => exact Or.inr ⟨i, rfl, hc⟩
    | Omega v =>
      have hn := no_diagonal_of_subterms xs i (hr'.1 i) hc hs
      rw [domF_nondiag hf hc hn] at hd; cases hd

theorem fund_zero_subterms (s : multi.T)
    (hs : ∀ a, Subterm a s → a < s) :
    ∀ a, Subterm a (T.fund s .Z) → a < T.fund s .Z := by
  have hc := (childrenBelow_iff s s).mpr hs
  have hc' := hc.fund_zero
  intro a ha
  have hlt := (hc'.subterm ha).root_lt
  have hm := kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha
  have hf := kumakuma.SourceFundGap.mass_fund_zero_le s
  have hg : kumakuma.SourceFundGap.mass a < kumakuma.SourceFundGap.gap s .Z := by
    rw [kumakuma.SourceFundGap.gap, ite_eq_left rfl]
    omega
  exact kumakuma.SourceFundGap.small_lt_fund_all s .Z a hlt hg

theorem treeBelow_fund_of_small (s t : multi.T) : ∀ (c : multi.T), TreeBelow s c →
    kumakuma.SourceFundGap.mass c < kumakuma.SourceFundGap.gap s t →
    TreeBelow (T.fund s t) c
  | .Z, hc, hm => TreeBelow_Z.2 (kumakuma.SourceFundGap.small_lt_fund_all s t .Z hc.root_lt hm)
  | .P xs b, hc, hm => by
    have hc' := TreeBelow_P.1 hc
    refine TreeBelow_P.2 ⟨kumakuma.SourceFundGap.small_lt_fund_all s t _ hc'.1 hm, ?_, ?_⟩
    · intro i
      exact treeBelow_fund_of_small s t (V.get0 xs i) (hc'.2.1 i)
        (Nat.lt_trans (kumakuma.SourceFundGap.mass_idx_lt xs b i) hm)
    · exact treeBelow_fund_of_small s t b hc'.2.2
        (Nat.lt_trans (kumakuma.SourceFundGap.mass_tail_lt xs b) hm)
termination_by c => c.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem regular_fund_subterms (xs : V multi.T) (m : Nat)
    (hv : V.fnz xs = some (m + 1)) (hd : domF (V.get0 xs (m + 1)) = .one) (t : multi.T)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z)
    (ht : ∀ a, Subterm a t → a < t)
    (hinc : t < T.fund (.P xs .Z) t) :
    ∀ a, Subterm a (T.fund (.P xs .Z) t) → a < T.fund (.P xs .Z) t := by
  by_cases ht0 : t = .Z
  · subst t; exact fund_zero_subterms (.P xs .Z) hs
  · have hml := fnz_lt_length hv
    have hc := (childrenBelow_iff (.P xs .Z) (.P xs .Z)).mpr hs
    have hm := kumakuma.SourceFundGap.mass_fund_one (V.get0 xs (m + 1)) .Z hd
    have hmi := kumakuma.SourceFundGap.vectorMass_get0_le xs (m + 1)
    have hgap : kumakuma.SourceFundGap.gap (.P xs .Z) t = kumakuma.SourceFundGap.vectorMass xs := by
      rw [kumakuma.SourceFundGap.gap, ite_eq_right ht0, kumakuma.SourceFundGap.mass_P,
        kumakuma.SourceFundGap.mass_Z]
      omega
    have hp : TreeBelow (T.fund (.P xs .Z) t) (T.fund (V.get0 xs (m + 1)) .Z) := by
      apply treeBelow_fund_of_small (.P xs .Z) t _ (hc.1 (m + 1)).fund_zero
      rw [hgap]
      omega
    have harg : TreeBelow (T.fund (.P xs .Z) t) t :=
      treeBelow_of_subterms _ t hinc (fun a ha => T.lt_trans (ht a ha) hinc)
    have hcoords : ∀ i, i ≠ m + 1 → TreeBelow (T.fund (.P xs .Z) t) (V.get0 xs i) := by
      intro i hi
      apply treeBelow_fund_of_small (.P xs .Z) t _ (hc.1 i)
      rw [hgap]
      have hpair := kumakuma.SourceFundGap.vectorMass_pair_le xs i (m + 1) hi
      omega
    apply (childrenBelow_iff _ _).mp
    rw [fund_one_succ hv hd] at hp harg hcoords ⊢
    refine ⟨?_, harg.zero⟩
    intro i
    rw [V.get0_set _ m t i (by rw [V.length_set]; omega)]
    by_cases hi : i = m
    · rw [ite_eq_left hi]; exact harg
    · rw [ite_eq_right hi, V.get0_set xs (m + 1) _ i hml]
      by_cases hij : i = m + 1
      · rw [ite_eq_left hij]; exact hp
      · rw [ite_eq_right hij]
        exact hcoords i hij

end kumakuma.SourceSubtermBounds

import Subsp.Support.Order

/-! `RecursiveWF`, the wf invariant of images, and source subterm/fund gap bounds. -/

namespace Support.GeneralImageWFInvariant

open new OCF.Jaeger Support.OTQuotient Support.CountableSource Support.DimensionCut
open Support.GeneralImageEmbedding Support.GeneralImageRawOrder

universe u

theorem recursive_zero (d lam : Nat) : RecursiveWF d (.Z : new.T lam) := by
  rw [RecursiveWF]; trivial

theorem fixed_LF_wf (k n : Nat) :
    Term.wf (DimensionImage.convert (k + 3) (code (new.T.LF (k + 3) n))) = true := by
  cases n with
  | zero => simp [new.T.LF, code, DimensionImage.convert, Term.wf]
  | succ n =>
    cases n with
    | zero =>
      rw [LF_one, Support.FiniteCorrespondence.code_ofNat]
      change Term.wf (DimensionImage.convert (k + 3) Support.UserImage.oneCode) = true
      rw [DimensionImage.convert_one]
      exact Term.wf_one
    | succ n => rw [fixed_LF_value]; exact tower_wf k (n + 1)

theorem LF_recursiveWF (k n : Nat) : RecursiveWF (k + 3) (new.T.LF (k + 3) n) := by
  induction n with
  | zero => rw [new.T.LF]; exact recursive_zero _ _
  | succ n ih =>
    rw [LF_step (k + 2) n, RecursiveWF]
    refine ⟨?_, recursive_zero _ _, ?_⟩
    · intro i
      rw [lastVec_idx]
      split
      · exact ih
      · exact recursive_zero _ _
    · simpa only [LF_step (k + 2) n] using fixed_LF_wf k (n + 1)

theorem fixed_basis_wf (k n : Nat) :
    Term.wf (DimensionImage.convert (k + 3) (code (basis k n).2.val)) = true := by
  cases n with
  | zero =>
    have hc : code (basis k 0).2.val = Support.UserImage.oneCode := by
      simp [basis, lowerBase, new.T.LF, code, trim_codes_lowVec, trim,
        Code.isZero, Support.UserImage.oneCode]
    rw [hc, DimensionImage.convert_one]
    exact Term.wf_one
  | succ n =>
    cases n with
    | zero =>
      have hc : code (basis k 1).2.val = .p [Support.UserImage.oneCode] .zero := by
        change code (.P (lowVec (k + 2) (new.T.LF ((k + 2) + 1) 1)) .Z) = _
        rw [LF_one]
        simp [code, trim_codes_lowVec, Support.FiniteCorrespondence.code_ofNat,
          Support.FiniteCorrespondence.natCode, trim, Code.isZero, Support.UserImage.oneCode]
      rw [hc]
      simp only [DimensionImage.convert, DimensionImage.arguments,
        DimensionImage.principal_singleton, DimensionImage.convert_one, OT2.assemble, ↓reduceIte]
      decide +kernel
    | succ n =>
      have hc : code (basis k (n + 2)).2.val = .p [code (new.T.LF (k + 3) (n + 2))] .zero := by
        simp only [basis, lowerBase, code, trim_codes_lowVec]
        cases he : code (new.T.LF (k + 3) (n + 2)) with
        | zero => exact False.elim (LF_positive (k + 2) (n + 1) (code_injective he))
        | p xs b => rfl
      rw [hc]
      simp only [DimensionImage.convert, DimensionImage.arguments,
        DimensionImage.principal_singleton, fixed_LF_value, OT2.assemble, ↓reduceIte]
      exact psi_tower_wf k (n + 1)

theorem basis_recursiveWF (k n : Nat) : RecursiveWF (k + 3) (basis k n).2.val := by
  change RecursiveWF (k + 3) (.P (lowVec (k + 2) (new.T.LF (k + 3) n)) .Z)
  rw [RecursiveWF]
  refine ⟨?_, recursive_zero _ _, fixed_basis_wf k n⟩
  intro i
  rw [lowVec, Vec.ofFn_idx]
  split
  · exact LF_recursiveWF k n
  · exact recursive_zero _ _

theorem assemble_succ (p t : Term) (hp : Term.isPrin p = true) :
    OT2.assemble p (Support.BinaryTranslation.succTerm t) =
      Support.BinaryTranslation.succTerm (OT2.assemble p t) := by
  unfold OT2.assemble
  rw [ite_eq_right (Support.TargetArithmetic.succTerm_ne_zero t)]
  by_cases ht : t = .zero
  · subst t
    simp only [↓reduceIte, Support.BinaryTranslation.succTerm]
    cases p with
    | zero | add => cases hp
    | inacc | psi => rfl
  · rw [ite_eq_right ht]
    rfl

theorem convert_succ (d : Nat) {lam : Nat} (s : new.T lam) :
    DimensionImage.convert d (code (Support.SourceSuccessor.succ s)) =
      Support.BinaryTranslation.succTerm (DimensionImage.convert d (code s)) := by
  cases s with
  | Z =>
    change DimensionImage.convert d (code (new.T.ofNat (lam := lam) 1)) = _
    rw [Support.FiniteCorrespondence.code_ofNat]
    simp only [code, DimensionImage.convert, Support.BinaryTranslation.succTerm]
    change DimensionImage.convert d Support.UserImage.oneCode = Term.one
    exact DimensionImage.convert_one d
  | P xs b =>
    change DimensionImage.convert d (code (.P xs (Support.SourceSuccessor.succ b))) = _
    simp only [code, DimensionImage.convert, convert_succ d b]
    exact assemble_succ _ _ (principal_isPrin _ _)
termination_by new.T.size s
decreasing_by exact new.T.add_size_lt_P _ _

theorem recursive_head {d lam : Nat} (s : new.T lam) (hs : RecursiveWF d s) :
    RecursiveWF d (new.T.head s) := by
  cases s with
  | Z => exact hs
  | P xs b =>
    rw [RecursiveWF] at hs
    change RecursiveWF d (.P xs .Z)
    rw [RecursiveWF]
    refine ⟨hs.1, recursive_zero _ _, ?_⟩
    simp only [code, DimensionImage.convert, OT2.assemble, ↓reduceIte]
    exact assemble_wf_left (by simpa only [code, DimensionImage.convert] using hs.2.2)

theorem assemble_wf_of_succ {p t : Term} (hp : Term.isPrin p = true)
    (ht : Term.wf t = true)
    (h : Term.wf (OT2.assemble p (Support.BinaryTranslation.succTerm t)) = true) :
    Term.wf (OT2.assemble p t) = true := by
  have hwp := assemble_wf_left h
  by_cases hz : t = .zero
  · subst t
    simpa only [OT2.assemble, ↓reduceIte] using hwp
  · unfold OT2.assemble at h ⊢
    rw [ite_eq_right (Support.TargetArithmetic.succTerm_ne_zero t)] at h
    rw [ite_eq_right hz]
    have hh := ((Term.wf_add_iff _ _).mp h).2.2.2.2
    rw [Support.TargetArithmetic.head_succTerm hz] at hh
    exact (Term.wf_add_iff _ _).mpr ⟨hp, hwp, ht, hz, hh⟩

theorem recursive_succ_iff (d : Nat) {lam : Nat} (s : new.T lam) :
    RecursiveWF d (Support.SourceSuccessor.succ s) ↔ RecursiveWF d s := by
  cases s with
  | Z =>
    constructor
    · intro _; exact recursive_zero _ _
    · intro _
      change RecursiveWF d (.P (zeros lam) .Z)
      rw [RecursiveWF]
      refine ⟨?_, recursive_zero _ _, ?_⟩
      · intro i
        rw [zeros, Vec.ofFn_idx]
        exact recursive_zero _ _
      · change Term.wf (DimensionImage.convert d (code (new.T.ofNat (lam := lam) 1))) = true
        rw [Support.FiniteCorrespondence.code_ofNat]
        change Term.wf (DimensionImage.convert d Support.UserImage.oneCode) = true
        rw [DimensionImage.convert_one]
        exact Term.wf_one
  | P xs b =>
    change RecursiveWF d (.P xs (Support.SourceSuccessor.succ b)) ↔ RecursiveWF d (.P xs b)
    constructor
    · intro hs
      have hw := hs.wf
      rw [RecursiveWF] at hs
      rw [RecursiveWF]
      have hb := ((recursive_succ_iff d b).mp hs.2.1).wf
      refine ⟨hs.1, (recursive_succ_iff d b).mp hs.2.1, ?_⟩
      simp only [code, DimensionImage.convert, convert_succ] at hw ⊢
      exact assemble_wf_of_succ (principal_isPrin _ _) hb hw
    · intro hs
      have hw := hs.wf
      rw [RecursiveWF] at hs
      rw [RecursiveWF]
      refine ⟨hs.1, (recursive_succ_iff d b).mpr hs.2.1, ?_⟩
      rw [show (.P xs (Support.SourceSuccessor.succ b)) = Support.SourceSuccessor.succ (.P xs b) from rfl,
        convert_succ]
      exact Support.TargetArithmetic.succTerm_wf hw
termination_by new.T.size s
decreasing_by all_goals exact new.T.add_size_lt_P _ _

theorem dom_one_succ {lam : Nat} (s : new.T lam) (hd : new.T.dom s = .one) :
    ∃ a, s = Support.SourceSuccessor.succ a := by
  cases he : s with
  | Z => rw [he, new.T.dom] at hd; cases hd
  | P xs b =>
    rw [he] at hd
    by_cases hb : b = .Z
    · subst b
      rw [dom_one_principal xs hd]
      exact ⟨.Z, rfl⟩
    · rw [new.T.dom, ite_eq_right hb] at hd
      obtain ⟨a, ha⟩ := dom_one_succ b hd
      exact ⟨.P xs a, by rw [ha]; rfl⟩
termination_by new.T.size s
decreasing_by simp only [he]; exact new.T.add_size_lt_P _ _

theorem fund_one_recursiveWF {d lam : Nat} (s t : new.T lam)
    (hs : RecursiveWF d s) (hd : new.T.dom s = .one) : RecursiveWF d (new.T.fund s t) := by
  obtain ⟨a, ha⟩ := dom_one_succ s hd
  rw [ha, Support.SourceSuccessor.fund_succ]
  rw [ha] at hs
  exact (recursive_succ_iff d a).mp hs

theorem assemble_head (p t : Term) (hp : Term.isPrin p = true) :
    Term.head (OT2.assemble p t) = p := by
  unfold OT2.assemble
  split
  · cases p with
    | zero | add => cases hp
    | inacc | psi => rfl
  · rfl

theorem convert_head (d : Nat) {lam : Nat} (s : new.T lam) :
    Term.head (DimensionImage.convert d (code s)) = DimensionImage.convert d (code (new.T.head s)) := by
  cases s with
  | Z => simp only [code, DimensionImage.convert, Term.head, new.T.head]
  | P xs b =>
    simp only [code, DimensionImage.convert, new.T.head, OT2.assemble, ↓reduceIte]
    split
    · have hp := principal_isPrin d (DimensionImage.arguments d (trim (codes xs)))
      cases he : DimensionImage.principal d (DimensionImage.arguments d (trim (codes xs))) with
      | zero | add => rw [he] at hp; cases hp
      | inacc | psi => rfl
    · rfl

theorem image_le_of_le [LargeCardinals.{u}] (k : Nat) (s t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t) (h : new.T.le s t) :
    Term.le (DimensionImage.convert (k + 3) (code s))
      (DimensionImage.convert (k + 3) (code t)) = true := by
  apply (Term.le_iff_eq_or_lt _ _).mpr
  rcases h with h | h
  · exact Or.inr ((convert_order k s t hs ht).mp h)
  · exact Or.inl (congrArg (fun a => DimensionImage.convert (k + 3) (code a))
      (new.T_eq_sound _ _ h))

theorem target_le_trans [LargeCardinals.{u}] {a b c : Term}
    (ha : Term.wf a = true) (hb : Term.wf b = true) (hc : Term.wf c = true)
    (hab : Term.le a b = true) (hbc : Term.le b c = true) : Term.le a c = true := by
  apply (Term.le_iff_eq_or_lt _ _).mpr
  rcases (Term.le_iff_eq_or_lt _ _).mp hab with rfl | hab
  · exact (Term.le_iff_eq_or_lt _ _).mp hbc
  · rcases (Term.le_iff_eq_or_lt _ _).mp hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (lemma_6_1.{u}.2.1 _ _ _ ha hb hc hab hbc)

theorem replace_tail_recursiveWF [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (b c : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs b)) (hc : RecursiveWF (k + 3) c)
    (hb : b ≠ .Z) (hcb : new.T.lt c b) : RecursiveWF (k + 3) (.P xs c) := by
  have hs0 := hs
  have hpwf := principal_wf hs
  rw [RecursiveWF] at hs
  rw [RecursiveWF]
  refine ⟨hs.1, hc, ?_⟩
  by_cases hz : c = .Z
  · subst c
    simpa only [code, DimensionImage.convert, OT2.assemble, ↓reduceIte] using hpwf
  · have hbnz : DimensionImage.convert (k + 3) (code b) ≠ .zero := by
      intro h
      exact hb (code_injective ((fixed_convert_zero_iff _ _).mp h))
    have hcnz : DimensionImage.convert (k + 3) (code c) ≠ .zero := by
      intro h
      exact hz (code_injective ((fixed_convert_zero_iff _ _).mp h))
    have hw := hs.2.2
    simp only [code, DimensionImage.convert] at hw
    rw [OT2.assemble, ite_eq_right hbnz] at hw
    have hbound := ((Term.wf_add_iff _ _).mp hw).2.2.2.2
    have hh := image_le_of_le k (new.T.head c) (new.T.head b)
      (recursive_head c hc) (recursive_head b hs.2.1)
      (Support.SourceDescending.head_le_of_lt hcb)
    rw [← convert_head, ← convert_head] at hh
    have hnew := target_le_trans (wf_head hc.wf) (wf_head hs.2.1.wf) hpwf hh hbound
    simp only [code, DimensionImage.convert]
    rw [OT2.assemble, ite_eq_right hcnz]
    exact (Term.wf_add_iff _ _).mpr ⟨principal_isPrin _ _, hpwf, hc.wf, hcnz, hnew⟩

theorem fund_nonzero_tail_recursiveWF [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (b t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs b)) (hb : b ≠ .Z)
    (hc : RecursiveWF (k + 3) (new.T.fund b t)) :
    RecursiveWF (k + 3) (new.T.fund (.P xs b) t) := by
  rw [new.T.fund, ite_eq_right hb]
  exact replace_tail_recursiveWF k xs b _ hs hc hb (Support.SourceFundOrder.fund_lt b t hb)

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
    (h : Term.wf (.psi Term.bigOmega (Support.BinaryTranslation.succTerm a)) = true) :
    Term.wf (.psi Term.bigOmega a) = true := by
  apply (Term.wf_psi_iff _ _).mpr
  refine ⟨by decide +kernel, Term.wf_bigOmega, ha, ?_⟩
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  have hzw := Support.GeneralImageCoefficients.H_coefficient_wf Term.bigOmega a ha hz
  have hzs : z ∈ Term.H Term.bigOmega (Support.BinaryTranslation.succTerm a) := by
    rw [Support.OT2.H_succTerm]
    exact List.mem_append_left _ hz
  have hlt := (Term.allLt_iff _ _).mp ((Term.wf_psi_iff _ _).mp h).2.2.2 z hzs
  rw [Support.TargetArithmetic.lt_succTerm_eq_le hzw ha] at hlt
  rcases (Term.le_iff_eq_or_lt _ _).mp hlt with he | he
  · have hn := H_size_lt Term.bigOmega a hz
    rw [he] at hn
    exact False.elim (Nat.lt_irrefl _ hn)
  · exact he

theorem convert_low_principal (d m : Nat) (a : new.T (m + 1)) :
    DimensionImage.convert d (code (.P (lowVec m a) .Z)) =
      .psi Term.bigOmega (DimensionImage.convert d (code a)) := by
  simp only [code, trim_codes_lowVec]
  cases he : code a with
  | zero =>
    simp only [trim, Code.isZero, ↓reduceIte, DimensionImage.convert,
      DimensionImage.arguments, DimensionImage.principal_nil, OT2.assemble, Term.one]
  | p xs b =>
    simp [trim, Code.isZero, DimensionImage.convert,
      DimensionImage.arguments, DimensionImage.principal_singleton, OT2.assemble]

theorem low_principal_recursiveWF_iff (d m : Nat) (a : new.T (m + 1)) :
    RecursiveWF d (.P (lowVec m a) .Z) ↔
      RecursiveWF d a ∧ Term.allLt
        (Term.H Term.bigOmega (DimensionImage.convert d (code a)))
        (DimensionImage.convert d (code a)) = true := by
  constructor
  · intro hs
    rw [RecursiveWF] at hs
    have ha := hs.1 (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1))
    rw [lowVec_idx, ite_eq_left rfl] at ha
    have hw := hs.2.2
    rw [convert_low_principal] at hw
    exact ⟨ha, ((Term.wf_psi_iff _ _).mp hw).2.2.2⟩
  · rintro ⟨ha, hH⟩
    rw [RecursiveWF]
    refine ⟨?_, recursive_zero _ _, ?_⟩
    · intro i
      rw [lowVec_idx]
      split
      · exact ha
      · exact recursive_zero _ _
    · rw [convert_low_principal]
      exact (Term.wf_psi_iff _ _).mpr ⟨by decide +kernel, Term.wf_bigOmega, ha.wf, hH⟩

theorem low_principal_succ_predecessor (k : Nat) (a : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (.P (lowVec (k + 2) (Support.SourceSuccessor.succ a)) .Z)) :
    RecursiveWF (k + 3) (.P (lowVec (k + 2) a) .Z) := by
  rw [RecursiveWF] at hs
  have ha := hs.1 (⟨0, by omega⟩ : Fin (k + 3))
  rw [lowVec_idx, ite_eq_left rfl] at ha
  have hw := hs.2.2
  rw [convert_low_principal, convert_succ] at hw
  have har := (recursive_succ_iff (k + 3) a).mp ha
  rw [RecursiveWF]
  refine ⟨?_, recursive_zero _ _, ?_⟩
  · intro i
    rw [lowVec_idx]
    split
    · exact har
    · exact recursive_zero _ _
  · rw [convert_low_principal]
    exact psi_omega_wf_of_succ har.wf hw

theorem mul_principal_recursiveWF {d lam : Nat} (xs : Vec (new.T lam) lam)
    (hs : RecursiveWF d (.P xs .Z)) (t : new.T lam) :
    RecursiveWF d (new.T.mul (.P xs .Z) t) := by
  cases t with
  | Z => rw [new.T.mul]; exact recursive_zero _ _
  | P ys b =>
    change RecursiveWF d (.P xs (new.T.mul (.P xs .Z) b))
    have hc := mul_principal_recursiveWF xs hs b
    have hpwf := principal_wf hs
    rw [RecursiveWF] at hs
    rw [RecursiveWF]
    refine ⟨hs.1, hc, ?_⟩
    simp only [code, DimensionImage.convert]
    rw [OT2.assemble]
    split
    · exact hpwf
    · rename_i hn
      apply (Term.wf_add_iff _ _).mpr
      refine ⟨principal_isPrin _ _, hpwf, hc.wf, hn, ?_⟩
      cases b with
      | Z => simp [new.T.mul, code, DimensionImage.convert] at hn
      | P us c =>
        change Term.le (Term.head (DimensionImage.convert d (code (.P xs (new.T.mul (.P xs .Z) c))))) _ = true
        simp only [code, DimensionImage.convert, assemble_head _ _ (principal_isPrin _ _)]
        exact (Term.le_iff_eq_or_lt _ _).mpr (Or.inl rfl)
termination_by new.T.size t
decreasing_by exact new.T.add_size_lt_P _ _

theorem fund_low_successor_recursiveWF (k : Nat)
    (a t : new.T (k + 3)) (hd : new.T.dom a = .one)
    (hs : RecursiveWF (k + 3) (.P (lowVec (k + 2) a) .Z)) :
    RecursiveWF (k + 3) (new.T.fund (.P (lowVec (k + 2) a) .Z) t) := by
  obtain ⟨b, hb⟩ := dom_one_succ a hd
  have hp : RecursiveWF (k + 3) (.P (lowVec (k + 2) b) .Z) := by
    rw [hb] at hs
    exact low_principal_succ_predecessor k b hs
  rw [new.T.fund]
  simp only [↓reduceIte, minIdx_lowVec, hd, reduceCtorEq, GetElem.getElem,
    lowVec_idx, lowVec_rplc_zero]
  rw [hb, Support.SourceSuccessor.fund_succ]
  exact mul_principal_recursiveWF _ hp t

theorem fund_low_zero_recursiveWF (d m : Nat) (t : new.T (m + 1)) :
    RecursiveWF d (new.T.fund (.P (lowVec m .Z) .Z) t) := by
  rw [new.T.fund]
  simp only [↓reduceIte, minIdx_lowVec, new.T.dom]
  exact recursive_zero _ _

theorem fund_low_omega (m : Nat) (a t : new.T (m + 1)) (hd : new.T.dom a = .omega) :
    new.T.fund (.P (lowVec m a) .Z) t = .P (lowVec m (new.T.fund a t)) .Z := by
  rw [new.T.fund]
  simp only [↓reduceIte, minIdx_lowVec, hd, reduceCtorEq, GetElem.getElem,
    lowVec_idx, lowVec_rplc_zero]

theorem fund_low_Omega (m : Nat) (a t : new.T (m + 1))
    (v : Vec (new.T (m + 1)) (m + 1)) (hd : new.T.dom a = .Omega v) :
    new.T.fund (.P (lowVec m a) .Z) t =
      .P (lowVec m (new.T.fund a (new.T.iter (new.T.fund a) t))) .Z := by
  obtain ⟨i, hi, hm⟩ := Support.SourceFundOrder.domOmega_regular a hd
  have hv : Vec.lt (lowVec m a) v := Support.SourceFundOrder.lowVec_below_regular a v i hi hm
  rw [new.T.fund]
  simp only [↓reduceIte, minIdx_lowVec, hd, reduceCtorEq, GetElem.getElem,
    lowVec_idx, hv, lowVec_rplc_zero]

def FundClosure (k : Nat) : Prop :=
  ∀ (s : new.T (k + 3)), new.T.isOT (k + 3) s → RecursiveWF (k + 3) s →
    ∀ n, RecursiveWF (k + 3) (new.T.fund s (new.T.ofNat n))

def PrincipalFundClosure (k : Nat) : Prop :=
  ∀ xs : Vec (new.T (k + 3)) (k + 3), new.T.isOT (k + 3) (.P xs .Z) →
    RecursiveWF (k + 3) (.P xs .Z) →
    ∀ n, RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat n))

theorem fundClosure_iff_principal [LargeCardinals.{u}] (k : Nat) :
    FundClosure k ↔ PrincipalFundClosure k := by
  constructor
  · intro h xs ho hw n
    exact h _ ho hw n
  · intro h
    intro s ho hw n
    induction hs : new.T.size s using Nat.strongRecOn generalizing s with
    | ind size ih =>
      cases he : s with
      | Z => rw [new.T.fund]; exact recursive_zero _ _
      | P xs b =>
        rw [he] at ho hw
        by_cases hb : b = .Z
        · subst b
          exact h xs ho hw n
        · have hbo : new.T.isOT (k + 3) b := by
            simpa only [Support.SourceSummands.tail] using Support.SourceSummands.tail_isOT ho
          have hw0 := hw
          rw [RecursiveWF] at hw
          have hc := ih (new.T.size b) (by rw [← hs, he]; exact new.T.add_size_lt_P _ _)
            b hbo hw.2.1 rfl
          exact fund_nonzero_tail_recursiveWF k xs b _ hw0 hb hc

def LimitLowFundClosure (k : Nat) : Prop :=
  ∀ a : new.T (k + 3), new.T.isOT (k + 3) (.P (lowVec (k + 2) a) .Z) →
    RecursiveWF (k + 3) (.P (lowVec (k + 2) a) .Z) →
    (new.T.dom a = .omega ∨ ∃ v, new.T.dom a = .Omega v) →
    ∀ n, RecursiveWF (k + 3) (new.T.fund (.P (lowVec (k + 2) a) .Z) (new.T.ofNat n))

theorem principalFundClosure_iff_limit_low [LargeCardinals.{u}] (k : Nat) :
    PrincipalFundClosure k ↔ LimitLowFundClosure k := by
  constructor
  · intro h a ho hw _ n
    exact h _ ho hw n
  · intro h xs ho hw n
    have houter := Support.CountableSource.isOT_outer ho
    cases houter with
    | cons a _ _ =>
      cases hd : new.T.dom a with
      | zero =>
        have ha := (dom_eq_zero_iff a).mp hd
        rw [ha]
        exact fund_low_zero_recursiveWF _ _ _
      | one => exact fund_low_successor_recursiveWF k a _ hd hw
      | omega => exact h a ho hw (Or.inl hd) n
      | Omega v => exact h a ho hw (Or.inr ⟨v, hd⟩) n

theorem fundClosure_iff_limit_low [LargeCardinals.{u}] (k : Nat) :
    FundClosure k ↔ LimitLowFundClosure k :=
  (fundClosure_iff_principal k).trans (principalFundClosure_iff_limit_low k)

private theorem generated_recursiveWF_cast (k : Nat) (hc : FundClosure k)
    {lam : Nat} {s : new.T lam} (hs : new.T.isOT lam s) :
    ∀ e : lam = k + 3, RecursiveWF (k + 3) (e ▸ s) := by
  induction hs with
  | base_0 n => intro e; omega
  | base_succ lam n =>
    intro e
    have hl : lam = k + 2 := by omega
    subst lam
    cases e
    simpa only [basis, lowerBase, lowVec] using basis_recursiveWF k n
  | step lam s hs n ih =>
    intro e
    subst lam
    exact hc s hs (ih rfl) n

theorem original_recursiveWF_of_closure (k : Nat) (hc : FundClosure k)
    (s : new.T (k + 3)) (hs : new.T.isOT (k + 3) s) : RecursiveWF (k + 3) s :=
  generated_recursiveWF_cast k hc hs rfl

theorem original_wf_of_closure (k : Nat) (hc : FundClosure k)
    (s : new.T (k + 3)) (hs : new.T.isOT (k + 3) s) :
    Term.wf (DimensionImage.convert (k + 3) (code s)) = true :=
  (original_recursiveWF_of_closure k hc s hs).wf

theorem original_order_of_closure [LargeCardinals.{u}] (k : Nat) (hc : FundClosure k)
    (s t : new.T (k + 3)) (hs : new.T.isOT (k + 3) s) (ht : new.T.isOT (k + 3) t) :
    new.T.lt s t ↔ Term.lt (DimensionImage.convert (k + 3) (code s))
      (DimensionImage.convert (k + 3) (code t)) = true :=
  convert_order k s t (original_recursiveWF_of_closure k hc s hs)
    (original_recursiveWF_of_closure k hc t ht)

end Support.GeneralImageWFInvariant

namespace Support.GeneralImageIndexSupport

open new OCF.Jaeger Support.OTQuotient Support.CodeReification
open Support.BinaryTranslation Support.TargetIndexCuts Support.DimensionImage
open Support.GeneralImageTopPair Support.GeneralImageLayerOrder
open Support.GeneralImagePrincipalOrder Support.GeneralImageRawOrder

universe u

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

theorem argsWidth_coordinates {lam m : Nat} (xs : Vec (new.T lam) m) (n : Nat)
    (h : ∀ i, width (code (xs.idx i)) ≤ n) : argsWidth (codes xs) ≤ n := by
  apply (argsWidth_le _ _).mpr
  intro a ha
  induction xs with
  | nil => cases ha
  | snoc m xs x ih =>
    rw [codes] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ih (fun i => by simpa only [vec_snoc_idx_cast] using h i.castSucc) ha
    · have he := List.mem_singleton.mp ha
      subst a
      simpa only [vec_snoc_idx_last] using h (Fin.last m)

theorem width_of_indices (k : Nat) (s : new.T (k + 3))
    (h : IndicesBelow (k + 1) (convert (k + 3) (code s))) : width (code s) ≤ k + 2 := by
  cases hs : s with
  | Z => simp only [code, width]; omega
  | P xs b =>
    rw [hs] at h
    simp only [code, convert] at h
    obtain ⟨hp, hb⟩ := assemble_indices _ _ h
    obtain ⟨hc, hz⟩ := principal_indices (by omega : 0 < k + 1) k _ hp
    have hi : ∀ i : Fin (k + 3),
        IndicesBelow (k + 1) (convert (k + 3) (code (xs.idx i))) := by
      intro i
      simpa only [converted_coordinate] using hc i.val i.isLt
    have hlast : xs.idx (Fin.last (k + 2)) = .Z := by
      have he := hz (Nat.le_refl _)
      have he' : convert (k + 3) (code (xs.idx (Fin.last (k + 2)))) = .zero := by
        have hcoord := converted_coordinate (d := k + 3) xs (Fin.last (k + 2))
        simp only [Fin.val_last] at hcoord
        exact hcoord.symm.trans he
      have hec := (Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he'
      exact code_injective hec
    have hlen : (trim (codes xs)).length ≤ k + 2 := by
      cases xs with
      | snoc _ xs x =>
        simp only [vec_snoc_idx_last] at hlast
        subst x
        rw [codes, code, Support.FiniteCorrespondence.trim_append_zero]
        exact Nat.le_trans (trim_length_le _) (by rw [codes_length]; exact Nat.le_refl _)
    have hargs := argsWidth_coordinates xs (k + 2)
      (fun i => width_of_indices k _ (hi i))
    rw [code, width]
    exact Nat.max_le.mpr ⟨hlen, Nat.max_le.mpr
      ⟨Nat.le_trans (argsWidth_trim_le _) hargs, width_of_indices k b hb⟩⟩
termination_by new.T.size s
decreasing_by
  all_goals simp only [hs]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem class_not_lower_indices (k : Nat) (q : Classes)
    (hd : Support.GeneralImageEmbedding.ambient (representative q) = k + 4) :
    ¬ IndicesBelow (k + 2) (Support.GeneralImageEmbedding.classConversion q) := by
  intro h
  let s := Support.GeneralImageEmbedding.fixedWitness (k + 4) q
    (by rw [← hd]; exact Nat.le_max_right 3 _)
  have he : code s.val = representative q := Support.GeneralImageEmbedding.fixedWitness_code _ _ _
  rw [Support.GeneralImageEmbedding.class_fixed_value (k + 4) q hd] at h
  have hw := width_of_indices (k + 1) s.val h
  rw [he] at hw
  unfold Support.GeneralImageEmbedding.ambient at hd
  omega

theorem source_lt_of_ambient_lt (q r : Classes)
    (hd : Support.GeneralImageEmbedding.ambient (representative q) <
      Support.GeneralImageEmbedding.ambient (representative r)) : ClassLT q r := by
  let k := Support.GeneralImageEmbedding.ambient (representative r) - 2
  have hr3 := Nat.le_max_left 3 (width (representative r))
  have hq3 := Nat.le_max_left 3 (width (representative q))
  have hrw : width (representative r) = k + 2 := by
    unfold Support.GeneralImageEmbedding.ambient at hd
    dsimp [k]
    unfold Support.GeneralImageEmbedding.ambient
    omega
  have hqw : width (representative q) ≤ k + 1 := by
    have h := Nat.le_max_right 3 (width (representative q))
    change width (representative q) ≤ Support.GeneralImageEmbedding.ambient (representative q) at h
    dsimp [k]
    unfold Support.GeneralImageEmbedding.ambient at hd
    omega
  have hq : HasDimensionWitness (k + 1) q := by
    apply (hasDimensionWitness_iff _ _).mpr
    rw [minDimension_eq_width]
    exact hqw
  have hqb := Support.DimensionCut.dimension_witness_below_boundary hq
  rcases classLT_total (Support.DimensionCut.boundaryClass k) r with hl | hl | he
  · exact classLT_trans hqb hl
  · have hr := (Support.DimensionCut.dimension_witness_iff_below_boundary k r).mpr hl
    have hw := (hasDimensionWitness_iff r (k + 1)).mp hr
    rw [minDimension_eq_width, hrw] at hw
    omega
  · simpa only [he] using hqb

theorem target_lt_of_ambient_lt [LargeCardinals.{u}] (q r : Classes)
    (hd : Support.GeneralImageEmbedding.ambient (representative q) <
      Support.GeneralImageEmbedding.ambient (representative r))
    (hq : Term.wf (Support.GeneralImageEmbedding.classConversion q) = true)
    (hr : Term.wf (Support.GeneralImageEmbedding.classConversion r) = true) :
    Term.lt (Support.GeneralImageEmbedding.classConversion q)
      (Support.GeneralImageEmbedding.classConversion r) = true := by
  have hq3 := Nat.le_max_left 3 (width (representative q))
  change 3 ≤ Support.GeneralImageEmbedding.ambient (representative q) at hq3
  have hr4 : 4 ≤ Support.GeneralImageEmbedding.ambient (representative r) := by omega
  let k := Support.GeneralImageEmbedding.ambient (representative r) - 4
  have hdim : Support.GeneralImageEmbedding.ambient (representative r) = k + 4 := by dsimp [k]; omega
  have hnot := class_not_lower_indices k r hdim
  have hidx : IndicesBelow (k + 2) (Support.GeneralImageEmbedding.classConversion q) := by
    apply (Support.GeneralImageEmbedding.indices_convert (representative q)).mono
    omega
  rcases lemma_6_1.{u}.2.2 _ _ hq hr with hl | he | hl
  · exact hl
  · exact False.elim (hnot (he ▸ hidx))
  · exact False.elim (hnot (indicesBelow_initial (by omega : 0 < k + 2)
      ⟨_, hr, Support.GeneralImageEmbedding.class_below r⟩
      ⟨_, hq, Support.GeneralImageEmbedding.class_below q⟩ hl hidx))

theorem different_ambient_order [LargeCardinals.{u}] (q r : Classes)
    (hd : Support.GeneralImageEmbedding.ambient (representative q) <
      Support.GeneralImageEmbedding.ambient (representative r))
    (hq : Term.wf (Support.GeneralImageEmbedding.classConversion q) = true)
    (hr : Term.wf (Support.GeneralImageEmbedding.classConversion r) = true) :
    ClassLT q r ↔ Term.lt (Support.GeneralImageEmbedding.classConversion q)
      (Support.GeneralImageEmbedding.classConversion r) = true :=
  ⟨fun _ => target_lt_of_ambient_lt q r hd hq hr, fun _ => source_lt_of_ambient_lt q r hd⟩

theorem global_certificate_of_fundClosure [LargeCardinals.{u}]
    (hc : ∀ k, Support.GeneralImageWFInvariant.FundClosure k) :
    Support.GeneralImageEmbedding.GlobalCertificate := by
  have hw : ∀ q : Classes,
      Term.wf (Support.GeneralImageEmbedding.classConversion q) = true := by
    apply Support.GeneralImageEmbedding.global_wf_of_fixed
    intro d hd s
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
    have he : d = k + 3 := by omega
    clear hk
    subst d
    exact Support.GeneralImageWFInvariant.original_wf_of_closure k (hc k) s.val s.property
  refine ⟨hw, ?_⟩
  intro q r
  by_cases he : Support.GeneralImageEmbedding.ambient (representative q) =
      Support.GeneralImageEmbedding.ambient (representative r)
  · have hd : 3 ≤ Support.GeneralImageEmbedding.ambient (representative q) := Nat.le_max_left 3 _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd
    have hdq : Support.GeneralImageEmbedding.ambient (representative q) = k + 3 := by omega
    exact Support.GeneralImageEmbedding.same_ambient_order_of_fixed (k + 3) q r hdq (he.symm.trans hdq)
      (fun s t => Support.GeneralImageWFInvariant.original_order_of_closure k (hc k)
        s.val t.val s.property t.property)
  · rcases Nat.lt_or_gt_of_ne he with hd | hd
    · exact different_ambient_order q r hd (hw q) (hw r)
    · have hs := source_lt_of_ambient_lt r q hd
      have ht := target_lt_of_ambient_lt r q hd (hw r) (hw q)
      constructor
      · intro h
        exact False.elim (classLT_irrefl q (classLT_trans h hs))
      · intro h
        have hf := wf_not_lt_reverse (hw r) (hw q) ht
        rw [h] at hf
        cases hf

theorem global_certificate_of_limit_low [LargeCardinals.{u}]
    (hc : ∀ k, Support.GeneralImageWFInvariant.LimitLowFundClosure k) :
    Support.GeneralImageEmbedding.GlobalCertificate :=
  global_certificate_of_fundClosure
    (fun k => (Support.GeneralImageWFInvariant.fundClosure_iff_limit_low k).mpr (hc k))

end Support.GeneralImageIndexSupport

namespace Support.GeneralImageLimitBranches

open new OCF.Jaeger Support.OTQuotient Support.CountableSource
open Support.GeneralImageEmbedding Support.GeneralImageRawOrder
open Support.GeneralImageWFInvariant Support.BinaryTranslation
open Support.DimensionCut Support.TargetArithmetic

universe u

theorem H_mul_principal_support (d : Nat) {lam : Nat}
    (xs : Vec (new.T lam) lam) (n : Nat) (u : Term) {z : Term}
    (hz : z ∈ Term.H u (DimensionImage.convert d
      (code (new.T.mul (.P xs .Z) (new.T.ofNat n))))) :
    z ∈ Term.H u (DimensionImage.convert d (code (.P xs .Z))) := by
  induction n with
  | zero => simp [new.T.ofNat, new.T.mul, code, DimensionImage.convert, Term.H] at hz
  | succ n ih =>
    change z ∈ Term.H u (DimensionImage.convert d (code
      (.P xs (new.T.mul (.P xs .Z) (new.T.ofNat n))))) at hz
    simp only [code, DimensionImage.convert] at hz
    rcases Support.GeneralImageCoefficients.H_assemble_support u _ _ hz with hz | hz
    · simpa only [code, DimensionImage.convert, OT2.assemble, ↓reduceIte] using hz
    · exact ih hz

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
    rcases Support.GeneralImageCoefficients.H_inacc_support n b hz with rfl | hz
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
          Support.CountableTarget.lt_zero]
    rw [he]
    rcases Support.GeneralImageCoefficients.H_psi_support hz with rfl | hz | hz
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihb hw.2.2.1 hz))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihv hw.2.1 hz))

theorem H_nat_support (u : Term) (n : Nat) {z : Term}
    (hz : z ∈ Term.H u (Support.FiniteCorrespondence.natTerm n)) : z = .zero := by
  induction n with
  | zero => cases hz
  | succ n ih =>
    cases n with
    | zero => exact Support.GeneralImageCoefficients.H_one_mem hz
    | succ n =>
      rw [Support.FiniteCorrespondence.natTerm, Term.H] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact Support.GeneralImageCoefficients.H_one_mem hz
      · exact ih hz

theorem H_nat_bound (u : Term) (n : Nat) :
    Term.allLt (Term.H u (Support.FiniteCorrespondence.natTerm n))
      (Support.FiniteCorrespondence.natTerm n) = true := by
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  rw [H_nat_support u n hz]
  cases n with
  | zero => cases hz
  | succ n => cases n <;> simp [Support.FiniteCorrespondence.natTerm, Term.lt, Term.one]

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

def topNode (k : Nat) (a : new.T (k + 3)) : new.T (k + 3) :=
  .P (lastVec (k + 2) a) .Z

theorem topNode_zero (k : Nat) : topNode k .Z = new.T.ofNat 1 := by
  change new.T.P (lastVec (k + 2) (.Z : new.T (k + 3))) .Z = new.T.P (zeros (k + 3)) .Z
  rfl

theorem convert_topNode (k : Nat) (a : new.T (k + 3)) (ha : a ≠ .Z) :
    DimensionImage.convert (k + 3) (code (topNode k a)) =
      .inacc (k + 1) (dropOne (DimensionImage.convert (k + 3) (code a))) := by
  have hc : code a ≠ .zero := fun h => ha (code_injective h)
  simp only [topNode, code, lastVec, codes, codes_zeros]
  rw [trim_before_nonzero _ _ hc]
  simp only [DimensionImage.convert, DimensionImage.arguments_append,
    DimensionImage.arguments_zeros, DimensionImage.arguments]
  have hn : DimensionImage.convert (k + 3) (code a) ≠ .zero := by
    intro h
    exact hc ((fixed_convert_zero_iff _ _).mp h)
  rw [principal_top_term k _ hn]
  rfl

theorem ofNat_one_recursiveWF (d lam : Nat) :
    RecursiveWF d (new.T.ofNat (lam := lam) 1) := by
  change RecursiveWF d (Support.SourceSuccessor.succ (.Z : new.T lam))
  exact (recursive_succ_iff _ _).mpr (recursive_zero _ _)

theorem topNode_recursiveWF (k : Nat) (a : new.T (k + 3))
    (ha : RecursiveWF (k + 3) a) : RecursiveWF (k + 3) (topNode k a) := by
  by_cases hz : a = .Z
  · subst a
    rw [topNode_zero]
    exact ofNat_one_recursiveWF _ _
  · rw [topNode, RecursiveWF]
    refine ⟨?_, recursive_zero _ _, ?_⟩
    · intro i
      rw [lastVec_idx]
      split
      · exact ha
      · exact recursive_zero _ _
    · change Term.wf (DimensionImage.convert (k + 3) (code (topNode k a))) = true
      rw [convert_topNode k a hz]
      apply (Term.wf_inacc_iff _ _).mpr
      refine ⟨dropOne_wf ha.wf, ?_⟩
      have hi := DimensionImage.indices_drop
        (DimensionImage.indices_convert (k + 3) (by omega) (code a))
      have hf := Support.TargetIndexCuts.IndicesBelow.fT_lt (by omega : 0 < k + 2) hi
      exact Nat.le_of_lt_succ hf

theorem H_topNode_support (k : Nat) (a : new.T (k + 3)) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega (DimensionImage.convert (k + 3) (code (topNode k a)))) :
    z = .zero ∨ z ∈ Term.H Term.bigOmega (DimensionImage.convert (k + 3) (code a)) := by
  by_cases hn : a = .Z
  · subst a
    rw [topNode_zero, Support.FiniteCorrespondence.code_ofNat] at hz
    change z ∈ Term.H Term.bigOmega
      (DimensionImage.convert (k + 3) Support.UserImage.oneCode) at hz
    rw [DimensionImage.convert_one] at hz
    exact Or.inl (Support.GeneralImageCoefficients.H_one_mem hz)
  · rw [convert_topNode k a hn] at hz
    rcases Support.GeneralImageCoefficients.H_inacc_support _ _ hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (Support.OT2.mem_H_dropOne hz)

end Support.GeneralImageLimitBranches

namespace Support.SourceRecursiveDescending

open new Support.OTQuotient Support.SourceDescending

def Recursive {lam : Nat} : T lam → Prop
  | .Z => True
  | .P xs b => (∀ i, Recursive (xs.idx i)) ∧ Recursive b ∧ Descending (.P xs b)
termination_by s => T.size s
decreasing_by
  all_goals first | exact T.idx_size_lt_P _ _ _ | exact T.add_size_lt_P _ _

theorem recursive_zero {lam : Nat} : Recursive (.Z : T lam) := by rw [Recursive]; trivial

theorem coordinates_rplc {lam m : Nat} (xs : Vec (T lam) m) (i : Fin m) (s : T lam)
    (hx : ∀ j, Recursive (xs.idx j)) (hs : Recursive s) : ∀ j, Recursive ((xs.rplc i s).idx j) := by
  intro j
  rw [vec_rplc_idx]
  by_cases hj : j.val = i.val
  · rw [ite_eq_left hj]
    exact hs
  · rw [ite_eq_right hj]
    exact hx j

theorem principal {lam : Nat} (xs : Vec (T lam) lam) (hx : ∀ i, Recursive (xs.idx i)) :
    Recursive (.P xs .Z) := by
  rw [Recursive]
  exact ⟨hx, recursive_zero, principal_descending xs⟩

theorem mul_principal {lam : Nat} (xs : Vec (T lam) lam) (hx : ∀ i, Recursive (xs.idx i)) (t : T lam) :
    Recursive (T.mul (.P xs .Z) t) := by
  cases t with
  | Z => rw [T.mul]; exact recursive_zero
  | P ys b =>
    change Recursive (.P xs (T.mul (.P xs .Z) b))
    rw [Recursive]
    exact ⟨hx, mul_principal xs hx b, mul_principal_descending xs (.P ys b)⟩
termination_by T.size t
decreasing_by exact T.add_size_lt_P _ _

theorem iter_recursive {lam : Nat} (F : T lam → T lam)
    (hf : ∀ s, Recursive s → Recursive (F s)) (t : T lam) (ht : Recursive t) : Recursive (T.iter F t) := by
  cases t with
  | Z => rw [T.iter]; exact recursive_zero
  | P ys b =>
    rw [Recursive] at ht
    change Recursive (F (T.iter F b))
    exact hf _ (iter_recursive F hf b ht.2.1)
termination_by T.size t
decreasing_by all_goals simp_all only [T.size]; all_goals omega

theorem fund_recursive {lam : Nat} (s t : T lam) (hs : Recursive s) (ht : Recursive t) :
    Recursive (T.fund s t) := by
  cases s with
  | Z => rw [T.fund]; exact recursive_zero
  | P xs b =>
    rw [Recursive] at hs
    have hx := hs.1
    have hdesc := hs.2.2
    rw [T.fund]
    by_cases hb : b = .Z
    · subst b
      simp only [↓reduceIte]
      cases hm : T.domVecMinIdx xs with
      | none => exact recursive_zero
      | some p =>
        obtain ⟨i, d⟩ := p
        have hf : ∀ a, Recursive a → Recursive (T.fund (xs.idx i) a) :=
          fun a ha => fund_recursive (xs.idx i) a (hx i) ha
        cases d with
        | zero | omega => exact principal _ (coordinates_rplc xs i _ hx (hf t ht))
        | Omega ys =>
          change Recursive (if Vec.lt xs ys then
            .P (xs.rplc i (T.fund (xs.idx i) (T.iter (T.fund (xs.idx i)) t))) .Z
            else .P (xs.rplc i (T.fund (xs.idx i) t)) .Z)
          by_cases hv : Vec.lt xs ys
          · rw [ite_eq_left hv]
            exact principal _ (coordinates_rplc xs i _ hx (hf _ (iter_recursive _ hf t ht)))
          · rw [ite_eq_right hv]
            exact principal _ (coordinates_rplc xs i _ hx (hf t ht))
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero =>
            exact mul_principal _ (coordinates_rplc xs ⟨0, hj⟩ _ hx (hf .Z recursive_zero)) t
          | succ j =>
            exact principal _ (coordinates_rplc _ ⟨j, Nat.lt_of_succ_lt hj⟩ t
              (coordinates_rplc xs ⟨j + 1, hj⟩ _ hx (hf .Z recursive_zero)) ht)
    · rw [ite_eq_right hb]
      rw [Recursive]
      refine ⟨hx, fund_recursive b t hs.2.1 ht, ?_⟩
      have hd := fund_descending (.P xs b) t hdesc
      rwa [T.fund, ite_eq_right hb] at hd
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hi := Vec.idx_size_lt xs i; omega) | omega

theorem ofNat_recursive (lam n : Nat) : Recursive (T.ofNat (lam := lam) n) := by
  induction n with
  | zero => rw [T.ofNat]; exact recursive_zero
  | succ n ih =>
    change Recursive (.P (zeros lam) (T.ofNat n))
    rw [Recursive]
    refine ⟨?_, ih, ofNat_descending lam (n + 1)⟩
    intro i
    rw [zeros, Vec.ofFn_idx]
    exact recursive_zero

theorem LF_recursive (lam n : Nat) : Recursive (T.LF lam n) := by
  induction n with
  | zero => rw [T.LF]; exact recursive_zero
  | succ n ih =>
    cases lam with
    | zero =>
      change Recursive (.P .nil (T.LF 0 n))
      rw [Recursive]
      refine ⟨fun i => i.elim0, ih, ?_⟩
      change Descending (T.LF 0 (n + 1))
      rw [← FiniteCorrespondence.ofNat_zero_eq_LF]
      exact ofNat_descending 0 (n + 1)
    | succ k =>
      rw [T.LF]
      apply principal
      intro i
      rw [Vec.ofFn_idx]
      split
      · exact ih
      · exact recursive_zero

theorem isOT_recursive {lam : Nat} {s : T lam} (hs : T.isOT lam s) : Recursive s := by
  induction hs with
  | base_0 n => exact LF_recursive 0 n
  | base_succ k n =>
    apply principal
    intro i
    rw [Vec.ofFn_idx]
    split
    · exact LF_recursive (k + 1) n
    · exact recursive_zero
  | step lam s hs n ih => exact fund_recursive s _ ih (ofNat_recursive lam n)

theorem domain_principal_le_head {lam : Nat} (s : T lam) (hs : Recursive s)
    {v : Vec (T lam) lam} (hd : T.dom s = .Omega v) :
    T.le (.P v .Z) (T.head s) := by
  cases s with
  | Z => cases hd
  | P xs b =>
    rw [Recursive] at hs
    by_cases hb : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte] at hd
      cases hm : T.domVecMinIdx xs with
      | none => simp only [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        have hchild := (Support.DimensionCut.minIdx_spec xs hm).1.symm
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          simp only [hm] at hd
          by_cases hi : i.val = 0
          · simp only [hi, ↓reduceIte] at hd; cases hd
          · simp only [hi, ↓reduceIte] at hd
            have he := Dom.Omega.inj hd
            subst v
            exact Or.inr (T_refl _)
        | Omega ys =>
          simp only [hm] at hd
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte] at hd; cases hd
          · simp only [hv, ↓reduceIte] at hd
            have he := Dom.Omega.inj hd
            subst v
            rcases Vec_total ys xs with h | h | h
            · exact Or.inl (by simp only [T.head, compareT, h])
            · exact False.elim (hv h)
            · subst ys; exact Or.inr (T_refl _)
    · rw [T.dom, ite_eq_right hb] at hd
      exact le_trans (domain_principal_le_head b hs.2.1 hd) hs.2.2.2
termination_by T.size s
decreasing_by simp_all only [T.size]; omega

theorem head_le_self {lam : Nat} (s : T lam) : T.le (T.head s) s := by
  cases s with
  | Z => exact Or.inr (T_refl _)
  | P xs b =>
    cases b with
    | Z => exact Or.inr (T_refl _)
    | P ys c => exact Or.inl (by simp only [T.head, compareT, Vec_refl])

theorem diagonal_principal_lt_argument {lam : Nat} (xs : Vec (T lam) lam)
    (a : T lam) (ha : Recursive a) {v : Vec (T lam) lam}
    (hd : T.dom a = .Omega v) (hv : Vec.lt xs v) : T.lt (.P xs .Z) a := by
  have hhead := le_trans (domain_principal_le_head a ha hd) (head_le_self a)
  have hpr : T.lt (.P xs .Z) (.P v .Z) := by
    change compareVec xs v = .lt at hv
    simp only [T.lt, compareT, hv]
  rcases hhead with hhead | hhead
  · exact T_trans _ _ _ hpr hhead
  · rw [← T_eq_sound _ _ hhead]; exact hpr

end Support.SourceRecursiveDescending

namespace Support.SourceFundGap

open new Support.OTQuotient Support.DimensionCut Support.SourceFundOrder

mutual
  def mass {lam : Nat} : new.T lam → Nat
    | .Z => 0
    | .P xs b => 1 + vectorMass xs + mass b
  termination_by s => new.T.size s
  decreasing_by all_goals simp only [new.T.size]; all_goals omega

  def vectorMass {lam : Nat} : {m : Nat} → Vec (new.T lam) m → Nat
    | _, .nil => 0
    | _, .snoc _ xs x => vectorMass xs + mass x
  termination_by _ xs => Vec.size xs
  decreasing_by all_goals simp_all only [Vec.size]; all_goals omega
end

theorem vectorMass_idx_le {lam m : Nat} (xs : Vec (new.T lam) m) (i : Fin m) :
    mass (xs.idx i) ≤ vectorMass xs := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    by_cases hi : i.val < m
    · let j : Fin m := ⟨i.val, hi⟩
      have he : i = j.castSucc := Fin.ext rfl
      rw [he, vec_snoc_idx_cast, vectorMass]
      exact Nat.le_trans (ih j) (Nat.le_add_right _ _)
    · have he : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
      rw [he, vec_snoc_idx_last, vectorMass]
      omega

theorem mass_idx_lt {lam : Nat} (xs : Vec (new.T lam) lam) (b : new.T lam) (i : Fin lam) :
    mass (xs.idx i) < mass (.P xs b) := by
  have hi := vectorMass_idx_le xs i
  rw [mass]
  omega

theorem vectorMass_pair_le {lam m : Nat} (xs : Vec (new.T lam) m) (i j : Fin m)
    (hij : i ≠ j) : mass (xs.idx i) + mass (xs.idx j) ≤ vectorMass xs := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    by_cases hi : i.val < m
    · let i' : Fin m := ⟨i.val, hi⟩
      have hei : i = i'.castSucc := Fin.ext rfl
      by_cases hj : j.val < m
      · let j' : Fin m := ⟨j.val, hj⟩
        have hej : j = j'.castSucc := Fin.ext rfl
        have hij' : i' ≠ j' := by intro h; apply hij; rw [hei, hej, h]
        rw [hei, hej, vec_snoc_idx_cast, vec_snoc_idx_cast, vectorMass]
        exact Nat.le_trans (ih i' j' hij') (Nat.le_add_right _ _)
      · have hej : j = Fin.last m := Fin.ext (by have := j.isLt; simp; omega)
        rw [hei, hej, vec_snoc_idx_cast, vec_snoc_idx_last, vectorMass]
        have hm := vectorMass_idx_le xs i'
        omega
    · have hei : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
      have hj : j.val < m := by
        by_cases hj : j.val < m
        · exact hj
        · have hej : j = Fin.last m := Fin.ext (by have := j.isLt; simp; omega)
          exact False.elim (hij (hei.trans hej.symm))
      let j' : Fin m := ⟨j.val, hj⟩
      have hej : j = j'.castSucc := Fin.ext rfl
      rw [hei, hej, vec_snoc_idx_last, vec_snoc_idx_cast, vectorMass]
      have hm := vectorMass_idx_le xs j'
      omega

theorem mass_tail_lt {lam : Nat} (xs : Vec (new.T lam) lam) (b : new.T lam) :
    mass b < mass (.P xs b) := by rw [mass]; omega

theorem vectorMass_rplc {lam m : Nat} (xs : Vec (new.T lam) m) (i : Fin m)
    (a : new.T lam) : vectorMass (xs.rplc i a) + mass (xs.idx i) =
      vectorMass xs + mass a := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    by_cases hi : i.val < m
    · let j : Fin m := ⟨i.val, hi⟩
      have he : i = j.castSucc := Fin.ext rfl
      have hr : (Vec.snoc m xs x).rplc j.castSucc a = Vec.snoc m (xs.rplc j a) x := by
        apply vec_ext
        intro l
        by_cases hl : l.val < m
        · let q : Fin m := ⟨l.val, hl⟩
          have hel : l = q.castSucc := Fin.ext rfl
          simp only [hel, vec_rplc_idx, vec_snoc_idx_cast, Fin.val_castSucc]
        · have hel : l = Fin.last m := Fin.ext (by have := l.isLt; simp; omega)
          have hlj : m ≠ j.val := by have := j.isLt; omega
          simp only [hel, vec_rplc_idx, vec_snoc_idx_last, Fin.val_last,
            Fin.val_castSucc, hlj, ↓reduceIte]
      rw [he, hr, vec_snoc_idx_cast, vectorMass, vectorMass]
      have hm := ih j
      omega
    · have he : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
      have hr : (Vec.snoc m xs x).rplc (Fin.last m) a = Vec.snoc m xs a := by
        apply vec_ext
        intro l
        by_cases hl : l.val < m
        · let q : Fin m := ⟨l.val, hl⟩
          have hel : l = q.castSucc := Fin.ext rfl
          have hne : q.val ≠ m := by change l.val ≠ m; omega
          simp only [hel, vec_rplc_idx, vec_snoc_idx_cast, Fin.val_castSucc,
            Fin.val_last, hne, ↓reduceIte]
        · have hel : l = Fin.last m := Fin.ext (by have := l.isLt; simp; omega)
          simp only [hel, vec_rplc_idx, vec_snoc_idx_last, ↓reduceIte]
      rw [he, hr, vec_snoc_idx_last, vectorMass, vectorMass]
      omega

theorem vectorMass_eq_zero {lam m : Nat} (xs : Vec (new.T lam) m)
    (hz : ∀ i, xs.idx i = .Z) : vectorMass xs = 0 := by
  induction xs with
  | nil => simp only [vectorMass]
  | snoc m xs x ih =>
    have hx := hz (Fin.last m)
    rw [vec_snoc_idx_last] at hx
    rw [vectorMass, hx, mass, Nat.add_zero]
    exact ih (fun i => by simpa only [vec_snoc_idx_cast] using hz i.castSucc)

theorem mass_succ {lam : Nat} (s : new.T lam) :
    mass (Support.SourceSuccessor.succ s) = mass s + 1 := by
  cases s with
  | Z =>
    change mass (.P (zeros lam) .Z) = _
    simp only [mass]
    rw [vectorMass_eq_zero _ (by intro i; simp [zeros, Vec.ofFn_idx])]
  | P xs b =>
    change mass (.P xs (Support.SourceSuccessor.succ b)) = _
    rw [mass, mass_succ b, mass]
    omega
termination_by new.T.size s
decreasing_by exact new.T.add_size_lt_P _ _

theorem mass_fund_one {lam : Nat} (s t : new.T lam) (hd : new.T.dom s = .one) :
    mass (new.T.fund s t) + 1 = mass s := by
  obtain ⟨b, rfl⟩ := Support.GeneralImageWFInvariant.dom_one_succ s hd
  rw [Support.SourceSuccessor.fund_succ, mass_succ]

theorem source_le_antisymm {lam : Nat} {a b : new.T lam}
    (hab : new.T.le a b) (hba : new.T.le b a) : a = b := by
  rcases hab with hab | hab
  · rcases hba with hba | hba
    · have hi := new.T_trans _ _ _ hab hba
      rw [new.T_refl] at hi
      cases hi
    · exact (new.T_eq_sound _ _ hba).symm
  · exact new.T_eq_sound _ _ hab

theorem vec_le_last {lam m : Nat} (xs ys : Vec (new.T lam) m) (x y : new.T lam)
    (h : Vec.le (.snoc m xs x) (.snoc m ys y)) : new.T.le x y := by
  unfold Vec.le at h
  simp only [compareVec] at h
  cases he : compareT x y with
  | lt => exact Or.inl he
  | eq => exact Or.inr he
  | gt => simp [he] at h

theorem vec_lt_last {lam m : Nat} (xs ys : Vec (new.T lam) m) (x y : new.T lam)
    (h : Vec.lt (.snoc m xs x) (.snoc m ys y)) : new.T.le x y :=
  vec_le_last xs ys x y (Or.inl h)

theorem vec_same_last_le {lam m : Nat} (xs ys : Vec (new.T lam) m) (x : new.T lam) :
    Vec.le (.snoc m xs x) (.snoc m ys x) ↔ Vec.le xs ys := by
  simp only [Vec.le, compareVec, new.T_refl]

theorem vec_same_last_lt {lam m : Nat} (xs ys : Vec (new.T lam) m) (x : new.T lam) :
    Vec.lt (.snoc m xs x) (.snoc m ys x) ↔ Vec.lt xs ys := by
  simp only [Vec.lt, compareVec, new.T_refl]

theorem vector_interval {lam m : Nat} (xs lo ys : Vec (new.T lam) m) (i : Fin m)
    (hz : ∀ j : Fin m, j.val < i.val → xs.idx j = .Z)
    (hh : ∀ j : Fin m, i.val < j.val → lo.idx j = xs.idx j)
    (hlo : Vec.le lo ys) (hhi : Vec.lt ys xs) :
    new.T.le (lo.idx i) (ys.idx i) ∧ new.T.lt (ys.idx i) (xs.idx i) ∧
      vectorMass xs - mass (xs.idx i) + mass (ys.idx i) ≤ vectorMass ys := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    cases lo with
    | snoc _ lo a =>
      cases ys with
      | snoc _ ys y =>
        by_cases him : i.val < m
        · let j : Fin m := ⟨i.val, him⟩
          have he : i = j.castSucc := Fin.ext rfl
          have hax : a = x := by
            simpa only [vec_snoc_idx_last] using hh (Fin.last m) him
          subst a
          have hyx : y = x := source_le_antisymm (vec_lt_last ys xs y x hhi)
            (vec_le_last lo ys x y hlo)
          subst y
          have hlo' := (vec_same_last_le lo ys x).mp hlo
          have hhi' := (vec_same_last_lt ys xs x).mp hhi
          have hs := ih lo ys j
            (fun l hl => by simpa only [he, vec_snoc_idx_cast] using hz l.castSucc hl)
            (fun l hl => by simpa only [he, vec_snoc_idx_cast] using hh l.castSucc hl) hlo' hhi'
          simp only [he, vec_snoc_idx_cast, vectorMass]
          have hi := vectorMass_idx_le xs j
          exact ⟨hs.1, hs.2.1, by omega⟩
        · have he : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
          have hxs : xs = zeros m := by
            apply vec_ext
            intro j
            have hj : j.val < i.val := by simp only [he, Fin.val_last]; exact j.isLt
            have h := hz j.castSucc hj
            rw [vec_snoc_idx_cast] at h
            simpa only [zeros, Vec.ofFn_idx] using h
          have hyx : new.T.lt y x := by
            change (match compareT y x with | .eq => compareVec ys xs | o => o) = .lt at hhi
            cases hc : compareT y x with
            | lt => exact hc
            | eq =>
              rw [hc, hxs] at hhi
              exact False.elim (compareVec_zero_not_lt ys hhi)
            | gt => rw [hc] at hhi; cases hhi
          simp only [he, vec_snoc_idx_last, vectorMass]
          have hv : vectorMass xs = 0 := by
            rw [hxs]
            apply vectorMass_eq_zero
            intro j
            simp [zeros, Vec.ofFn_idx]
          exact ⟨vec_le_last lo ys a y hlo, hyx, by omega⟩

theorem vectors_le_of_term_le {lam : Nat} (xs ys : Vec (new.T lam) lam)
    (b c : new.T lam) (h : new.T.le (.P xs b) (.P ys c)) : Vec.le xs ys := by
  unfold new.T.le at h
  simp only [compareT] at h
  cases he : compareVec xs ys with
  | lt => exact Or.inl he
  | eq => exact Or.inr he
  | gt => simp [he] at h

theorem vectors_lt_of_principal_lt {lam : Nat} (ys xs : Vec (new.T lam) lam)
    (b : new.T lam) (h : new.T.lt (.P ys b) (.P xs .Z)) : Vec.lt ys xs := by
  change (match compareVec ys xs with | .eq => compareT b .Z | o => o) = .lt at h
  cases he : compareVec ys xs with
  | lt => exact he
  | eq => rw [he] at h; cases b <;> cases h
  | gt => rw [he] at h; cases h

theorem source_vec_le_antisymm {lam m : Nat} {xs ys : Vec (new.T lam) m}
    (hxy : Vec.le xs ys) (hyx : Vec.le ys xs) : xs = ys := by
  rcases hxy with hxy | hxy
  · rcases hyx with hyx | hyx
    · have hi := new.Vec_trans _ _ _ hxy hyx
      rw [new.Vec_refl] at hi
      cases hi
    · exact (new.Vec_eq_sound _ _ hyx).symm
  · exact new.Vec_eq_sound _ _ hxy

theorem principal_interval_mass {lam : Nat} (xs lo : Vec (new.T lam) lam)
    (b w : new.T lam) (i : Fin lam) (g : Nat)
    (hz : ∀ j : Fin lam, j.val < i.val → xs.idx j = .Z)
    (hh : ∀ j : Fin lam, i.val < j.val → lo.idx j = xs.idx j)
    (hgap : ∀ z, new.T.le (lo.idx i) z → new.T.lt z (xs.idx i) → g ≤ mass z)
    (hlo : new.T.le (.P lo b) w) (hhi : new.T.lt w (.P xs .Z)) :
    1 + (vectorMass xs - mass (xs.idx i)) + g ≤ mass w := by
  cases w with
  | Z => rcases hlo with hlo | hlo <;> cases hlo
  | P ys c =>
    have hv := vector_interval xs lo ys i hz hh
      (vectors_le_of_term_le lo ys b c hlo) (vectors_lt_of_principal_lt ys xs c hhi)
    have hg := hgap (ys.idx i) hv.1 hv.2.1
    rw [mass]
    omega

theorem tail_interval {lam : Nat} (xs : Vec (new.T lam) lam) (b c w : new.T lam)
    (hlo : new.T.le (.P xs c) w) (hhi : new.T.lt w (.P xs b)) :
    ∃ r, w = .P xs r ∧ new.T.le c r ∧ new.T.lt r b := by
  cases w with
  | Z => rcases hlo with hlo | hlo <;> cases hlo
  | P ys r =>
    have hv := source_vec_le_antisymm
      (vectors_le_of_term_le xs ys c r hlo)
      (vectors_le_of_term_le ys xs r b (Or.inl hhi))
    subst ys
    simp only [new.T.le, new.T.lt, compareT, new.Vec_refl] at hlo hhi
    exact ⟨r, rfl, hlo, hhi⟩

theorem mass_gap_one_coordinate {lam : Nat} (a z : new.T lam)
    (ha : new.T.dom a = .one) (hlo : new.T.le (new.T.fund a .Z) z)
    (hhi : new.T.lt z a) : mass a - 1 ≤ mass z := by
  obtain ⟨b, he⟩ := Support.GeneralImageWFInvariant.dom_one_succ a ha
  rw [he, Support.SourceSuccessor.fund_succ] at hlo
  rw [he] at hhi ⊢
  have hz := source_le_antisymm hlo ((Support.SourceSuccessor.lt_succ_iff_le z b).mp hhi)
  rw [← hz, mass_succ]
  omega

theorem mass_positive {lam : Nat} {s : new.T lam} (hs : s ≠ .Z) : 0 < mass s := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P xs b => rw [mass]; omega

theorem principal_step_gap {lam : Nat} (xs lo : Vec (new.T lam) lam)
    (b w : new.T lam) (i : Fin lam)
    (hz : ∀ j : Fin lam, j.val < i.val → xs.idx j = .Z)
    (hn : xs.idx i ≠ .Z)
    (hh : ∀ j : Fin lam, i.val < j.val → lo.idx j = xs.idx j)
    (hg : ∀ z, new.T.le (lo.idx i) z → new.T.lt z (xs.idx i) → mass (xs.idx i) - 1 ≤ mass z)
    (hlo : new.T.le (.P lo b) w) (hhi : new.T.lt w (.P xs .Z)) :
    mass (.P xs .Z) - 1 ≤ mass w := by
  have h := principal_interval_mass xs lo b w i (mass (xs.idx i) - 1) hz hh hg hlo hhi
  have hi := vectorMass_idx_le xs i
  have hp := mass_positive hn
  simp only [mass] at *
  omega

theorem gap_mass {lam : Nat} (s t w : new.T lam)
    (hd : new.T.dom s = .omega ∨ ∃ v, new.T.dom s = .Omega v)
    (ht : new.T.dom s = .omega → t ≠ .Z)
    (hlo : new.T.le (new.T.fund s t) w) (hhi : new.T.lt w s) :
    mass s - 1 ≤ mass w := by
  cases he : s with
  | Z =>
    rw [he] at hd
    cases hd with
    | inl hd => cases hd
    | inr hd => obtain ⟨v, hd⟩ := hd; cases hd
  | P xs b =>
    simp only [he] at hd ht hlo hhi ⊢
    by_cases hb : b = .Z
    · subst b
      rw [new.T.fund] at hlo
      simp only [↓reduceIte] at hlo
      cases hm : new.T.domVecMinIdx xs with
      | none =>
        have hdom : new.T.dom (.P xs .Z) = .one := by simp [new.T.dom, hm]
        rw [hdom] at hd
        rcases hd with hd | ⟨v, hd⟩ <;> cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        have hs := minIdx_spec xs hm
        have hc : new.T.dom (xs.idx i) = d := hs.1.symm
        have hn : xs.idx i ≠ .Z := by
          intro h
          rw [h, new.T.dom] at hc
          exact hs.2.1 hc.symm
        rw [hm] at hlo
        simp only [GetElem.getElem, Fin.eta] at hlo
        cases d with
        | zero => exact False.elim (hs.2.1 rfl)
        | omega =>
          have hdom : new.T.dom (.P xs .Z) = .omega := by simp [new.T.dom, hm]
          apply principal_step_gap xs (xs.rplc i (new.T.fund (xs.idx i) t)) .Z w i
            hs.2.2 hn ?_ ?_ hlo hhi
          · intro j hj
            rw [vec_rplc_idx, ite_eq_right (by omega)]
          · intro z hz hz'
            rw [vec_rplc_idx, ite_eq_left rfl] at hz
            exact gap_mass (xs.idx i) t z (Or.inl hc) (fun _ => ht hdom) hz hz'
        | Omega v =>
          change new.T.le (if Vec.lt xs v then
            .P (xs.rplc i (new.T.fund (xs.idx i) (new.T.iter (new.T.fund (xs.idx i)) t))) .Z
            else .P (xs.rplc i (new.T.fund (xs.idx i) t)) .Z) w at hlo
          by_cases hv : Vec.lt xs v
          · rw [ite_eq_left hv] at hlo
            apply principal_step_gap xs
              (xs.rplc i (new.T.fund (xs.idx i) (new.T.iter (new.T.fund (xs.idx i)) t)))
              .Z w i hs.2.2 hn ?_ ?_ hlo hhi
            · intro j hj
              rw [vec_rplc_idx, ite_eq_right (by omega)]
            · intro z hz hz'
              rw [vec_rplc_idx, ite_eq_left rfl] at hz
              exact gap_mass (xs.idx i) _ z (Or.inr ⟨v, hc⟩)
                (by intro h; rw [hc] at h; cases h) hz hz'
          · rw [ite_eq_right hv] at hlo
            apply principal_step_gap xs (xs.rplc i (new.T.fund (xs.idx i) t)) .Z w i
              hs.2.2 hn ?_ ?_ hlo hhi
            · intro j hj
              rw [vec_rplc_idx, ite_eq_right (by omega)]
            · intro z hz hz'
              rw [vec_rplc_idx, ite_eq_left rfl] at hz
              exact gap_mass (xs.idx i) t z (Or.inr ⟨v, hc⟩)
                (by intro h; rw [hc] at h; cases h) hz hz'
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero =>
            have hdom : new.T.dom (.P xs .Z) = .omega := by simp [new.T.dom, hm]
            have htn := ht hdom
            cases t with
            | Z => exact False.elim (htn rfl)
            | P us c =>
              change new.T.le (.P (xs.rplc ⟨0, hj⟩ (new.T.fund (xs.idx ⟨0, hj⟩) .Z))
                (new.T.mul (.P (xs.rplc ⟨0, hj⟩ (new.T.fund (xs.idx ⟨0, hj⟩) .Z)) .Z) c)) w at hlo
              apply principal_step_gap xs _ _ w ⟨0, hj⟩ hs.2.2 hn ?_ ?_ hlo hhi
              · intro l hl
                rw [vec_rplc_idx, ite_eq_right (by omega)]
              · intro z hz hz'
                rw [vec_rplc_idx, ite_eq_left rfl] at hz
                exact mass_gap_one_coordinate _ _ hc hz hz'
          | succ j =>
            change new.T.le (.P ((xs.rplc ⟨j + 1, hj⟩
              (new.T.fund (xs.idx ⟨j + 1, hj⟩) .Z)).rplc ⟨j, Nat.lt_of_succ_lt hj⟩ t) .Z) w at hlo
            apply principal_step_gap xs _ .Z w ⟨j + 1, hj⟩ hs.2.2 hn ?_ ?_ hlo hhi
            · intro l hl
              have hl' : j + 1 < l.val := hl
              rw [vec_rplc_idx, ite_eq_right (show l.val ≠ j from by omega),
                vec_rplc_idx, ite_eq_right (show l.val ≠ j + 1 from by omega)]
            · intro z hz hz'
              rw [vec_rplc_idx] at hz
              rw [ite_eq_right (show j + 1 ≠ j from by omega), vec_rplc_idx, ite_eq_left rfl] at hz
              exact mass_gap_one_coordinate _ _ hc hz hz'
    · rw [new.T.fund, ite_eq_right hb] at hlo
      obtain ⟨r, hw, hl, hh⟩ := tail_interval xs b (new.T.fund b t) w hlo hhi
      have hdom : new.T.dom (.P xs b) = new.T.dom b := by rw [new.T.dom, ite_eq_right hb]
      have hdb : new.T.dom b = .omega ∨ ∃ v, new.T.dom b = .Omega v := hdom ▸ hd
      have hg := gap_mass b t r hdb (fun h => ht (hdom.trans h)) hl hh
      have hp := mass_positive hb
      rw [hw]
      simp only [mass]
      omega
termination_by new.T.size s
decreasing_by
  all_goals try simp only [he]
  all_goals first
    | exact new.T.idx_size_lt_P _ _ _
    | exact new.T.add_size_lt_P _ _

def zeroGap {lam : Nat} (s : new.T lam) : Nat :=
  match s with
  | .Z => 0
  | .P xs b =>
    if b = .Z then
      match new.T.domVecMinIdx xs with
      | none => 0
      | some (i, d) =>
        match d with
        | .zero => 0
        | .one => if i.val = 0 then 0 else vectorMass xs
        | .omega => 1 + (vectorMass xs - mass (xs.idx i)) + zeroGap (xs.idx i)
        | .Omega _ => vectorMass xs
    else 1 + vectorMass xs + zeroGap b
termination_by new.T.size s
decreasing_by
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem gap_zero {lam : Nat} (s w : new.T lam)
    (hlo : new.T.le (new.T.fund s .Z) w) (hhi : new.T.lt w s) : zeroGap s ≤ mass w := by
  cases he : s with
  | Z => simp only [he] at hhi; cases w <;> cases hhi
  | P xs b =>
    simp only [he] at hlo hhi ⊢
    by_cases hb : b = .Z
    · subst b
      rw [zeroGap, new.T.fund] at *
      simp only [↓reduceIte] at *
      cases hm : new.T.domVecMinIdx xs with
      | none => exact Nat.zero_le _
      | some p =>
        obtain ⟨i, d⟩ := p
        have hs := minIdx_spec xs hm
        have hc : new.T.dom (xs.idx i) = d := hs.1.symm
        have hn : xs.idx i ≠ .Z := by
          intro h
          rw [h, new.T.dom] at hc
          exact hs.2.1 hc.symm
        simp only [hm] at hlo ⊢
        simp only [GetElem.getElem, Fin.eta] at hlo
        cases d with
        | zero => exact False.elim (hs.2.1 rfl)
        | omega =>
          apply principal_interval_mass xs (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z w i
            (zeroGap (xs.idx i)) hs.2.2 ?_ ?_ hlo hhi
          · intro j hj
            rw [vec_rplc_idx, ite_eq_right (by omega)]
          · intro z hz hz'
            rw [vec_rplc_idx, ite_eq_left rfl] at hz
            exact gap_zero (xs.idx i) z hz hz'
        | Omega v =>
          change new.T.le (if Vec.lt xs v then
            .P (xs.rplc i (new.T.fund (xs.idx i) (new.T.iter (new.T.fund (xs.idx i)) .Z))) .Z
            else .P (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z) w at hlo
          have hg : mass (.P xs .Z) - 1 ≤ mass w := by
            by_cases hv : Vec.lt xs v
            · rw [ite_eq_left hv] at hlo
              apply principal_step_gap xs _ .Z w i hs.2.2 hn ?_ ?_ hlo hhi
              · intro j hj
                rw [vec_rplc_idx, ite_eq_right (by omega)]
              · intro z hz hz'
                rw [vec_rplc_idx, ite_eq_left rfl] at hz
                exact gap_mass (xs.idx i) _ z (Or.inr ⟨v, hc⟩)
                  (by intro h; rw [hc] at h; cases h) hz hz'
            · rw [ite_eq_right hv] at hlo
              apply principal_step_gap xs _ .Z w i hs.2.2 hn ?_ ?_ hlo hhi
              · intro j hj
                rw [vec_rplc_idx, ite_eq_right (by omega)]
              · intro z hz hz'
                rw [vec_rplc_idx, ite_eq_left rfl] at hz
                exact gap_mass (xs.idx i) .Z z (Or.inr ⟨v, hc⟩)
                  (by intro h; rw [hc] at h; cases h) hz hz'
          simpa only [mass, Nat.add_zero, Nat.add_sub_cancel_left] using hg
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero => exact Nat.zero_le _
          | succ j =>
            simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
            change new.T.le (.P ((xs.rplc ⟨j + 1, hj⟩
              (new.T.fund (xs.idx ⟨j + 1, hj⟩) .Z)).rplc ⟨j, Nat.lt_of_succ_lt hj⟩ .Z) .Z) w at hlo
            have hg : mass (.P xs .Z) - 1 ≤ mass w := by
              apply principal_step_gap xs _ .Z w ⟨j + 1, hj⟩ hs.2.2 hn ?_ ?_ hlo hhi
              · intro l hl
                have hl' : j + 1 < l.val := hl
                rw [vec_rplc_idx, ite_eq_right (show l.val ≠ j from by omega),
                  vec_rplc_idx, ite_eq_right (show l.val ≠ j + 1 from by omega)]
              · intro z hz hz'
                rw [vec_rplc_idx] at hz
                rw [ite_eq_right (show j + 1 ≠ j from by omega), vec_rplc_idx, ite_eq_left rfl] at hz
                exact mass_gap_one_coordinate _ _ hc hz hz'
            simpa only [mass, Nat.add_zero, Nat.add_sub_cancel_left] using hg
    · rw [zeroGap, ite_eq_right hb]
      rw [new.T.fund, ite_eq_right hb] at hlo
      obtain ⟨r, hw, hl, hh⟩ := tail_interval xs b (new.T.fund b .Z) w hlo hhi
      have hg := gap_zero b r hl hh
      rw [hw, mass]
      omega
termination_by new.T.size s
decreasing_by
  all_goals try simp only [he]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

def gap {lam : Nat} (s t : new.T lam) : Nat :=
  if t = .Z then zeroGap s else mass s - 1

theorem gap_all {lam : Nat} (s t w : new.T lam)
    (hlo : new.T.le (new.T.fund s t) w) (hhi : new.T.lt w s) : gap s t ≤ mass w := by
  by_cases ht : t = .Z
  · subst t
    rw [gap, ite_eq_left rfl]
    exact gap_zero s w hlo hhi
  · rw [gap, ite_eq_right ht]
    cases hd : new.T.dom s with
    | zero =>
      have hs := (dom_eq_zero_iff s).mp hd
      rw [hs] at hhi
      cases w <;> cases hhi
    | one =>
      rw [Support.SourceFundOrder.dom_one_fund_constant s hd t .Z] at hlo
      exact mass_gap_one_coordinate s w hd hlo hhi
    | omega => exact gap_mass s t w (Or.inl hd) (fun _ => ht) hlo hhi
    | Omega v => exact gap_mass s t w (Or.inr ⟨v, hd⟩) (by intro h; rw [hd] at h; cases h) hlo hhi

theorem small_lt_fund_all {lam : Nat} (s t z : new.T lam)
    (hz : new.T.lt z s) (hm : mass z < gap s t) : new.T.lt z (new.T.fund s t) := by
  rcases new.T_total z (new.T.fund s t) with h | h | he
  · exact h
  · exact False.elim (Nat.not_le_of_lt hm (gap_all s t z (Or.inl h) hz))
  · exact False.elim (Nat.not_le_of_lt hm
      (gap_all s t z (Or.inr (by rw [he]; exact new.T_refl _)) hz))

theorem zeroGap_le_mass {lam : Nat} (s : new.T lam) : zeroGap s ≤ mass s - 1 := by
  cases he : s with
  | Z => simp only [zeroGap, mass]; omega
  | P xs b =>
    simp only [mass, zeroGap]
    by_cases hb : b = .Z
    · subst b
      simp only [↓reduceIte, mass, Nat.add_zero]
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only; omega
      | some p =>
        obtain ⟨i, d⟩ := p
        simp only
        cases d with
        | zero => change 0 ≤ 1 + vectorMass xs - 1; omega
        | one =>
          change (if i.val = 0 then 0 else vectorMass xs) ≤ 1 + vectorMass xs - 1
          split <;> omega
        | Omega v => change vectorMass xs ≤ 1 + vectorMass xs - 1; omega
        | omega =>
          change 1 + (vectorMass xs - mass (xs.idx i)) + zeroGap (xs.idx i) ≤
            1 + vectorMass xs - 1
          have hs := minIdx_spec xs hm
          have hn : xs.idx i ≠ .Z := by
            intro h
            have hc := hs.1
            rw [h, new.T.dom] at hc
            cases hc
          have hi := vectorMass_idx_le xs i
          have hp := mass_positive hn
          have hg := zeroGap_le_mass (xs.idx i)
          omega
    · rw [ite_eq_right hb]
      have hp := mass_positive hb
      have hg := zeroGap_le_mass b
      omega
termination_by new.T.size s
decreasing_by
  all_goals try simp only [he]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem zeroGap_Omega {lam : Nat} (s : new.T lam) (v : Vec (new.T lam) lam)
    (hd : new.T.dom s = .Omega v) : zeroGap s + 1 = mass s := by
  cases he : s with
  | Z => rw [he, new.T.dom] at hd; cases hd
  | P xs b =>
    simp only [he] at hd ⊢
    by_cases hb : b = .Z
    · subst b
      rw [new.T.dom] at hd
      simp only [↓reduceIte] at hd
      rw [zeroGap, ite_eq_left rfl]
      cases hm : new.T.domVecMinIdx xs with
      | none => rw [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        simp only
        rw [hm] at hd
        cases d with
        | zero | omega => cases hd
        | one =>
          by_cases hi : i.val = 0
          · simp [hi] at hd
          · simp only [hi, ↓reduceIte, mass, Nat.add_zero]
            omega
        | Omega ys =>
          simp only [mass, Nat.add_zero]
          omega
    · rw [new.T.dom, ite_eq_right hb] at hd
      rw [zeroGap, ite_eq_right hb, mass]
      have hg := zeroGap_Omega b v hd
      omega
termination_by new.T.size s
decreasing_by
  all_goals try simp only [he]
  all_goals exact new.T.add_size_lt_P _ _

theorem gap_nonzero {lam : Nat} (s t : new.T lam) (ht : t ≠ .Z) :
    gap s t = mass s - 1 := by rw [gap, ite_eq_right ht]

theorem gap_Omega {lam : Nat} (s t : new.T lam) (v : Vec (new.T lam) lam)
    (hd : new.T.dom s = .Omega v) : gap s t = mass s - 1 := by
  by_cases ht : t = .Z
  · rw [gap, ite_eq_left ht]
    have hg := zeroGap_Omega s v hd
    omega
  · exact gap_nonzero s t ht

theorem mass_fund_zero_le {lam : Nat} (s : new.T lam) :
    mass (new.T.fund s .Z) ≤ zeroGap s := by
  cases he : s with
  | Z => simp only [new.T.fund, mass, zeroGap, Nat.le_refl]
  | P xs b =>
    rw [new.T.fund, zeroGap]
    by_cases hb : b = .Z
    · rw [ite_eq_left hb, ite_eq_left hb]
      cases hm : new.T.domVecMinIdx xs with
      | none => simp only [mass, Nat.zero_le]
      | some p =>
        obtain ⟨i, d⟩ := p
        have hs := minIdx_spec xs hm
        have hchild := hs.1.symm
        have hr := vectorMass_rplc xs i (new.T.fund (xs.idx i) .Z)
        have hi := vectorMass_idx_le xs i
        have hg := mass_fund_zero_le (xs.idx i)
        cases d with
        | zero => exact False.elim (hs.2.1 rfl)
        | omega =>
          change mass (.P (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z) ≤
            1 + (vectorMass xs - mass (xs.idx i)) + zeroGap (xs.idx i)
          simp only [mass]
          omega
        | Omega ys =>
          have hgΩ := zeroGap_Omega (xs.idx i) ys hchild
          simp only [new.T.iter]
          split
          all_goals change mass (.P (xs.rplc i (new.T.fund (xs.idx i) .Z)) .Z) ≤ vectorMass xs
          all_goals simp only [mass]
          all_goals omega
        | one =>
          have hg1 := mass_fund_one (xs.idx i) .Z hchild
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero => simp only [new.T.mul, mass, ↓reduceIte, Nat.le_refl]
          | succ j =>
            change mass (.P ((xs.rplc ⟨j + 1, hj⟩ (new.T.fund (xs.idx ⟨j + 1, hj⟩) .Z)).rplc
              ⟨j, Nat.lt_of_succ_lt hj⟩ .Z) .Z) ≤ vectorMass xs
            have hl : xs.idx ⟨j, Nat.lt_of_succ_lt hj⟩ = .Z := hs.2.2 _ (by simp)
            have hp : ((xs.rplc ⟨j + 1, hj⟩ (new.T.fund (xs.idx ⟨j + 1, hj⟩) .Z))).idx
                ⟨j, Nat.lt_of_succ_lt hj⟩ = .Z := by
              rw [vec_rplc_idx, ite_eq_right (by simp), hl]
            have hr2 := vectorMass_rplc
              (xs.rplc ⟨j + 1, hj⟩ (new.T.fund (xs.idx ⟨j + 1, hj⟩) .Z))
              ⟨j, Nat.lt_of_succ_lt hj⟩ .Z
            simp only [hp, mass] at hr2
            simp only [mass]
            omega
    · rw [ite_eq_right hb, ite_eq_right hb]
      simp only [mass]
      have hg := mass_fund_zero_le b
      omega
termination_by new.T.size s
decreasing_by
  all_goals try simp only [he]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

end Support.SourceFundGap

namespace Support.SourceCoefficientGap

open new Support.OTQuotient Support.SourceFundGap
open Support.GeneralImageCoefficients

theorem mass_lt_of_subterm {lam : Nat} {a s : new.T lam} (h : Subterm a s) : mass a < mass s := by
  induction h with
  | coordinate => exact mass_idx_lt _ _ _
  | tail => exact mass_tail_lt _ _
  | trans _ _ ha hb => exact Nat.lt_trans ha hb

end Support.SourceCoefficientGap

namespace Support.GeneralImageLimitSupport

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageCoefficients Support.TargetArithmetic Support.BinaryTranslation
open Support.DimensionCut Support.GeneralImageLimitBranches
open Support.CountableSource
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair

universe u

theorem convert_principal (d : Nat) {lam : Nat} (xs : Vec (T lam) lam) :
    convert d (code (.P xs .Z)) = principal d (arguments d (trim (codes xs))) := by
  simp only [code, convert, Support.OT2.assemble, ↓reduceIte]

theorem principal_image_ne_one [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (T (k + 3)) (k + 3)) (i : Fin (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (hn : xs.idx i ≠ .Z) :
    convert (k + 3) (code (.P xs .Z)) ≠ Term.one := by
  intro he
  have ho : RecursiveWF (k + 3) (Support.SourceSuccessor.succ (.Z : new.T (k + 3))) :=
    (recursive_succ_iff _ _).mpr (recursive_zero _ _)
  have hone : convert (k + 3) (code (Support.SourceSuccessor.succ (.Z : new.T (k + 3)))) =
      Term.one := by rw [convert_succ, code, convert]; rfl
  have heq := convert_injective k (.P xs .Z) (Support.SourceSuccessor.succ .Z) hs ho
    (he.trans hone.symm)
  have hx : xs = zeros (k + 3) := (T.P.inj heq).1
  apply hn
  rw [hx, zeros, Vec.ofFn_idx]

theorem lt_inacc_drop [LargeCardinals.{u}] (n : Nat) (a : Term)
    (ha : Term.wf a = true) (hi : Term.wf (.inacc n (dropOne a)) = true) :
    Term.lt a (.inacc n (dropOne a)) = true := by
  by_cases hh : Term.head a = Term.one
  · obtain ⟨m, he⟩ := head_one_nat ha hh
    rw [he]
    simpa only [he] using
      nat_lt_of_head_ne hi (by intro h; cases h) (by intro h; cases h) (m + 1)
  · rw [dropOne_of_head_ne hh] at hi ⊢
    apply (lt_iff_V.{u} ha hi).mpr
    exact (sem_of_wf.{u} hi).inacc_ok n a rfl

theorem no_diagonal_highest [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (T (k + 3)) (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hr : Support.SourceRecursiveDescending.Recursive (xs.idx (Fin.last (k + 2))))
    {v : Vec (T (k + 3)) (k + 3)}
    (hm : T.domVecMinIdx xs = some (Fin.last (k + 2), .Omega v)) : ¬ Vec.lt xs v := by
  intro hv
  have hd := (minIdx_spec xs hm).1.symm
  have hn : xs.idx (Fin.last (k + 2)) ≠ .Z := by
    intro he; rw [he, T.dom] at hd; cases hd
  have hx : xs = lastVec (k + 2) (xs.idx (Fin.last (k + 2))) := by
    apply vec_ext
    intro j
    rw [lastVec_idx]
    by_cases hj : j.val = k + 2
    · rw [ite_eq_left hj]
      exact congrArg xs.idx (Fin.ext hj)
    · rw [ite_eq_right hj]
      exact (minIdx_spec xs hm).2.2 j (by have := j.isLt; simp only [Fin.val_last]; omega)
  have he : convert (k + 3) (code (.P xs .Z)) =
      .inacc (k + 1) (dropOne (convert (k + 3) (code (xs.idx (Fin.last (k + 2)))))) := by
    have ht := convert_topNode k (xs.idx (Fin.last (k + 2))) hn
    simpa only [topNode, ← hx] using ht
  have ha : RecursiveWF (k + 3) (xs.idx (Fin.last (k + 2))) := by
    rw [RecursiveWF] at hs; exact hs.1 _
  have hlt := (convert_order k (.P xs .Z) (xs.idx (Fin.last (k + 2))) hs ha).mp
    (Support.SourceRecursiveDescending.diagonal_principal_lt_argument xs _ hr hd hv)
  have hrev : Term.lt (convert (k + 3) (code (xs.idx (Fin.last (k + 2)))))
      (convert (k + 3) (code (.P xs .Z))) = true := by
    rw [he]
    exact lt_inacc_drop _ _ ha.wf (he ▸ hs.wf)
  have hf := Support.GeneralImageTopPair.wf_not_lt_reverse hs.wf ha.wf hlt
  rw [hf] at hrev
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
    rw [Support.OT2.H_succTerm]; exact List.mem_append_left _ hz
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
        rw [Support.OT2.H_succTerm]
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
          rw [Support.OT2.H_succTerm]
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

theorem zero_coordinate_predecessor (k : Nat) (xs : Vec (T (k + 3)) (k + 3))
    (b : new.T (k + 3))
    (hx : xs.idx ⟨0, by omega⟩ = Support.SourceSuccessor.succ b)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) :
    RecursiveWF (k + 3) (.P (xs.rplc ⟨0, by omega⟩ b) .Z) ∧
      ∀ z, z ∈ Term.H Term.bigOmega
        (convert (k + 3) (code (.P (xs.rplc ⟨0, by omega⟩ b) .Z))) →
        z = convert (k + 3) (code b) ∨ z = dropOne (convert (k + 3) (code b)) ∨
          z ∈ Term.H Term.bigOmega (convert (k + 3) (code (.P xs .Z))) := by
  let ys := xs.rplc ⟨0, by omega⟩ b
  let us := arguments (k + 3) (trim (codes xs))
  let vs := arguments (k + 3) (trim (codes ys))
  have hb : RecursiveWF (k + 3) b := by
    rw [RecursiveWF] at hs
    exact (recursive_succ_iff _ _).mp (hx ▸ hs.1 ⟨0, by omega⟩)
  have he : ∀ i, 0 < i → i < k + 3 → us[i]?.getD .zero = vs[i]?.getD .zero := by
    intro i hi hik
    rw [converted_coordinate xs ⟨i, hik⟩, converted_coordinate ys ⟨i, hik⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : i ≠ 0)]
  have htop : topPair (k + 1) (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero) =
      topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero) := by
    rw [he (k + 2) (by omega) (by omega), he (k + 1) (by omega) (by omega)]
  have hctx : Context (k + 1)
      (topPair (k + 1) (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero)) := by
    rcases topPair_shape (k + 1) _ _ with h | ⟨h, hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, Nat.le_of_eq hf.symm⟩
  have h0 : us[0]?.getD .zero = succTerm (convert (k + 3) (code b)) := by
    rw [converted_coordinate xs ⟨0, by omega⟩, hx, convert_succ]
  have h0' : vs[0]?.getD .zero = convert (k + 3) (code b) := by
    rw [converted_coordinate ys ⟨0, by omega⟩]
    simp only [ys, vec_rplc_idx, ↓reduceIte]
  have hw := hs.wf
  rw [convert_principal, principal_as_layers] at hw
  have hp := lower_zero_predecessor (k + 1) (by omega) us vs _ _ hctx hb.wf h0 h0'
    (fun i hi hik => he i hi (by omega)) hw
  have hnew : RecursiveWF (k + 3) (.P ys .Z) := by
    rw [RecursiveWF]
    refine ⟨?_, recursive_zero _ _, ?_⟩
    · intro i
      simp only [ys, vec_rplc_idx]
      split
      · exact hb
      · rw [RecursiveWF] at hs; exact hs.1 i
    · rw [convert_principal, principal_as_layers, ← htop]
      exact hp.1
  refine ⟨hnew, ?_⟩
  intro z hz
  change z ∈ Term.H Term.bigOmega (convert (k + 3) (code (.P ys .Z))) at hz
  rw [convert_principal, principal_as_layers, ← htop] at hz
  have hpz := hp.2 z hz
  simpa only [convert_principal, principal_as_layers] using hpz

theorem minIdx_first {lam m : Nat} (xs : Vec (T lam) (m + 1))
    (hn : T.dom (xs.idx ⟨0, Nat.zero_lt_succ m⟩) ≠ .zero) :
    T.domVecMinIdx xs = some (⟨0, Nat.zero_lt_succ m⟩,
      T.dom (xs.idx ⟨0, Nat.zero_lt_succ m⟩)) := by
  induction m with
  | zero =>
    cases xs with
    | snoc _ xs x =>
      cases xs
      simp only [Vec.idx, Nat.not_lt_zero, ↓reduceDIte] at hn ⊢
      simp only [T.domVecMinIdx, hn, ↓reduceIte]
      rfl
  | succ m ih =>
    cases xs with
    | snoc _ xs x =>
      have hn' : T.dom (xs.idx ⟨0, Nat.zero_lt_succ m⟩) ≠ .zero := by
        simpa only [Vec.idx, Nat.zero_lt_succ, ↓reduceDIte] using hn
      rw [T.domVecMinIdx, ih xs hn']
      rfl

theorem fund_zero_coordinate_successor (k : Nat) (xs : Vec (T (k + 3)) (k + 3))
    (b t : new.T (k + 3)) (hx : xs.idx ⟨0, by omega⟩ = Support.SourceSuccessor.succ b) :
    T.fund (.P xs .Z) t = T.mul (.P (xs.rplc ⟨0, by omega⟩ b) .Z) t := by
  have hd : T.dom (xs.idx ⟨0, by omega⟩) = .one := by rw [hx, Support.SourceSuccessor.dom_succ]
  have hm := minIdx_first xs (by rw [hd]; intro h; cases h)
  rw [T.fund]
  simp only [↓reduceIte, hm, GetElem.getElem, hx, Support.SourceSuccessor.dom_succ,
    Support.SourceSuccessor.fund_succ]

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

end Support.GeneralImageLimitSupport

namespace Support.SourceSubtermBounds

open new Support.OTQuotient Support.DimensionCut Support.SourceFundOrder
open Support.GeneralImageCoefficients Support.SourceRecursiveDescending

theorem last_coordinate_lt {m : Nat} (xs : Vec (T (m + 1)) (m + 1)) (b : T (m + 1)) :
    T.lt (xs.idx (Fin.last m)) (.P xs b) := by
  cases he : xs.idx (Fin.last m) with
  | Z => rfl
  | P ys c =>
    have hh := last_coordinate_lt ys c
    have hv := compareVec_of_lt_at ys xs (Fin.last m)
      (by rw [he]; exact hh) (by intro j hj; have := j.isLt; simp only [Fin.val_last] at hj; omega)
    simp only [T.lt, compareT, hv]
termination_by T.size (.P xs b)
decreasing_by
  have h := T.idx_size_lt_P xs b (Fin.last m)
  change T.size (xs.idx (Fin.last m)) < T.size (.P xs b) at h
  rw [he] at h
  exact h

theorem descending_tail_lt {lam : Nat} (xs : Vec (T lam) lam) (b : T lam)
    (hs : Support.SourceDescending.Descending (.P xs b)) : T.lt b (.P xs b) := by
  cases b with
  | Z => rfl
  | P ys c =>
    have hb := hs.1
    have hh := hs.2
    rcases hh with hh | hh
    · change compareT (.P ys .Z) (.P xs .Z) = .lt at hh
      change compareT (.P ys c) (.P xs (.P ys c)) = .lt
      simp only [compareT] at hh ⊢
      cases hv : compareVec ys xs with
      | lt => rfl
      | eq | gt => rw [hv] at hh; cases hh
    · have he := (T.P.inj (T_eq_sound _ _ hh)).1
      subst ys
      have h := descending_tail_lt xs c hb
      simpa only [T.lt, compareT, Vec_refl] using h
termination_by T.size b
decreasing_by simp_all only [T.size]; omega

def TreeBelow {lam : Nat} (bound : T lam) : T lam → Prop
  | .Z => T.lt .Z bound
  | .P xs b => T.lt (.P xs b) bound ∧ (∀ i, TreeBelow bound (xs.idx i)) ∧ TreeBelow bound b
termination_by s => T.size s
decreasing_by
  all_goals first | exact T.idx_size_lt_P _ _ _ | exact T.add_size_lt_P _ _

def ChildrenBelow {lam : Nat} (bound : T lam) : T lam → Prop
  | .Z => True
  | .P xs b => (∀ i, TreeBelow bound (xs.idx i)) ∧ TreeBelow bound b

theorem TreeBelow.root_lt {lam : Nat} {bound s : T lam} (hs : TreeBelow bound s) : T.lt s bound := by
  cases s with
  | Z => rw [TreeBelow] at hs; exact hs
  | P => rw [TreeBelow] at hs; exact hs.1

theorem TreeBelow.children {lam : Nat} {bound s : T lam} (hs : TreeBelow bound s) : ChildrenBelow bound s := by
  cases s with
  | Z => trivial
  | P => rw [TreeBelow] at hs; exact hs.2

theorem treeBelow_iff {lam : Nat} (bound s : T lam) :
    TreeBelow bound s ↔ T.lt s bound ∧ ChildrenBelow bound s := by
  cases s <;> simp only [TreeBelow, ChildrenBelow, and_true]

theorem Subterm.treeBelow {lam : Nat} {a s bound : T lam} (h : Subterm a s)
    (hs : TreeBelow bound s) : TreeBelow bound a := by
  induction h with
  | coordinate xs b i => rw [TreeBelow] at hs; exact hs.2.1 i
  | tail xs b => rw [TreeBelow] at hs; exact hs.2.2
  | trans _ _ ha hb => exact ha (hb hs)

theorem ChildrenBelow.subterm {lam : Nat} {s bound : T lam} (hs : ChildrenBelow bound s)
    {a : T lam} (h : Subterm a s) : TreeBelow bound a := by
  induction h with
  | coordinate xs b i => exact hs.1 i
  | tail xs b => exact hs.2
  | trans _ _ ha hb => exact ha (hb hs).children

theorem treeBelow_of_subterms {lam : Nat} (bound s : T lam) (hr : T.lt s bound)
    (hs : ∀ a, Subterm a s → T.lt a bound) : TreeBelow bound s := by
  cases s with
  | Z => rw [TreeBelow]; exact hr
  | P xs b =>
    rw [TreeBelow]
    refine ⟨hr, ?_, ?_⟩
    · intro i
      exact treeBelow_of_subterms bound (xs.idx i) (hs _ (Subterm.coordinate xs b i))
        (fun a ha => hs a (Subterm.trans ha (Subterm.coordinate xs b i)))
    · exact treeBelow_of_subterms bound b (hs _ (Subterm.tail xs b))
        (fun a ha => hs a (Subterm.trans ha (Subterm.tail xs b)))
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hi := Vec.idx_size_lt xs i; omega) | omega

theorem childrenBelow_iff {lam : Nat} (bound s : T lam) :
    ChildrenBelow bound s ↔ ∀ a, Subterm a s → T.lt a bound := by
  constructor
  · intro hs a ha; exact (hs.subterm ha).root_lt
  · intro hs
    cases s with
    | Z => trivial
    | P xs b =>
      refine ⟨?_, ?_⟩
      · intro i
        exact treeBelow_of_subterms bound (xs.idx i) (hs _ (Subterm.coordinate xs b i))
          (fun a ha => hs a (Subterm.trans ha (Subterm.coordinate xs b i)))
      · exact treeBelow_of_subterms bound b (hs _ (Subterm.tail xs b))
          (fun a ha => hs a (Subterm.trans ha (Subterm.tail xs b)))

theorem treeBelow_rplc {lam m : Nat} (xs : Vec (T lam) m) (i : Fin m) (a bound : T lam)
    (hx : ∀ j, TreeBelow bound (xs.idx j)) (ha : TreeBelow bound a) :
    ∀ j, TreeBelow bound ((xs.rplc i a).idx j) := by
  intro j
  rw [vec_rplc_idx]
  split
  · exact ha
  · exact hx j

theorem fund_zero_bounds {lam : Nat} (s bound : T lam) :
    (ChildrenBelow bound s → ChildrenBelow bound (T.fund s .Z)) ∧
      (TreeBelow bound s → TreeBelow bound (T.fund s .Z)) := by
  have hchildren : ChildrenBelow bound s → ChildrenBelow bound (T.fund s .Z) := by
    cases s with
    | Z => simp only [T.fund, ChildrenBelow]; exact id
    | P xs b =>
      intro hs
      rw [ChildrenBelow] at hs
      have hf : ∀ i, TreeBelow bound (T.fund (xs.idx i) .Z) :=
        fun i => (fund_zero_bounds (xs.idx i) bound).2 (hs.1 i)
      by_cases hb : b = .Z
      · subst b
        rw [T.fund]
        simp only [↓reduceIte]
        cases hm : T.domVecMinIdx xs with
        | none => trivial
        | some p =>
          obtain ⟨i, d⟩ := p
          cases d with
          | zero | omega =>
            exact ⟨treeBelow_rplc xs i _ bound hs.1 (hf i), hs.2⟩
          | Omega v =>
            simp only [T.iter, ite_self]
            exact ⟨treeBelow_rplc xs i _ bound hs.1 (hf i), hs.2⟩
          | one =>
            obtain ⟨j, hj⟩ := i
            cases j with
            | zero => trivial
            | succ j =>
              exact ⟨treeBelow_rplc _ ⟨j, Nat.lt_of_succ_lt hj⟩ .Z bound
                (treeBelow_rplc xs ⟨j + 1, hj⟩ _ bound hs.1 (hf ⟨j + 1, hj⟩)) hs.2, hs.2⟩
      · rw [T.fund, ite_eq_right hb]
        exact ⟨hs.1, (fund_zero_bounds b bound).2 hs.2⟩
  refine ⟨hchildren, ?_⟩
  intro hs
  apply (treeBelow_iff _ _).mpr
  refine ⟨?_, hchildren hs.children⟩
  cases s with
  | Z => simpa only [T.fund] using hs.root_lt
  | P xs b =>
    exact T_trans _ _ _ (fund_lt (.P xs b) .Z (by intro he; cases he)) hs.root_lt
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hi := Vec.idx_size_lt xs i; omega) | omega

theorem TreeBelow.fund_zero {lam : Nat} {s bound : T lam} (hs : TreeBelow bound s) :
    TreeBelow bound (T.fund s .Z) := (fund_zero_bounds s bound).2 hs

theorem ChildrenBelow.fund_zero {lam : Nat} {s bound : T lam} (hs : ChildrenBelow bound s) :
    ChildrenBelow bound (T.fund s .Z) := (fund_zero_bounds s bound).1 hs

theorem TreeBelow.zero {lam : Nat} {bound s : T lam} (hs : TreeBelow bound s) :
    TreeBelow bound .Z := by
  cases bound with
  | Z => cases s <;> cases hs.root_lt
  | P => rw [TreeBelow]; rfl

theorem treeBelow_iter {lam : Nat} (F : T lam → T lam) (bound t : T lam)
    (hz : TreeBelow bound .Z)
    (hf : ∀ a, TreeBelow bound a → TreeBelow bound (F a)) :
    TreeBelow bound (T.iter F t) := by
  cases t with
  | Z => rw [T.iter]; exact hz
  | P xs b => rw [T.iter]; exact hf _ (treeBelow_iter F bound b hz hf)
termination_by T.size t
decreasing_by simp_all only [T.size]; omega

theorem treeBelow_mul_principal {lam : Nat} (xs : Vec (T lam) lam) (bound t : T lam)
    (hx : ∀ i, TreeBelow bound (xs.idx i)) (hz : TreeBelow bound .Z)
    (hr : ∀ a, a ≠ .Z → T.lt (T.mul (.P xs .Z) a) bound) :
    TreeBelow bound (T.mul (.P xs .Z) t) := by
  cases t with
  | Z => rw [T.mul]; exact hz
  | P ys b =>
    change TreeBelow bound (.P xs (T.mul (.P xs .Z) b))
    rw [TreeBelow]
    exact ⟨hr (.P ys b) (by intro he; cases he), hx,
      treeBelow_mul_principal xs bound b hx hz hr⟩
termination_by T.size t
decreasing_by simp_all only [T.size]; omega

theorem fund_bounds {lam : Nat} (s bound : T lam) :
    (∀ t, ChildrenBelow bound s → T.le s bound → TreeBelow bound t →
      ChildrenBelow bound (T.fund s t)) ∧
    (∀ t, TreeBelow bound s → TreeBelow bound t → TreeBelow bound (T.fund s t)) := by
  have hchildren : ∀ t, ChildrenBelow bound s → T.le s bound → TreeBelow bound t →
      ChildrenBelow bound (T.fund s t) := by
    cases s with
    | Z => intro t hs hl ht; rw [T.fund, ChildrenBelow]; trivial
    | P xs b =>
      intro t hs hl ht
      rw [ChildrenBelow] at hs
      have lift : ∀ a, T.lt a (.P xs b) → T.lt a bound := by
        intro a ha
        rcases hl with hl | hl
        · exact T_trans _ _ _ ha hl
        · rw [← T_eq_sound _ _ hl]; exact ha
      have hf : ∀ i a, TreeBelow bound a → TreeBelow bound (T.fund (xs.idx i) a) :=
        fun i a ha => (fund_bounds (xs.idx i) bound).2 a (hs.1 i) ha
      by_cases hb : b = .Z
      · subst b
        rw [T.fund]
        simp only [↓reduceIte]
        cases hm : T.domVecMinIdx xs with
        | none => trivial
        | some p =>
          obtain ⟨i, d⟩ := p
          cases d with
          | zero | omega =>
            exact ⟨treeBelow_rplc xs i _ bound hs.1 (hf i t ht), hs.2⟩
          | Omega v =>
            change ChildrenBelow bound (if Vec.lt xs v then
              .P (xs.rplc i (T.fund (xs.idx i) (T.iter (T.fund (xs.idx i)) t))) .Z
              else .P (xs.rplc i (T.fund (xs.idx i) t)) .Z)
            by_cases hv : Vec.lt xs v
            · rw [ite_eq_left hv]
              exact ⟨treeBelow_rplc xs i _ bound hs.1
                (hf i _ (treeBelow_iter (T.fund (xs.idx i)) bound t ht.zero (hf i))), hs.2⟩
            · rw [ite_eq_right hv]
              exact ⟨treeBelow_rplc xs i _ bound hs.1 (hf i t ht), hs.2⟩
          | one =>
            obtain ⟨j, hj⟩ := i
            cases j with
            | zero =>
              have hx := treeBelow_rplc xs ⟨0, hj⟩ _ bound hs.1 (hf ⟨0, hj⟩ .Z ht.zero)
              apply TreeBelow.children
              apply treeBelow_mul_principal _ bound t hx ht.zero
              intro a ha
              apply lift
              have hh := fund_lt (.P xs .Z) a (by intro he; cases he)
              simpa only [T.fund, ↓reduceIte, hm, GetElem.getElem] using hh
            | succ j =>
              exact ⟨treeBelow_rplc _ ⟨j, Nat.lt_of_succ_lt hj⟩ t bound
                (treeBelow_rplc xs ⟨j + 1, hj⟩ _ bound hs.1
                  (hf ⟨j + 1, hj⟩ .Z ht.zero)) ht, hs.2⟩
      · rw [T.fund, ite_eq_right hb]
        exact ⟨hs.1, (fund_bounds b bound).2 t hs.2 ht⟩
  refine ⟨hchildren, ?_⟩
  intro t hs ht
  apply (treeBelow_iff _ _).mpr
  refine ⟨?_, hchildren t hs.children (Or.inl hs.root_lt) ht⟩
  cases s with
  | Z => simpa only [T.fund] using hs.root_lt
  | P xs b => exact T_trans _ _ _ (fund_lt (.P xs b) t (by intro he; cases he)) hs.root_lt
termination_by T.size s
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hi := Vec.idx_size_lt xs i; omega) | omega

theorem TreeBelow.fund {lam : Nat} {s t bound : T lam} (hs : TreeBelow bound s)
    (ht : TreeBelow bound t) : TreeBelow bound (T.fund s t) := (fund_bounds s bound).2 t hs ht

theorem no_diagonal_of_subterms {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam)
    (hr : Recursive (xs.idx i)) {v : Vec (T lam) lam} (hd : T.dom (xs.idx i) = .Omega v)
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z)) : ¬ Vec.lt xs v := by
  intro hv
  have h1 := diagonal_principal_lt_argument xs (xs.idx i) hr hd hv
  have h2 := hs _ (Subterm.coordinate xs .Z i)
  have h3 := T_trans _ _ _ h1 h2
  rw [T_refl] at h3
  cases h3

theorem omega_selector_of_subterms (m : Nat) (xs : Vec (T (m + 1)) (m + 1))
    (hr : Recursive (.P xs .Z))
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z))
    (hd : T.dom (.P xs .Z) = .omega) :
    T.domVecMinIdx xs = some (⟨0, by omega⟩, .one) ∨
      ∃ i, T.domVecMinIdx xs = some (i, .omega) := by
  rw [Recursive] at hr
  rw [T.dom] at hd
  simp only [↓reduceIte] at hd
  cases hm : T.domVecMinIdx xs with
  | none => rw [hm] at hd; cases hd
  | some p =>
    obtain ⟨i, d⟩ := p
    cases d with
    | zero => exact False.elim ((minIdx_spec xs hm).2.1 rfl)
    | one =>
      by_cases hi : i.val = 0
      · have he : i = ⟨0, by omega⟩ := Fin.ext hi
        exact Or.inl (congrArg (fun j => some (j, Dom.one)) he)
      · simp only [hm, hi, ↓reduceIte] at hd; cases hd
    | omega => exact Or.inr ⟨i, rfl⟩
    | Omega v =>
      have hn := no_diagonal_of_subterms xs i (hr.1 i) (minIdx_spec xs hm).1.symm hs
      simp only [hm, hn, ↓reduceIte] at hd
      cases hd

theorem fund_zero_subterms {lam : Nat} (s : T lam)
    (hs : ∀ a, Subterm a s → T.lt a s) :
    ∀ a, Subterm a (T.fund s .Z) → T.lt a (T.fund s .Z) := by
  have hc := (childrenBelow_iff s s).mpr hs
  have hc' := hc.fund_zero
  intro a ha
  have hlt := (hc'.subterm ha).root_lt
  have hm := Support.SourceCoefficientGap.mass_lt_of_subterm ha
  have hf := Support.SourceFundGap.mass_fund_zero_le s
  have hg : Support.SourceFundGap.mass a < Support.SourceFundGap.gap s .Z := by
    rw [Support.SourceFundGap.gap, ite_eq_left rfl]
    omega
  exact Support.SourceFundGap.small_lt_fund_all s .Z a hlt hg

theorem treeBelow_fund_of_small {lam : Nat} (s t c : T lam)
    (hc : TreeBelow s c) (hm : Support.SourceFundGap.mass c < Support.SourceFundGap.gap s t) :
    TreeBelow (T.fund s t) c := by
  cases c with
  | Z =>
    rw [TreeBelow]
    exact Support.SourceFundGap.small_lt_fund_all s t .Z hc.root_lt hm
  | P xs b =>
    rw [TreeBelow] at hc ⊢
    refine ⟨Support.SourceFundGap.small_lt_fund_all s t _ hc.1 hm, ?_, ?_⟩
    · intro i
      exact treeBelow_fund_of_small s t (xs.idx i) (hc.2.1 i)
        (Nat.lt_trans (Support.SourceFundGap.mass_idx_lt xs b i) hm)
    · exact treeBelow_fund_of_small s t b hc.2.2
        (Nat.lt_trans (Support.SourceFundGap.mass_tail_lt xs b) hm)
termination_by T.size c
decreasing_by
  all_goals simp_all only [T.size]
  all_goals first | (have hi := Vec.idx_size_lt xs i; omega) | omega

theorem regular_fund_subterms {lam m : Nat} (xs : Vec (T lam) lam) (hml : m + 1 < lam)
    (hv : T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one)) (t : T lam)
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z))
    (ht : ∀ a, Subterm a t → T.lt a t)
    (hinc : T.lt t (T.fund (.P xs .Z) t)) :
    ∀ a, Subterm a (T.fund (.P xs .Z) t) → T.lt a (T.fund (.P xs .Z) t) := by
  by_cases ht0 : t = .Z
  · subst t; exact fund_zero_subterms (.P xs .Z) hs
  · have hc := (childrenBelow_iff (.P xs .Z) (.P xs .Z)).mpr hs
    have hd := (minIdx_spec xs hv).1.symm
    have hm := Support.SourceFundGap.mass_fund_one (xs.idx ⟨m + 1, hml⟩) .Z hd
    have hmi := Support.SourceFundGap.vectorMass_idx_le xs ⟨m + 1, hml⟩
    have hpos : 0 < Support.SourceFundGap.mass (xs.idx ⟨m + 1, hml⟩) := by omega
    have hgap : Support.SourceFundGap.gap (.P xs .Z) t = Support.SourceFundGap.vectorMass xs := by
      rw [Support.SourceFundGap.gap, ite_eq_right ht0, Support.SourceFundGap.mass,
        Support.SourceFundGap.mass]
      omega
    have hp : TreeBelow (T.fund (.P xs .Z) t) (T.fund (xs.idx ⟨m + 1, hml⟩) .Z) := by
      apply treeBelow_fund_of_small (.P xs .Z) t _ (hc.1 ⟨m + 1, hml⟩).fund_zero
      rw [hgap]
      omega
    have harg : TreeBelow (T.fund (.P xs .Z) t) t :=
      treeBelow_of_subterms _ t hinc (fun a ha => T_trans _ _ _ (ht a ha) hinc)
    have hcoords : ∀ i : Fin lam, i ≠ ⟨m + 1, hml⟩ →
        TreeBelow (T.fund (.P xs .Z) t) (xs.idx i) := by
      intro i hi
      apply treeBelow_fund_of_small (.P xs .Z) t _ (hc.1 i)
      rw [hgap]
      have hpair := Support.SourceFundGap.vectorMass_pair_le xs i ⟨m + 1, hml⟩ hi
      omega
    apply (childrenBelow_iff _ _).mp
    rw [fund_regular_bound xs hml hv t]
    rw [fund_regular_bound xs hml hv t] at hp harg hcoords
    refine ⟨?_, ?_⟩
    · intro i
      rw [vec_rplc_idx]
      by_cases hi : i.val = m
      · rw [ite_eq_left hi]; exact harg
      · rw [ite_eq_right hi, vec_rplc_idx]
        by_cases hij : i.val = m + 1
        · rw [ite_eq_left hij]; exact hp
        · rw [ite_eq_right hij]
          exact hcoords i (by intro he; exact hij (congrArg Fin.val he))
    · exact harg.zero

end Support.SourceSubtermBounds

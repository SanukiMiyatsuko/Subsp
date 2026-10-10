import Subsp.Support.Image

/-! The image is an order embedding (`Term.lt` of images versus the source order) and its H coefficients. -/

namespace Support.GeneralImageEmbedding

open new OCF.Jaeger Support.OTQuotient Support.BinaryTranslation

def ambient (s : Code) : Nat := max 3 (Support.CodeReification.width s)

def convert (s : Code) : Term := DimensionImage.convert (ambient s) s

def classConversion (q : Classes) : Term := convert (representative q)

theorem indices_convert (s : Code) :
    Support.TargetIndexCuts.IndicesBelow (ambient s - 1) (convert s) := by
  apply DimensionImage.indices_convert
  have h := Nat.le_max_left 3 (Support.CodeReification.width s)
  change 3 ≤ ambient s at h
  omega

theorem lower_ne_zero (k : Nat) (hk : 0 < k) (xs : List Term) (h : Term) :
    DimensionImage.lower k xs h ≠ .zero := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      simp only [DimensionImage.lower]
      split
      · simp
      · split
        · assumption
        · simp
    | succ k =>
      rw [DimensionImage.lower]
      exact lower_ne_zero (k + 1) (by omega) xs _
termination_by k

theorem lower_isPrin (k : Nat) (hk : 0 < k) (xs : List Term) (h : Term)
    (hh : h = .zero ∨ Term.isPrin h = true) :
    Term.isPrin (DimensionImage.lower k xs h) = true := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      simp only [DimensionImage.lower]
      split
      · rfl
      · rename_i hn
        split
        · exact hh.resolve_left hn
        · rfl
    | succ k =>
      rw [DimensionImage.lower]
      apply lower_isPrin (k + 1) (by omega)
      split
      · split
        · exact Or.inr rfl
        · split
          · exact Or.inl rfl
          · exact Or.inr rfl
      · split
        · exact hh
        · exact Or.inr rfl
termination_by k

theorem principal_isPrin (d : Nat) (xs : List Term) :
    Term.isPrin (DimensionImage.principal d xs) = true := by
  rw [DimensionImage.principal]
  split
  · exact OT2.principal_isPrin _ _
  · apply lower_isPrin (d - 2) (by omega)
    split
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inr rfl

theorem principal_ne_zero (d : Nat) (xs : List Term) : DimensionImage.principal d xs ≠ .zero := by
  rw [DimensionImage.principal]
  split
  · rw [OT2.principal]
    split <;> (try split) <;> simp
  · exact lower_ne_zero (d - 2) (by omega) xs _

theorem fixed_convert_zero_iff (d : Nat) (s : Code) :
    DimensionImage.convert d s = .zero ↔ s = .zero := by
  cases s with
  | zero => simp [DimensionImage.convert]
  | p xs b =>
    rw [DimensionImage.convert, OT2.assemble]
    split
    · simp [principal_ne_zero]
    · simp

theorem fixed_outer_below (d : Nat) (s : Code) (hs : Support.CountableSource.OuterForm s) :
    Term.lt (DimensionImage.convert d s) Term.bigOmega = true := by
  cases s with
  | zero => simp [DimensionImage.convert, Term.bigOmega, Term.lt]
  | p xs b =>
    rw [Support.CountableSource.OuterForm] at hs
    cases xs with
    | nil =>
      simp only [DimensionImage.convert, DimensionImage.arguments, DimensionImage.principal_nil]
      rw [OT2.assemble]
      split <;> simp [Term.one, Term.bigOmega, Term.lt, Term.fT]
    | cons a xs =>
      cases xs with
      | nil =>
        simp only [DimensionImage.convert, DimensionImage.arguments, DimensionImage.principal_singleton]
        rw [OT2.assemble]
        split <;> simp [Term.bigOmega, Term.lt, Term.fT]
      | cons a' xs => simp only [List.length_cons] at hs; omega

theorem class_below (q : Classes) : Term.lt (classConversion q) Term.bigOmega = true :=
  fixed_outer_below _ _ (Support.CountableSource.representative_outer q)

structure GlobalCertificate : Prop where
  wf : ∀ q : Classes, Term.wf (classConversion q) = true
  order : ∀ q r : Classes,
    ClassLT q r ↔ Term.lt (classConversion q) (classConversion r) = true

end Support.GeneralImageEmbedding

namespace Support.GeneralImageTopPair

open OCF.Jaeger Support.BinaryTranslation Support.TargetArithmetic

universe u

def topPair (n : Nat) (h m : Term) : Term :=
  if m = .zero then
    if h = .zero then .zero else .inacc n (dropOne h)
  else .psi (.inacc n (if h = .zero then .zero else succTerm (dropOne h))) (dropOne m)

theorem inacc_same_lt (n : Nat) (a b : Term) :
    Term.lt (.inacc n a) (.inacc n b) = Term.lt a b := by simp [Term.lt]

theorem inacc_same_lt_psi (n : Nat) (a b c : Term) :
    Term.lt (.inacc n a) (.psi (.inacc n b) c) = Term.lt a b := by simp [Term.lt, Term.fT]

theorem psi_same_lt_inacc (n : Nat) (a b c : Term) :
    Term.lt (.psi (.inacc n a) b) (.inacc n c) = Term.le a c := by simp [Term.lt, Term.fT, Term.le]

theorem psi_same_lt_raw (n : Nat) (a b c d : Term) :
    Term.lt (.psi (.inacc n a) b) (.psi (.inacc n c) d) =
      (Term.lt a c || (decide (a = c) && Term.lt b d) || (Term.lt c a && Term.le a c)) := by
  rw [Term.lt]
  simp [inacc_same_lt, inacc_same_lt_psi, psi_same_lt_inacc]

theorem wf_not_lt_reverse [LargeCardinals.{u}] {a c : Term}
    (ha : Term.wf a = true) (hc : Term.wf c = true) (hac : Term.lt a c = true) :
    Term.lt c a = false := by
  cases hca : Term.lt c a with
  | false => rfl
  | true =>
    have h := lemma_6_1.{u}.2.1 a c a ha hc ha hac hca
    rw [lt_self] at h
    cases h

theorem psi_same_lt [LargeCardinals.{u}] (n : Nat) (a b c d : Term)
    (ha : Term.wf a = true) (hc : Term.wf c = true) :
    Term.lt (.psi (.inacc n a) b) (.psi (.inacc n c) d) =
      (Term.lt a c || (decide (a = c) && Term.lt b d)) := by
  rw [psi_same_lt_raw]
  have hbad : (Term.lt c a && Term.le a c) = false := by
    by_cases he : a = c
    · subst c; simp [lt_self]
    · rw [Term.le]
      simp only [he, decide_false, Bool.false_or]
      cases hac : Term.lt a c with
      | false => simp
      | true => simp [wf_not_lt_reverse ha hc hac]
  rw [hbad, Bool.or_false]

theorem topPair_order [LargeCardinals.{u}] (n : Nat) {h m h' m' : Term}
    (hh : Term.wf h = true) (hm : Term.wf m = true)
    (hh' : Term.wf h' = true) (hm' : Term.wf m' = true) :
    Term.lt (topPair n h m) (topPair n h' m') =
      (Term.lt h h' || (decide (h = h') && Term.lt m m')) := by
  by_cases hm0 : m = .zero <;> by_cases hm'0 : m' = .zero
  · subst m; subst m'
    by_cases hh0 : h = .zero <;> by_cases hh'0 : h' = .zero
    · subst h; subst h'; simp [topPair, Term.lt]
    · subst h; simp [topPair, hh'0, Term.lt, (zero_lt_iff h').mpr hh'0]
    · subst h'; simp [topPair, hh0, Support.CountableTarget.lt_zero]
    · simp only [topPair, hh0, hh'0, ↓reduceIte, inacc_same_lt,
        dropOne_order hh hh' hh0 hh'0, Term.lt, Bool.and_false, Bool.or_false]
  · subst m
    by_cases hh0 : h = .zero <;> by_cases hh'0 : h' = .zero
    · subst h; subst h'; simp [topPair, hm'0, Term.lt, (zero_lt_iff m').mpr hm'0]
    · subst h; simp [topPair, hh'0, hm'0, Term.lt, (zero_lt_iff h').mpr hh'0]
    · subst h'
      simp [topPair, hh0, hm'0, inacc_same_lt_psi, Support.CountableTarget.lt_zero]
    · have hdeq : dropOne h = dropOne h' ↔ h = h' :=
        ⟨dropOne_injective hh hh' hh0 hh'0, congrArg dropOne⟩
      simp only [topPair, hh0, hh'0, hm'0, ↓reduceIte, inacc_same_lt_psi,
        lt_succTerm_eq_le (dropOne_wf hh) (dropOne_wf hh'), Term.le,
        dropOne_order hh hh' hh0 hh'0]
      apply Bool.eq_iff_iff.mpr
      simp [hdeq, (zero_lt_iff m').mpr hm'0, or_comm]
  · subst m'
    by_cases hh0 : h = .zero <;> by_cases hh'0 : h' = .zero
    · subst h; subst h'; simp [topPair, hm0, Support.CountableTarget.lt_zero]
    · subst h
      simp [topPair, hm0, hh'0, psi_same_lt_inacc, Support.OT2.zero_le, (zero_lt_iff h').mpr hh'0]
    · subst h'; simp [topPair, hh0, hm0, Support.CountableTarget.lt_zero]
    · simp only [topPair, hh0, hh'0, hm0, ↓reduceIte, psi_same_lt_inacc,
        succTerm_le_eq_lt (dropOne_wf hh) (dropOne_wf hh'),
        dropOne_order hh hh' hh0 hh'0, Support.CountableTarget.lt_zero,
        Bool.and_false, Bool.or_false]
  · by_cases hh0 : h = .zero <;> by_cases hh'0 : h' = .zero
    · subst h; subst h'
      simp only [topPair, hm0, hm'0, ↓reduceIte, psi_same_lt n _ _ _ _ Term.wf_zero Term.wf_zero,
        lt_self, decide_true, Bool.true_and, Bool.false_or,
        dropOne_order hm hm' hm0 hm'0]
    · subst h
      simp only [topPair, hh'0, hm0, hm'0, ↓reduceIte,
        psi_same_lt n _ _ _ _ Term.wf_zero (succTerm_wf (dropOne_wf hh'))]
      simp [(zero_lt_iff _).mpr (succTerm_ne_zero _), (zero_lt_iff h').mpr hh'0]
    · subst h'
      simp only [topPair, hh0, hm0, hm'0, ↓reduceIte,
        psi_same_lt n _ _ _ _ (succTerm_wf (dropOne_wf hh)) Term.wf_zero]
      simp [Support.CountableTarget.lt_zero, succTerm_ne_zero]
    · have hseq : succTerm (dropOne h) = succTerm (dropOne h') ↔ h = h' :=
        ⟨fun he => dropOne_injective hh hh' hh0 hh'0
            (succTerm_injective (dropOne_wf hh) (dropOne_wf hh') he),
          congrArg (fun a => succTerm (dropOne a))⟩
      simp only [topPair, hh0, hh'0, hm0, hm'0, ↓reduceIte,
        psi_same_lt n _ _ _ _ (succTerm_wf (dropOne_wf hh)) (succTerm_wf (dropOne_wf hh')),
        succTerm_order (dropOne_wf hh) (dropOne_wf hh'),
        dropOne_order hh hh' hh0 hh'0, dropOne_order hm hm' hm0 hm'0]
      simp only [hseq]

theorem topPair_shape (n : Nat) (h m : Term) : topPair n h m = .zero ∨
    (Term.isPrin (topPair n h m) = true ∧ Term.fT (topPair n h m) = n) := by
  by_cases hh0 : h = .zero <;> by_cases hm0 : m = .zero <;>
    simp [topPair, hh0, hm0, Term.isPrin, Term.fT]

theorem topPair_eq_iff [LargeCardinals.{u}] (n : Nat) {h m h' m' : Term}
    (hh : Term.wf h = true) (hm : Term.wf m = true)
    (hh' : Term.wf h' = true) (hm' : Term.wf m' = true) :
    topPair n h m = topPair n h' m' ↔ h = h' ∧ m = m' := by
  constructor
  · intro he
    have hf := topPair_order n hh hm hh' hm'
    have hr := topPair_order n hh' hm' hh hm
    rw [he, lt_self] at hf
    rw [he, lt_self] at hr
    have heh : h = h' := by
      rcases lemma_6_1.{u}.2.2 h h' hh hh' with hl | he | hl
      · rw [hl, Bool.true_or] at hf; cases hf
      · exact he
      · rw [hl, Bool.true_or] at hr; cases hr
    refine ⟨heh, ?_⟩
    subst h'
    simp only [lt_self, decide_true, Bool.true_and, Bool.false_or] at hf hr
    rcases lemma_6_1.{u}.2.2 m m' hm hm' with hl | he | hl
    · rw [hl] at hf; cases hf
    · exact he
    · rw [hl] at hr; cases hr
  · rintro ⟨rfl, rfl⟩; rfl

end Support.GeneralImageTopPair

namespace Support.GeneralImageLayerOrder

open OCF.Jaeger Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageTopPair

universe u

def regular (n : Nat) (a : Term) : Term := .inacc n (succTerm a)

def step (n : Nat) (a c : Term) : Term :=
  if a = .zero then
    if n = 0 then .psi Term.bigOmega c
    else if c = .zero then .zero else .psi (.inacc n .zero) (dropOne c)
  else if c = .zero then a else .psi (regular n a) (dropOne c)

def Above (n : Nat) (a : Term) : Prop := a = .zero ∨ n < Term.fT a

theorem above_principal {n : Nat} {a : Term} (ha : n < Term.fT a) : Term.isPrin a = true := by
  cases a <;> simp_all [Term.fT, Term.isPrin]

theorem succ_principal {a : Term} (ha : Term.isPrin a = true) : succTerm a = .add a Term.one := by
  cases a <;> simp_all [Term.isPrin, succTerm]

theorem regular_wf (n : Nat) {a : Term} (ha : Term.wf a = true) (hp : Term.isPrin a = true) :
    Term.wf (regular n a) = true := by
  apply (Term.wf_inacc_iff n (succTerm a)).mpr
  refine ⟨succTerm_wf ha, ?_⟩
  rw [succ_principal hp]
  simp [Term.fT]

theorem regular_isRT (n : Nat) (a : Term) : Term.isRT (regular n a) = true := by
  simp [regular, Term.isRT, Term.isLimT, succTerm_ne_zero, succTerm_isSucc]

theorem regular_lt_context {n : Nat} {a b : Term}
    (ha : Term.isPrin a = true) (hb : n < Term.fT b) :
    Term.lt (regular n a) b = Term.lt a b := by
  cases b with
  | zero | add => simp [Term.fT] at hb
  | inacc m c =>
    simp only [Term.fT] at hb
    simp [regular, Term.lt, hb, succ_principal ha]
  | psi v c =>
    simp only [Term.fT] at hb
    simp [regular, Term.lt, hb, show ¬ Term.fT v ≤ n by omega, succ_principal ha]

theorem context_lt_regular {n : Nat} {a b : Term}
    (ha : n < Term.fT a) (hb : Term.isPrin b = true) :
    Term.lt a (regular n b) = Term.le a b := by
  have hs := succ_principal hb
  cases a with
  | zero | add => simp [Term.fT] at ha
  | inacc m c =>
    simp only [Term.fT] at ha
    simp only [regular, Term.lt, show ¬m < n by omega, show ¬m = n by omega, ↓reduceIte, hs]
    by_cases he : Term.inacc m c = b <;> simp [Term.le, he, lt_self]
  | psi v c =>
    simp only [Term.fT] at ha
    simp only [regular, Term.lt, ha, show ¬ Term.fT v ≤ n by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.or_false, hs]
    simp only [reduceCtorEq, decide_false, Bool.false_or]
    by_cases he : Term.psi v c = b <;> simp [Term.le, he, lt_self]

theorem wf_le_iff_reverse_false [LargeCardinals.{u}] {a b : Term}
    (ha : Term.wf a = true) (hb : Term.wf b = true) :
    Term.le a b = true ↔ Term.lt b a = false := by
  simp only [Term.le, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (rfl | h)
    · exact lt_self a
    · exact wf_not_lt_reverse ha hb h
  · intro h
    rcases lemma_6_1.{u}.2.2 a b ha hb with hl | he | hl
    · exact Or.inr hl
    · exact Or.inl he
    · rw [h] at hl; cases hl

theorem wf_lt_iff_reverse_false_of_ne [LargeCardinals.{u}] {a b : Term}
    (ha : Term.wf a = true) (hb : Term.wf b = true) (hne : a ≠ b) :
    Term.lt a b = true ↔ Term.lt b a = false := by
  constructor
  · exact wf_not_lt_reverse ha hb
  · intro h
    rcases lemma_6_1.{u}.2.2 a b ha hb with hl | he | hl
    · exact hl
    · exact False.elim (hne he)
    · rw [h] at hl; cases hl

theorem psi_regular_lt_context [LargeCardinals.{u}] {n : Nat} {a b : Term} (x : Term)
    (ha : Term.wf a = true) (hap : Term.isPrin a = true)
    (hb : Term.wf b = true) (hbf : n < Term.fT b) :
    Term.lt (.psi (regular n a) x) b = Term.lt a b := by
  cases b with
  | zero | add => simp [Term.fT] at hbf
  | inacc m c =>
    simp only [Term.fT] at hbf
    have hr := regular_lt_context hap (show n < Term.fT (.inacc m c) from hbf)
    simp only [Term.lt, regular, Term.fT, show ¬m < n by omega, show n ≤ m by omega,
      decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.false_or,
      Term.inacc.injEq, show ¬n = m by omega, false_and, decide_false]
    simpa only [regular, Term.lt, hbf, ↓reduceIte] using hr
  | psi v c =>
    have hv := (Term.wf_psi_iff v c).mp hb
    cases v with
    | zero | add | psi => simp [Term.isRT] at hv
    | inacc m d =>
      simp only [Term.fT] at hbf
      have hvf : n < Term.fT (.inacc m d) := hbf
      have hrb := regular_lt_context hap (show n < Term.fT (.psi (.inacc m d) c) from hbf)
      have hrv := regular_lt_context hap hvf
      have hvr := context_lt_regular hvf hap
      have hpv : Term.lt (.psi (regular n a) x) (.inacc m d) = Term.lt a (.inacc m d) := by
        simp only [Term.lt, regular, Term.fT, show ¬m < n by omega, show n ≤ m by omega,
          decide_false, decide_true, Bool.false_and, Bool.true_and, Bool.false_or,
          Term.inacc.injEq, show ¬n = m by omega, false_and, decide_false]
        simpa only [regular, Term.lt, hbf, ↓reduceIte] using hrv
      have hne : regular n a ≠ .inacc m d := by
        intro he
        have hf := congrArg Term.fT he
        simp [regular, Term.fT] at hf
        omega
      rw [Term.lt, hrv, hrb, hvr, hpv]
      simp only [hne, decide_false, Bool.false_and, Bool.or_false]
      have hbad : (Term.le (.inacc m d) a && Term.lt a (.inacc m d)) = false := by
        cases h : Term.lt a (.inacc m d) with
        | false => simp
        | true =>
          have hle : Term.le (.inacc m d) a = false := by
            cases hl : Term.le (.inacc m d) a with
            | false => rfl
            | true =>
              have bad := (wf_le_iff_reverse_false hv.2.1 ha).mp hl
              rw [h] at bad
              cases bad
          simp [hle]
      rw [hbad, Bool.or_false]
      cases hab : Term.lt a (.psi (.inacc m d) c) with
      | false => simp
      | true =>
        have hβv : Term.lt (.psi (.inacc m d) c) (.inacc m d) = true := by simp [Term.lt, Term.fT]
        have hav := lemma_6_1.{u}.2.1 a (.psi (.inacc m d) c) (.inacc m d) ha hb hv.2.1 hab hβv
        simp [hav]

theorem context_lt_psi_regular [LargeCardinals.{u}] {n : Nat} {a b : Term} (x : Term)
    (ha : Term.wf a = true) (hap : Term.isPrin a = true)
    (hb : Term.wf b = true) (hbf : n < Term.fT b)
    (hw : Term.wf (.psi (regular n a) x) = true) :
    Term.lt b (.psi (regular n a) x) = Term.le b a := by
  have hne : b ≠ .psi (regular n a) x := by
    intro he
    have hf := congrArg Term.fT he
    simp [regular, Term.fT] at hf
    omega
  apply Bool.eq_iff_iff.mpr
  rw [wf_lt_iff_reverse_false_of_ne hb hw hne,
    psi_regular_lt_context x ha hap hb hbf, wf_le_iff_reverse_false hb ha]

theorem step_context_wf {n : Nat} {a c : Term} (ha : Above n a)
    (hw : Term.wf (step n a c) = true) : Term.wf a = true := by
  by_cases ha0 : a = .zero
  · rw [ha0]; rfl
  · have hap := above_principal (ha.resolve_left ha0)
    by_cases hc0 : c = .zero
    · simpa only [step, ha0, hc0, ↓reduceIte] using hw
    · simp only [step, ha0, hc0, ↓reduceIte] at hw
      have hu := ((Term.wf_psi_iff _ _).mp hw).2.1
      have hs := ((Term.wf_inacc_iff _ _).mp hu).1
      rw [succ_principal hap] at hs
      exact ((Term.wf_add_iff _ _).mp hs).2.1

theorem step_shape {n : Nat} {a : Term} (c : Term) (ha : Above n a) :
    step n a c = .zero ∨ (Term.isPrin (step n a c) = true ∧ n ≤ Term.fT (step n a c)) := by
  by_cases ha0 : a = .zero
  · subst a
    by_cases hn0 : n = 0 <;> by_cases hc0 : c = .zero <;>
      simp [step, hn0, hc0, Term.isPrin, Term.fT, Term.bigOmega]
  · have hft := ha.resolve_left ha0
    have hap := above_principal hft
    by_cases hc0 : c = .zero
    · simp only [step, ha0, hc0, ↓reduceIte]
      exact Or.inr ⟨hap, Nat.le_of_lt hft⟩
    · simp only [step, ha0, hc0, ↓reduceIte]
      exact Or.inr ⟨rfl, Nat.le_refl _⟩

theorem zero_step_order (n : Nat) {c d : Term} (hc : Term.wf c = true) (hd : Term.wf d = true) :
    Term.lt (step n .zero c) (step n .zero d) = Term.lt c d := by
  by_cases hn0 : n = 0
  · subst n
    simp only [step, ↓reduceIte, Support.Unary.psi_omega_lt]
  · by_cases hc0 : c = .zero <;> by_cases hd0 : d = .zero
    · subst c; subst d; simp [step, hn0, Term.lt]
    · subst c; simp [step, hn0, hd0, Term.lt, (zero_lt_iff d).mpr hd0]
    · subst d; simp [step, hn0, hc0, Support.CountableTarget.lt_zero]
    · simp only [step, hn0, hc0, hd0, ↓reduceIte, psi_same_lt_raw,
        lt_self, decide_true, Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false,
        dropOne_order hc hd hc0 hd0]

theorem zero_step_lt_context {n : Nat} (c : Term) {b : Term}
    (hb : Term.wf b = true) (hbf : n < Term.fT b) :
    Term.lt (step n .zero c) b = true := by
  have hpos : b ≠ .zero := by intro he; rw [he, Term.fT] at hbf; omega
  have hp : ∀ x : Term, Term.lt (.psi (.inacc n .zero) x) b = true := by
    intro x
    cases b with
    | zero | add => simp [Term.fT] at hbf
    | inacc m d =>
      simp only [Term.fT] at hbf
      simp [Term.lt, Term.fT, hbf, show ¬m < n by omega, show n ≤ m by omega]
    | psi v d =>
      have hv := (Term.wf_psi_iff v d).mp hb
      cases v with
      | zero | add | psi => simp [Term.isRT] at hv
      | inacc m e =>
        simp only [Term.fT] at hbf
        simp [Term.lt, Term.fT, hbf, show ¬m < n by omega, show ¬m ≤ n by omega]
  by_cases hn0 : n = 0
  · subst n
    simpa only [step, ↓reduceIte, Term.bigOmega] using hp c
  · by_cases hc0 : c = .zero
    · simp only [step, hn0, hc0, ↓reduceIte]
      exact (zero_lt_iff b).mpr hpos
    · simpa only [step, hn0, hc0, ↓reduceIte] using hp (dropOne c)

theorem zero_step_lt_positive_step {n : Nat} (c d : Term) {b : Term}
    (hb : Term.wf b = true) (hbf : n < Term.fT b) :
    Term.lt (step n .zero c) (step n b d) = true := by
  have hb0 : b ≠ .zero := by intro he; rw [he, Term.fT] at hbf; omega
  by_cases hd0 : d = .zero
  · simp only [step, hb0, hd0, ↓reduceIte]
    exact zero_step_lt_context c hb hbf
  · have hp : ∀ x : Term,
        Term.lt (.psi (.inacc n .zero) x) (.psi (regular n b) (dropOne d)) = true := by
      intro x
      rw [regular, psi_same_lt_raw]
      simp [(zero_lt_iff _).mpr (succTerm_ne_zero _)]
    by_cases hn0 : n = 0
    · subst n
      simpa only [step, hb0, hd0, ↓reduceIte, Term.bigOmega] using hp c
    · by_cases hc0 : c = .zero
      · simp [step, hb0, hd0, hn0, hc0, Term.lt]
      · simpa only [step, hb0, hd0, hn0, hc0, ↓reduceIte] using hp (dropOne c)

theorem step_order [LargeCardinals.{u}] {n : Nat} {a b c d : Term}
    (haa : Above n a) (hba : Above n b)
    (ha : Term.wf a = true) (hb : Term.wf b = true)
    (hc : Term.wf c = true) (hd : Term.wf d = true)
    (hwac : Term.wf (step n a c) = true) (hwbd : Term.wf (step n b d) = true) :
    Term.lt (step n a c) (step n b d) =
      (Term.lt a b || (decide (a = b) && Term.lt c d)) := by
  by_cases ha0 : a = .zero <;> by_cases hb0 : b = .zero
  · subst a; subst b
    simp only [zero_step_order n hc hd, lt_self, decide_true, Bool.true_and, Bool.false_or]
  · subst a
    have hbf := hba.resolve_left hb0
    rw [zero_step_lt_positive_step c d hb hbf, (zero_lt_iff b).mpr hb0, Bool.true_or]
  · subst b
    have haf := haa.resolve_left ha0
    have hforward := zero_step_lt_positive_step d c ha haf
    have hreverse := wf_not_lt_reverse hwbd hwac hforward
    simp only [hreverse, Support.CountableTarget.lt_zero, ha0, decide_false, Bool.false_and, Bool.false_or]
  · have haf := haa.resolve_left ha0
    have hbf := hba.resolve_left hb0
    have hap := above_principal haf
    have hbp := above_principal hbf
    by_cases hc0 : c = .zero <;> by_cases hd0 : d = .zero
    · subst c; subst d
      simp [step, ha0, hb0, Term.lt]
    · subst c
      have hw : Term.wf (.psi (regular n b) (dropOne d)) = true := by
        simpa only [step, hb0, hd0, ↓reduceIte] using hwbd
      have hcompare := context_lt_psi_regular (dropOne d) hb hbp ha haf hw
      simp only [step, ha0, hb0, hd0, ↓reduceIte, hcompare,
        (zero_lt_iff d).mpr hd0, Bool.and_true, Term.le]
      exact Bool.or_comm _ _
    · subst d
      simp only [step, ha0, hb0, hc0, ↓reduceIte,
        psi_regular_lt_context (dropOne c) ha hap hb hbf,
        Support.CountableTarget.lt_zero, Bool.and_false, Bool.or_false]
    · have hseq : succTerm a = succTerm b ↔ a = b :=
        ⟨succTerm_injective ha hb, congrArg succTerm⟩
      simp only [step, ha0, hb0, hc0, hd0, ↓reduceIte, regular,
        psi_same_lt n _ _ _ _ (succTerm_wf ha) (succTerm_wf hb),
        succTerm_order ha hb, dropOne_order hc hd hc0 hd0, hseq]

theorem step_injective [LargeCardinals.{u}] {n : Nat} {a b c d : Term}
    (haa : Above n a) (hba : Above n b)
    (ha : Term.wf a = true) (hb : Term.wf b = true)
    (hc : Term.wf c = true) (hd : Term.wf d = true)
    (hwac : Term.wf (step n a c) = true) (hwbd : Term.wf (step n b d) = true)
    (he : step n a c = step n b d) : a = b ∧ c = d := by
  have hf := step_order haa hba ha hb hc hd hwac hwbd
  have hr := step_order hba haa hb ha hd hc hwbd hwac
  rw [he, lt_self] at hf
  rw [he, lt_self] at hr
  have hab : a = b := by
    rcases lemma_6_1.{u}.2.2 a b ha hb with hl | he | hl
    · rw [hl, Bool.true_or] at hf; cases hf
    · exact he
    · rw [hl, Bool.true_or] at hr; cases hr
  refine ⟨hab, ?_⟩
  subst b
  simp only [lt_self, decide_true, Bool.true_and, Bool.false_or] at hf hr
  rcases lemma_6_1.{u}.2.2 c d hc hd with hl | he | hl
  · rw [hl] at hf; cases hf
  · exact he
  · rw [hl] at hr; cases hr

theorem step_eq_iff [LargeCardinals.{u}] {n : Nat} {a b c d : Term}
    (haa : Above n a) (hba : Above n b)
    (ha : Term.wf a = true) (hb : Term.wf b = true)
    (hc : Term.wf c = true) (hd : Term.wf d = true)
    (hwac : Term.wf (step n a c) = true) (hwbd : Term.wf (step n b d) = true) :
    step n a c = step n b d ↔ a = b ∧ c = d := by
  constructor
  · exact step_injective haa hba ha hb hc hd hwac hwbd
  · rintro ⟨rfl, rfl⟩; rfl

end Support.GeneralImageLayerOrder

namespace Support.GeneralImagePrincipalOrder

open OCF.Jaeger Support.DimensionImage Support.GeneralImageTopPair
open Support.GeneralImageLayerOrder

universe u

def Context (k : Nat) (a : Term) : Prop := a = .zero ∨ (Term.isPrin a = true ∧ k ≤ Term.fT a)

def lexArgs : Nat → List Term → List Term → Bool
  | 0, _, _ => false
  | k + 1, xs, ys =>
    let a := xs[k]?.getD .zero
    let b := ys[k]?.getD .zero
    Term.lt a b || (decide (a = b) && lexArgs k xs ys)

theorem context_above {k : Nat} {a : Term} (ha : Context (k + 1) a) : Above k a := by
  rcases ha with ha | ⟨_, ha⟩
  · exact Or.inl ha
  · exact Or.inr (by omega)

theorem lower_succ (k : Nat) (xs : List Term) (a : Term) :
    lower (k + 1) xs a = lower k xs (step k a (xs[k]?.getD .zero)) := rfl

theorem lower_context_wf (k : Nat) (xs : List Term) (a : Term)
    (ha : Context k a) (hw : Term.wf (lower k xs a) = true) : Term.wf a = true := by
  induction k generalizing a with
  | zero => exact hw
  | succ k ih =>
    rw [lower_succ] at hw
    have habove := context_above ha
    have hshape : Context k (step k a (xs[k]?.getD .zero)) := step_shape _ habove
    have hwa := ih _ hshape hw
    exact step_context_wf habove hwa

theorem lower_order [LargeCardinals.{u}] (k : Nat) (xs ys : List Term) (a b : Term)
    (ha : Context k a) (hb : Context k b)
    (hxs : ∀ i, i < k → Term.wf (xs[i]?.getD .zero) = true)
    (hys : ∀ i, i < k → Term.wf (ys[i]?.getD .zero) = true)
    (hwx : Term.wf (lower k xs a) = true) (hwy : Term.wf (lower k ys b) = true) :
    Term.lt (lower k xs a) (lower k ys b) =
      (Term.lt a b || (decide (a = b) && lexArgs k xs ys)) := by
  induction k generalizing a b with
  | zero => simp [lower, lexArgs]
  | succ k ih =>
    rw [lower_succ] at hwx hwy
    rw [lower_succ, lower_succ]
    have haa := context_above ha
    have hba := context_above hb
    have has : Context k (step k a (xs[k]?.getD .zero)) := step_shape _ haa
    have hbs : Context k (step k b (ys[k]?.getD .zero)) := step_shape _ hba
    have hwas := lower_context_wf k xs _ has hwx
    have hwbs := lower_context_wf k ys _ hbs hwy
    have hwa := step_context_wf haa hwas
    have hwb := step_context_wf hba hwbs
    have hwc := hxs k (by omega)
    have hwd := hys k (by omega)
    rw [ih _ _ has hbs (fun i hi => hxs i (by omega)) (fun i hi => hys i (by omega)) hwx hwy,
      step_order haa hba hwa hwb hwc hwd hwas hwbs]
    simp only [step_eq_iff haa hba hwa hwb hwc hwd hwas hwbs, lexArgs]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    simp only [and_or_left, and_assoc, or_assoc]

theorem principal_as_layers (k : Nat) (xs : List Term) :
    principal (k + 3) xs = lower (k + 1) xs
      (topPair (k + 1) (xs[k + 2]?.getD .zero) (xs[k + 1]?.getD .zero)) := by
  simp [principal, topPair]

theorem principal_order [LargeCardinals.{u}] (k : Nat) (xs ys : List Term)
    (hxs : ∀ i, i < k + 3 → Term.wf (xs[i]?.getD .zero) = true)
    (hys : ∀ i, i < k + 3 → Term.wf (ys[i]?.getD .zero) = true)
    (hwx : Term.wf (principal (k + 3) xs) = true)
    (hwy : Term.wf (principal (k + 3) ys) = true) :
    Term.lt (principal (k + 3) xs) (principal (k + 3) ys) = lexArgs (k + 3) xs ys := by
  simp only [principal_as_layers] at hwx hwy ⊢
  have hshape : ∀ zs : List Term, Context (k + 1)
      (topPair (k + 1) (zs[k + 2]?.getD .zero) (zs[k + 1]?.getD .zero)) := by
    intro zs
    rcases topPair_shape (k + 1) (zs[k + 2]?.getD .zero) (zs[k + 1]?.getD .zero) with hz | ⟨hp, hf⟩
    · exact Or.inl hz
    · exact Or.inr ⟨hp, by omega⟩
  rw [lower_order (k + 1) xs ys _ _ (hshape xs) (hshape ys)
      (fun i hi => hxs i (by omega)) (fun i hi => hys i (by omega)) hwx hwy,
    topPair_order (k + 1) (hxs (k + 2) (by omega)) (hxs (k + 1) (by omega))
      (hys (k + 2) (by omega)) (hys (k + 1) (by omega))]
  simp only [topPair_eq_iff (k + 1) (hxs (k + 2) (by omega)) (hxs (k + 1) (by omega))
      (hys (k + 2) (by omega)) (hys (k + 1) (by omega)), lexArgs]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  simp only [and_or_left, and_assoc, or_assoc]

end Support.GeneralImagePrincipalOrder

namespace Support.GeneralImageEmbedding

open new OCF.Jaeger Support.OTQuotient Support.CodeReification

def fixedWitness (d : Nat) (q : Classes) (hw : width (representative q) ≤ d) : T.OT d :=
  ⟨reify d (representative q), by
    obtain ⟨⟨lam, s⟩, hs⟩ := exists_rep q
    have hc : code s.val = representative q := congrArg representative hs
    have hs' := generated_reify lam d s (by rw [hc]; exact hw)
    simpa only [hc] using hs'⟩

theorem fixedWitness_code (d : Nat) (q : Classes) (hw : width (representative q) ≤ d) :
    code (fixedWitness d q hw).val = representative q :=
  code_reify_normal d (representative q) (representative_normal q) hw

theorem class_fixed_value (d : Nat) (q : Classes) (hd : ambient (representative q) = d) :
    classConversion q = DimensionImage.convert d
      (code (fixedWitness d q (by rw [← hd]; exact Nat.le_max_right 3 _)).val) := by
  rw [fixedWitness_code]
  exact congrArg (fun k => DimensionImage.convert k (representative q)) hd

theorem global_wf_of_fixed
    (h : ∀ d, 3 ≤ d → ∀ s : T.OT d, Term.wf (DimensionImage.convert d (code s.val)) = true) :
    ∀ q : Classes, Term.wf (classConversion q) = true := by
  intro q
  let d := ambient (representative q)
  rw [class_fixed_value d q rfl]
  exact h d (Nat.le_max_left 3 _) _

theorem same_ambient_order_of_fixed (d : Nat) (q r : Classes)
    (hq : ambient (representative q) = d) (hr : ambient (representative r) = d)
    (h : ∀ s t : T.OT d, T.lt s.val t.val ↔
      Term.lt (DimensionImage.convert d (code s.val)) (DimensionImage.convert d (code t.val)) = true) :
    ClassLT q r ↔ Term.lt (classConversion q) (classConversion r) = true := by
  rw [class_fixed_value d q hq, class_fixed_value d r hr]
  let s := fixedWitness d q (by rw [← hq]; exact Nat.le_max_right 3 _)
  let t := fixedWitness d r (by rw [← hr]; exact Nat.le_max_right 3 _)
  have hcq := fixedWitness_code d q (by rw [← hq]; exact Nat.le_max_right 3 _)
  have hcr := fixedWitness_code d r (by rw [← hr]; exact Nat.le_max_right 3 _)
  have hsource : compareCode (representative q) (representative r) = compareT s.val t.val := by
    calc
      compareCode (representative q) (representative r) =
          compareCode (code s.val) (code t.val) := by
            congr 1
            · exact hcq.symm
            · exact hcr.symm
      _ = compareT s.val t.val := compareCode_code _ _
  change compareCode (representative q) (representative r) = .lt ↔ _
  rw [hsource]
  exact h s t

end Support.GeneralImageEmbedding

namespace Support.GeneralImageRawOrder

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImagePrincipalOrder Support.CodeReification

universe u

def RecursiveWF (d : Nat) {lam : Nat} : new.T lam → Prop
  | .Z => True
  | .P xs b => (∀ i, RecursiveWF d (xs.idx i)) ∧ RecursiveWF d b ∧
      Term.wf (convert d (code (.P xs b))) = true
termination_by s => new.T.size s
decreasing_by
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem RecursiveWF.wf {d lam : Nat} {s : new.T lam} (hs : RecursiveWF d s) :
    Term.wf (convert d (code s)) = true := by
  cases s with
  | Z => simp only [code, convert, Term.wf]
  | P => rw [RecursiveWF] at hs; exact hs.2.2

theorem trim_getD (xs : List Code) (i : Nat) :
    (trim xs)[i]?.getD .zero = xs[i]?.getD .zero := by
  induction xs generalizing i with
  | nil => simp [trim]
  | cons x xs ih =>
    cases ht : trim xs with
    | nil =>
      have hz : ∀ j : Nat, xs[j]?.getD Code.zero = Code.zero := by
        intro j
        simpa only [ht, List.getElem?_nil, Option.getD_none] using (ih j).symm
      cases x <;> cases i <;> simp [trim, ht, Code.isZero, hz]
    | cons y ys =>
      cases i with
      | zero => simp [trim, ht]
      | succ i => simpa only [trim, ht, List.getElem?_cons_succ] using ih i

theorem arguments_getD (d : Nat) (xs : List Code) (i : Nat) :
    (arguments d xs)[i]?.getD .zero = convert d (xs[i]?.getD .zero) := by
  induction xs generalizing i with
  | nil => simp [arguments, convert]
  | cons x xs ih => cases i <;> simp [arguments, ih]

theorem codes_getD {lam m : Nat} (xs : Vec (new.T lam) m) (i : Fin m) :
    (codes xs)[i.val]?.getD .zero = code (xs.idx i) := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    by_cases hi : i.val < m
    · simpa [codes, List.getElem?_append, codes_length, Vec.idx, hi] using ih ⟨i.val, hi⟩
    · have he : i.val = m := by have := i.isLt; omega
      simp [codes, codes_length, Vec.idx, he]

theorem converted_coordinate {d lam m : Nat} (xs : Vec (new.T lam) m) (i : Fin m) :
    (arguments d (trim (codes xs)))[i.val]?.getD .zero = convert d (code (xs.idx i)) := by
  rw [arguments_getD, trim_getD, codes_getD]

theorem assemble_wf_left {p t : Term} (h : Term.wf (OT2.assemble p t) = true) :
    Term.wf p = true := by
  unfold OT2.assemble at h
  split at h
  · exact h
  · exact ((Term.wf_add_iff _ _).mp h).2.1

theorem principal_wf {d lam : Nat} {xs : Vec (new.T lam) lam} {b : new.T lam}
    (hs : RecursiveWF d (.P xs b)) :
    Term.wf (principal d (arguments d (trim (codes xs)))) = true := by
  rw [RecursiveWF] at hs
  apply assemble_wf_left
  simpa only [code, convert] using hs.2.2

theorem lower_congr (k : Nat) (xs ys : List Term) (a : Term)
    (h : ∀ i, i < k → xs[i]?.getD .zero = ys[i]?.getD .zero) :
    lower k xs a = lower k ys a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [lower_succ, h k (by omega)]
    exact ih _ (fun i hi => h i (by omega))

theorem principal_congr (k : Nat) (xs ys : List Term)
    (h : ∀ i, i < k + 3 → xs[i]?.getD .zero = ys[i]?.getD .zero) :
    principal (k + 3) xs = principal (k + 3) ys := by
  simp only [principal_as_layers, h (k + 2) (by omega), h (k + 1) (by omega)]
  exact lower_congr (k + 1) xs ys _ (fun i hi => h i (by omega))

theorem lex_equal_of_false [LargeCardinals.{u}] (k : Nat) (xs ys : List Term)
    (hxs : ∀ i, i < k → Term.wf (xs[i]?.getD .zero) = true)
    (hys : ∀ i, i < k → Term.wf (ys[i]?.getD .zero) = true)
    (hf : lexArgs k xs ys = false) (hr : lexArgs k ys xs = false) :
    ∀ i, i < k → xs[i]?.getD .zero = ys[i]?.getD .zero := by
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    have he : xs[k]?.getD .zero = ys[k]?.getD .zero := by
      rcases lemma_6_1.{u}.2.2 _ _ (hxs k (by omega)) (hys k (by omega)) with hl | he | hl
      · simp [lexArgs, hl] at hf
      · exact he
      · simp [lexArgs, hl] at hr
    have hf' : lexArgs k xs ys = false := by simpa [lexArgs, he, Support.TargetArithmetic.lt_self] using hf
    have hr' : lexArgs k ys xs = false := by simpa [lexArgs, he, Support.TargetArithmetic.lt_self] using hr
    intro i hi
    by_cases hik : i < k
    · exact ih (fun j hj => hxs j (by omega)) (fun j hj => hys j (by omega)) hf' hr' i hik
    · have : i = k := by omega
      subst i; exact he

theorem principal_eq_iff [LargeCardinals.{u}] (k : Nat) (xs ys : List Term)
    (hxs : ∀ i, i < k + 3 → Term.wf (xs[i]?.getD .zero) = true)
    (hys : ∀ i, i < k + 3 → Term.wf (ys[i]?.getD .zero) = true)
    (hwx : Term.wf (principal (k + 3) xs) = true)
    (hwy : Term.wf (principal (k + 3) ys) = true) :
    principal (k + 3) xs = principal (k + 3) ys ↔
      ∀ i, i < k + 3 → xs[i]?.getD .zero = ys[i]?.getD .zero := by
  constructor
  · intro he
    have hf := principal_order k xs ys hxs hys hwx hwy
    have hr := principal_order k ys xs hys hxs hwy hwx
    rw [he, Support.TargetArithmetic.lt_self] at hf hr
    exact lex_equal_of_false (k + 3) xs ys hxs hys hf.symm hr.symm
  · exact principal_congr k xs ys

theorem convert_injective [LargeCardinals.{u}] (k : Nat) (s t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t)
    (he : convert (k + 3) (code s) = convert (k + 3) (code t)) : s = t := by
  cases hS : s with
  | Z =>
    rw [hS] at he
    simp only [code, convert] at he
    have hz := (Support.GeneralImageEmbedding.fixed_convert_zero_iff _ (code t)).mp he.symm
    exact (code_injective hz).symm
  | P xs b =>
    rw [hS] at hs he
    cases t with
    | Z =>
      have hz := (Support.GeneralImageEmbedding.fixed_convert_zero_iff (k + 3)
        (code (.P xs b))).mp (he.trans (by simp only [code, convert]))
      cases hz
    | P ys c =>
      have hs' := hs
      have ht' := ht
      rw [RecursiveWF] at hs ht
      simp only [code, convert] at he
      have hh := OT2.assemble_injective (Support.GeneralImageEmbedding.principal_isPrin _ _)
        (Support.GeneralImageEmbedding.principal_isPrin _ _) he
      have ha : ∀ i, i < k + 3 → Term.wf
          ((arguments (k + 3) (trim (codes xs)))[i]?.getD .zero) = true := by
        intro i hi
        rw [converted_coordinate xs ⟨i, hi⟩]
        exact (hs.1 ⟨i, hi⟩).wf
      have hb : ∀ i, i < k + 3 → Term.wf
          ((arguments (k + 3) (trim (codes ys)))[i]?.getD .zero) = true := by
        intro i hi
        rw [converted_coordinate ys ⟨i, hi⟩]
        exact (ht.1 ⟨i, hi⟩).wf
      have hi := (principal_eq_iff k _ _ ha hb (principal_wf hs') (principal_wf ht')).mp hh.1
      have hv : xs = ys := by
        apply vec_ext
        intro i
        have hc := hi i.val i.isLt
        simp only [converted_coordinate] at hc
        exact convert_injective k _ _ (hs.1 i) (ht.1 i) hc
      have ht := convert_injective k b c hs.2.1 ht.2.1 hh.2
      rw [hv, ht]
termination_by new.T.size s
decreasing_by
  all_goals simp only [hS]
  all_goals first | exact new.T.idx_size_lt_P _ _ _ | exact new.T.add_size_lt_P _ _

theorem principal_source_eq_iff [LargeCardinals.{u}] (k : Nat)
    (xs ys : Vec (new.T (k + 3)) (k + 3)) (b c : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs b)) (ht : RecursiveWF (k + 3) (.P ys c)) :
    principal (k + 3) (arguments (k + 3) (trim (codes xs))) =
      principal (k + 3) (arguments (k + 3) (trim (codes ys))) ↔ xs = ys := by
  constructor
  · intro he
    have hs0 := hs
    have ht0 := ht
    rw [RecursiveWF] at hs ht
    have hc := (principal_eq_iff k _ _
      (by intro i hi; rw [converted_coordinate xs ⟨i, hi⟩]; exact (hs.1 ⟨i, hi⟩).wf)
      (by intro i hi; rw [converted_coordinate ys ⟨i, hi⟩]; exact (ht.1 ⟨i, hi⟩).wf)
      (principal_wf hs0) (principal_wf ht0)).mp he
    apply vec_ext
    intro i
    have he := hc i.val i.isLt
    simp only [converted_coordinate] at he
    exact convert_injective k _ _ (hs.1 i) (ht.1 i) he
  · rintro rfl; rfl

theorem vector_lex {lam m : Nat} (xs ys : Vec (new.T lam) m) (as bs : List Term)
    (hlt : ∀ i : Fin m, Term.lt (as[i.val]?.getD .zero) (bs[i.val]?.getD .zero) =
      decide (new.T.lt (xs.idx i) (ys.idx i)))
    (heq : ∀ i : Fin m, as[i.val]?.getD .zero = bs[i.val]?.getD .zero ↔ xs.idx i = ys.idx i) :
    lexArgs m as bs = decide (Vec.lt xs ys) := by
  induction xs with
  | nil => cases ys; rfl
  | snoc m xs x ih =>
    cases ys with
    | snoc _ ys y =>
      have hlast := hlt (Fin.last m)
      have elast := heq (Fin.last m)
      simp only [vec_snoc_idx_last, Fin.val_last] at hlast elast
      have hrest := ih ys (fun i => by simpa only [vec_snoc_idx_cast, Fin.val_castSucc] using hlt i.castSucc)
        (fun i => by simpa only [vec_snoc_idx_cast, Fin.val_castSucc] using heq i.castSucc)
      cases hc : compareT x y with
      | lt => simp [lexArgs, hlast, elast, hrest, Vec.lt, new.T.lt, compareVec, hc]
      | gt =>
        have hne : x ≠ y := by intro he; subst y; rw [T_refl] at hc; cases hc
        simp [lexArgs, hlast, elast, hrest, Vec.lt, new.T.lt, compareVec, hc, hne]
      | eq =>
        have he := T_eq_sound x y hc
        apply Bool.eq_iff_iff.mpr
        simp [lexArgs, hlast, elast, hrest, Vec.lt, new.T.lt, compareVec, he, T_refl]
        exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩

theorem convert_lt [LargeCardinals.{u}] (k : Nat) (s t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t) :
    Term.lt (convert (k + 3) (code s)) (convert (k + 3) (code t)) =
      decide (new.T.lt s t) := by
  cases hS : s with
  | Z =>
    cases t with
    | Z => simp [code, convert, Term.lt, new.T.lt, compareT]
    | P ys c =>
      have hne : convert (k + 3) (code (.P ys c)) ≠ .zero := by
        intro hz
        have hc := (Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp hz
        cases hc
      rw [show convert (k + 3) (code (.Z : new.T (k + 3))) = Term.zero by simp [code, convert],
        (Support.TargetArithmetic.zero_lt_iff _).mpr hne]
      rfl
  | P xs b =>
    cases hT : t with
    | Z =>
      simp [code, convert, Support.CountableTarget.lt_zero, new.T.lt, compareT]
    | P ys c =>
      simp only [hS, hT] at hs ht
      have hs0 := hs
      have ht0 := ht
      rw [RecursiveWF] at hs ht
      have ha : ∀ i, i < k + 3 → Term.wf
          ((arguments (k + 3) (trim (codes xs)))[i]?.getD .zero) = true := by
        intro i hi
        rw [converted_coordinate xs ⟨i, hi⟩]
        exact (hs.1 ⟨i, hi⟩).wf
      have hb : ∀ i, i < k + 3 → Term.wf
          ((arguments (k + 3) (trim (codes ys)))[i]?.getD .zero) = true := by
        intro i hi
        rw [converted_coordinate ys ⟨i, hi⟩]
        exact (ht.1 ⟨i, hi⟩).wf
      have hp := principal_order k _ _ ha hb (principal_wf hs0) (principal_wf ht0)
      have hlex := vector_lex xs ys (arguments (k + 3) (trim (codes xs)))
        (arguments (k + 3) (trim (codes ys)))
        (fun i => by
          simp only [converted_coordinate]
          exact convert_lt k _ _ (hs.1 i) (ht.1 i))
        (fun i => by
          simp only [converted_coordinate]
          exact ⟨convert_injective k _ _ (hs.1 i) (ht.1 i), fun h => congrArg (fun z => convert (k + 3) (code z)) h⟩)
      rw [hlex] at hp
      have heq := principal_source_eq_iff k xs ys b c hs0 ht0
      simp only [code, convert]
      rw [OT2.assemble_lt (Support.GeneralImageEmbedding.principal_isPrin _ _)
        (Support.GeneralImageEmbedding.principal_isPrin _ _)]
      split
      · rename_i he
        have hv := heq.mp he
        subst ys
        rw [convert_lt k b c hs.2.1 ht.2.1]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, new.T.lt, compareT, Vec_refl]
        exact ⟨of_decide_eq_true, fun h => decide_eq_true h⟩
      · rename_i he
        rw [hp]
        have hv : xs ≠ ys := fun h => he (heq.mpr h)
        apply Bool.eq_iff_iff.mpr
        have hcmp : new.T.lt (.P xs b) (.P ys c) ↔ Vec.lt xs ys := by
          simp only [new.T.lt, compareT, Vec.lt]
          cases hc : compareVec xs ys with
          | lt | gt => rfl
          | eq => exact False.elim (hv (Vec_eq_sound xs ys hc))
        exact ⟨fun h => decide_eq_true (hcmp.mpr (of_decide_eq_true h)),
          fun h => decide_eq_true (hcmp.mp (of_decide_eq_true h))⟩
termination_by new.T.size s + new.T.size t
decreasing_by
  all_goals simp only [hS, hT, new.T.size]
  all_goals first
    | (have hi := Vec.idx_size_lt xs i; have hj := Vec.idx_size_lt ys i; omega)
    | omega

theorem convert_order [LargeCardinals.{u}] (k : Nat) (s t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (ht : RecursiveWF (k + 3) t) :
    new.T.lt s t ↔ Term.lt (convert (k + 3) (code s)) (convert (k + 3) (code t)) = true := by
  rw [convert_lt k s t hs ht, decide_eq_true_eq]

end Support.GeneralImageRawOrder

namespace Support.GeneralImageCoefficients

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageTopPair Support.GeneralImageLayerOrder
open Support.GeneralImagePrincipalOrder Support.GeneralImageRawOrder

universe u

inductive Subterm {lam : Nat} : new.T lam → new.T lam → Prop
  | coordinate (xs : Vec (new.T lam) lam) (b : new.T lam) (i : Fin lam) :
      Subterm (xs.idx i) (.P xs b)
  | tail (xs : Vec (new.T lam) lam) (b : new.T lam) : Subterm b (.P xs b)
  | trans {a b c : new.T lam} : Subterm a b → Subterm b c → Subterm a c

theorem Subterm.size_lt {lam : Nat} {a s : new.T lam} (h : Subterm a s) :
    new.T.size a < new.T.size s := by
  induction h with
  | coordinate => exact new.T.idx_size_lt_P _ _ _
  | tail => exact new.T.add_size_lt_P _ _
  | trans _ _ ha hb => exact Nat.lt_trans ha hb

theorem Subterm.recursiveWF {d lam : Nat} {a s : new.T lam} (h : Subterm a s)
    (hs : RecursiveWF d s) : RecursiveWF d a := by
  induction h with
  | coordinate xs b i => rw [RecursiveWF] at hs; exact hs.1 i
  | tail xs b => rw [RecursiveWF] at hs; exact hs.2.1
  | trans _ _ ha hb => exact ha (hb hs)

theorem hOne_mem {u z : Term} (h : z ∈ Term.hOne u) : z = .zero := by
  unfold Term.hOne at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact List.mem_singleton.mp h

theorem H_inacc_support {u z : Term} (n : Nat) (b : Term) (h : z ∈ Term.H u (.inacc n b)) :
    z = .zero ∨ z ∈ Term.H u b := by
  rw [Term.H] at h
  rcases List.mem_append.mp h with h | h
  · split at h
    · cases h
    · exact Or.inl (hOne_mem h)
  · exact Or.inr h

theorem H_psi_support {u z v b : Term} (h : z ∈ Term.H u (.psi v b)) :
    z = b ∨ z ∈ Term.H u b ∨ z ∈ Term.H u v := by
  rw [Term.H] at h
  split at h
  · cases h
  · split at h
    · exact Or.inr (Or.inr h)
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

theorem H_one_mem {u z : Term} (h : z ∈ Term.H u Term.one) : z = .zero := by
  rcases H_psi_support h with h | h | h
  · exact h
  · cases h
  · simp only [Term.bigOmega, Term.H] at h
    cases h

theorem H_succ_support {u z : Term} (a : Term) (h : z ∈ Term.H u (succTerm a)) :
    z = .zero ∨ z ∈ Term.H u a := by
  rw [Support.OT2.H_succTerm] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inr h
  · exact Or.inl (H_one_mem h)

def ArgCoefficient (u z a : Term) : Prop :=
  z = a ∨ z = dropOne a ∨ z ∈ Term.H u a

theorem H_step_support (u : Term) (n : Nat) (a c : Term) {z : Term}
    (h : z ∈ Term.H u (step n a c)) :
    z = .zero ∨ z ∈ Term.H u a ∨ ArgCoefficient u z c := by
  unfold step at h
  by_cases ha : a = .zero
  · subst a
    simp only [↓reduceIte] at h
    by_cases hn : n = 0
    · rw [ite_eq_left hn] at h
      rcases H_psi_support h with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · simp only [Term.bigOmega, Term.H] at h; cases h
    · rw [ite_eq_right hn] at h
      by_cases hc : c = .zero
      · rw [ite_eq_left hc, Term.H] at h; cases h
      · rw [ite_eq_right hc] at h
        rcases H_psi_support h with h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Support.OT2.mem_H_dropOne h))))
        · rcases H_inacc_support n .zero h with h | h
          · exact Or.inl h
          · cases h
  · rw [ite_eq_right ha] at h
    by_cases hc : c = .zero
    · rw [ite_eq_left hc] at h
      exact Or.inr (Or.inl h)
    · rw [ite_eq_right hc] at h
      rcases H_psi_support h with h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Support.OT2.mem_H_dropOne h))))
      · rcases H_inacc_support n (succTerm a) h with h | h
        · exact Or.inl h
        · rcases H_succ_support a h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)

theorem H_topPair_support (u : Term) (n : Nat) (a b : Term) {z : Term}
    (h : z ∈ Term.H u (topPair n a b)) :
    z = .zero ∨ ArgCoefficient u z a ∨ ArgCoefficient u z b := by
  unfold topPair at h
  by_cases hb : b = .zero
  · rw [ite_eq_left hb] at h
    by_cases ha : a = .zero
    · rw [ite_eq_left ha, Term.H] at h; cases h
    · rw [ite_eq_right ha] at h
      rcases H_inacc_support n (dropOne a) h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Support.OT2.mem_H_dropOne h))))
  · rw [ite_eq_right hb] at h
    rcases H_psi_support h with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Support.OT2.mem_H_dropOne h))))
    · rcases H_inacc_support n _ h with h | h
      · exact Or.inl h
      · by_cases ha : a = .zero
        · rw [ite_eq_left ha, Term.H] at h; cases h
        · rw [ite_eq_right ha] at h
          rcases H_succ_support (dropOne a) h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (Or.inr (Or.inr (Support.OT2.mem_H_dropOne h))))

theorem H_lower_support (u : Term) (j : Nat) (xs : List Term) (a : Term) {z : Term}
    (h : z ∈ Term.H u (lower j xs a)) :
    z = .zero ∨ z ∈ Term.H u a ∨ ∃ i, i < j ∧ ArgCoefficient u z (xs[i]?.getD .zero) := by
  induction j generalizing a with
  | zero => exact Or.inr (Or.inl h)
  | succ j ih =>
    rw [lower_succ] at h
    rcases ih _ h with h | h | ⟨i, hi, h⟩
    · exact Or.inl h
    · rcases H_step_support u j _ _ h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨j, by omega, h⟩)
    · exact Or.inr (Or.inr ⟨i, by omega, h⟩)

theorem H_principal_support (u : Term) (k : Nat) (xs : List Term) {z : Term}
    (h : z ∈ Term.H u (principal (k + 3) xs)) :
    z = .zero ∨ ∃ i, i < k + 3 ∧ ArgCoefficient u z (xs[i]?.getD .zero) := by
  rw [principal_as_layers] at h
  rcases H_lower_support u (k + 1) xs _ h with h | h | ⟨i, hi, h⟩
  · exact Or.inl h
  · rcases H_topPair_support u (k + 1) _ _ h with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨k + 2, by omega, h⟩
    · exact Or.inr ⟨k + 1, by omega, h⟩
  · exact Or.inr ⟨i, by omega, h⟩

theorem H_assemble_support (u : Term) (a b : Term) {z : Term}
    (h : z ∈ Term.H u (OT2.assemble a b)) : z ∈ Term.H u a ∨ z ∈ Term.H u b := by
  unfold OT2.assemble at h
  split at h
  · exact Or.inl h
  · rw [Term.H] at h
    exact List.mem_append.mp h

theorem H_coefficient_wf (u t : Term) (ht : Term.wf t = true) {z : Term}
    (hz : z ∈ Term.H u t) : Term.wf z = true := by
  induction t with
  | zero => cases hz
  | add a b iha ihb =>
    have hw := (Term.wf_add_iff _ _).mp ht
    rw [Term.H] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact iha hw.2.1 hz
    · exact ihb hw.2.2.1 hz
  | inacc n b ih =>
    rcases H_inacc_support n b hz with rfl | hz
    · rfl
    · exact ih ((Term.wf_inacc_iff _ _).mp ht).1 hz
  | psi v b ihv ihb =>
    have hw := (Term.wf_psi_iff _ _).mp ht
    rcases H_psi_support hz with rfl | hz | hz
    · exact hw.2.2.1
    · exact ihb hw.2.2.1 hz
    · exact ihv hw.2.1 hz

theorem H_convert_source (k : Nat) (u : Term) (s : new.T (k + 3)) {z : Term}
    (h : z ∈ Term.H u (convert (k + 3) (code s))) :
    z = .zero ∨ ∃ a : new.T (k + 3), Subterm a s ∧
      (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a))) := by
  cases he : s with
  | Z => rw [he, code, convert, Term.H] at h; cases h
  | P xs b =>
    rw [he, code, convert] at h
    rcases H_assemble_support u _ _ h with h | h
    · rcases H_principal_support u k _ h with h | ⟨i, hi, h⟩
      · exact Or.inl h
      · have hc := converted_coordinate (d := k + 3) xs (⟨i, hi⟩ : Fin (k + 3))
        rw [hc] at h
        rcases h with h | h | h
        · exact Or.inr ⟨xs.idx ⟨i, hi⟩, Subterm.coordinate xs b _, Or.inl h⟩
        · exact Or.inr ⟨xs.idx ⟨i, hi⟩, Subterm.coordinate xs b _, Or.inr h⟩
        · rcases H_convert_source k u (xs.idx ⟨i, hi⟩) h with h | ⟨a, ha, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨a, Subterm.trans ha (Subterm.coordinate xs b _), h⟩
    · rcases H_convert_source k u b h with h | ⟨a, ha, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨a, Subterm.trans ha (Subterm.tail xs b), h⟩
termination_by new.T.size s
decreasing_by
  all_goals simp only [he]
  all_goals first
    | (have hi := Vec.idx_size_lt xs (⟨i, hi⟩ : Fin (k + 3)); simp only [new.T.size]; omega)
    | exact new.T.add_size_lt_P _ _

theorem H_convert_bound_of_subterms [LargeCardinals.{u}] (k : Nat) (v : Term)
    (s : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
    (hsub : ∀ a, Subterm a s → new.T.lt a s) :
    Term.allLt (Term.H v (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true := by
  by_cases hz : s = .Z
  · subst s
    simp only [code, convert, Term.H, Term.allLt, List.all_nil]
  · have hnonzero : convert (k + 3) (code s) ≠ .zero := by
      intro h
      exact hz (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp h))
    apply (Term.allLt_iff _ _).mpr
    intro z h
    rcases H_convert_source k v s h with rfl | ⟨a, ha, h⟩
    · exact (zero_lt_iff _).mpr hnonzero
    · have har := ha.recursiveWF hs
      have hlt := (convert_order k a s har hs).mp (hsub a ha)
      rcases h with rfl | rfl
      · exact hlt
      · exact dropOne_lt_of_lt har.wf hs.wf hlt

theorem H_omega_psi_inacc (n : Nat) (a b : Term) :
    Term.H Term.bigOmega (.psi (.inacc n a) b) =
      b :: (Term.H Term.bigOmega b ++ Term.H Term.bigOmega (.inacc n a)) := by
  simp [Term.H, Term.bigOmega, Term.predR, Term.le, Term.lt,
    Support.CountableTarget.lt_zero]

theorem H_omega_step_context (n : Nat) (a c : Term) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega a) :
    z ∈ Term.H Term.bigOmega (step n a c) := by
  unfold step
  by_cases ha : a = .zero
  · subst a; cases hz
  · rw [ite_eq_right ha]
    by_cases hc : c = .zero
    · rw [ite_eq_left hc]; exact hz
    · rw [ite_eq_right hc, regular, H_omega_psi_inacc]
      apply List.mem_cons_of_mem
      apply List.mem_append_right
      rw [Term.H]
      apply List.mem_append_right
      rw [Support.OT2.H_succTerm]
      exact List.mem_append_left _ hz

theorem H_omega_lower_context (j : Nat) (xs : List Term) (a : Term) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega a) :
    z ∈ Term.H Term.bigOmega (lower j xs a) := by
  induction j generalizing a with
  | zero => exact hz
  | succ j ih =>
    rw [lower_succ]
    exact ih _ (H_omega_step_context j a _ hz)

theorem H_omega_step_argument (n : Nat) (a c : Term) (hc : c ≠ .zero) :
    c ∈ Term.H Term.bigOmega (step n a c) ∨
      dropOne c ∈ Term.H Term.bigOmega (step n a c) := by
  unfold step
  by_cases ha : a = .zero
  · rw [ite_eq_left ha]
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      change c ∈ Term.H Term.bigOmega (.psi (.inacc 0 .zero) c) ∨
        dropOne c ∈ Term.H Term.bigOmega (.psi (.inacc 0 .zero) c)
      rw [H_omega_psi_inacc 0 .zero c]
      exact Or.inl List.mem_cons_self
    · rw [ite_eq_right hn, ite_eq_right hc, H_omega_psi_inacc]
      exact Or.inr List.mem_cons_self
  · rw [ite_eq_right ha, ite_eq_right hc, regular, H_omega_psi_inacc]
    exact Or.inr List.mem_cons_self

theorem H_omega_lower_coordinate (j : Nat) (xs : List Term) (a : Term)
    (i : Nat) (hi : i < j) (hc : xs[i]?.getD .zero ≠ .zero) :
    xs[i]?.getD .zero ∈ Term.H Term.bigOmega (lower j xs a) ∨
      dropOne (xs[i]?.getD .zero) ∈ Term.H Term.bigOmega (lower j xs a) := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    rw [lower_succ]
    by_cases hij : i < j
    · exact ih _ hij
    · have he : i = j := by omega
      subst i
      rcases H_omega_step_argument j a _ hc with hz | hz
      · exact Or.inl (H_omega_lower_context j xs _ hz)
      · exact Or.inr (H_omega_lower_context j xs _ hz)

theorem H_omega_principal_coordinate (k : Nat) (xs : List Term)
    (i : Nat) (hi : i < k + 2) (hc : xs[i]?.getD .zero ≠ .zero) :
    xs[i]?.getD .zero ∈ Term.H Term.bigOmega (principal (k + 3) xs) ∨
      dropOne (xs[i]?.getD .zero) ∈ Term.H Term.bigOmega (principal (k + 3) xs) := by
  rw [principal_as_layers]
  by_cases hij : i < k + 1
  · exact H_omega_lower_coordinate (k + 1) xs _ i hij hc
  · have he : i = k + 1 := by omega
    subst i
    apply Or.inr
    apply H_omega_lower_context
    rw [topPair, ite_eq_right hc, H_omega_psi_inacc]
    exact List.mem_cons_self

end Support.GeneralImageCoefficients

namespace Support.GeneralImageEmbedding

open new OCF.Jaeger Support.OTQuotient Support.BinaryTranslation
open Support.CountableSource Support.DimensionCut

def tower (k : Nat) : Nat → Term
  | 0 => .zero
  | n + 1 => .inacc (k + 1) (tower k n)

theorem tower_wf (k n : Nat) : Term.wf (tower k n) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tower, Term.wf, ih, Bool.true_and]
    cases n <;> simp [tower, Term.fT]

theorem tower_drop (k n : Nat) : dropOne (tower k n) = tower k n := by
  cases n <;> simp [tower, dropOne]

theorem tower_H (k n : Nat) :
    ∀ t ∈ Term.H Term.bigOmega (tower k n), t = .zero := by
  induction n with
  | zero => simp [tower, Term.H]
  | succ n ih =>
    simp only [tower, Term.H, show k + 1 ≠ 0 by omega, ↓reduceIte]
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · simpa [Term.hOne, Term.bigOmega, Term.predR, Term.le, Term.one, Term.lt, Term.fT] using ht
    · exact ih t ht

theorem psi_tower_wf (k n : Nat) : Term.wf (.psi Term.bigOmega (tower k n)) = true := by
  rw [Term.wf]
  have h : Term.allLt (Term.H Term.bigOmega (tower k n)) (tower k n) = true := by
    cases n with
    | zero => rfl
    | succ n =>
      apply List.all_eq_true.mpr
      intro t ht
      rw [tower_H k (n + 1) t ht]
      simp [tower, Term.lt]
  simp only [show Term.isRT Term.bigOmega = true by decide +kernel,
    show Term.wf Term.bigOmega = true by decide +kernel, tower_wf, h, Bool.true_and]

theorem principal_top_term (k : Nat) (t : Term) (ht : t ≠ .zero) :
    DimensionImage.principal (k + 3) (List.replicate (k + 2) .zero ++ [t]) =
      .inacc (k + 1) (dropOne t) := by
  let xs := List.replicate (k + 2) Term.zero ++ [t]
  have hhigh : xs[k + 2]?.getD .zero = t := by simp [xs]
  have hzero : ∀ i, i < k + 2 → xs[i]?.getD .zero = .zero := by
    intro i hi
    simp [xs, List.getElem?_append, hi]
  change DimensionImage.principal (k + 3) xs = _
  rw [DimensionImage.principal, ite_eq_right (by omega)]
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    hhigh, hzero (k + 1) (by omega), ht, ↓reduceIte]
  exact DimensionImage.lower_keep (k + 1) xs _ (by intro h; cases h)
    (fun i hi => hzero i (by omega))

theorem codes_zeros {lam : Nat} (k : Nat) :
    codes (zeros (lam := lam) k) = List.replicate k Code.zero := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [zeros_succ, codes, code, ih]
    exact Support.CodeReification.replicate_append_singleton k .zero

theorem trim_before_nonzero (k : Nat) (c : Code) (hc : c ≠ .zero) :
    trim (List.replicate k .zero ++ [c]) = List.replicate k .zero ++ [c] := by
  induction k with
  | zero => cases c <;> simp_all [trim, Code.isZero]
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, trim, ih]
    cases he : List.replicate k Code.zero ++ [c] with
    | nil => have hl := congrArg List.length he; simp at hl
    | cons a xs => rfl

theorem fixed_LF_value (k n : Nat) :
    DimensionImage.convert (k + 3) (code (T.LF (k + 3) (n + 2))) = tower k (n + 1) := by
  have hcode : ∀ n, code (T.LF (k + 3) (n + 1)) ≠ .zero := by
    intro n hn
    have he : T.LF (k + 3) (n + 1) = .Z := code_injective hn
    exact LF_positive (k + 2) n he
  induction n with
  | zero =>
    rw [LF_step, LF_one]
    simp only [code, lastVec, codes, codes_zeros]
    rw [trim_before_nonzero _ _ (show code (T.ofNat 1 : new.T (k + 3)) ≠ .zero by
      rw [Support.FiniteCorrespondence.code_ofNat]; intro h; cases h)]
    simp only [DimensionImage.convert, DimensionImage.arguments_append,
      DimensionImage.arguments_zeros, DimensionImage.arguments,
      Support.FiniteCorrespondence.code_ofNat]

    change OT2.assemble (DimensionImage.principal (k + 3)
      (List.replicate (k + 2) .zero ++ [DimensionImage.convert (k + 3) UserImage.oneCode])) .zero = _
    rw [DimensionImage.convert_one, principal_top_term k Term.one (by decide +kernel)]
    rfl
  | succ n ih =>
    rw [LF_step]
    simp only [code, lastVec, codes, codes_zeros]
    rw [trim_before_nonzero _ _ (hcode (n + 1))]
    simp only [DimensionImage.convert, DimensionImage.arguments_append,
      DimensionImage.arguments_zeros, DimensionImage.arguments]
    rw [ih, principal_top_term k _ (by simp [tower]), tower_drop]
    rfl

def basis (k n : Nat) : AllOT :=
  ⟨k + 3, lowerBase (k + 2) n, by
    simpa only [lowerBase, lowVec] using T.isOT.base_succ (k + 2) n⟩

end Support.GeneralImageEmbedding

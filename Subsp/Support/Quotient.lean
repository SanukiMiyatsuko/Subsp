import Subsp.KumaKuma.kumakuma
import Subsp.OCF.Jaeger.Notation

/-! OT classes of the source system, their order, and the basic finite translations. -/

namespace Support.OTQuotient

open new

inductive Code where
  | zero : Code
  | p (args : List Code) (tail : Code) : Code
  deriving Repr

def Code.isZero : Code → Bool
  | .zero => true
  | .p _ _ => false

def trim : List Code → List Code
  | [] => []
  | x :: xs =>
    match trim xs with
    | [] => if x.isZero then [] else [x]
    | y :: ys => x :: y :: ys

mutual

  def code {lam : Nat} : T lam → Code
    | .Z => .zero
    | .P args tail => .p (trim (codes args)) (code tail)

  def codes {lam m : Nat} : Vec (T lam) m → List Code
    | .nil => []
    | .snoc _ xs x => codes xs ++ [code x]
end

def AllOT := (lam : Nat) × T.OT lam

def key (s : AllOT) : Code := code s.2.val

def equivalent (s t : AllOT) : Prop := key s = key t

instance equivalentSetoid : Setoid AllOT where
  r := equivalent
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

def Classes := Quotient equivalentSetoid

def classOf (s : AllOT) : Classes := Quotient.mk _ s

theorem class_eq_iff (s t : AllOT) :
    classOf s = classOf t ↔ code s.2.val = code t.2.val :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound (s := equivalentSetoid) h⟩

def classCode : Classes → Code :=
  Quotient.lift key (fun _ _ h => h)

abbrev representative := classCode

theorem classCode_injective : Function.Injective classCode := by
  intro q r
  induction q using Quotient.inductionOn with
  | h s =>
    induction r using Quotient.inductionOn with
    | h t => exact fun h => Quotient.sound (s := equivalentSetoid) h

theorem exists_rep (q : Classes) : ∃ s : AllOT, classOf s = q := by
  induction q using Quotient.inductionOn with
  | h s => exact ⟨s, rfl⟩

theorem exists_dimension (q : Classes) :
    ∃ lam, ∃ s : T.OT lam, classOf ⟨lam, s⟩ = q := by
  obtain ⟨⟨lam, s⟩, h⟩ := exists_rep q
  exact ⟨lam, s, h⟩

private theorem exists_least (p : Nat → Prop) (h : ∃ n, p n) :
    ∃ n, p n ∧ ∀ m, p m → n ≤ m := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hsm : ∃ m, m < n ∧ p m
    · obtain ⟨m, hmn, hm⟩ := hsm
      exact ih m hmn hm
    · exact ⟨n, hn, fun m hm => Nat.le_of_not_gt (fun hmn => hsm ⟨m, hmn, hm⟩)⟩

private theorem exists_minDimension (q : Classes) :
    ∃ lam, (∃ s : T.OT lam, classOf ⟨lam, s⟩ = q) ∧
      ∀ m, (∃ s : T.OT m, classOf ⟨m, s⟩ = q) → lam ≤ m :=
  exists_least _ (exists_dimension q)

noncomputable def minDimension (q : Classes) : Nat :=
  Classical.choose (exists_minDimension q)

theorem minDimension_spec (q : Classes) :
    ∃ s : T.OT (minDimension q), classOf ⟨minDimension q, s⟩ = q :=
  (Classical.choose_spec (exists_minDimension q)).1

noncomputable def dimensionWitness (q : Classes) : AllOT :=
  ⟨minDimension q, Classical.choose (minDimension_spec q)⟩

theorem dimensionWitness_spec (q : Classes) : classOf (dimensionWitness q) = q :=
  Classical.choose_spec (minDimension_spec q)

theorem dimensionWitness_minimal (q : Classes) (s : AllOT)
    (h : classOf s = q) : (dimensionWitness q).1 ≤ s.1 := by
  exact (Classical.choose_spec (exists_minDimension q)).2 s.1 ⟨s.2, h⟩

theorem representative_spec (q : Classes) :
    code (dimensionWitness q).2.val = representative q := by
  exact congrArg classCode (dimensionWitness_spec q)

def noTrailingZero : List Code → Bool
  | [] => true
  | [x] => !x.isZero
  | _ :: y :: ys => noTrailingZero (y :: ys)

theorem trim_noTrailingZero (xs : List Code) : noTrailingZero (trim xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : trim xs with
    | nil =>
      cases hx : x.isZero <;> simp [trim, h, hx, noTrailingZero]
    | cons y ys => simpa [trim, h, noTrailingZero] using ih

theorem mem_trim {x : Code} {xs : List Code} (h : x ∈ trim xs) : x ∈ xs := by
  induction xs with
  | nil => exact h
  | cons y ys ih =>
    cases ht : trim ys with
    | nil =>
      cases hy : y.isZero <;> simp [trim, ht, hy] at h
      exact List.mem_cons.mpr (Or.inl h)
    | cons z zs =>
      have hm : x = y ∨ x ∈ trim ys := by simpa [trim, ht] using h
      exact List.mem_cons.mpr (hm.imp_right ih)

def Code.normal : Code → Prop
  | .zero => True
  | .p args tail => noTrailingZero args = true ∧ (∀ x ∈ args, x.normal) ∧ tail.normal

mutual
  theorem code_normal {lam : Nat} (s : T lam) : (code s).normal := by
    cases s with
    | Z => simp only [code, Code.normal]
    | P args tail =>
      simp only [code, Code.normal]
      exact ⟨trim_noTrailingZero _, fun x hx => codes_normal args x (mem_trim hx),
        code_normal tail⟩

  theorem codes_normal {lam m : Nat} (v : Vec (T lam) m) :
      ∀ x ∈ codes v, x.normal := by
    cases v with
    | nil => intro x h; cases h
    | snoc _ xs x =>
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact codes_normal xs y hy
      · have := List.mem_singleton.mp hy
        subst y
        exact code_normal x
end

theorem representative_normal (q : Classes) : (representative q).normal := by
  induction q using Quotient.inductionOn with
  | h s => exact code_normal s.2.val

end Support.OTQuotient

namespace Support.FiniteCorrespondence

open new OCF.Jaeger OTQuotient

def natCode : Nat → Code
  | 0 => .zero
  | n + 1 => .p [] (natCode n)

theorem trim_append_zero (xs : List Code) : trim (xs ++ [.zero]) = trim xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, trim, ih]

theorem trim_codes_zero (lam k : Nat) :
    trim (codes (Vec.ofFn k (fun _ => (T.Z : T lam)))) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Vec.ofFn, codes, code, trim_append_zero] using ih

theorem code_ofNat (lam n : Nat) : code (T.ofNat (lam := lam) n) = natCode n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [T.ofNat, code, trim_codes_zero, ih, natCode]

theorem ofNat_zero_eq_LF (n : Nat) : T.ofNat (lam := 0) n = T.LF 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [T.ofNat, T.LF, Vec.ofFn, ih]

theorem ofNat_isOT_zero (n : Nat) : T.isOT 0 (T.ofNat n) := by
  rw [ofNat_zero_eq_LF]
  exact T.isOT.base_0 n

theorem zero_dimension_exhaustive (s : new.T 0) : ∃ n, s = T.ofNat n := by
  cases s with
  | Z => exact ⟨0, rfl⟩
  | P args tail =>
    cases args
    obtain ⟨n, hn⟩ := zero_dimension_exhaustive tail
    exact ⟨n + 1, congrArg (T.P .nil) hn⟩

def natTerm : Nat → Term
  | 0 => .zero
  | 1 => Term.one
  | n + 2 => .add Term.one (natTerm (n + 1))

theorem natTerm_ne_zero (n : Nat) : natTerm (n + 1) ≠ Term.zero := by
  cases n <;> intro h <;> cases h

theorem natTerm_lt (m n : Nat) :
    Term.lt (natTerm m) (natTerm n) = true ↔ m < n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simp [natTerm, Term.one, Term.lt]
  | succ m ih =>
    cases n with
    | zero => cases m <;> simp [natTerm, Term.one, Term.lt]
    | succ n =>
      cases m with
      | zero =>
        cases n with
        | zero => simp [natTerm, Term.one, Term.bigOmega, Term.lt]
        | succ n => simp [natTerm, Term.one, Term.lt]
      | succ m =>
        cases n with
        | zero => simp [natTerm, Term.one, Term.bigOmega, Term.lt]
        | succ n =>
          simpa only [natTerm, Term.lt, ↓reduceIte, Nat.succ_lt_succ_iff] using ih (n + 1)

theorem natTerm_injective : Function.Injective natTerm := by
  intro m n h
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hnm
    have hn := (natTerm_lt n m).mpr hnm
    rw [h] at hn
    have := (natTerm_lt n n).mp hn
    exact Nat.lt_irrefl n this
  · apply Nat.le_of_not_gt
    intro hmn
    have hm := (natTerm_lt m n).mpr hmn
    rw [h] at hm
    have := (natTerm_lt n n).mp hm
    exact Nat.lt_irrefl n this

end Support.FiniteCorrespondence

namespace Support.OTQuotient

open new

mutual

  def compareCode : Code → Code → Ordering
    | .zero, .zero => .eq
    | .zero, .p _ _ => .lt
    | .p _ _, .zero => .gt
    | .p xs a, .p ys b =>
      match compareArgs xs ys with
      | .eq => compareCode a b
      | o => o
  termination_by a b => sizeOf a + sizeOf b

  def compareArgs : List Code → List Code → Ordering
    | [], [] => .eq
    | [], y :: ys =>
      match compareArgs [] ys with
      | .eq => compareCode .zero y
      | o => o
    | x :: xs, [] =>
      match compareArgs xs [] with
      | .eq => compareCode x .zero
      | o => o
    | x :: xs, y :: ys =>
      match compareArgs xs ys with
      | .eq => compareCode x y
      | o => o
  termination_by xs ys => sizeOf xs + sizeOf ys
end

theorem compareArgs_trim_left (xs ys : List Code) :
    compareArgs (trim xs) ys = compareArgs xs ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ht : trim xs with
    | nil =>
      have ih' : ∀ ys, compareArgs [] ys = compareArgs xs ys := by
        intro ys; simpa only [ht] using ih ys
      cases x with
      | zero =>
        cases ys <;> simp [trim, ht, Code.isZero, compareArgs, ← ih', compareCode]
      | p args tail =>
        cases ys <;> simp [trim, ht, Code.isZero, compareArgs, ← ih']
    | cons z zs =>
      have ih' : ∀ ys, compareArgs (z :: zs) ys = compareArgs xs ys := by
        intro ys; simpa only [ht] using ih ys
      cases ys <;> simp only [trim, ht, compareArgs, ← ih']

theorem compareArgs_trim_right (xs ys : List Code) :
    compareArgs xs (trim ys) = compareArgs xs ys := by
  induction ys generalizing xs with
  | nil => rfl
  | cons y ys ih =>
    cases ht : trim ys with
    | nil =>
      have ih' : ∀ xs, compareArgs xs [] = compareArgs xs ys := by
        intro xs; simpa only [ht] using ih xs
      cases y with
      | zero =>
        cases xs <;> simp [trim, ht, Code.isZero, compareArgs, ← ih', compareCode]
      | p args tail =>
        cases xs <;> simp [trim, ht, Code.isZero, compareArgs, ← ih']
    | cons z zs =>
      have ih' : ∀ xs, compareArgs xs (z :: zs) = compareArgs xs ys := by
        intro xs; simpa only [ht] using ih xs
      cases xs <;> simp only [trim, ht, compareArgs, ← ih']

theorem compareArgs_snoc {xs ys : List Code} (hlen : xs.length = ys.length) (x y : Code) :
    compareArgs (xs ++ [x]) (ys ++ [y]) =
      match compareCode x y with
      | .eq => compareArgs xs ys
      | o => o := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [compareArgs]; cases compareCode x y <;> rfl
    | cons y ys => simp at hlen
  | cons a xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons b ys =>
      have he : xs.length = ys.length := Nat.succ.inj hlen
      simp only [List.cons_append, compareArgs, ih he]
      cases compareCode x y <;> rfl

theorem codes_length {lam m : Nat} (v : Vec (T lam) m) : (codes v).length = m := by
  induction v with
  | nil => rfl
  | snoc n xs x ih => simp only [codes, List.length_append, List.length_singleton, ih]

mutual

  theorem compareCode_code {lam : Nat} (s t : T lam) :
      compareCode (code s) (code t) = compareT s t := by
    cases s with
    | Z => cases t <;> simp [code, compareCode, compareT]
    | P xs a =>
      cases t with
      | Z => simp [code, compareCode, compareT]
      | P ys b =>
        simp only [code, compareCode, compareArgs_trim_left, compareArgs_trim_right,
          compareArgs_codes xs ys, compareCode_code a b, compareT]
        rfl

  theorem compareArgs_codes {lam m : Nat} (xs ys : Vec (T lam) m) :
      compareArgs (codes xs) (codes ys) = compareVec xs ys := by
    cases xs with
    | nil => cases ys; simp [codes, compareArgs, compareVec]
    | snoc n xs x =>
      cases ys with
      | snoc _ ys y =>
        rw [codes, codes, compareArgs_snoc (by simp only [codes_length])]
        rw [compareCode_code x y, compareArgs_codes xs ys]
        rfl
end

def classCompare (q r : Classes) : Ordering := compareCode (representative q) (representative r)

def ClassLT (q r : Classes) : Prop := classCompare q r = .lt

end Support.OTQuotient

namespace Support.OTQuotient

open new

mutual

  def pad {lam : Nat} : T lam → T (lam + 1)
    | .Z => .Z
    | .P xs b => .P (.snoc lam (padVec xs) .Z) (pad b)

  def padVec {lam m : Nat} : Vec (T lam) m → Vec (T (lam + 1)) m
    | .nil => .nil
    | .snoc n xs x => .snoc n (padVec xs) (pad x)
end

mutual
  theorem code_pad {lam : Nat} (s : T lam) : code (pad s) = code s := by
    cases s with
    | Z => simp [pad, code]
    | P xs b =>
      simp only [pad, code, codes, codes_padVec, code_pad,
        FiniteCorrespondence.trim_append_zero]

  theorem codes_padVec {lam m : Nat} (xs : Vec (T lam) m) : codes (padVec xs) = codes xs := by
    cases xs with
    | nil => rfl
    | snoc _ xs x => simp only [padVec, codes, codes_padVec xs, code_pad x]
end

def liftBy {lam : Nat} : (k : Nat) → T lam → T (lam + k)
  | 0, s => s
  | k + 1, s => pad (liftBy k s)

theorem code_liftBy {lam : Nat} (k : Nat) (s : T lam) : code (liftBy k s) = code s := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [liftBy, code_pad, ih]

theorem code_cast {lam m : Nat} (e : lam = m) (s : T lam) : code (e ▸ s) = code s := by
  cases e
  rfl

def promote {lam m : Nat} (h : lam ≤ m) (s : T lam) : T m :=
  (Nat.add_sub_of_le h) ▸ liftBy (m - lam) s

theorem code_promote {lam m : Nat} (h : lam ≤ m) (s : T lam) :
    code (promote h s) = code s := by
  simp only [promote, code_cast, code_liftBy]

theorem compareCode_mixed {lam m k : Nat} (hlam : lam ≤ k) (hm : m ≤ k)
    (s : T lam) (t : T m) :
    compareCode (code s) (code t) = compareT (promote hlam s) (promote hm t) := by
  rw [← compareCode_code, code_promote, code_promote]

theorem code_injective {lam : Nat} : Function.Injective (@code lam) := by
  intro s t h
  apply T_eq_sound s t
  rw [← compareCode_code, h, compareCode_code]
  exact T_refl t

theorem classCompare_eq_iff (q r : Classes) : classCompare q r = .eq ↔ q = r := by
  induction q using Quotient.inductionOn with
  | h s =>
    induction r using Quotient.inductionOn with
    | h t =>
      constructor
      · intro h
        change compareCode (code s.2.val) (code t.2.val) = .eq at h
        rw [compareCode_mixed (Nat.le_max_left s.1 t.1) (Nat.le_max_right s.1 t.1)] at h
        have he := T_eq_sound _ _ h
        have hc := congrArg code he
        simp only [code_promote] at hc
        exact (class_eq_iff s t).mpr hc
      · intro h
        have hc := (class_eq_iff s t).mp h
        change compareCode (code s.2.val) (code t.2.val) = .eq
        rw [hc, compareCode_code]
        exact T_refl _

theorem classLT_irrefl (q : Classes) : ¬ ClassLT q q := by
  have h := (classCompare_eq_iff q q).mpr rfl
  intro he
  change classCompare q q = .lt at he
  rw [h] at he
  cases he

theorem classLT_trans {q r t : Classes} (hqr : ClassLT q r) (hrt : ClassLT r t) :
    ClassLT q t := by
  obtain ⟨s, rfl⟩ := exists_rep q
  obtain ⟨v, rfl⟩ := exists_rep r
  obtain ⟨w, rfl⟩ := exists_rep t
  let k := max s.1 (max v.1 w.1)
  have hs : s.1 ≤ k := Nat.le_max_left _ _
  have hv : v.1 ≤ k := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hw : w.1 ≤ k := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  change compareCode (code s.2.val) (code v.2.val) = .lt at hqr
  change compareCode (code v.2.val) (code w.2.val) = .lt at hrt
  change compareCode (code s.2.val) (code w.2.val) = .lt
  rw [compareCode_mixed hs hv] at hqr
  rw [compareCode_mixed hv hw] at hrt
  rw [compareCode_mixed hs hw]
  exact T_trans _ _ _ hqr hrt

theorem classLT_total (q r : Classes) : ClassLT q r ∨ ClassLT r q ∨ q = r := by
  obtain ⟨s, rfl⟩ := exists_rep q
  obtain ⟨t, rfl⟩ := exists_rep r
  let hs := Nat.le_max_left s.1 t.1
  let ht := Nat.le_max_right s.1 t.1
  rcases T_total (promote hs s.2.val) (promote ht t.2.val) with h | h | h
  · apply Or.inl
    change compareCode (code s.2.val) (code t.2.val) = .lt
    rwa [compareCode_mixed hs ht]
  · apply Or.inr ∘ Or.inl
    change compareCode (code t.2.val) (code s.2.val) = .lt
    rwa [compareCode_mixed ht hs]
  · apply Or.inr ∘ Or.inr
    apply (class_eq_iff s t).mpr
    have hc := congrArg code h
    simpa only [code_promote] using hc

end Support.OTQuotient

namespace Support.FirstLimit

open new OCF OCF.Jaeger OTQuotient FiniteCorrespondence

def omegaSource : new.T 1 := .P (.snoc 0 .nil (T.ofNat 1)) .Z

theorem omegaSource_isOT : T.isOT 1 omegaSource := T.isOT.base_succ 0 1

private theorem one_mul_nat (n : Nat) :
    T.mul (T.ofNat (lam := 1) 1) (T.ofNat n) = T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [T.ofNat, T.mul, HAdd.hAdd, Add.add, T.oplus, Vec.ofFn] using
      congrArg (fun s : new.T 1 => T.P (.snoc 0 .nil .Z) s) ih

theorem omegaSource_fund (n : Nat) :
    T.fund omegaSource (T.ofNat n) = T.ofNat n := by
  simpa [omegaSource, T.fund, T.ofNat, T.domVecMinIdx, T.dom, Vec.idx,
    Vec.ofFn, Vec.rplc, GetElem.getElem] using one_mul_nat n

theorem ofNat_isOT_one (n : Nat) : T.isOT 1 (T.ofNat n) := by
  rw [← omegaSource_fund n]
  exact T.isOT.step 1 omegaSource omegaSource_isOT n

section Semantics

universe u
open Ordinal
variable [LargeCardinals.{u}]

end Semantics
end Support.FirstLimit

namespace Support.Unary

open new OCF.Jaeger

private theorem omega_lt_self : Term.lt Term.bigOmega Term.bigOmega = false := by
  decide +kernel

theorem psi_omega_lt (a b : Term) :
    Term.lt (.psi Term.bigOmega a) (.psi Term.bigOmega b) = Term.lt a b := by
  simp only [Term.lt, omega_lt_self, Bool.false_and, Bool.false_or,
    decide_true, Bool.true_and, Bool.or_false]

end Support.Unary

namespace Support

open new OCF.Jaeger OTQuotient

def WFBelowOmega := { t : Term // Term.wf t = true ∧ Term.lt t Term.bigOmega = true }

end Support

namespace Support.BinaryTranslation

open new OCF.Jaeger

def dropOne : Term → Term
  | .zero => .zero
  | .add a b => if a = Term.one then b else .add a b
  | .inacc n b => .inacc n b
  | .psi u b => if .psi u b = Term.one then .zero else .psi u b

def succTerm : Term → Term
  | .zero => Term.one
  | .add a b => .add a (succTerm b)
  | .inacc n b => .add (.inacc n b) Term.one
  | .psi u b => .add (.psi u b) Term.one

end Support.BinaryTranslation

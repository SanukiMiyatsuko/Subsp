import Subsp.multi.Lex
import Subsp.multi.kuma.nt
import Subsp.OCF.Jaeger.Notation
import Subsp.multi.kuma.JaegerFacts
import Subsp.multi.kuma.Decide

/-! Codes of `multi` source terms, fixed-dimension source terms, the OT terms of each
dimension and their classes, their order, and the basic finite translations.

This is the `multi` version of `Subsp/Support/Quotient.lean`. A source term of dimension `d`
of the fixed-dimension system is represented by a `multi.T` all of whose vectors have length
exactly `d` (`Dim d`); `padTo d` moves an arbitrary `multi.T` to such a representative. -/

namespace kumakuma.OTQuotient

open multi

/-! ### Codes -/

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
  def code : multi.T → Code
    | .Z => .zero
    | .P args tail => .p (trim (codes args)) (code tail)

  def codes : V multi.T → List Code
    | .emp => []
    | .snoc x xs => codes xs ++ [code x]
end

theorem code_Z : code multi.T.Z = .zero := by rw [code]

theorem code_P (v : V multi.T) (a : multi.T) :
    code (multi.T.P v a) = .p (trim (codes v)) (code a) := by rw [code]

theorem codes_emp : codes (V.emp : V multi.T) = [] := by rw [codes]

theorem codes_snoc (x : multi.T) (xs : V multi.T) : codes (.snoc x xs) = codes xs ++ [code x] := by
  rw [codes]

theorem codes_length (v : V multi.T) : (codes v).length = v.length := by
  induction v with
  | emp => rw [codes_emp]; rfl
  | snoc x xs ih => rw [codes_snoc, List.length_append, ih]; rfl

theorem code_isZero_iff (s : multi.T) : (code s).isZero = true ↔ s = multi.T.Z := by
  cases s with
  | Z => simp [code_Z, Code.isZero]
  | P v a => simp [code_P, Code.isZero]

theorem code_eq_zero_iff (s : multi.T) : code s = .zero ↔ s = multi.T.Z := by
  cases s with
  | Z => simp [code_Z]
  | P v a => simp [code_P]

/-- The coordinate of a list of codes, padded with zeros. -/
def cget (xs : List Code) (i : Nat) : Code := (xs[i]?).getD .zero

theorem cget_nil (i : Nat) : cget [] i = .zero := rfl

theorem cget_cons_zero (x : Code) (xs : List Code) : cget (x :: xs) 0 = x := rfl

theorem cget_cons_succ (x : Code) (xs : List Code) (i : Nat) : cget (x :: xs) (i + 1) = cget xs i := rfl

theorem cget_append_singleton (xs : List Code) (x : Code) (i : Nat) :
    cget (xs ++ [x]) i = if i < xs.length then cget xs i else if i = xs.length then x else .zero := by
  unfold cget
  by_cases h : i < xs.length
  · rw [ite_eq_left h, List.getElem?_append_left h]
  · rw [ite_eq_right h, List.getElem?_append_right (Nat.le_of_not_lt h)]
    by_cases he : i = xs.length
    · rw [ite_eq_left he, he, Nat.sub_self]; rfl
    · rw [ite_eq_right he]
      have : i - xs.length ≠ 0 := by omega
      obtain ⟨m, hm⟩ : ∃ m, i - xs.length = m + 1 := ⟨i - xs.length - 1, by omega⟩
      rw [hm]; rfl

theorem cget_ge (xs : List Code) (i : Nat) (h : xs.length ≤ i) : cget xs i = .zero := by
  unfold cget
  rw [List.getElem?_eq_none h]; rfl

theorem codes_get (v : V multi.T) (i : Nat) : cget (codes v) i = code (V.get0 v i) := by
  induction v with
  | emp => rw [codes_emp]; show Code.zero = code multi.T.Z; rw [code_Z]
  | snoc x xs ih =>
    rw [codes_snoc, cget_append_singleton, codes_length]
    show _ = code (if i = xs.length then x else V.get0 xs i)
    by_cases h : i < xs.length
    · rw [ite_eq_left h, ite_eq_right (Nat.ne_of_lt h), ih]
    · rw [ite_eq_right h]
      by_cases he : i = xs.length
      · rw [ite_eq_left he, ite_eq_left he]
      · rw [ite_eq_right he, ite_eq_right he, V.get0_ge xs i (by omega), code_Z]

/-! ### Trimming code lists -/

theorem trim_append_zero (xs : List Code) : trim (xs ++ [.zero]) = trim xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, trim, ih]

theorem trim_append_nonzero (xs : List Code) (y : Code) (hy : y.isZero = false) :
    trim (xs ++ [y]) = xs ++ [y] := by
  induction xs with
  | nil => simp [trim, hy]
  | cons x xs ih =>
    rw [List.cons_append, trim, ih]
    cases h : xs ++ [y] with
    | nil => simp at h
    | cons z zs => rfl

theorem trim_codes (v : V multi.T) : trim (codes v) = codes (V.trim v) := by
  induction v with
  | emp => rfl
  | snoc a ax ih =>
    cases a with
    | Z =>
      show trim (codes (V.snoc multi.T.Z ax)) = codes (V.trim ax)
      rw [codes_snoc, code_Z, trim_append_zero, ih]
    | P w b =>
      show trim (codes (V.snoc (multi.T.P w b) ax)) = codes (V.snoc (multi.T.P w b) ax)
      rw [codes_snoc, trim_append_nonzero _ _ (by rw [code_P]; rfl)]

theorem trim_cons_of {x y : Code} {xs ys : List Code} (h : trim xs = y :: ys) :
    trim (x :: xs) = x :: y :: ys := by
  simp only [trim, h]

theorem trim_trim (xs : List Code) : trim (trim xs) = trim xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases ht : trim xs with
    | nil =>
      cases hx : x.isZero
      · simp [trim, ht, hx]
      · simp [trim, ht, hx]
    | cons y ys =>
      have ih' : trim (y :: ys) = y :: ys := by rw [← ht, ih]
      rw [trim_cons_of ht, trim_cons_of ih']

mutual
  theorem code_norm : ∀ s : multi.T, code (multi.T.norm s) = code s
    | .Z => by rw [multi.T.norm]
    | .P v a => by
      rw [multi.T.norm_P, code_P, code_P, code_norm a, multi.V.norm, ← trim_codes, trim_trim,
        codes_mapNorm v]

  theorem codes_mapNorm : ∀ v : V multi.T, codes (V.mapNorm v) = codes v
    | .emp => by rw [V.mapNorm]
    | .snoc x xs => by
      rw [V.mapNorm, codes_snoc, codes_snoc, codes_mapNorm xs, code_norm x]
end

/-! ### The order of codes -/

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

/-- Compare two code functions on the indices below `k`, the highest index first. -/
def cmpC (f g : Nat → Code) : Nat → Ordering
  | 0 => .eq
  | k + 1 => (compareCode (f k) (g k)).then (cmpC f g k)

theorem ordering_then_eq (o : Ordering) : o.then .eq = o := by cases o <;> rfl

theorem ordering_then_assoc (a b c : Ordering) : (a.then b).then c = a.then (b.then c) := by
  cases a <;> rfl

theorem cmpC_shift (f g : Nat → Code) :
    ∀ N, cmpC f g (N + 1) =
      (cmpC (fun i => f (i + 1)) (fun i => g (i + 1)) N).then (compareCode (f 0) (g 0))
  | 0 => by simp only [cmpC]; rw [ordering_then_eq]; rfl
  | N + 1 => by
    rw [cmpC, cmpC_shift f g N, cmpC, ← ordering_then_assoc]

theorem compareCode_zero_zero : compareCode .zero .zero = .eq := by rw [compareCode]

theorem compareArgs_nil_nil : compareArgs [] [] = .eq := by rw [compareArgs]

theorem compareArgs_eq_then (xs ys : List Code) (h : xs ≠ [] ∨ ys ≠ []) :
    compareArgs xs ys = (compareArgs xs.tail ys.tail).then (compareCode (cget xs 0) (cget ys 0)) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      rw [compareArgs]
      show _ = (compareArgs [] ys).then _
      cases compareArgs [] ys <;> rfl
  | cons x xs =>
    cases ys with
    | nil =>
      rw [compareArgs]
      show _ = (compareArgs xs []).then _
      cases compareArgs xs [] <;> rfl
    | cons y ys =>
      rw [compareArgs]
      show _ = (compareArgs xs ys).then _
      cases compareArgs xs ys <;> rfl

theorem compareArgs_eq_cmpC : ∀ (N : Nat) (xs ys : List Code),
    xs.length ≤ N → ys.length ≤ N → compareArgs xs ys = cmpC (cget xs) (cget ys) N
  | 0, xs, ys, hx, hy => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hx), List.length_eq_zero_iff.1 (Nat.le_zero.1 hy),
      compareArgs_nil_nil]
    rfl
  | N + 1, xs, ys, hx, hy => by
    by_cases h : xs = [] ∧ ys = []
    · obtain ⟨rfl, rfl⟩ := h
      rw [compareArgs_nil_nil]
      have : ∀ M, cmpC (cget []) (cget []) M = .eq := by
        intro M
        induction M with
        | zero => rfl
        | succ M ih => rw [cmpC, ih]; show (compareCode .zero .zero).then .eq = .eq; rw [compareCode_zero_zero]; rfl
      rw [this]
    · rw [compareArgs_eq_then xs ys (by
        by_cases hx0 : xs = []
        · exact Or.inr (fun hy0 => h ⟨hx0, hy0⟩)
        · exact Or.inl hx0), cmpC_shift]
      rw [compareArgs_eq_cmpC N xs.tail ys.tail (by rw [List.length_tail]; omega)
        (by rw [List.length_tail]; omega)]
      congr 1
      · congr 1
        · funext i; cases xs <;> rfl
        · funext i; cases ys <;> rfl

theorem cmpC_code_eq_cmpUpTo (f g : Nat → multi.T) :
    ∀ N, (∀ i, i < N → compareCode (code (f i)) (code (g i)) = compareT (f i) (g i)) →
      cmpC (fun i => code (f i)) (fun i => code (g i)) N = cmpUpTo f g N
  | 0, _ => rfl
  | N + 1, h => by
    rw [cmpC, cmpUpTo, h N (Nat.lt_succ_self N),
      cmpC_code_eq_cmpUpTo f g N (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem compareCode_code_aux : ∀ (n : Nat) (s t : multi.T), s.size + t.size < n →
    compareCode (code s) (code t) = compareT s t
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, t, h => by
    cases s with
    | Z =>
      cases t with
      | Z => rw [code_Z, compareCode_zero_zero, compareT_ZZ]
      | P w b => rw [code_Z, code_P, compareT_ZP, compareCode]
    | P v a =>
      cases t with
      | Z => rw [code_Z, code_P, compareT_PZ, compareCode]
      | P w b =>
        rw [code_P, code_P, compareCode, compareT_PP, compareArgs_trim_left,
          compareArgs_trim_right]
        have hv : compareArgs (codes v) (codes w) = compareV v w := by
          rw [compareArgs_eq_cmpC (v.length + w.length) _ _ (by rw [codes_length]; omega)
            (by rw [codes_length]; omega)]
          have hfun : cget (codes v) = fun i => code (V.get0 v i) := funext (codes_get v)
          have hgun : cget (codes w) = fun i => code (V.get0 w i) := funext (codes_get w)
          rw [hfun, hgun, cmpC_code_eq_cmpUpTo, ← compareV_eq_cmpUpTo v w _ (by omega) (by omega)]
          intro i _
          apply compareCode_code_aux n
          have h1 := multi.V.size_get0_le v i
          have h2 := multi.V.size_get0_le w i
          have h3 : (multi.T.P v a).size = multi.V.size v + a.size + 1 := rfl
          have h4 : (multi.T.P w b).size = multi.V.size w + b.size + 1 := rfl
          omega
        rw [hv]
        cases compareV v w with
        | lt => rfl
        | gt => rfl
        | eq =>
          show compareCode (code a) (code b) = compareT a b
          apply compareCode_code_aux n
          have h3 : (multi.T.P v a).size = multi.V.size v + a.size + 1 := rfl
          have h4 : (multi.T.P w b).size = multi.V.size w + b.size + 1 := rfl
          omega

theorem compareCode_code (s t : multi.T) : compareCode (code s) (code t) = compareT s t :=
  compareCode_code_aux _ s t (Nat.lt_succ_self _)

theorem code_eq_iff (s t : multi.T) : code s = code t ↔ multi.T.norm s = multi.T.norm t := by
  constructor
  · intro h
    have h1 := compareCode_code s s
    rw [compareT_self] at h1
    rw [← compareT_eq_iff, ← compareCode_code, ← h]
    exact h1
  · intro h
    rw [← code_norm s, ← code_norm t, h]

theorem code_congr {s t : multi.T} (h : compareT s t = .eq) : code s = code t :=
  (code_eq_iff s t).2 ((compareT_eq_iff s t).1 h)

/-! ### Fixed dimension and padding -/

mutual
  /-- All vectors occurring in the term have length exactly `d`. -/
  def Dim (d : Nat) : multi.T → Prop
    | .Z => True
    | .P v a => v.length = d ∧ DimV d v ∧ Dim d a

  def DimV (d : Nat) : V multi.T → Prop
    | .emp => True
    | .snoc x xs => Dim d x ∧ DimV d xs
end

theorem Dim_Z (d : Nat) : Dim d multi.T.Z := by rw [Dim]; trivial

theorem Dim_P_iff (d : Nat) (v : V multi.T) (a : multi.T) :
    Dim d (multi.T.P v a) ↔ v.length = d ∧ DimV d v ∧ Dim d a := by rw [Dim]

theorem DimV_iff (d : Nat) (v : V multi.T) : DimV d v ↔ ∀ i, Dim d (V.get0 v i) := by
  induction v with
  | emp => rw [DimV]; exact ⟨fun _ _ => Dim_Z d, fun _ => trivial⟩
  | snoc x xs ih =>
    rw [DimV, ih]
    constructor
    · rintro ⟨hx, hxs⟩ i
      show Dim d (if i = xs.length then x else V.get0 xs i)
      by_cases hi : i = xs.length
      · rw [ite_eq_left hi]; exact hx
      · rw [ite_eq_right hi]; exact hxs i
    · intro h
      refine ⟨by have := h xs.length; rwa [V.get0_snoc_top] at this, fun i => ?_⟩
      by_cases hi : i < xs.length
      · have := h i; rwa [V.get0_snoc_low x xs i hi] at this
      · rw [V.get0_ge xs i (Nat.le_of_not_lt hi)]; exact Dim_Z d

theorem Dim_P {d : Nat} {v : V multi.T} {a : multi.T} (hl : v.length = d)
    (hv : ∀ i, Dim d (V.get0 v i)) (ha : Dim d a) : Dim d (multi.T.P v a) :=
  (Dim_P_iff d v a).2 ⟨hl, (DimV_iff d v).2 hv, ha⟩

theorem Dim.length {d : Nat} {v : V multi.T} {a : multi.T} (h : Dim d (multi.T.P v a)) :
    v.length = d := ((Dim_P_iff d v a).1 h).1

theorem Dim.coord {d : Nat} {v : V multi.T} {a : multi.T} (h : Dim d (multi.T.P v a)) (i : Nat) :
    Dim d (V.get0 v i) := (DimV_iff d v).1 ((Dim_P_iff d v a).1 h).2.1 i

theorem Dim.tail {d : Nat} {v : V multi.T} {a : multi.T} (h : Dim d (multi.T.P v a)) :
    Dim d a := ((Dim_P_iff d v a).1 h).2.2

/-- Extend a vector with `k` zero coordinates on top. -/
def extendZ (v : V multi.T) : Nat → V multi.T
  | 0 => v
  | k + 1 => .snoc .Z (extendZ v k)

theorem length_extendZ (v : V multi.T) : ∀ k, (extendZ v k).length = v.length + k
  | 0 => rfl
  | k + 1 => by
    show (extendZ v k).length + 1 = v.length + (k + 1)
    rw [length_extendZ v k]; omega

theorem get0_extendZ (v : V multi.T) : ∀ k i, V.get0 (extendZ v k) i = V.get0 v i
  | 0, _ => rfl
  | k + 1, i => by
    show (if i = (extendZ v k).length then multi.T.Z else V.get0 (extendZ v k) i) = _
    by_cases hi : i = (extendZ v k).length
    · rw [ite_eq_left hi, V.get0_ge v i (by rw [hi, length_extendZ]; omega)]
    · rw [ite_eq_right hi, get0_extendZ v k i]

mutual
  /-- Pad all vectors of the term to length `d` (structurally). -/
  def padN (d : Nat) : multi.T → multi.T
    | .Z => .Z
    | .P v a => .P (extendZ (padMap d v) (d - v.length)) (padN d a)

  def padMap (d : Nat) : V multi.T → V multi.T
    | .emp => .emp
    | .snoc x xs => .snoc (padN d x) (padMap d xs)
end

theorem padN_Z (d : Nat) : padN d multi.T.Z = multi.T.Z := by rw [padN]

theorem padN_P (d : Nat) (v : V multi.T) (a : multi.T) :
    padN d (multi.T.P v a) = .P (extendZ (padMap d v) (d - v.length)) (padN d a) := by rw [padN]

theorem length_padMap (d : Nat) (v : V multi.T) : (padMap d v).length = v.length := by
  induction v with
  | emp => rw [padMap]
  | snoc x xs ih => rw [padMap]; show (padMap d xs).length + 1 = xs.length + 1; rw [ih]

theorem get0_padMap (d : Nat) (v : V multi.T) (i : Nat) :
    V.get0 (padMap d v) i = padN d (V.get0 v i) := by
  induction v with
  | emp => rw [padMap]; show multi.T.Z = padN d multi.T.Z; rw [padN_Z]
  | snoc x xs ih =>
    rw [padMap]
    show (if i = (padMap d xs).length then padN d x else V.get0 (padMap d xs) i) =
      padN d (if i = xs.length then x else V.get0 xs i)
    rw [length_padMap]
    by_cases hi : i = xs.length
    · rw [ite_eq_left hi, ite_eq_left hi]
    · rw [ite_eq_right hi, ite_eq_right hi, ih]

mutual
  /-- Width of a term: the largest trimmed vector length occurring in it. -/
  def tWidth : multi.T → Nat
    | .Z => 0
    | .P v a => max (V.trim v).length (max (vWidth v) (tWidth a))

  def vWidth : V multi.T → Nat
    | .emp => 0
    | .snoc x xs => max (tWidth x) (vWidth xs)
end

theorem vWidth_get0 (v : V multi.T) (i : Nat) : tWidth (V.get0 v i) ≤ vWidth v := by
  induction v with
  | emp => show tWidth multi.T.Z ≤ _; rw [tWidth]; exact Nat.zero_le _
  | snoc x xs ih =>
    show tWidth (if i = xs.length then x else V.get0 xs i) ≤ vWidth (.snoc x xs)
    rw [vWidth]
    by_cases hi : i = xs.length
    · rw [ite_eq_left hi]; exact Nat.le_max_left _ _
    · rw [ite_eq_right hi]; exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem vWidth_le (v : V multi.T) (n : Nat) (h : ∀ i, tWidth (V.get0 v i) ≤ n) : vWidth v ≤ n := by
  induction v with
  | emp => rw [vWidth]; exact Nat.zero_le _
  | snoc x xs ih =>
    rw [vWidth]
    refine Nat.max_le.2 ⟨by have := h xs.length; rwa [V.get0_snoc_top] at this, ih (fun i => ?_)⟩
    by_cases hi : i < xs.length
    · have := h i; rwa [V.get0_snoc_low x xs i hi] at this
    · rw [V.get0_ge xs i (Nat.le_of_not_lt hi), tWidth]; exact Nat.zero_le _

/-- The fixed-dimension representative of a term in dimension `d`. -/
def padTo (d : Nat) (s : multi.T) : multi.T := padN d (multi.T.norm s)

theorem padN_Dim (d : Nat) : ∀ s : multi.T, multi.T.norm s = s → tWidth s ≤ d → Dim d (padN d s)
  | .Z, _, _ => by rw [padN_Z]; exact Dim_Z d
  | .P v a, hn, hw => by
    rw [multi.T.norm_P] at hn
    injection hn with hv ha
    rw [tWidth] at hw
    have htrim : V.trim v = v := by rw [← hv, multi.V.norm, multi.V.trim_trim]
    rw [htrim] at hw
    have hw1 := Nat.le_trans (Nat.le_max_left _ _) hw
    have hw2 := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_right _ _) hw)
    have hw3 := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _) hw)
    rw [padN_P]
    refine Dim_P ?_ (fun i => ?_) (padN_Dim d a ha hw3)
    · rw [length_extendZ, length_padMap]; omega
    · rw [get0_extendZ, get0_padMap]
      apply padN_Dim d
      · have h1 : multi.T.norm (V.get0 v i) = V.get0 v i := by rw [← multi.V.get0_norm, hv]
        exact h1
      · exact Nat.le_trans (vWidth_get0 v i) hw2
termination_by s => s.size
decreasing_by
  · exact multi.T.size_get0_lt_P _ _ _
  · exact multi.T.size_lt_P_right _ _

theorem tWidth_norm_le_code (s : multi.T) : tWidth (multi.T.norm s) = tWidth (multi.T.norm s) := rfl

mutual
  theorem code_padN (d : Nat) : ∀ s : multi.T, code (padN d s) = code s
    | .Z => by rw [padN_Z]
    | .P v a => by
      rw [padN_P, code_P, code_P, code_padN d a]
      congr 1
      rw [trim_codes, trim_codes]
      have h1 : codes (V.trim (extendZ (padMap d v) (d - v.length))) = codes (V.trim (padMap d v)) := by
        rw [← trim_codes, ← trim_codes]
        generalize d - v.length = k
        induction k with
        | zero => rfl
        | succ k ih =>
          show trim (codes (V.snoc multi.T.Z (extendZ (padMap d v) k))) = _
          rw [codes_snoc, code_Z, trim_append_zero, ih]
      rw [h1, ← trim_codes, ← trim_codes, codes_padMap d v]

  theorem codes_padMap (d : Nat) : ∀ v : V multi.T, codes (padMap d v) = codes v
    | .emp => by rw [padMap]
    | .snoc x xs => by rw [padMap, codes_snoc, codes_snoc, codes_padMap d xs, code_padN d x]
end

theorem code_padTo (d : Nat) (s : multi.T) : code (padTo d s) = code s := by
  rw [padTo, code_padN, code_norm]

theorem padN_of_Dim (d : Nat) : ∀ s : multi.T, Dim d s → padN d s = s
  | .Z, _ => padN_Z d
  | .P v a, h => by
    rw [padN_P, h.length, Nat.sub_self, padN_of_Dim d a h.tail]
    show multi.T.P (padMap d v) a = multi.T.P v a
    congr 1
    apply V.eq_of_get0 _ _ (length_padMap d v)
    intro i
    rw [get0_padMap, padN_of_Dim d _ (h.coord i)]
termination_by s => s.size
decreasing_by
  · exact multi.T.size_lt_P_right _ _
  · exact multi.T.size_get0_lt_P _ _ _

/-- Padding the normal form of a fixed-dimension term recovers it. -/
theorem padN_norm_of_Dim (d : Nat) : ∀ s : multi.T, Dim d s → padN d (multi.T.norm s) = s
  | .Z, _ => by rw [multi.T.norm, padN_Z]
  | .P v a, h => by
    rw [multi.T.norm_P, padN_P, padN_norm_of_Dim d a h.tail]
    congr 1
    apply V.eq_of_get0
    · rw [length_extendZ, length_padMap]
      have h1 : (V.norm v).length ≤ v.length := by
        unfold multi.V.norm
        have := multi.V.length_trim_le (V.mapNorm v)
        rwa [multi.V.length_mapNorm] at this
      have h2 := h.length
      omega
    · intro i
      rw [get0_extendZ, get0_padMap, multi.V.get0_norm, padN_norm_of_Dim d _ (h.coord i)]
termination_by s => s.size
decreasing_by
  · exact multi.T.size_lt_P_right _ _
  · exact multi.T.size_get0_lt_P _ _ _

theorem padTo_of_Dim {d : Nat} {s : multi.T} (h : Dim d s) : padTo d s = s :=
  padN_norm_of_Dim d s h

theorem padTo_congr {d : Nat} {s t : multi.T} (h : code s = code t) : padTo d s = padTo d t := by
  rw [padTo, padTo, (code_eq_iff s t).1 h]

/-- Fixed-dimension terms with the same code are equal. -/
theorem eq_of_code_eq {d : Nat} {s t : multi.T} (hs : Dim d s) (ht : Dim d t)
    (h : code s = code t) : s = t := by
  rw [← padTo_of_Dim hs, ← padTo_of_Dim ht, padTo_congr h]

theorem eq_of_compare_eq {d : Nat} {s t : multi.T} (hs : Dim d s) (ht : Dim d t)
    (h : compareT s t = .eq) : s = t :=
  eq_of_code_eq hs ht (code_congr h)

/-! ### Vectors of a fixed length -/

def vOf (f : Nat → multi.T) : Nat → V multi.T
  | 0 => .emp
  | n + 1 => .snoc (f n) (vOf f n)

theorem vOf_length (f : Nat → multi.T) : ∀ n, (vOf f n).length = n
  | 0 => rfl
  | n + 1 => by show (vOf f n).length + 1 = n + 1; rw [vOf_length f n]

theorem get0_vOf (f : Nat → multi.T) :
    ∀ n j, V.get0 (vOf f n) j = if j < n then f j else multi.T.Z
  | 0, j => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | n + 1, j => by
    show (if j = (vOf f n).length then f n else V.get0 (vOf f n) j) = _
    rw [vOf_length, get0_vOf f n j]
    by_cases hjn : j = n
    · rw [ite_eq_left hjn, ite_eq_left (by omega), hjn]
    · rw [ite_eq_right hjn]
      by_cases hj : j < n
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
      · rw [ite_eq_right hj, ite_eq_right (by omega)]

theorem vOf_get0 (v : V multi.T) : vOf (V.get0 v) v.length = v := by
  apply V.eq_of_get0 _ _ (vOf_length _ _)
  intro j
  rw [get0_vOf]
  by_cases hj : j < v.length
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj, V.get0_ge v j (Nat.le_of_not_lt hj)]

theorem vOf_ext {f g : Nat → multi.T} {n : Nat} (h : ∀ j, j < n → f j = g j) : vOf f n = vOf g n := by
  apply V.eq_of_get0 _ _ (by rw [vOf_length, vOf_length])
  intro j
  rw [get0_vOf, get0_vOf]
  by_cases hj : j < n
  · rw [ite_eq_left hj, ite_eq_left hj, h j hj]
  · rw [ite_eq_right hj, ite_eq_right hj]

theorem Dim_vOf {d : Nat} {f : Nat → multi.T} (hf : ∀ j, j < d → Dim d (f j)) (a : multi.T)
    (ha : Dim d a) : Dim d (multi.T.P (vOf f d) a) := by
  refine Dim_P (vOf_length f d) (fun i => ?_) ha
  rw [get0_vOf]
  by_cases hi : i < d
  · rw [ite_eq_left hi]; exact hf i hi
  · rw [ite_eq_right hi]; exact Dim_Z d

/-- The zero vector of length `m`. -/
def zeros (m : Nat) : V multi.T := vOf (fun _ => multi.T.Z) m

theorem get0_zeros (m j : Nat) : V.get0 (zeros m) j = multi.T.Z := by
  rw [zeros, get0_vOf]; split <;> rfl

theorem zeros_length (m : Nat) : (zeros m).length = m := vOf_length _ _

theorem zeros_succ (m : Nat) : zeros (m + 1) = .snoc multi.T.Z (zeros m) := rfl

theorem fnz_zeros (m : Nat) : V.fnz (zeros m) = none := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [zeros_succ, V.fnz, ih]
    simp

/-- The natural number `n` in dimension `d`. -/
def ofNatD (d : Nat) : Nat → multi.T
  | 0 => .Z
  | n + 1 => .P (zeros d) (ofNatD d n)

theorem Dim_ofNatD (d : Nat) : ∀ n, Dim d (ofNatD d n)
  | 0 => Dim_Z d
  | n + 1 => Dim_P (zeros_length d) (fun i => by rw [get0_zeros]; exact Dim_Z d) (Dim_ofNatD d n)

/-- The tower `T.LF lam n` of the fixed-dimension system, as a term of dimension `lam`. -/
def towerD : Nat → Nat → multi.T
  | _, 0 => .Z
  | 0, n + 1 => .P .emp (towerD 0 n)
  | lam + 1, n + 1 => .P (vOf (fun i => if i = lam then towerD (lam + 1) n else .Z) (lam + 1)) .Z

theorem Dim_towerD : ∀ lam n, Dim lam (towerD lam n)
  | _, 0 => by rw [towerD]; exact Dim_Z _
  | 0, n + 1 => by
    rw [towerD]
    exact Dim_P rfl (fun i => Dim_Z 0) (Dim_towerD 0 n)
  | lam + 1, n + 1 => by
    rw [towerD]
    apply Dim_vOf _ _ (Dim_Z _)
    intro j _
    split
    · exact Dim_towerD (lam + 1) n
    · exact Dim_Z _

/-- The generators of OT in dimension `lam + 1`. -/
def baseD (lam n : Nat) : multi.T :=
  .P (vOf (fun i => if i = 0 then towerD (lam + 1) n else .Z) (lam + 1)) .Z

/-- The OT terms of the fixed-dimension system, as `multi` terms of dimension `lam`. -/
inductive DOT : (lam : Nat) → multi.T → Prop
  | base_0 (n : Nat) : DOT 0 (towerD 0 n)
  | base_succ (lam n : Nat) : DOT (lam + 1) (baseD lam n)
  | step (lam : Nat) (s : multi.T) (hs : DOT lam s) (n : Nat) : DOT lam (T.fund s (ofNatD lam n))

def OTD (lam : Nat) := { s : multi.T // DOT lam s }

/-! ### Classes of OT terms -/

def AllOT := (lam : Nat) × OTD lam

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
    ∃ lam, ∃ s : OTD lam, classOf ⟨lam, s⟩ = q := by
  obtain ⟨⟨lam, s⟩, h⟩ := exists_rep q
  exact ⟨lam, s, h⟩

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

theorem code_normal_aux : ∀ (n : Nat) (s : multi.T), s.size < n → (code s).normal
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, h => by
    cases s with
    | Z => rw [code_Z, Code.normal]; trivial
    | P v a =>
      rw [code_P, Code.normal]
      have hsz : (multi.T.P v a).size = multi.V.size v + a.size + 1 := rfl
      refine ⟨trim_noTrailingZero _, fun x hx => ?_, code_normal_aux n a (by omega)⟩
      have hx' := mem_trim hx
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx'
      have hci := codes_get v i
      unfold cget at hci
      rw [List.getElem?_eq_getElem hi] at hci
      simp only [Option.getD_some] at hci
      rw [← he, hci]
      apply code_normal_aux n
      have := multi.V.size_get0_le v i
      omega

theorem code_normal (s : multi.T) : (code s).normal := code_normal_aux _ s (Nat.lt_succ_self _)

theorem representative_normal (q : Classes) : (representative q).normal := by
  induction q using Quotient.inductionOn with
  | h s => exact code_normal s.2.val

end kumakuma.OTQuotient

namespace kumakuma.FiniteCorrespondence

open multi OCF.Jaeger kumakuma.OTQuotient

def natCode : Nat → Code
  | 0 => .zero
  | n + 1 => .p [] (natCode n)

theorem trim_codes_zeros (k : Nat) : trim (codes (zeros k)) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [zeros_succ, codes_snoc, code_Z, trim_append_zero, ih]

theorem code_ofNatD (d n : Nat) : code (ofNatD d n) = natCode n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofNatD, code_P, trim_codes_zeros, ih]; rfl

theorem code_ofNat (n : Nat) : code (multi.T.ofNat n) = natCode n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [multi.T.ofNat, code_P, ih]; rfl

theorem ofNatD_zero_eq_tower (n : Nat) : ofNatD 0 n = towerD 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ofNatD, towerD, ih]; rfl

theorem ofNat_isOT_zero (n : Nat) : DOT 0 (ofNatD 0 n) := by
  rw [ofNatD_zero_eq_tower]
  exact DOT.base_0 n

theorem zero_dimension_exhaustive : ∀ s : multi.T, Dim 0 s → ∃ n, s = ofNatD 0 n
  | .Z, _ => ⟨0, rfl⟩
  | .P v a, h => by
    obtain ⟨n, hn⟩ := zero_dimension_exhaustive a h.tail
    have hv : v = zeros 0 := by
      cases v with
      | emp => rfl
      | snoc x xs => have := h.length; simp [V.length] at this
    exact ⟨n + 1, by rw [hv, hn]; rfl⟩

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

end kumakuma.FiniteCorrespondence

namespace kumakuma.OTQuotient

open multi

def classCompare (q r : Classes) : Ordering := compareCode (representative q) (representative r)

def ClassLT (q r : Classes) : Prop := classCompare q r = .lt

theorem compareCode_mixed (s t : multi.T) : compareCode (code s) (code t) = compareT s t :=
  compareCode_code s t

theorem classCompare_eq_iff (q r : Classes) : classCompare q r = .eq ↔ q = r := by
  induction q using Quotient.inductionOn with
  | h s =>
    induction r using Quotient.inductionOn with
    | h t =>
      constructor
      · intro h
        change compareCode (code s.2.val) (code t.2.val) = .eq at h
        rw [compareCode_code] at h
        exact (class_eq_iff s t).mpr (code_congr h)
      · intro h
        have hc := (class_eq_iff s t).mp h
        change compareCode (code s.2.val) (code t.2.val) = .eq
        rw [hc, compareCode_code]
        exact compareT_self _

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
  change compareCode (code s.2.val) (code v.2.val) = .lt at hqr
  change compareCode (code v.2.val) (code w.2.val) = .lt at hrt
  change compareCode (code s.2.val) (code w.2.val) = .lt
  rw [compareCode_code] at hqr hrt ⊢
  exact multi.T.lt_trans hqr hrt

theorem classLT_total (q r : Classes) : ClassLT q r ∨ ClassLT r q ∨ q = r := by
  obtain ⟨s, rfl⟩ := exists_rep q
  obtain ⟨t, rfl⟩ := exists_rep r
  rcases multi.T.lt_trichotomy s.2.val t.2.val with h | h | h
  · apply Or.inl
    change compareCode (code s.2.val) (code t.2.val) = .lt
    rw [compareCode_code]; exact h
  · apply Or.inr ∘ Or.inr
    exact (class_eq_iff s t).mpr ((code_eq_iff _ _).2 h)
  · apply Or.inr ∘ Or.inl
    change compareCode (code t.2.val) (code s.2.val) = .lt
    rw [compareCode_code]; exact h

end kumakuma.OTQuotient

namespace kumakuma.Unary

open OCF.Jaeger

private theorem omega_lt_self : Term.lt Term.bigOmega Term.bigOmega = false := by
  decide +kernel

theorem psi_omega_lt (a b : Term) :
    Term.lt (.psi Term.bigOmega a) (.psi Term.bigOmega b) = Term.lt a b := by
  simp only [Term.lt, omega_lt_self, Bool.false_and, Bool.false_or,
    decide_true, Bool.true_and, Bool.or_false]

end kumakuma.Unary

namespace kumakuma

open OCF.Jaeger

def WFBelowOmega := { t : Term // Term.wf t = true ∧ Term.lt t Term.bigOmega = true }

end kumakuma

namespace kumakuma.BinaryTranslation

open OCF.Jaeger

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

end kumakuma.BinaryTranslation

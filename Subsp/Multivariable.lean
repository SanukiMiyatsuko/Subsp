import Subsp.Base

namespace new
namespace Multi

mutual
  /-- An unindexed term used to compare fixed-arity terms across different arities. -/
  inductive UTerm where
  | Z : UTerm
  | P (ls : UVec) (add : UTerm) : UTerm

  /-- Unindexed vectors, kept in the same snoc orientation as `Vec`. -/
  inductive UVec where
  | nil : UVec
  | snoc (init : UVec) (last : UTerm) : UVec
end

mutual
  /--
  Normalize a term by recursively normalizing all subterms and removing trailing
  zero coordinates from every principal vector.
  -/
  def UTerm.normalize : UTerm → UTerm
  | .Z => .Z
  | .P ls add => .P (UVec.normalize ls) (UTerm.normalize add)

  /-- Normalize entries without changing the vector length. -/
  def UVec.mapNormalize : UVec → UVec
  | .nil => .nil
  | .snoc xs x => .snoc (UVec.mapNormalize xs) (UTerm.normalize x)

  /-- Normalize entries and discard exactly the trailing zero coordinates. -/
  def UVec.normalize : UVec → UVec
  | .nil => .nil
  | .snoc xs x =>
      match UTerm.normalize x with
      | .Z => UVec.normalize xs
      | x' => .snoc (UVec.mapNormalize xs) x'
end

mutual
  /-- Forget the fixed arity of an indexed term. -/
  def UTerm.ofT {n : Nat} : T n → UTerm
  | .Z => .Z
  | .P ls add => .P (UVec.ofVec ls) (UTerm.ofT add)

  /-- Forget the length index of a vector. -/
  def UVec.ofVec {n m : Nat} : Vec (T n) m → UVec
  | .nil => .nil
  | .snoc _ xs x => .snoc (UVec.ofVec xs) (UTerm.ofT x)
end

def UVec.length : UVec → Nat
| .nil => 0
| .snoc xs _ => length xs + 1

mutual
  /--
  The least ambient arity suggested by an unindexed term: it bounds both every
  principal vector length and the arities required by all nested subterms.
  -/
  def UTerm.arity : UTerm → Nat
  | .Z => 0
  | .P ls add =>
      Nat.max (UVec.length ls) (Nat.max (UVec.maxArity ls) (UTerm.arity add))

  def UVec.maxArity : UVec → Nat
  | .nil => 0
  | .snoc xs x => Nat.max (UVec.maxArity xs) (UTerm.arity x)
end

def vecGetD {A : Type} {m : Nat} (v : Vec A m) (fallback : A) (i : Nat) : A :=
  if h : i < m then v.idx ⟨i, h⟩ else fallback

mutual
  /--
  Compile an unindexed term into any requested fixed arity. Coordinates beyond
  the unindexed vector are padded by `Z`; excess coordinates are truncated.
  -/
  def UTerm.compile (n : Nat) : UTerm → T n
  | .Z => T.Z
  | .P ls add =>
      match UVec.compileElems n ls with
      | ⟨_, v⟩ =>
          T.P (Vec.ofFn n (fun i => vecGetD v T.Z i.val)) (UTerm.compile n add)

  /-- Compile all entries while retaining their unindexed vector length. -/
  def UVec.compileElems (n : Nat) : UVec → Sigma (Vec (T n))
  | .nil => ⟨0, Vec.nil⟩
  | .snoc xs x =>
      match UVec.compileElems n xs with
      | ⟨m, v⟩ => ⟨m + 1, Vec.snoc m v (UTerm.compile n x)⟩
end

/-- The disjoint union of all fixed-arity term types. -/
abbrev RawT := Sigma T

/-- Canonical unindexed code of a raw fixed-arity term. -/
def RawT.code (s : RawT) : UTerm :=
  UTerm.normalize (UTerm.ofT s.2)

/--
Two raw terms are equivalent when they become identical after recursively
forgetting trailing zero coordinates.
-/
def RawT.Rel (s t : RawT) : Prop :=
  s.code = t.code

def rawSetoid : Setoid RawT where
  r := RawT.Rel
  iseqv := ⟨
    fun _ => rfl,
    fun h => h.symm,
    fun h₁ h₂ => h₁.trans h₂
  ⟩

/-- Genuine finite-multivariable terms, independent of a preselected arity. -/
abbrev Term := Quotient rawSetoid

def Term.ofFixed {n : Nat} (s : T n) : Term :=
  Quotient.mk rawSetoid ⟨n, s⟩

/-- The canonical unindexed code of a genuine multivariable term. -/
def Term.code : Term → UTerm :=
  Quotient.lift RawT.code (fun _ _ h => h)

/-- The canonical support bound extracted from the normalized code. -/
def Term.support (s : Term) : Nat :=
  UTerm.arity s.code

/--
A constructive fixed-arity realization of the canonical code.  Subsequent
lemmas will identify this with the least representative of the quotient class.
-/
def Term.representative (s : Term) : RawT :=
  ⟨s.support, UTerm.compile s.support s.code⟩

theorem UVec.normalize_snoc_Z (xs : UVec) :
    UVec.normalize (.snoc xs .Z) = UVec.normalize xs := by
  rfl

theorem Term.code_ofFixed {n : Nat} (s : T n) :
    (Term.ofFixed s).code = RawT.code ⟨n, s⟩ := by
  rfl


theorem UVec.length_mapNormalize :
    (xs : UVec) → UVec.length (UVec.mapNormalize xs) = UVec.length xs
  | .nil => rfl
  | .snoc xs x => by
      simp only [UVec.mapNormalize, UVec.length, UVec.length_mapNormalize xs]

theorem UVec.length_ofVec {n m : Nat} (v : Vec (T n) m) :
    UVec.length (UVec.ofVec v) = m := by
  induction v with
  | nil => rfl
  | snoc k xs x ih =>
      simp only [UVec.ofVec, UVec.length, ih]

theorem UVec.maxArity_mapNormalize_ofVec_le {n m : Nat}
    (v : Vec (T n) m)
    (h : ∀ i : Fin m,
      UTerm.arity (UTerm.normalize (UTerm.ofT (v.idx i))) ≤ n) :
    UVec.maxArity (UVec.mapNormalize (UVec.ofVec v)) ≤ n := by
  induction v with
  | nil =>
      simp [UVec.ofVec, UVec.mapNormalize, UVec.maxArity]
  | snoc k xs x ih =>
      have hxs : ∀ i : Fin k,
          UTerm.arity (UTerm.normalize (UTerm.ofT (xs.idx i))) ≤ n := by
        intro i
        simpa [Vec.idx, i.isLt] using h i.castSucc
      have hx :
          UTerm.arity (UTerm.normalize (UTerm.ofT x)) ≤ n := by
        simpa [Vec.idx] using h (Fin.last k)
      have hih := ih hxs
      simp only [UVec.ofVec, UVec.mapNormalize, UVec.maxArity]
      exact (Nat.max_le).2 ⟨hih, hx⟩

theorem UVec.normalize_ofVec_bounds {n m : Nat}
    (v : Vec (T n) m)
    (h : ∀ i : Fin m,
      UTerm.arity (UTerm.normalize (UTerm.ofT (v.idx i))) ≤ n) :
    UVec.length (UVec.normalize (UVec.ofVec v)) ≤ m ∧
      UVec.maxArity (UVec.normalize (UVec.ofVec v)) ≤ n := by
  induction v with
  | nil =>
      simp [UVec.ofVec, UVec.normalize, UVec.length, UVec.maxArity]
  | snoc k xs x ih =>
      have hxs : ∀ i : Fin k,
          UTerm.arity (UTerm.normalize (UTerm.ofT (xs.idx i))) ≤ n := by
        intro i
        simpa [Vec.idx, i.isLt] using h i.castSucc
      have hx :
          UTerm.arity (UTerm.normalize (UTerm.ofT x)) ≤ n := by
        simpa [Vec.idx] using h (Fin.last k)
      have hih := ih hxs
      simp only [UVec.ofVec, UVec.normalize]
      cases hnx : UTerm.normalize (UTerm.ofT x) with
      | Z =>
          simpa [hnx] using ⟨Nat.le_trans hih.1 (Nat.le_succ k), hih.2⟩
      | P ls add =>
          have hmap :=
            UVec.maxArity_mapNormalize_ofVec_le xs hxs
          have hlen :
              UVec.length (UVec.mapNormalize (UVec.ofVec xs)) = k := by
            rw [UVec.length_mapNormalize, UVec.length_ofVec]
          rw [hnx] at hx
          simp only [hnx, UVec.length, UVec.maxArity]
          constructor
          · omega
          · exact (Nat.max_le).2 ⟨hmap, hx⟩

theorem RawT.code_arity_le (n : Nat) (s : T n) :
    UTerm.arity (RawT.code ⟨n, s⟩) ≤ n := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z =>
          simp [RawT.code, UTerm.ofT, UTerm.normalize, UTerm.arity]
      | P ls add =>
          have hadd :
              UTerm.arity (UTerm.normalize (UTerm.ofT add)) ≤ n :=
            ih add (T.add_size_lt_P ls add)
          have hcoords : ∀ i : Fin n,
              UTerm.arity
                (UTerm.normalize (UTerm.ofT (ls.idx i))) ≤ n := by
            intro i
            exact ih (ls.idx i) (T.idx_size_lt_P ls add i)
          have hv := UVec.normalize_ofVec_bounds ls hcoords
          simp only [RawT.code, UTerm.ofT, UTerm.normalize, UTerm.arity]
          exact (Nat.max_le).2 ⟨hv.1, (Nat.max_le).2 ⟨hv.2, hadd⟩⟩

theorem Term.support_le_fixed {n : Nat} (s : T n) :
    (Term.ofFixed s).support ≤ n := by
  exact RawT.code_arity_le n s


theorem Term.support_minimal {s : Term} {n : Nat} (t : T n)
    (h : Term.ofFixed t = s) :
    s.support ≤ n := by
  rw [← h]
  exact Term.support_le_fixed t

/-- Forgetting an `ofFn` reconstruction gives back the original vector. -/
theorem Vec.ofFn_eta {A : Type} {n : Nat} (v : Vec A n) :
    Vec.ofFn n (fun i => v.idx i) = v := by
  induction v with
  | nil => rfl
  | snoc k xs x ih =>
      simp only [Vec.ofFn]
      congr
      · simpa [Vec.idx] using ih
      · simp [Vec.idx]

/-- Compile an unindexed vector into a vector of any requested output length. -/
def UVec.compileVec (ambient len : Nat) (xs : UVec) : Vec (T ambient) len :=
  match UVec.compileElems ambient xs with
  | ⟨_, v⟩ =>
      Vec.ofFn len (fun i => vecGetD v T.Z i.val)

/-- The unindexed code obtained by compiling every entry without resizing. -/
def UVec.compiledCode (ambient : Nat) (xs : UVec) : UVec :=
  match UVec.compileElems ambient xs with
  | ⟨_, v⟩ => UVec.ofVec v

theorem UVec.compiledCode_nil (ambient : Nat) :
    UVec.compiledCode ambient .nil = .nil := by
  rfl

theorem UVec.compiledCode_snoc (ambient : Nat) (xs : UVec) (x : UTerm) :
    UVec.compiledCode ambient (.snoc xs x) =
      .snoc (UVec.compiledCode ambient xs)
        (UTerm.ofT (UTerm.compile ambient x)) := by
  cases h : UVec.compileElems ambient xs with
  | mk m v =>
      simp [UVec.compiledCode, UVec.compileElems, h, UVec.ofVec]

theorem UVec.compileElems_length (ambient : Nat) :
    (xs : UVec) →
      (UVec.compileElems ambient xs).1 = UVec.length xs
  | .nil => rfl
  | .snoc xs x => by
      cases h : UVec.compileElems ambient xs with
      | mk m v =>
          have ih := UVec.compileElems_length ambient xs
          rw [h] at ih
          simp [UVec.compileElems, h, UVec.length, ih]

theorem UVec.ofVec_compileElems (ambient : Nat) (xs : UVec) :
    (match UVec.compileElems ambient xs with
     | ⟨_, v⟩ => UVec.ofVec v) =
      UVec.compiledCode ambient xs := by
  rfl

theorem UVec.normalize_ofVec_resize {ambient m k : Nat}
    (v : Vec (T ambient) m) (h : m ≤ k) :
    UVec.normalize
        (UVec.ofVec
          (Vec.ofFn k (fun i => vecGetD v T.Z i.val))) =
      UVec.normalize (UVec.ofVec v) := by
  induction k generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero h
      subst m
      cases v
      rfl
  | succ k ih =>
      by_cases hm : m = k + 1
      · subst m
        have hf :
            (fun i : Fin (k + 1) => vecGetD v T.Z i.val) =
              (fun i => v.idx i) := by
          funext i
          simp [vecGetD, i.isLt]
        rw [hf, Vec.ofFn_eta]
      · have hmk : m ≤ k := by omega
        simp only [Vec.ofFn, UVec.ofVec]
        have hlast : ¬ k < m := Nat.not_lt_of_ge hmk
        have hget :
            vecGetD v T.Z (Fin.last k).val = T.Z := by
          simp [vecGetD, hlast]
        rw [hget]
        simp only [UVec.normalize, UTerm.ofT, UTerm.normalize]
        simpa [vecGetD] using ih v hmk

theorem UVec.normalize_compileVec {ambient len : Nat}
    (xs : UVec) (h : UVec.length xs ≤ len) :
    UVec.normalize (UVec.ofVec (UVec.compileVec ambient len xs)) =
      UVec.normalize (UVec.compiledCode ambient xs) := by
  unfold UVec.compileVec
  cases hc : UVec.compileElems ambient xs with
  | mk m v =>
      have hm : m = UVec.length xs := by
        simpa [hc] using UVec.compileElems_length ambient xs
      have hmv : m ≤ len := hm ▸ h
      rw [UVec.normalize_ofVec_resize v hmv]
      change UVec.normalize (UVec.ofVec v) =
        UVec.normalize (UVec.compiledCode ambient xs)
      exact congrArg UVec.normalize
        (by
          change UVec.ofVec v =
            UVec.ofVec (UVec.compileElems ambient xs).2
          rw [hc])


mutual
  theorem UTerm.normalize_compile_normalize :
      (u : UTerm) → (n : Nat) →
        UTerm.arity (UTerm.normalize u) ≤ n →
        UTerm.normalize
            (UTerm.ofT (UTerm.compile n (UTerm.normalize u))) =
          UTerm.normalize u
    | .Z, n, h => rfl
    | .P ls add, n, h => by
        change
          Nat.max (UVec.length (UVec.normalize ls))
            (Nat.max (UVec.maxArity (UVec.normalize ls))
              (UTerm.arity (UTerm.normalize add))) ≤ n at h
        have hlen : UVec.length (UVec.normalize ls) ≤ n :=
          Nat.le_trans (Nat.le_max_left _ _) h
        have hrest :
            Nat.max (UVec.maxArity (UVec.normalize ls))
              (UTerm.arity (UTerm.normalize add)) ≤ n :=
          Nat.le_trans (Nat.le_max_right _ _) h
        have hvec : UVec.maxArity (UVec.normalize ls) ≤ n :=
          Nat.le_trans (Nat.le_max_left _ _) hrest
        have hadd : UTerm.arity (UTerm.normalize add) ≤ n :=
          Nat.le_trans (Nat.le_max_right _ _) hrest
        have hv :
            UVec.normalize
                (UVec.ofVec
                  (UVec.compileVec n n (UVec.normalize ls))) =
              UVec.normalize ls := by
          exact (UVec.normalize_compileVec
            (ambient := n) (len := n) (UVec.normalize ls) hlen).trans
              (UVec.normalize_compile_normalize ls n hvec)
        have ha :
            UTerm.normalize
                (UTerm.ofT
                  (UTerm.compile n (UTerm.normalize add))) =
              UTerm.normalize add :=
          UTerm.normalize_compile_normalize add n hadd
        change
          UTerm.P
              (UVec.normalize
                (UVec.ofVec
                  (UVec.compileVec n n (UVec.normalize ls))))
              (UTerm.normalize
                (UTerm.ofT
                  (UTerm.compile n (UTerm.normalize add)))) =
            UTerm.P (UVec.normalize ls) (UTerm.normalize add)
        rw [hv, ha]

  theorem UVec.mapNormalize_compile_normalize :
      (xs : UVec) → (n : Nat) →
        UVec.maxArity (UVec.mapNormalize xs) ≤ n →
        UVec.mapNormalize
            (UVec.compiledCode n (UVec.mapNormalize xs)) =
          UVec.mapNormalize xs
    | .nil, n, h => rfl
    | .snoc xs x, n, h => by
        change
          Nat.max (UVec.maxArity (UVec.mapNormalize xs))
            (UTerm.arity (UTerm.normalize x)) ≤ n at h
        have hxs : UVec.maxArity (UVec.mapNormalize xs) ≤ n :=
          Nat.le_trans (Nat.le_max_left _ _) h
        have hx : UTerm.arity (UTerm.normalize x) ≤ n :=
          Nat.le_trans (Nat.le_max_right _ _) h
        simp only [UVec.mapNormalize, UVec.compiledCode_snoc]
        have hv := UVec.mapNormalize_compile_normalize xs n hxs
        have ht := UTerm.normalize_compile_normalize x n hx
        rw [hv, ht]

  theorem UVec.normalize_compile_normalize :
      (xs : UVec) → (n : Nat) →
        UVec.maxArity (UVec.normalize xs) ≤ n →
        UVec.normalize
            (UVec.compiledCode n (UVec.normalize xs)) =
          UVec.normalize xs
    | .nil, n, h => rfl
    | .snoc xs x, n, h => by
        cases hnx : UTerm.normalize x with
        | Z =>
            have hxs : UVec.maxArity (UVec.normalize xs) ≤ n := by
              simpa [UVec.normalize, hnx] using h
            simpa [UVec.normalize, hnx] using
              UVec.normalize_compile_normalize xs n hxs
        | P ls add =>
            have h' :
                Nat.max (UVec.maxArity (UVec.mapNormalize xs))
                  (UTerm.arity (UTerm.P ls add)) ≤ n := by
              have hh := h
              rw [UVec.normalize, hnx] at hh
              change
                Nat.max (UVec.maxArity (UVec.mapNormalize xs))
                  (UTerm.arity (UTerm.P ls add)) ≤ n at hh
              exact hh
            have hxs : UVec.maxArity (UVec.mapNormalize xs) ≤ n :=
              Nat.le_trans (Nat.le_max_left _ _) h'
            have hx : UTerm.arity (UTerm.normalize x) ≤ n := by
              rw [hnx]
              exact Nat.le_trans (Nat.le_max_right _ _) h'
            have hmap :=
              UVec.mapNormalize_compile_normalize xs n hxs
            have hterm :
                UTerm.normalize
                    (UTerm.ofT
                      (UTerm.compile n (UTerm.P ls add))) =
                  UTerm.P ls add := by
              simpa [hnx] using
                UTerm.normalize_compile_normalize x n hx
            simp only [UVec.normalize, hnx, UVec.compiledCode_snoc]
            rw [hterm]
            exact congrArg
              (fun ys => UVec.snoc ys (UTerm.P ls add)) hmap
end

end Multi
end new

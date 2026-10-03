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
  | .P ls add => .P (UVec.normalize ls) (normalize add)

  /-- Normalize entries without changing the vector length. -/
  def UVec.mapNormalize : UVec → UVec
  | .nil => .nil
  | .snoc xs x => .snoc (mapNormalize xs) (UTerm.normalize x)

  /-- Normalize entries and discard exactly the trailing zero coordinates. -/
  def UVec.normalize : UVec → UVec
  | .nil => .nil
  | .snoc xs x =>
      match UTerm.normalize x with
      | .Z => normalize xs
      | x' => .snoc (mapNormalize xs) x'
end

mutual
  /-- Forget the fixed arity of an indexed term. -/
  def UTerm.ofT {n : Nat} : T n → UTerm
  | .Z => .Z
  | .P ls add => .P (UVec.ofVec ls) (ofT add)

  /-- Forget the length index of a vector. -/
  def UVec.ofVec {n m : Nat} : Vec (T n) m → UVec
  | .nil => .nil
  | .snoc _ xs x => .snoc (ofVec xs) (UTerm.ofT x)
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
      Nat.max (UVec.length ls) (Nat.max (UVec.maxArity ls) (arity add))

  def UVec.maxArity : UVec → Nat
  | .nil => 0
  | .snoc xs x => Nat.max (maxArity xs) (UTerm.arity x)
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
          T.P (Vec.ofFn n (fun i => vecGetD v T.Z i.val)) (compile n add)

  /-- Compile all entries while retaining their unindexed vector length. -/
  def UVec.compileElems (n : Nat) : UVec → Sigma (Vec (T n))
  | .nil => ⟨0, Vec.nil⟩
  | .snoc xs x =>
      match compileElems n xs with
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

end Multi
end new

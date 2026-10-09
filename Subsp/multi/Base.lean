import Subsp.order

namespace multi

inductive V (A : Type) where
| emp
| snoc (a : A) (ax : V A)

def V.length {A : Type} : V A → Nat
| .emp => 0
| .snoc _ ax => V.length ax + 1

def V.set {A : Type} (v : V A) (i : Nat) (a : A) : V A :=
  match v with
  | .emp => .emp
  | .snoc b bx =>
    if i = bx.length then
      .snoc a bx
    else
      .snoc b (V.set bx i a)

def V.append {A : Type} (u v : V A) : V A :=
  match u with
  | .emp => v
  | .snoc a ax => .snoc a (V.append ax v)

inductive T where
| Z
| P (vs : V T) (as : T)

open T

mutual
def decEqT : (a b : T) → Decidable (a = b)
  | Z, Z => isTrue rfl
  | Z, P _ _ => isFalse (fun h => by injection h)
  | P _ _, Z => isFalse (fun h => by injection h)
  | P vs0 as0, P vs1 as1 =>
    match decEqVT vs0 vs1 with
    | isTrue hl =>
      match decEqT as0 as1 with
      | isTrue ha => isTrue (by rw [hl, ha])
      | isFalse hna => isFalse (fun h => by injection h; contradiction)
    | isFalse hnl => isFalse (fun h => by injection h; contradiction)

def decEqVT : (a b : V T) → Decidable (a = b)
  | .emp, .emp => isTrue rfl
  | .emp, .snoc _ _ => isFalse (fun h => by injection h)
  | .snoc _ _, .emp => isFalse (fun h => by injection h)
  | .snoc a' ax, .snoc b' bx =>
    match decEqT a' b' with
    | isTrue hx =>
      match decEqVT ax bx with
      | isTrue hxs => isTrue (by rw [hx, hxs])
      | isFalse hnxs => isFalse (fun h => by injection h; contradiction)
    | isFalse hnx => isFalse (fun h => by injection h; contradiction)
end

instance : DecidableEq T := decEqT

instance : DecidableEq (V T) := decEqVT

mutual
def T.size : T → Nat
| Z => 0
| P vs as =>
  V.size vs + T.size as + 1

def V.size : V T → Nat
| .emp => 0
| .snoc a ax => T.size a + V.size ax + 1
end

def V.get0 : V T → Nat → T
  | .emp, _ => Z
  | .snoc a ax, i => if i = ax.length then a else V.get0 ax i

def V.fnz : V T → Option Nat
  | .emp => none
  | .snoc a ax =>
    match V.fnz ax with
    | some i => some i
    | none => if a ≠ Z then some ax.length else none

theorem V.size_get0_le : ∀ (v : V T) (i : Nat), (V.get0 v i).size ≤ v.size
  | .emp, i => by simp [V.get0, T.size, V.size]
  | .snoc a ax, i => by
    simp only [V.get0, V.size]
    by_cases hi : i = ax.length
    · simp only [hi, ite_true]; omega
    · simp only [hi, ite_false]
      have := V.size_get0_le ax i
      omega

theorem V.get0_ge : ∀ (v : V T) (i : Nat), v.length ≤ i → V.get0 v i = Z
  | .emp, i, _ => by simp [V.get0]
  | .snoc a ax, i, h => by
    simp only [V.length] at h
    have : i ≠ ax.length := by omega
    simp [V.get0, this, V.get0_ge ax i (by omega)]

def V.trim (vs : V T) : V T :=
  match vs with
  | .emp => .emp
  | .snoc a ax =>
    match a with
    | Z => trim ax
    | P _ _ => .snoc a ax

theorem V.length_trim_le : ∀ v : V T, (V.trim v).length ≤ v.length
  | .emp => by simp [V.trim]
  | .snoc a ax => by
    cases a with
    | Z => simp only [V.trim, V.length]; have := V.length_trim_le ax; omega
    | P _ _ => simp [V.trim]

theorem V.trim_snoc_ne {a : T} {ax : V T} (h : V.trim (.snoc a ax) = .snoc a ax) : a ≠ Z := by
  rintro rfl
  simp only [V.trim] at h
  have h1 := V.length_trim_le ax
  have h2 := congrArg V.length h
  simp only [V.length] at h2
  omega

theorem V.get0_trim : ∀ (v : V T) (i : Nat), V.get0 (V.trim v) i = V.get0 v i
  | .emp, i => by simp [V.trim]
  | .snoc a ax, i => by
    cases a with
    | Z =>
      simp only [V.trim, V.get0]
      rw [V.get0_trim ax i]
      by_cases hi : i = ax.length
      · subst hi; simp [V.get0_ge ax ax.length (Nat.le_refl _)]
      · simp [hi]
    | P vs as => simp [V.trim]

theorem V.size_trim_le (vs : V T) : vs.trim.size ≤ vs.size := by
  induction vs with
  | emp => simp [V.trim]
  | snoc a ax ih =>
    cases a with
    | Z => simp only [V.trim, V.size, T.size]; omega
    | P _ _ => simp [V.trim]

theorem V.eq_of_get0 : ∀ (a b : V T), a.length = b.length → (∀ i, V.get0 a i = V.get0 b i) → a = b
  | .emp, .emp, _, _ => rfl
  | .emp, .snoc _ _, h, _ => by simp only [V.length] at h; omega
  | .snoc _ _, .emp, h, _ => by simp only [V.length] at h; omega
  | .snoc a ax, .snoc b bx, hl, h => by
    simp only [V.length] at hl
    have hl' : ax.length = bx.length := by omega
    have hab : a = b := by
      have := h ax.length
      simpa [V.get0, hl'] using this
    subst hab
    have : ax = bx := V.eq_of_get0 ax bx hl' (fun i => by
      by_cases hi : i = ax.length
      · subst hi
        rw [V.get0_ge ax _ (Nat.le_refl _), V.get0_ge bx _ (by omega)]
      · have := h i
        simpa [V.get0, hi, show i ≠ bx.length by omega] using this)
    subst this; rfl

theorem V.length_le_of_trim : ∀ (c d : V T), V.trim c = c →
    (∀ i, V.get0 c i = V.get0 d i) → c.length ≤ d.length
  | .emp, d, _, _ => by simp [V.length]
  | .snoc a ax, d, tc, h => by
    apply Nat.le_of_not_lt
    intro hlt
    have hlt : d.length ≤ ax.length := by simp only [V.length] at hlt; omega
    have h1 := h ax.length
    have h2 : V.get0 d ax.length = Z := V.get0_ge d _ hlt
    have h3 : V.get0 (.snoc a ax) ax.length = a := by simp [V.get0]
    rw [h3, h2] at h1
    exact V.trim_snoc_ne tc h1

mutual
def compareT : T → T → Ordering
  | Z, Z => .eq
  | Z, P _ _ => .lt
  | P _ _, Z => .gt
  | P vs0 as0, P vs1 as1 =>
    match compareV vs0 vs1 with
    | .lt => .lt
    | .gt => .gt
    | .eq => compareT as0 as1
termination_by a b => (T.size a + T.size b, 2)
decreasing_by
  all_goals
    simp only [T.size]
    omega

def compareV' : V T → V T → Ordering
  | .emp, .emp => .eq
  | .emp, .snoc _ _ => .lt
  | .snoc _ _, .emp => .gt
  | .snoc a ax, .snoc b bx =>
    match compareT a b with
    | .lt => .lt
    | .gt => .gt
    | .eq => compareV' ax bx
termination_by a b => (V.size a + V.size b, 0)
decreasing_by
  all_goals
    simp only [V.size]
    omega

def compareV (a b : V T) : Ordering :=
  let ta := V.trim a
  let tb := V.trim b
  if ta.length < tb.length then
    .lt
  else if ta.length > tb.length then
    .gt
  else
    compareV' ta tb
termination_by (V.size a + V.size b, 1)
decreasing_by
  have := V.size_trim_le a
  have := V.size_trim_le b
  omega
end

instance : Ord T := ⟨compareT⟩

def T.lt (x y : T) : Prop := compareT x y = .lt
def T.le (x y : T) : Prop := compareT x y = .lt ∨ compareT x y = .eq

def V.lt (x y : V T) : Prop := compareV x y = .lt
def V.le (x y : V T) : Prop := compareV x y = .lt ∨ compareV x y = .eq

instance : LT T := ⟨T.lt⟩
instance : LE T := ⟨T.le⟩

instance : LT (V T) := ⟨V.lt⟩
instance : LE (V T) := ⟨V.le⟩

instance (x y : T) : Decidable (T.lt x y) :=
  inferInstanceAs (Decidable (compareT x y = .lt))

instance (x y : T) : Decidable (T.le x y) :=
  inferInstanceAs (Decidable (compareT x y = .lt ∨ compareT x y = .eq))

instance (x y : V T) : Decidable (V.lt x y) :=
  inferInstanceAs (Decidable (compareV x y = .lt))

instance (x y : V T) : Decidable (V.le x y) :=
  inferInstanceAs (Decidable (compareV x y = .lt ∨ compareV x y = .eq))

instance (x y : T) : Decidable (x < y) := inferInstanceAs (Decidable (T.lt x y))
instance (x y : T) : Decidable (x ≤ y) := inferInstanceAs (Decidable (T.le x y))

instance (x y : V T) : Decidable (x < y) := inferInstanceAs (Decidable (V.lt x y))
instance (x y : V T) : Decidable (x ≤ y) := inferInstanceAs (Decidable (V.le x y))

def T.oplus : T → T → T
| Z, t => t
| P ls add, t => P ls (T.oplus add t)

instance : Add T where
  add := T.oplus

def T.mul (s : T) : T → T
| Z => Z
| P _ add => s + mul s add

def T.iter (F : T → T) : T → T
| Z => Z
| P _ add => F (iter F add)

def T.ofNat : Nat → T
| 0 => Z
| n + 1 => P .emp (ofNat n)

mutual
def T.norm : T → T
  | Z => Z
  | P vs as => P (V.trim (V.mapNorm vs)) (T.norm as)

def V.mapNorm : V T → V T
  | .emp => .emp
  | .snoc a ax => .snoc (T.norm a) (V.mapNorm ax)
end

def V.norm (v : V T) : V T := V.trim (V.mapNorm v)

theorem T.norm_P (vs : V T) (as : T) : T.norm (P vs as) = P (V.norm vs) (T.norm as) := by
  simp [T.norm, V.norm]

theorem T.norm_eq_Z {t : T} : T.norm t = Z ↔ t = Z := by
  cases t <;> simp [T.norm]

theorem V.length_mapNorm (v : V T) : (V.mapNorm v).length = v.length := by
  induction v with
  | emp => simp [V.mapNorm]
  | snoc a ax ih => simp [V.mapNorm, V.length, ih]

theorem V.trim_mapNorm (v : V T) : V.trim (V.mapNorm v) = V.mapNorm (V.trim v) := by
  induction v with
  | emp => simp [V.mapNorm, V.trim]
  | snoc a ax ih =>
    cases a with
    | Z => simp [V.mapNorm, V.trim, T.norm, ih]
    | P vs as => simp [V.mapNorm, V.trim, T.norm]

theorem V.norm_eq (v : V T) : V.norm v = V.mapNorm (V.trim v) := V.trim_mapNorm v

theorem V.trim_trim (v : V T) : V.trim (V.trim v) = V.trim v := by
  induction v with
  | emp => simp [V.trim]
  | snoc a ax ih =>
    cases a with
    | Z => simp [V.trim, ih]
    | P vs as => simp [V.trim]

mutual
theorem T.norm_norm : ∀ t : T, T.norm (T.norm t) = T.norm t
  | Z => by simp [T.norm]
  | P vs as => by
    simp only [T.norm]
    rw [← V.trim_mapNorm, V.mapNorm_mapNorm, V.trim_trim, T.norm_norm as]

theorem V.mapNorm_mapNorm : ∀ v : V T, V.mapNorm (V.mapNorm v) = V.mapNorm v
  | .emp => by simp [V.mapNorm]
  | .snoc a ax => by simp [V.mapNorm, T.norm_norm a, V.mapNorm_mapNorm ax]
end

theorem V.norm_norm (v : V T) : V.norm (V.norm v) = V.norm v := by
  rw [V.norm_eq, V.norm_eq, V.trim_mapNorm, V.mapNorm_mapNorm, V.trim_trim]

def Cons (o1 o2 o3 : Ordering) : Prop :=
  (o1 = .lt → o2 = .lt → o3 = .lt) ∧ (o1 = .lt → o2 = .eq → o3 = .lt) ∧
  (o1 = .eq → o2 = .lt → o3 = .lt) ∧ (o1 = .eq → o2 = .eq → o3 = .eq)

theorem Cons.then {x1 x2 x3 y1 y2 y3 : Ordering} (hx : Cons x1 x2 x3) (hy : Cons y1 y2 y3) :
    Cons (x1.then y1) (x2.then y2) (x3.then y3) := by
  revert hx hy
  cases x1 <;> cases x2 <;> cases x3 <;> cases y1 <;> cases y2 <;> cases y3 <;>
    simp [Cons, Ordering.then]

theorem Ordering.then_eq_eq {x y : Ordering} : x.then y = .eq ↔ x = .eq ∧ y = .eq := by
  cases x <;> simp [Ordering.then]

def lenCmp (m n : Nat) : Ordering :=
  if m < n then .lt else if m > n then .gt else .eq

theorem lenCmp_of_lt {m n : Nat} (h : m < n) : lenCmp m n = .lt := by
  simp [lenCmp, h]

theorem lenCmp_of_gt {m n : Nat} (h : n < m) : lenCmp m n = .gt := by
  have h' : ¬ m < n := by omega
  simp [lenCmp, h', h]

theorem lenCmp_of_eq {m n : Nat} (h : m = n) : lenCmp m n = .eq := by
  subst h; simp [lenCmp]

theorem lenCmp_eq_lt {m n : Nat} : lenCmp m n = .lt ↔ m < n := by
  rcases Nat.lt_trichotomy m n with h | h | h
  · simp [lenCmp_of_lt h, h]
  · subst h; simp [lenCmp]
  · simp [lenCmp_of_gt h]; omega

theorem lenCmp_eq_eq {m n : Nat} : lenCmp m n = .eq ↔ m = n := by
  rcases Nat.lt_trichotomy m n with h | h | h
  · simp [lenCmp_of_lt h]; omega
  · subst h; simp [lenCmp]
  · simp [lenCmp_of_gt h]; omega

theorem lenCmp_swap (m n : Nat) : lenCmp m n = (lenCmp n m).swap := by
  rcases Nat.lt_trichotomy m n with h | h | h
  · rw [lenCmp_of_lt h, lenCmp_of_gt h]; rfl
  · subst h; simp [lenCmp]
  · rw [lenCmp_of_gt h, lenCmp_of_lt h]; rfl

theorem lenCmp_cons (m n p : Nat) : Cons (lenCmp m n) (lenCmp n p) (lenCmp m p) :=
  ⟨fun h1 h2 => lenCmp_eq_lt.2 (Nat.lt_trans (lenCmp_eq_lt.1 h1) (lenCmp_eq_lt.1 h2)),
   fun h1 h2 => lenCmp_eq_lt.2 (Nat.lt_of_lt_of_eq (lenCmp_eq_lt.1 h1) (lenCmp_eq_eq.1 h2)),
   fun h1 h2 => lenCmp_eq_lt.2 (Nat.lt_of_le_of_lt (Nat.le_of_eq (lenCmp_eq_eq.1 h1)) (lenCmp_eq_lt.1 h2)),
   fun h1 h2 => lenCmp_eq_eq.2 ((lenCmp_eq_eq.1 h1).trans (lenCmp_eq_eq.1 h2))⟩

theorem compareT_ZZ : compareT Z Z = .eq := by rw [compareT]
theorem compareT_ZP (vs : V T) (as : T) : compareT Z (P vs as) = .lt := by rw [compareT]
theorem compareT_PZ (vs : V T) (as : T) : compareT (P vs as) Z = .gt := by rw [compareT]
theorem compareT_PP (vs0 vs1 : V T) (as0 as1 : T) :
    compareT (P vs0 as0) (P vs1 as1) = (compareV vs0 vs1).then (compareT as0 as1) := by
  rw [compareT]
  cases compareV vs0 vs1 <;> rfl

theorem compareV'_ee : compareV' (.emp : V T) .emp = .eq := by rw [compareV']
theorem compareV'_es (b : T) (bx : V T) : compareV' .emp (.snoc b bx) = .lt := by rw [compareV']
theorem compareV'_se (a : T) (ax : V T) : compareV' (.snoc a ax) .emp = .gt := by rw [compareV']
theorem compareV'_ss (a b : T) (ax bx : V T) :
    compareV' (.snoc a ax) (.snoc b bx) = (compareT a b).then (compareV' ax bx) := by
  rw [compareV']
  cases compareT a b <;> rfl

theorem compareV_eq (a b : V T) :
    compareV a b = (lenCmp (V.trim a).length (V.trim b).length).then
      (compareV' (V.trim a) (V.trim b)) := by
  rw [compareV]
  by_cases h1 : (V.trim a).length < (V.trim b).length
  · simp [lenCmp_of_lt h1, h1, Ordering.then]
  · by_cases h2 : (V.trim b).length < (V.trim a).length
    · simp [lenCmp_of_gt h2, h1, h2, Ordering.then]
    · have h3 : (V.trim a).length = (V.trim b).length := by omega
      simp [lenCmp_of_eq h3, h1, h2, Ordering.then]

mutual
theorem compareT_swap : ∀ a b : T, compareT a b = (compareT b a).swap
  | Z, Z => by rw [compareT_ZZ]; rfl
  | Z, P vs as => by rw [compareT_ZP, compareT_PZ]; rfl
  | P vs as, Z => by rw [compareT_ZP, compareT_PZ]; rfl
  | P vs0 as0, P vs1 as1 => by
    rw [compareT_PP, compareT_PP, compareV_swap vs0 vs1, compareT_swap as0 as1]
    cases compareV vs1 vs0 <;> cases compareT as1 as0 <;> rfl
termination_by a b => (T.size a + T.size b, 2)
decreasing_by
  all_goals
    simp only [T.size]
    omega

theorem compareV'_swap : ∀ a b : V T, compareV' a b = (compareV' b a).swap
  | .emp, .emp => by rw [compareV'_ee]; rfl
  | .emp, .snoc b bx => by rw [compareV'_es, compareV'_se]; rfl
  | .snoc a ax, .emp => by rw [compareV'_es, compareV'_se]; rfl
  | .snoc a ax, .snoc b bx => by
    rw [compareV'_ss, compareV'_ss, compareT_swap a b, compareV'_swap ax bx]
    cases compareT b a <;> cases compareV' bx ax <;> rfl
termination_by a b => (V.size a + V.size b, 0)
decreasing_by
  all_goals
    simp only [V.size]
    omega

theorem compareV_swap (a b : V T) : compareV a b = (compareV b a).swap := by
  rw [compareV_eq, compareV_eq, lenCmp_swap (V.trim a).length (V.trim b).length,
    compareV'_swap (V.trim a) (V.trim b)]
  cases lenCmp (V.trim b).length (V.trim a).length <;>
    cases compareV' (V.trim b) (V.trim a) <;> rfl
termination_by (V.size a + V.size b, 1)
decreasing_by
  have := V.size_trim_le a
  have := V.size_trim_le b
  omega
end

mutual
theorem compareT_cons (a b c : T) :
    Cons (compareT a b) (compareT b c) (compareT a c) := by
  match a, b, c with
  | Z, Z, Z => simp [compareT_ZZ, Cons]
  | Z, Z, P vs2 as2 => simp [compareT_ZZ, compareT_ZP, Cons]
  | Z, P vs1 as1, Z => simp [compareT_ZZ, compareT_ZP, compareT_PZ, Cons]
  | Z, P vs1 as1, P vs2 as2 => simp [compareT_ZP, Cons]
  | P vs0 as0, Z, Z => simp [compareT_PZ, Cons]
  | P vs0 as0, Z, P vs2 as2 => simp [compareT_PZ, compareT_ZP, Cons]
  | P vs0 as0, P vs1 as1, Z => simp [compareT_PZ, Cons]
  | P vs0 as0, P vs1 as1, P vs2 as2 =>
    rw [compareT_PP, compareT_PP, compareT_PP]
    exact Cons.then (compareV_cons vs0 vs1 vs2) (compareT_cons as0 as1 as2)
termination_by (T.size a + T.size b + T.size c, 2)
decreasing_by
  all_goals
    simp only [T.size]
    omega

theorem compareV'_cons (a b c : V T) :
    Cons (compareV' a b) (compareV' b c) (compareV' a c) := by
  match a, b, c with
  | .emp, .emp, .emp => simp [compareV'_ee, Cons]
  | .emp, .emp, .snoc c' cx => simp [compareV'_ee, compareV'_es, Cons]
  | .emp, .snoc b' bx, .emp => simp [compareV'_ee, compareV'_es, compareV'_se, Cons]
  | .emp, .snoc b' bx, .snoc c' cx => simp [compareV'_es, Cons]
  | .snoc a' ax, .emp, .emp => simp [compareV'_se, Cons]
  | .snoc a' ax, .emp, .snoc c' cx => simp [compareV'_se, compareV'_es, Cons]
  | .snoc a' ax, .snoc b' bx, .emp => simp [compareV'_se, Cons]
  | .snoc a' ax, .snoc b' bx, .snoc c' cx =>
    rw [compareV'_ss, compareV'_ss, compareV'_ss]
    exact Cons.then (compareT_cons a' b' c') (compareV'_cons ax bx cx)
termination_by (V.size a + V.size b + V.size c, 0)
decreasing_by
  all_goals
    simp only [V.size]
    omega

theorem compareV_cons (a b c : V T) :
    Cons (compareV a b) (compareV b c) (compareV a c) := by
  rw [compareV_eq, compareV_eq, compareV_eq]
  exact Cons.then (lenCmp_cons _ _ _) (compareV'_cons (V.trim a) (V.trim b) (V.trim c))
termination_by (V.size a + V.size b + V.size c, 1)
decreasing_by
  have := V.size_trim_le a
  have := V.size_trim_le b
  have := V.size_trim_le c
  omega
end

mutual
theorem compareT_eq_iff : ∀ a b : T, compareT a b = .eq ↔ T.norm a = T.norm b
  | Z, Z => by simp [compareT_ZZ]
  | Z, P vs as => by simp [compareT_ZP, T.norm]
  | P vs as, Z => by simp [compareT_PZ, T.norm]
  | P vs0 as0, P vs1 as1 => by
    rw [compareT_PP, Ordering.then_eq_eq, compareV_eq_iff vs0 vs1, compareT_eq_iff as0 as1]
    simp [T.norm_P]
termination_by a b => (T.size a + T.size b, 2)
decreasing_by
  all_goals
    simp only [T.size]
    omega

theorem compareV'_eq_iff : ∀ a b : V T, compareV' a b = .eq ↔ V.mapNorm a = V.mapNorm b
  | .emp, .emp => by simp [compareV'_ee]
  | .emp, .snoc b bx => by simp [compareV'_es, V.mapNorm]
  | .snoc a ax, .emp => by simp [compareV'_se, V.mapNorm]
  | .snoc a ax, .snoc b bx => by
    rw [compareV'_ss, Ordering.then_eq_eq, compareT_eq_iff a b, compareV'_eq_iff ax bx]
    simp [V.mapNorm]
termination_by a b => (V.size a + V.size b, 0)
decreasing_by
  all_goals
    simp only [V.size]
    omega

theorem compareV_eq_iff (a b : V T) : compareV a b = .eq ↔ V.norm a = V.norm b := by
  rw [compareV_eq, Ordering.then_eq_eq, lenCmp_eq_eq,
    compareV'_eq_iff (V.trim a) (V.trim b), V.norm_eq, V.norm_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have := congrArg V.length h
    simpa [V.length_mapNorm] using this
termination_by (V.size a + V.size b, 1)
decreasing_by
  have := V.size_trim_le a
  have := V.size_trim_le b
  omega
end

theorem compareT_self (a : T) : compareT a a = .eq := (compareT_eq_iff a a).2 rfl
theorem compareV_self (a : V T) : compareV a a = .eq := (compareV_eq_iff a a).2 rfl

theorem compareT_gt_iff {a b : T} : compareT a b = .gt ↔ compareT b a = .lt := by
  rw [compareT_swap a b]; cases compareT b a <;> simp [Ordering.swap]

theorem compareV_gt_iff {a b : V T} : compareV a b = .gt ↔ compareV b a = .lt := by
  rw [compareV_swap a b]; cases compareV b a <;> simp [Ordering.swap]

theorem T.lt_irrefl (a : T) : ¬ a < a := by
  intro h
  have h : compareT a a = .lt := h
  rw [compareT_self] at h; cases h

theorem T.lt_trans {a b c : T} (h1 : a < b) (h2 : b < c) : a < c :=
  (compareT_cons a b c).1 h1 h2

theorem T.lt_asymm {a b : T} (h : a < b) : ¬ b < a := fun h' => T.lt_irrefl a (T.lt_trans h h')

theorem T.lt_trichotomy (a b : T) : a < b ∨ T.norm a = T.norm b ∨ b < a := by
  show compareT a b = .lt ∨ _ ∨ compareT b a = .lt
  rw [← compareT_eq_iff a b, ← compareT_gt_iff (a := a) (b := b)]
  cases compareT a b <;> simp

theorem T.le_refl (a : T) : a ≤ a := Or.inr (compareT_self a)

theorem T.le_total (a b : T) : a ≤ b ∨ b ≤ a := by
  show (compareT a b = .lt ∨ compareT a b = .eq) ∨ (compareT b a = .lt ∨ compareT b a = .eq)
  rw [compareT_swap a b]
  cases compareT b a <;> simp [Ordering.swap]

theorem T.le_trans {a b c : T} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ((compareT_cons a b c).1 h1 h2)
  · exact Or.inl ((compareT_cons a b c).2.1 h1 h2)
  · exact Or.inl ((compareT_cons a b c).2.2.1 h1 h2)
  · exact Or.inr ((compareT_cons a b c).2.2.2 h1 h2)

theorem T.le_antisymm {a b : T} (h1 : a ≤ b) (h2 : b ≤ a) : T.norm a = T.norm b := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd h2 (T.lt_asymm h1)
    · exact ((compareT_eq_iff b a).1 h2).symm
  · exact (compareT_eq_iff a b).1 h1

theorem T.not_lt {a b : T} : ¬ a < b ↔ b ≤ a := by
  show ¬ compareT a b = .lt ↔ compareT b a = .lt ∨ compareT b a = .eq
  rw [compareT_swap a b]
  cases compareT b a <;> simp [Ordering.swap]

theorem V.lt_irrefl (a : V T) : ¬ a < a := by
  intro h
  have h : compareV a a = .lt := h
  rw [compareV_self] at h; cases h

theorem V.lt_trans {a b c : V T} (h1 : a < b) (h2 : b < c) : a < c :=
  (compareV_cons a b c).1 h1 h2

theorem V.lt_asymm {a b : V T} (h : a < b) : ¬ b < a := fun h' => V.lt_irrefl a (V.lt_trans h h')

theorem V.lt_trichotomy (a b : V T) : a < b ∨ V.norm a = V.norm b ∨ b < a := by
  show compareV a b = .lt ∨ _ ∨ compareV b a = .lt
  rw [← compareV_eq_iff a b, ← compareV_gt_iff (a := a) (b := b)]
  cases compareV a b <;> simp

theorem V.le_refl (a : V T) : a ≤ a := Or.inr (compareV_self a)

theorem V.le_total (a b : V T) : a ≤ b ∨ b ≤ a := by
  show (compareV a b = .lt ∨ compareV a b = .eq) ∨ (compareV b a = .lt ∨ compareV b a = .eq)
  rw [compareV_swap a b]
  cases compareV b a <;> simp [Ordering.swap]

theorem V.le_trans {a b c : V T} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl ((compareV_cons a b c).1 h1 h2)
  · exact Or.inl ((compareV_cons a b c).2.1 h1 h2)
  · exact Or.inl ((compareV_cons a b c).2.2.1 h1 h2)
  · exact Or.inr ((compareV_cons a b c).2.2.2 h1 h2)

theorem V.le_antisymm {a b : V T} (h1 : a ≤ b) (h2 : b ≤ a) : V.norm a = V.norm b := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact absurd h2 (V.lt_asymm h1)
    · exact ((compareV_eq_iff b a).1 h2).symm
  · exact (compareV_eq_iff a b).1 h1

theorem V.not_lt {a b : V T} : ¬ a < b ↔ b ≤ a := by
  show ¬ compareV a b = .lt ↔ compareV b a = .lt ∨ compareV b a = .eq
  rw [compareV_swap a b]
  cases compareV b a <;> simp [Ordering.swap]

instance T.setoid : Setoid T where
  r a b := compareT a b = .eq
  iseqv :=
    { refl := compareT_self
      symm := fun {a b} h => (compareT_eq_iff b a).2 ((compareT_eq_iff a b).1 h).symm
      trans := fun {a b c} h1 h2 =>
        (compareT_eq_iff a c).2 (((compareT_eq_iff a b).1 h1).trans ((compareT_eq_iff b c).1 h2)) }

instance V.setoid : Setoid (V T) where
  r a b := compareV a b = .eq
  iseqv :=
    { refl := compareV_self
      symm := fun {a b} h => (compareV_eq_iff b a).2 ((compareV_eq_iff a b).1 h).symm
      trans := fun {a b c} h1 h2 =>
        (compareV_eq_iff a c).2 (((compareV_eq_iff a b).1 h1).trans ((compareV_eq_iff b c).1 h2)) }

def QT : Type := Quotient T.setoid
def QV : Type := Quotient (V.setoid)

def NT : Type := { t : T // T.norm t = t }
def NV : Type := { v : V T // V.norm v = v }

instance : DecidableEq NT := inferInstanceAs (DecidableEq { t : T // T.norm t = t })
instance : DecidableEq NV := inferInstanceAs (DecidableEq { v : V T // V.norm v = v })

def T.rep (t : T) : NT := ⟨T.norm t, T.norm_norm t⟩
def V.rep (v : V T) : NV := ⟨V.norm v, V.norm_norm v⟩

theorem NT.compare_eq_iff (a b : NT) : compareT a.1 b.1 = .eq ↔ a = b := by
  rw [compareT_eq_iff, a.2, b.2]
  exact ⟨Subtype.ext, fun h => h ▸ rfl⟩

theorem NV.compare_eq_iff (a b : NV) : compareV a.1 b.1 = .eq ↔ a = b := by
  rw [compareV_eq_iff, a.2, b.2]
  exact ⟨Subtype.ext, fun h => h ▸ rfl⟩

theorem T.rep_equiv (t : T) : compareT (T.rep t).1 t = .eq :=
  (compareT_eq_iff _ _).2 (T.norm_norm t)

theorem V.rep_equiv (v : V T) : compareV (V.rep v).1 v = .eq :=
  (compareV_eq_iff _ _).2 (V.norm_norm v)

def QT.toNT : QT → NT :=
  Quotient.lift T.rep (fun a b h => Subtype.ext ((compareT_eq_iff a b).1 h))
def NT.toQT (n : NT) : QT := Quotient.mk T.setoid n.1

theorem QT.toNT_toQT (n : NT) : QT.toNT (NT.toQT n) = n := by
  apply Subtype.ext
  exact n.2

theorem QT.toQT_toNT (q : QT) : NT.toQT (QT.toNT q) = q := by
  induction q using Quotient.inductionOn with
  | _ t => exact Quotient.sound (T.rep_equiv t)

def QV.toNV : QV → NV :=
  Quotient.lift V.rep (fun a b h => Subtype.ext ((compareV_eq_iff a b).1 h))
def NV.toQV (n : NV) : QV := Quotient.mk V.setoid n.1

theorem QV.toNV_toQV (n : NV) : QV.toNV (NV.toQV n) = n := by
  apply Subtype.ext
  exact n.2

theorem QV.toQV_toNV (q : QV) : NV.toQV (QV.toNV q) = q := by
  induction q using Quotient.inductionOn with
  | _ v => exact Quotient.sound (V.rep_equiv v)

instance : LT NT := ⟨fun a b => a.1 < b.1⟩
instance : LE NT := ⟨fun a b => a.1 ≤ b.1⟩
instance : Ord NT := ⟨fun a b => compareT a.1 b.1⟩

instance : LT NV := ⟨fun a b => a.1 < b.1⟩
instance : LE NV := ⟨fun a b => a.1 ≤ b.1⟩
instance : Ord NV := ⟨fun a b => compareV a.1 b.1⟩

theorem NT.lt_irrefl (a : NT) : ¬ a < a := T.lt_irrefl a.1
theorem NT.lt_trans {a b c : NT} : a < b → b < c → a < c := T.lt_trans
theorem NT.lt_trichotomy (a b : NT) : a < b ∨ a = b ∨ b < a := by
  rcases T.lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl (Subtype.ext ?_))
    rwa [a.2, b.2] at h
  · exact Or.inr (Or.inr h)
theorem NT.le_antisymm {a b : NT} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  have := T.le_antisymm h1 h2
  rw [a.2, b.2] at this
  exact Subtype.ext this
theorem NT.le_total (a b : NT) : a ≤ b ∨ b ≤ a := T.le_total a.1 b.1

theorem NV.lt_irrefl (a : NV) : ¬ a < a := V.lt_irrefl a.1
theorem NV.lt_trans {a b c : NV} : a < b → b < c → a < c := V.lt_trans
theorem NV.lt_trichotomy (a b : NV) : a < b ∨ a = b ∨ b < a := by
  rcases V.lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl (Subtype.ext ?_))
    rwa [a.2, b.2] at h
  · exact Or.inr (Or.inr h)
theorem NV.le_antisymm {a b : NV} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  have := V.le_antisymm h1 h2
  rw [a.2, b.2] at this
  exact Subtype.ext this
theorem NV.le_total (a b : NV) : a ≤ b ∨ b ≤ a := V.le_total a.1 b.1

theorem T.lt_iff_le_not_le (a b : T) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro h
    refine ⟨Or.inl h, fun h' => ?_⟩
    have hs := compareT_swap b a
    have h : compareT a b = .lt := h
    rw [h] at hs
    rcases h' with h' | h' <;> rw [h'] at hs <;> simp [Ordering.swap] at hs
  · intro ⟨h1, h2⟩
    by_cases h : a < b
    · exact h
    · exact absurd (T.not_lt.1 h) h2

theorem V.lt_iff_le_not_le (a b : V T) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor
  · intro h
    refine ⟨Or.inl h, fun h' => ?_⟩
    have hs := compareV_swap b a
    have h : compareV a b = .lt := h
    rw [h] at hs
    rcases h' with h' | h' <;> rw [h'] at hs <;> simp [Ordering.swap] at hs
  · intro ⟨h1, h2⟩
    by_cases h : a < b
    · exact h
    · exact absurd (V.not_lt.1 h) h2

instance : Ord (V T) := ⟨compareV⟩

instance : Std.IsLinearPreorder T where
  le_refl := T.le_refl
  le_trans := fun _ _ _ => T.le_trans
  le_total := T.le_total

instance : Std.LawfulOrderLT T := ⟨T.lt_iff_le_not_le⟩

instance : Std.LawfulOrderOrd T where
  isLE_compare a b := by
    show (compareT a b).isLE = true ↔ (compareT a b = .lt ∨ compareT a b = .eq)
    cases compareT a b <;> simp
  isGE_compare a b := by
    show (compareT a b).isGE = true ↔ (compareT b a = .lt ∨ compareT b a = .eq)
    rw [compareT_swap a b]
    cases compareT b a <;> simp [Ordering.swap]

instance : Std.IsLinearPreorder (V T) where
  le_refl := V.le_refl
  le_trans := fun _ _ _ => V.le_trans
  le_total := V.le_total

instance : Std.LawfulOrderLT (V T) := ⟨V.lt_iff_le_not_le⟩

instance : Std.LawfulOrderOrd (V T) where
  isLE_compare a b := by
    show (compareV a b).isLE = true ↔ (compareV a b = .lt ∨ compareV a b = .eq)
    cases compareV a b <;> simp
  isGE_compare a b := by
    show (compareV a b).isGE = true ↔ (compareV b a = .lt ∨ compareV b a = .eq)
    rw [compareV_swap a b]
    cases compareV b a <;> simp [Ordering.swap]

instance : Std.IsLinearOrder NT where
  le_refl a := T.le_refl a.1
  le_trans _ _ _ := T.le_trans
  le_antisymm _ _ := NT.le_antisymm
  le_total := NT.le_total

instance : Std.LawfulOrderLT NT := ⟨fun a b => T.lt_iff_le_not_le a.1 b.1⟩

instance : Std.LawfulOrderOrd NT where
  isLE_compare a b := Std.LawfulOrderOrd.isLE_compare a.1 b.1
  isGE_compare a b := Std.LawfulOrderOrd.isGE_compare a.1 b.1

instance : Std.IsLinearOrder NV where
  le_refl a := V.le_refl a.1
  le_trans _ _ _ := V.le_trans
  le_antisymm _ _ := NV.le_antisymm
  le_total := NV.le_total

instance : Std.LawfulOrderLT NV := ⟨fun a b => V.lt_iff_le_not_le a.1 b.1⟩

instance : Std.LawfulOrderOrd NV where
  isLE_compare a b := Std.LawfulOrderOrd.isLE_compare a.1 b.1
  isGE_compare a b := Std.LawfulOrderOrd.isGE_compare a.1 b.1

mutual
def T.zeros : T → Nat
  | Z => 1
  | P vs as => V.zeros vs + T.zeros as

def V.zeros : V T → Nat
  | .emp => 0
  | .snoc a ax => T.zeros a + V.zeros ax
end

theorem V.zeros_trim_le (v : V T) : (V.trim v).zeros ≤ v.zeros := by
  induction v with
  | emp => simp [V.trim]
  | snoc a ax ih =>
    cases a with
    | Z => simp only [V.trim, V.zeros, T.zeros]; omega
    | P vs as => simp [V.trim]

mutual
theorem T.zeros_norm_le : ∀ t : T, (T.norm t).zeros ≤ t.zeros
  | Z => by simp [T.norm]
  | P vs as => by
    simp only [T.norm, T.zeros]
    have h1 := V.zeros_trim_le (V.mapNorm vs)
    have h2 := V.zeros_mapNorm_le vs
    have h3 := T.zeros_norm_le as
    omega

theorem V.zeros_mapNorm_le : ∀ v : V T, (V.mapNorm v).zeros ≤ v.zeros
  | .emp => by simp [V.mapNorm]
  | .snoc a ax => by
    simp only [V.mapNorm, V.zeros]
    have h1 := T.zeros_norm_le a
    have h2 := V.zeros_mapNorm_le ax
    omega
end

theorem V.zeros_norm_le (v : V T) : (V.norm v).zeros ≤ v.zeros := by
  simp [V.norm]
  have h1 := V.zeros_mapNorm_le v
  have h2 := V.zeros_trim_le (V.mapNorm v)
  omega

theorem T.zeros_norm_min {a b : T} (h : compareT a b = .eq) :
    (T.norm a).zeros ≤ b.zeros := by
  rw [(compareT_eq_iff a b).1 h]
  exact T.zeros_norm_le b

theorem V.zeros_norm_min {a b : V T} (h : compareV a b = .eq) :
    (V.norm a).zeros ≤ b.zeros := by
  rw [(compareV_eq_iff a b).1 h]
  exact V.zeros_norm_le b

theorem V.get0_mapNorm : ∀ (v : V T) (i : Nat), V.get0 (V.mapNorm v) i = T.norm (V.get0 v i)
  | .emp, i => by simp [V.mapNorm, V.get0, T.norm]
  | .snoc a ax, i => by
    simp only [V.mapNorm, V.get0, V.length_mapNorm]
    by_cases hi : i = ax.length
    · simp [hi]
    · simp [hi, V.get0_mapNorm ax i]

theorem V.get0_norm (v : V T) (i : Nat) : V.get0 (V.norm v) i = T.norm (V.get0 v i) := by
  unfold V.norm; rw [V.get0_trim, V.get0_mapNorm]

theorem V.norm_ext {a b : V T}
    (h : ∀ i, T.norm (V.get0 a i) = T.norm (V.get0 b i)) : V.norm a = V.norm b := by
  have hc : ∀ i, V.get0 (V.norm a) i = V.get0 (V.norm b) i := by
    intro i; rw [V.get0_norm, V.get0_norm]; exact h i
  have ta : V.trim (V.norm a) = V.norm a := V.trim_trim _
  have tb : V.trim (V.norm b) = V.norm b := V.trim_trim _
  generalize V.norm a = c at *
  generalize V.norm b = d at *
  apply V.eq_of_get0
  · exact Nat.le_antisymm (V.length_le_of_trim c d ta hc)
      (V.length_le_of_trim d c tb (fun i => (hc i).symm))
  · exact hc


/-! ### set -/

theorem V.length_set : ∀ (v : V T) (i : Nat) (x : T), (V.set v i x).length = v.length
  | .emp, i, x => by simp [V.set]
  | .snoc b bx, i, x => by
    simp only [V.set]
    by_cases hi : i = bx.length
    · simp [hi, V.length]
    · simp [hi, V.length, V.length_set bx i x]

theorem V.get0_set : ∀ (v : V T) (i : Nat) (x : T) (j : Nat), i < v.length →
    V.get0 (V.set v i x) j = if j = i then x else V.get0 v j
  | .emp, i, x, j, h => by simp [V.length] at h
  | .snoc b bx, i, x, j, h => by
    simp only [V.length] at h
    by_cases hi : i = bx.length
    · subst hi
      by_cases hj : j = bx.length <;> simp [V.set, V.get0, hj]
    · have hi' : i < bx.length := by omega
      by_cases hj : j = bx.length
      · subst hj; simp [V.set, V.get0, hi, V.length_set, Ne.symm hi]
      · by_cases hji : j = i
        · subst hji; simp [V.set, V.get0, hi, V.length_set, V.get0_set bx j x j hi']
        · simp [V.set, V.get0, hi, V.length_set, hj, hji, V.get0_set bx i x j hi']

theorem V.set_congr {v v' : V T} {i : Nat} {x x' : T}
    (hv : V.norm v = V.norm v') (hx : T.norm x = T.norm x')
    (hi : i < v.length) (hi' : i < v'.length) :
    V.norm (V.set v i x) = V.norm (V.set v' i x') := by
  apply V.norm_ext
  intro j
  rw [V.get0_set v i x j hi, V.get0_set v' i x' j hi']
  by_cases hj : j = i
  · simp [hj, hx]
  · have := congrArg (fun w => V.get0 w j) hv
    simp only [V.get0_norm] at this
    simpa [hj] using this

theorem V.fnz_mapNorm : ∀ v : V T, V.fnz (V.mapNorm v) = V.fnz v
  | .emp => rfl
  | .snoc a ax => by
    simp only [V.mapNorm, V.fnz, V.fnz_mapNorm ax, V.length_mapNorm]
    have : (T.norm a ≠ Z) ↔ (a ≠ Z) := not_congr T.norm_eq_Z
    simp [this]

theorem V.fnz_trim : ∀ v : V T, V.fnz (V.trim v) = V.fnz v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z =>
      simp only [V.trim, V.fnz, V.fnz_trim ax]
      rcases V.fnz ax <;> simp
    | P vs as => simp [V.trim]

theorem V.fnz_congr {v v' : V T} (h : V.norm v = V.norm v') : V.fnz v = V.fnz v' := by
  have h1 : V.fnz (V.norm v) = V.fnz v := by unfold V.norm; rw [V.fnz_trim, V.fnz_mapNorm]
  have h2 : V.fnz (V.norm v') = V.fnz v' := by unfold V.norm; rw [V.fnz_trim, V.fnz_mapNorm]
  rw [← h1, ← h2, h]

/-- `fnz` が返す添字は範囲内。`set_congr` の範囲条件を満たすのに使う。 -/
theorem V.lt_length_of_fnz : ∀ (v : V T) (i : Nat), V.fnz v = some i → i < v.length
  | .emp, i, h => by simp [V.fnz] at h
  | .snoc a ax, i, h => by
    simp only [V.fnz] at h
    simp only [V.length]
    rcases hh : V.fnz ax with _ | j
    · rw [hh] at h
      by_cases ha : a = Z
      · simp [ha] at h
      · simp [ha] at h; omega
    · rw [hh] at h
      simp at h
      have := V.lt_length_of_fnz ax j hh
      omega

/-- 同値な列の同じ添字の要素は同値。範囲条件は不要。 -/
theorem V.get0_congr {v v' : V T} (h : V.norm v = V.norm v') (i : Nat) :
    T.norm (V.get0 v i) = T.norm (V.get0 v' i) := by
  rw [← V.get0_norm, ← V.get0_norm, h]

/-! ### 基本演算の合同性 -/

theorem T.norm_add : ∀ a b : T, T.norm (a + b) = T.norm a + T.norm b
  | Z, b => by simp [HAdd.hAdd, Add.add, T.oplus, T.norm]
  | P vs as, b => by
    have ih := T.norm_add as b
    simp only [HAdd.hAdd, Add.add, T.oplus, T.norm] at ih ⊢
    rw [ih]

theorem T.add_congr {a a' b b' : T} (ha : T.norm a = T.norm a') (hb : T.norm b = T.norm b') :
    T.norm (a + b) = T.norm (a' + b') := by
  rw [T.norm_add, T.norm_add, ha, hb]

theorem T.mul_congr : ∀ {s s' t t' : T}, T.norm s = T.norm s' → T.norm t = T.norm t' →
    T.norm (T.mul s t) = T.norm (T.mul s' t')
  | s, s', Z, t', hs, ht => by
    have : t' = Z := T.norm_eq_Z.1 (by rw [← ht]; simp [T.norm])
    subst this; simp [T.mul]
  | s, s', P v a, t', hs, ht => by
    cases t' with
    | Z => simp [T.norm] at ht
    | P v' a' =>
      simp only [T.norm, T.P.injEq] at ht
      simp only [T.mul]
      exact T.add_congr hs (T.mul_congr hs ht.2)

theorem T.iter_congr {F F' : T → T}
    (hF : ∀ x x', T.norm x = T.norm x' → T.norm (F x) = T.norm (F' x')) :
    ∀ {t t' : T}, T.norm t = T.norm t' → T.norm (T.iter F t) = T.norm (T.iter F' t')
  | Z, t', ht => by
    have : t' = Z := T.norm_eq_Z.1 (by rw [← ht]; simp [T.norm])
    subst this; simp [T.iter]
  | P v a, t', ht => by
    cases t' with
    | Z => simp [T.norm] at ht
    | P v' a' =>
      simp only [T.norm, T.P.injEq] at ht
      simp only [T.iter]
      exact hF _ _ (T.iter_congr hF ht.2)


/-- kumakuma の `dom` が使う `li < ri` は同値で不変 -/
theorem V.lt_congr {a a' b b' : V T} (ha : V.norm a = V.norm a') (hb : V.norm b = V.norm b') :
    a < b ↔ a' < b' := by
  have e1 : compareV a' a = .eq := (compareV_eq_iff a' a).2 ha.symm
  have e2 : compareV b b' = .eq := (compareV_eq_iff b b').2 hb
  have e1' : compareV a a' = .eq := (compareV_eq_iff a a').2 ha
  have e2' : compareV b' b = .eq := (compareV_eq_iff b' b).2 hb.symm
  constructor
  · intro h
    have h : compareV a b = .lt := h
    have h1 : compareV a' b = .lt := (compareV_cons a' a b).2.2.1 e1 h
    exact (compareV_cons a' b b').2.1 h1 e2
  · intro h
    have h : compareV a' b' = .lt := h
    have h1 : compareV a b' = .lt := (compareV_cons a a' b').2.2.1 e1' h
    exact (compareV_cons a b' b).2.1 h1 e2'

/-! ### 合同性証明の定型部分 -/

/-- 同値な項の一方が `Z` なら他方も `Z`。 -/
theorem T.eq_Z_iff_of_norm_eq {a b : T} (h : T.norm a = T.norm b) : a = Z ↔ b = Z := by
  rw [← T.norm_eq_Z, ← T.norm_eq_Z (t := b), h]

/-- `P li add` と同値な項は `P li' add'` の形で、各成分も同値。 -/
theorem T.norm_eq_P {li : V T} {add s' : T} (h : T.norm (P li add) = T.norm s') :
    ∃ li' add', s' = P li' add' ∧ V.norm li = V.norm li' ∧ T.norm add = T.norm add' := by
  cases s' with
  | Z => simp [T.norm] at h
  | P li' add' =>
    rw [T.norm_P, T.norm_P] at h
    injection h with h1 h2
    exact ⟨li', add', rfl, h1, h2⟩

theorem T.norm_P_congr {a a' : V T} {b b' : T}
    (ha : V.norm a = V.norm a') (hb : T.norm b = T.norm b') :
    T.norm (P a b) = T.norm (P a' b') := by
  rw [T.norm_P, T.norm_P, ha, hb]

/-- `P (v.set i x) Z` の合同性。`fund` の各分岐の出力形。 -/
theorem T.norm_P_set_congr {v v' : V T} {i : Nat} {x x' : T}
    (hv : V.norm v = V.norm v') (hx : T.norm x = T.norm x')
    (hi : i < v.length) (hi' : i < v'.length) :
    T.norm (P (V.set v i x) Z) = T.norm (P (V.set v' i x') Z) :=
  T.norm_P_congr (V.set_congr hv hx hi hi') rfl

/-- 同値な2つの列の `fnz` は、ともに `none`、またはともに同じ範囲内の添字 `i` を返し、
その添字の要素は同値。 -/
theorem V.fnz_congr_cases {v v' : V T} (h : V.norm v = V.norm v') :
    (V.fnz v = none ∧ V.fnz v' = none) ∨
    ∃ i, V.fnz v = some i ∧ V.fnz v' = some i ∧ i < v.length ∧ i < v'.length ∧
      T.norm (V.get0 v i) = T.norm (V.get0 v' i) := by
  have hf := V.fnz_congr h
  rcases hA : V.fnz v with _ | i
  · rw [hA] at hf
    exact Or.inl ⟨rfl, hf.symm⟩
  · rw [hA] at hf
    exact Or.inr ⟨i, rfl, hf.symm, V.lt_length_of_fnz v i hA,
      V.lt_length_of_fnz v' i hf.symm, V.get0_congr h i⟩

/-! ### 終了性・長さの補助補題

`omega` は文脈に `Nat` 上の `∃` 仮定があると `Classical.choice` を使う。`fund_congr` などでは
`V.fnz_congr_cases` を分解した `∃ i : Nat, …` が再帰呼び出し時点の文脈に残るので、
`decreasing_by` や本体で `omega` を直接呼ばず、仮定のない文脈で証明した次の補題を使う。 -/

theorem T.size_lt_P_right (li : V T) (add : T) : add.size < (P li add).size := by
  simp only [T.size]; omega

theorem T.size_get0_lt_P (li : V T) (i : Nat) (add : T) :
    (V.get0 li i).size < (P li add).size := by
  have := V.size_get0_le li i
  simp only [T.size]; omega

theorem V.lt_length_set_pred {v : V T} {k : Nat} {x : T} (h : k + 1 < v.length) :
    k < (V.set v (k + 1) x).length := by
  rw [V.length_set]; omega

/-! ### NT への持ち上げ（4変種共通） -/

/-- `fund` と `isOT` の基底 `base` を束ねたもの。 -/
structure FundSys where
  fund : T → T → T
  base : Nat → T

/-- `fund` が `norm` による同値を保つ（s, t の両方について）。 -/
def FundSys.Cong (S : FundSys) : Prop :=
  ∀ s s' t t', T.norm s = T.norm s' → T.norm t = T.norm t' →
    T.norm (S.fund s t) = T.norm (S.fund s' t')

/-- 生の `T` 上の `isOT`。 -/
inductive FundSys.IsOT (S : FundSys) : T → Prop
  | base (n : Nat) : IsOT S (S.base n)
  | step (s : T) : IsOT S s → ∀ n : Nat, IsOT S (S.fund s (T.ofNat n))

/-- NT 上の fund。出力は正規形とは限らないので `rep` で正規化して定義する。 -/
def FundSys.ntFund (S : FundSys) (s t : NT) : NT := T.rep (S.fund s.1 t.1)

/-- NT 上の `isOT`。 -/
inductive FundSys.NIsOT (S : FundSys) : NT → Prop
  | base (n : Nat) : NIsOT S (T.rep (S.base n))
  | step (s : NT) : NIsOT S s → ∀ n : Nat, NIsOT S (S.ntFund s (T.rep (T.ofNat n)))

/-- `T.fund` と `NT.fund` の整合性（`Cong` の言い換え）。 -/
theorem FundSys.rep_fund {S : FundSys} (hS : S.Cong) (s t : T) :
    T.rep (S.fund s t) = S.ntFund (T.rep s) (T.rep t) :=
  Subtype.ext (hS s _ t _ (T.norm_norm s).symm (T.norm_norm t).symm)

theorem FundSys.IsOT.rep {S : FundSys} (hS : S.Cong) {t : T} (h : S.IsOT t) :
    S.NIsOT (T.rep t) := by
  induction h with
  | base n => exact .base n
  | step s _ n ih => rw [FundSys.rep_fund hS]; exact .step _ ih n

theorem FundSys.NIsOT.exists {S : FundSys} (hS : S.Cong) {a : NT} (h : S.NIsOT a) :
    ∃ t, S.IsOT t ∧ T.rep t = a := by
  induction h with
  | base n => exact ⟨_, .base n, rfl⟩
  | step s _ n ih =>
    obtain ⟨t, ht, rfl⟩ := ih
    exact ⟨_, .step t ht n, FundSys.rep_fund hS t (T.ofNat n)⟩

def FundSys.NOT {S : FundSys} := { s : NT // FundSys.NIsOT S s }


/-! ### 基本列による順序（4変種共通） -/

theorem NT.lt_or_eq_of_le {a b : NT} (h : a ≤ b) : a < b ∨ a = b := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ((NT.compare_eq_iff a b).1 h)

theorem NT.not_lt_of_eq_Z (a : NT) {b : NT} (hb : b.1 = Z) : ¬ a < b := by
  intro h
  have h' : compareT a.1 b.1 = .lt := h
  rw [hb] at h'
  cases ha : a.1 with
  | Z => rw [ha, compareT_ZZ] at h'; cases h'
  | P vs as => rw [ha, compareT_PZ] at h'; cases h'

/-- 基本列の 1 ステップ: `a` は `b` の基本列の項。 -/
def FundSys.NOTStep (S : FundSys) (a b : @FundSys.NOT S) : Prop :=
  b.val.1 ≠ Z ∧ ∃ n : Nat, a.val = S.ntFund b.val (T.rep (T.ofNat n))

/-- 基本列のステップの推移閉包。 -/
abbrev FundSys.NOTFundLt (S : FundSys) : @FundSys.NOT S → @FundSys.NOT S → Prop :=
  FundOrder.TransClosure S.NOTStep

/-- 基本列の項がもとの項より小さいこと。 -/
def FundSys.FundDesc (S : FundSys) : Prop :=
  ∀ (b : @FundSys.NOT S) (n : Nat), b.val.1 ≠ Z → S.ntFund b.val (T.rep (T.ofNat n)) < b.val

/-- 基本列が下から共終であること。 -/
def FundSys.FundCofinal (S : FundSys) : Prop :=
  ∀ a b : @FundSys.NOT S, b.val < a.val → ∃ n : Nat, b.val ≤ S.ntFund a.val (T.rep (T.ofNat n))

theorem FundSys.NOTStep_lt {S : FundSys} (hlt : S.FundDesc) {a b : @FundSys.NOT S}
    (h : S.NOTStep a b) : a.val < b.val := by
  obtain ⟨hbne, n, ha⟩ := h
  rw [ha]
  exact hlt b n hbne

theorem FundSys.NOTFundLt_lt {S : FundSys} (hlt : S.FundDesc) {a b : @FundSys.NOT S}
    (h : S.NOTFundLt a b) : a.val < b.val := by
  induction h with
  | single hstep => exact FundSys.NOTStep_lt hlt hstep
  | tail _ hstep ih => exact NT.lt_trans ih (FundSys.NOTStep_lt hlt hstep)

theorem FundSys.NOTFundLt_of_lt {S : FundSys} (hlt : S.FundDesc) (hcof : S.FundCofinal)
    (hwf : WellFounded (fun a b : @FundSys.NOT S => a.val < b.val)) (a b : @FundSys.NOT S)
    (hab : a.val < b.val) : S.NOTFundLt a b := by
  induction b using hwf.induction generalizing a with
  | h b ih =>
    obtain ⟨n, hn⟩ := hcof b a hab
    let c : @FundSys.NOT S := ⟨S.ntFund b.val (T.rep (T.ofNat n)), .step _ b.2 n⟩
    have hbne : b.val.1 ≠ Z := fun hz => NT.not_lt_of_eq_Z a.val hz hab
    have hstep : S.NOTStep c b := ⟨hbne, n, rfl⟩
    rcases NT.lt_or_eq_of_le hn with h | h
    · exact FundOrder.TransClosure.tail (ih c (hlt b n hbne) a h) hstep
    · have hac : a = c := Subtype.ext h
      subst hac
      exact FundOrder.TransClosure.single hstep

/-- 基本列の推移閉包による順序と項の順序の一致。 -/
theorem FundSys.NOTFundLt_iff_lt {S : FundSys} (hlt : S.FundDesc) (hcof : S.FundCofinal)
    (hwf : WellFounded (fun a b : @FundSys.NOT S => a.val < b.val)) (a b : @FundSys.NOT S) :
    S.NOTFundLt a b ↔ a.val < b.val :=
  ⟨FundSys.NOTFundLt_lt hlt, FundSys.NOTFundLt_of_lt hlt hcof hwf a b⟩

end multi

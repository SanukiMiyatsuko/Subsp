import Subsp.multi.old.source
import Subsp.multi.old.supp

/-! The translation of `old` into Buchholz notation.

For a vector `[a₀, …, aₙ]` whose top nonzero coordinate has index `n ≥ 1`,
`P[a₀, …, aₙ] + r ↦ ψ_n(Ω_n · (aₙ - 1) + ∑_{1 ≤ j < n} Ω_j · ec_j(aⱼ) + ec_0(a₀)) + r`,
and `P[a₀] + r ↦ ψ_0(a₀) + r`, where `ec_j` collapses at index `j` and `Ω_j ·` is `OB.ct j`. -/

namespace old

open OB

mutual
def tr : multi.T → T
  | .Z => .Z
  | .P v a => T.add (auxH v) (tr a)

/-- The principal summand of the translation of a vector. -/
def auxH : multi.V multi.T → T
  | .emp => .P 0 .Z .Z
  | .snoc x xs => match xs with
    | .emp => .P 0 (tr x) .Z
    | .snoc _ _ => if x = .Z then auxH xs else
        .P xs.length (T.add (ct xs.length (oneDel (tr x))) (auxL xs)) .Z

/-- The contributions of the coordinates of a vector, the highest first. -/
def auxL : multi.V multi.T → T
  | .emp => .Z
  | .snoc x xs => match xs with
    | .emp => ec 0 (tr x)
    | .snoc _ _ => T.add (ct xs.length (ec xs.length (tr x))) (auxL xs)
end

theorem tr_Z : tr multi.T.Z = T.Z := by rw [tr]

theorem tr_P (v : multi.V multi.T) (a : multi.T) : tr (multi.T.P v a) = T.add (auxH v) (tr a) := by
  rw [tr]

theorem ec_Z (n : Nat) : ec n T.Z = T.Z := ec_of_index n T.Z T.index_Prop1.z

/-! ### Compatibility with normalization -/

theorem auxH_single (x : multi.T) : auxH (.snoc x .emp) = T.P 0 (tr x) T.Z := by
  rw [auxH]

theorem auxL_single (x : multi.T) : auxL (.snoc x .emp) = ec 0 (tr x) := by
  rw [auxL]

theorem auxH_snoc_snoc (x y : multi.T) (ys : multi.V multi.T) :
    auxH (.snoc x (.snoc y ys)) = if x = .Z then auxH (.snoc y ys) else
      T.P (multi.V.snoc y ys).length
        (T.add (ct (multi.V.snoc y ys).length (oneDel (tr x))) (auxL (.snoc y ys))) T.Z := by
  rw [auxH]

theorem auxL_snoc_snoc (x y : multi.T) (ys : multi.V multi.T) :
    auxL (.snoc x (.snoc y ys)) =
      T.add (ct (multi.V.snoc y ys).length (ec (multi.V.snoc y ys).length (tr x)))
        (auxL (.snoc y ys)) := by
  rw [auxL]

theorem auxH_snocZ (xs : multi.V multi.T) : auxH (.snoc .Z xs) = auxH xs := by
  cases xs with
  | emp => rw [auxH_single, tr_Z]; rfl
  | snoc y ys => rw [auxH_snoc_snoc, ite_eq_left rfl]

theorem auxL_snocZ (xs : multi.V multi.T) : auxL (.snoc .Z xs) = auxL xs := by
  cases xs with
  | emp => rw [auxL_single, tr_Z, ec_Z]; rfl
  | snoc y ys => rw [auxL_snoc_snoc, tr_Z, ec_Z]; rfl

theorem auxH_trim : ∀ v : multi.V multi.T, auxH (multi.V.trim v) = auxH v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z => show auxH (multi.V.trim ax) = _; rw [auxH_trim ax, auxH_snocZ]
    | P _ _ => rfl

theorem auxL_trim : ∀ v : multi.V multi.T, auxL (multi.V.trim v) = auxL v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z => show auxL (multi.V.trim ax) = _; rw [auxL_trim ax, auxL_snocZ]
    | P _ _ => rfl

mutual
theorem tr_norm : ∀ s : multi.T, tr (multi.T.norm s) = tr s
  | .Z => by rw [multi.T.norm]
  | .P v a => by
    rw [multi.T.norm_P, tr_P, tr_P, tr_norm a, multi.V.norm, auxH_trim, auxH_mapNorm v]

theorem auxH_mapNorm : ∀ v : multi.V multi.T, auxH (multi.V.mapNorm v) = auxH v
  | .emp => by rw [multi.V.mapNorm]
  | .snoc a .emp => by
    show auxH (multi.V.snoc (multi.T.norm a) multi.V.emp) = auxH (multi.V.snoc a multi.V.emp)
    rw [auxH_single, auxH_single, tr_norm a]
  | .snoc a (.snoc b bx) => by
    have hm : multi.V.mapNorm (multi.V.snoc b bx) =
        multi.V.snoc (multi.T.norm b) (multi.V.mapNorm bx) := rfl
    show auxH (multi.V.snoc (multi.T.norm a) (multi.V.snoc (multi.T.norm b) (multi.V.mapNorm bx)))
      = auxH (multi.V.snoc a (multi.V.snoc b bx))
    rw [auxH_snoc_snoc, auxH_snoc_snoc, ← hm, multi.V.length_mapNorm,
      auxH_mapNorm (.snoc b bx), auxL_mapNorm (.snoc b bx), tr_norm a]
    by_cases ha : a = .Z
    · rw [ite_eq_left ha, ite_eq_left (by rw [ha]; rfl)]
    · rw [ite_eq_right ha, ite_eq_right (fun h => ha (multi.T.norm_eq_Z.1 h))]

theorem auxL_mapNorm : ∀ v : multi.V multi.T, auxL (multi.V.mapNorm v) = auxL v
  | .emp => by rw [multi.V.mapNorm]
  | .snoc a .emp => by
    show auxL (multi.V.snoc (multi.T.norm a) multi.V.emp) = auxL (multi.V.snoc a multi.V.emp)
    rw [auxL_single, auxL_single, tr_norm a]
  | .snoc a (.snoc b bx) => by
    have hm : multi.V.mapNorm (multi.V.snoc b bx) =
        multi.V.snoc (multi.T.norm b) (multi.V.mapNorm bx) := rfl
    show auxL (multi.V.snoc (multi.T.norm a) (multi.V.snoc (multi.T.norm b) (multi.V.mapNorm bx)))
      = auxL (multi.V.snoc a (multi.V.snoc b bx))
    rw [auxL_snoc_snoc, auxL_snoc_snoc, ← hm, multi.V.length_mapNorm,
      auxL_mapNorm (.snoc b bx), tr_norm a]
end


theorem tr_congr {a b : multi.T} (h : multi.compareT a b = .eq) : tr a = tr b := by
  rw [← tr_norm a, ← tr_norm b, (multi.compareT_eq_iff a b).1 h]

/-! ### Coordinatewise description -/

/-- The contributions of the coordinates below `k`. -/
def lowS (f : Nat → multi.T) : Nat → T
  | 0 => T.Z
  | 1 => ec 0 (tr (f 0))
  | k + 2 => T.add (ct (k + 1) (ec (k + 1) (tr (f (k + 1))))) (lowS f (k + 1))

/-- The principal summand determined by the coordinates below `k`. -/
def headS (f : Nat → multi.T) : Nat → T
  | 0 => T.P 0 T.Z T.Z
  | 1 => T.P 0 (tr (f 0)) T.Z
  | k + 2 => if f (k + 1) = multi.T.Z then headS f (k + 1) else
      T.P (k + 1) (T.add (ct (k + 1) (oneDel (tr (f (k + 1))))) (lowS f (k + 1))) T.Z

theorem lowS_two (f : Nat → multi.T) (k : Nat) :
    lowS f (k + 2) = T.add (ct (k + 1) (ec (k + 1) (tr (f (k + 1))))) (lowS f (k + 1)) := rfl

theorem headS_two_Z {f : Nat → multi.T} {k : Nat} (h : f (k + 1) = multi.T.Z) :
    headS f (k + 2) = headS f (k + 1) := by
  rw [headS, ite_eq_left h]

theorem headS_two_ne {f : Nat → multi.T} {k : Nat} (h : f (k + 1) ≠ multi.T.Z) :
    headS f (k + 2) =
      T.P (k + 1) (T.add (ct (k + 1) (oneDel (tr (f (k + 1))))) (lowS f (k + 1))) T.Z := by
  rw [headS, ite_eq_right h]

theorem lowS_congr {f g : Nat → multi.T} :
    ∀ k, (∀ j, j < k → multi.compareT (f j) (g j) = .eq) → lowS f k = lowS g k
  | 0, _ => rfl
  | 1, h => by
    show ec 0 (tr (f 0)) = ec 0 (tr (g 0))
    rw [tr_congr (h 0 Nat.one_pos)]
  | k + 2, h => by
    rw [lowS_two, lowS_two, tr_congr (h (k + 1) (Nat.lt_succ_self _)),
      lowS_congr (k + 1) (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self _)))]

theorem headS_congr {f g : Nat → multi.T} :
    ∀ k, (∀ j, j < k → multi.compareT (f j) (g j) = .eq) → headS f k = headS g k
  | 0, _ => rfl
  | 1, h => by
    show T.P 0 (tr (f 0)) T.Z = T.P 0 (tr (g 0)) T.Z
    rw [tr_congr (h 0 Nat.one_pos)]
  | k + 2, h => by
    have hk := h (k + 1) (Nat.lt_succ_self _)
    have hrest : ∀ j, j < k + 1 → multi.compareT (f j) (g j) = .eq :=
      fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self _))
    by_cases hz : f (k + 1) = multi.T.Z
    · have hz' : g (k + 1) = multi.T.Z := by
        rw [hz] at hk; exact multi.T.eqv_Z_iff.1 (multi.T.eqv_symm hk)
      rw [headS_two_Z hz, headS_two_Z hz', headS_congr (k + 1) hrest]
    · have hz' : g (k + 1) ≠ multi.T.Z := ne_Z_of_eqv hk hz
      rw [headS_two_ne hz, headS_two_ne hz', tr_congr hk, lowS_congr (k + 1) hrest]

theorem lowS_zeros (f : Nat → multi.T) (k : Nat) (hz : ∀ j, k ≤ j → f j = multi.T.Z) :
    ∀ m, lowS f (k + m) = lowS f k
  | 0 => rfl
  | m + 1 => by
    rcases Nat.eq_zero_or_pos (k + m) with h0 | hpos
    · have hk : k = 0 := by omega
      have hm : m = 0 := by omega
      subst hk; subst hm
      show ec 0 (tr (f 0)) = T.Z
      rw [hz 0 (Nat.le_refl 0), tr_Z, ec_Z]
    · obtain ⟨n, hn⟩ : ∃ n, k + m = n + 1 := ⟨k + m - 1, by omega⟩
      rw [show k + (m + 1) = n + 2 by omega, lowS_two, ← hn,
        hz (k + m) (Nat.le_add_right k m), tr_Z, ec_Z]
      show lowS f (k + m) = lowS f k
      exact lowS_zeros f k hz m

theorem headS_zeros (f : Nat → multi.T) (k : Nat) (hz : ∀ j, k ≤ j → f j = multi.T.Z) :
    ∀ m, headS f (k + m) = headS f k
  | 0 => rfl
  | m + 1 => by
    rcases Nat.eq_zero_or_pos (k + m) with h0 | hpos
    · have hk : k = 0 := by omega
      have hm : m = 0 := by omega
      subst hk; subst hm
      show T.P 0 (tr (f 0)) T.Z = T.P 0 T.Z T.Z
      rw [hz 0 (Nat.le_refl 0), tr_Z]
    · obtain ⟨n, hn⟩ : ∃ n, k + m = n + 1 := ⟨k + m - 1, by omega⟩
      rw [show k + (m + 1) = n + 2 by omega, headS_two_Z (by rw [← hn]; exact hz _ (Nat.le_add_right k m)),
        ← hn]
      exact headS_zeros f k hz m

theorem auxL_eq_length : ∀ v : multi.V multi.T, auxL v = lowS (multi.V.get0 v) v.length
  | .emp => rfl
  | .snoc x .emp => by
    show ec 0 (tr x) = ec 0 (tr (multi.V.get0 (multi.V.snoc x multi.V.emp) 0))
    rw [show multi.V.get0 (multi.V.snoc x multi.V.emp) 0 = x from multi.V.get0_snoc_top x _]
  | .snoc x (.snoc y ys) => by
    show T.add (ct _ (ec _ (tr x))) (auxL (multi.V.snoc y ys)) =
      lowS (multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys))) (ys.length + 2)
    rw [lowS_two, auxL_eq_length (.snoc y ys)]
    have htop : multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys)) (ys.length + 1) = x :=
      multi.V.get0_snoc_top x (multi.V.snoc y ys)
    rw [htop]
    congr 1
    exact lowS_congr _ (fun j hj => by
      rw [multi.V.get0_snoc_low x (multi.V.snoc y ys) j hj]; exact multi.T.eqv_refl _)

theorem auxH_eq_length : ∀ v : multi.V multi.T, auxH v = headS (multi.V.get0 v) v.length
  | .emp => rfl
  | .snoc x .emp => by
    show T.P 0 (tr x) T.Z = T.P 0 (tr (multi.V.get0 (multi.V.snoc x multi.V.emp) 0)) T.Z
    rw [show multi.V.get0 (multi.V.snoc x multi.V.emp) 0 = x from multi.V.get0_snoc_top x _]
  | .snoc x (.snoc y ys) => by
    have htop : multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys)) (ys.length + 1) = x :=
      multi.V.get0_snoc_top x (multi.V.snoc y ys)
    have hlow : ∀ j, j < ys.length + 1 → multi.compareT
        (multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys)) j)
        (multi.V.get0 (multi.V.snoc y ys) j) = .eq := fun j hj => by
      rw [multi.V.get0_snoc_low x (multi.V.snoc y ys) j hj]; exact multi.T.eqv_refl _
    show (if x = .Z then auxH (multi.V.snoc y ys) else
        T.P (ys.length + 1) (T.add (ct (ys.length + 1) (oneDel (tr x)))
          (auxL (multi.V.snoc y ys))) T.Z) =
      headS (multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys))) (ys.length + 2)
    by_cases hx : x = .Z
    · rw [ite_eq_left hx, headS_two_Z (by rw [htop]; exact hx), auxH_eq_length (.snoc y ys),
        headS_congr _ hlow]
      rfl
    · rw [ite_eq_right hx, headS_two_ne (by rw [htop]; exact hx), htop, auxL_eq_length (.snoc y ys),
        lowS_congr _ hlow]
      rfl

theorem auxL_eq (v : multi.V multi.T) (N : Nat) (hN : v.length ≤ N) :
    auxL v = lowS (multi.V.get0 v) N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = v.length + m := ⟨N - v.length, by omega⟩
  rw [auxL_eq_length, lowS_zeros _ _ (fun j hj => multi.V.get0_ge v j hj) m]

theorem auxH_eq (v : multi.V multi.T) (N : Nat) (hN : v.length ≤ N) :
    auxH v = headS (multi.V.get0 v) N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = v.length + m := ⟨N - v.length, by omega⟩
  rw [auxH_eq_length, headS_zeros _ _ (fun j hj => multi.V.get0_ge v j hj) m]

theorem auxH_congr {v w : multi.V multi.T} (h : multi.compareV v w = .eq) : auxH v = auxH w := by
  rw [auxH_eq v (v.length + w.length) (Nat.le_add_right _ _),
    auxH_eq w (v.length + w.length) (Nat.le_add_left _ _)]
  exact headS_congr _ (fun j _ => (multi.V.eqv_iff_get0 v w).1 h j)

/-! ### Shape of the principal summand -/

theorem headS_shape (f : Nat → multi.T) :
    ∀ k, ∃ p X, headS f k = T.P p X T.Z ∧ (p = 0 ∨ p < k)
  | 0 => ⟨0, T.Z, rfl, Or.inl rfl⟩
  | 1 => ⟨0, tr (f 0), rfl, Or.inl rfl⟩
  | k + 2 => by
    by_cases hz : f (k + 1) = multi.T.Z
    · rw [headS_two_Z hz]
      obtain ⟨p, X, he, hp⟩ := headS_shape f (k + 1)
      exact ⟨p, X, he, hp.imp_right (fun h => Nat.lt_trans h (Nat.lt_succ_self _))⟩
    · rw [headS_two_ne hz]
      exact ⟨k + 1, _, rfl, Or.inr (Nat.lt_succ_self _)⟩

theorem auxH_shape (v : multi.V multi.T) : ∃ p X, auxH v = T.P p X T.Z := by
  obtain ⟨p, X, he, _⟩ := headS_shape (multi.V.get0 v) v.length
  exact ⟨p, X, by rw [auxH_eq_length, he]⟩

theorem tr_P_eq (v : multi.V multi.T) (a : multi.T) :
    ∃ p X, auxH v = T.P p X T.Z ∧ tr (multi.T.P v a) = T.P p X (tr a) := by
  obtain ⟨p, X, he⟩ := auxH_shape v
  exact ⟨p, X, he, by rw [tr_P, he, p_zero_add]⟩

theorem tr_ne_Z {s : multi.T} (h : s ≠ multi.T.Z) : tr s ≠ T.Z := by
  cases s with
  | Z => exact absurd rfl h
  | P v a =>
    obtain ⟨p, X, _, he⟩ := tr_P_eq v a
    rw [he]; intro h; cases h

theorem Z_lt_tr {s : multi.T} (h : s ≠ multi.T.Z) : T.Z < tr s := MT.Z_lt_of_ne (tr_ne_Z h)

theorem head_tr (v : multi.V multi.T) (a : multi.T) : T.head (tr (multi.T.P v a)) = auxH v := by
  obtain ⟨p, X, he, htr⟩ := tr_P_eq v a
  rw [htr, he]; rfl

theorem tr_ne_Z_of_ne {x : multi.T} (hx : x ≠ multi.T.Z) : tr x ≠ T.Z := tr_ne_Z hx

theorem tr_eq_Z {x : multi.T} (h : tr x = T.Z) : x = multi.T.Z := by
  by_cases hx : x = multi.T.Z
  · exact hx
  · exact absurd h (tr_ne_Z hx)

/-! ### Normal forms of the principal summand -/

/-- Good coordinates at index `u`: normal translations whose level-`u` support lies below. -/
def Gd (u : Nat) (x : multi.T) : Prop := T.isNF1 (tr x) ∧ ∀ y, y ∈ T.G1 u (tr x) → y < tr x

theorem Gd_Z (u : Nat) : Gd u multi.T.Z :=
  ⟨by rw [tr_Z]; exact T.isNF1.z, fun y hy => by rw [tr_Z] at hy; cases hy⟩

theorem lowS_closed (f : Nat → multi.T) (hf : ∀ j, Gd j (f j)) :
    ∀ k, T.isNF1 (lowS f k) ∧ T.index_Prop1 (k - 1) (lowS f k) ∧ lowS f k < T.P k T.Z T.Z
  | 0 => ⟨T.isNF1.z, T.index_Prop1.z, T.Lt.Z_lt_P _ _ _⟩
  | 1 => by
    obtain ⟨h1, h2⟩ := ec_closed 0 (tr (f 0)) (hf 0).1 (hf 0).2
    exact ⟨h1, h2, index_Prop1_lt_succ 0 _ h2⟩
  | k + 2 => by
    obtain ⟨h1, h2, h3⟩ := lowS_closed f hf (k + 1)
    obtain ⟨heNF, heIdx⟩ := ec_closed (k + 1) _ (hf (k + 1)).1 (hf (k + 1)).2
    rw [lowS_two]
    have hidx : T.index_Prop1 (k + 1)
        (T.add (ct (k + 1) (ec (k + 1) (tr (f (k + 1))))) (lowS f (k + 1))) :=
      Rank1Termination.index_add _ _ _ (ct_index_self (k + 1) _ heIdx)
        (Rank1Termination.index_mono (Nat.le_succ k) _ h2)
    exact ⟨ct_append_closed (k + 1) _ _ heNF h1 h3, hidx, index_Prop1_lt_succ (k + 1) _ hidx⟩

theorem headS_closed (f : Nat → multi.T) (hf : ∀ j, Gd j (f j)) : ∀ k, T.isNF1 (headS f k)
  | 0 => T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z (fun x hx => by cases hx) (T.Z_le _)
  | 1 => T.isNF1.p 0 (tr (f 0)) T.Z (hf 0).1 T.isNF1.z (hf 0).2 (T.Z_le _)
  | k + 2 => by
    by_cases hz : f (k + 1) = multi.T.Z
    · rw [headS_two_Z hz]; exact headS_closed f hf (k + 1)
    · rw [headS_two_ne hz]
      obtain ⟨hlNF, hlIdx, hlB⟩ := lowS_closed f hf (k + 1)
      have haNF := oneDel_NF _ (hf (k + 1)).1
      have haGood := oneDel_good_pos (k + 1) (Nat.succ_pos k) _ (hf (k + 1)).1 (hf (k + 1)).2
      exact T.isNF1.p (k + 1) _ T.Z (ct_append_closed _ _ _ haNF hlNF hlB) T.isNF1.z
        (ct_append_good (k + 1) k (Nat.lt_succ_self k) _ _ haNF haGood hlIdx) (T.Z_le _)

theorem auxH_closed {v : multi.V multi.T} (hv : ∀ j, Gd j (multi.V.get0 v j)) :
    T.isNF1 (auxH v) := by
  rw [auxH_eq_length]; exact headS_closed _ hv _

/-! ### Comparison of principal summands -/

theorem headS_lt {f g : Nat → multi.T} (hf : ∀ j, Gd j (f j)) (hg : ∀ j, Gd j (g j))
    (hm : ∀ j, f j < g j → tr (f j) < tr (g j)) (p : Nat)
    (heq : ∀ j, p < j → multi.compareT (f j) (g j) = .eq) (hlt : f p < g p) :
    ∀ m, lowS f (p + 1 + m) < lowS g (p + 1 + m) ∧ headS f (p + 1 + m) < headS g (p + 1 + m)
  | 0 => by
    have htr := hm p hlt
    cases p with
    | zero =>
      exact ⟨ec_lt 0 _ _ (hf 0).1 (hf 0).2 (hg 0).1 htr, T.Lt.p_mid _ _ _ _ _ htr⟩
    | succ q =>
      have he := ec_lt (q + 1) _ _ (hf (q + 1)).1 (hf (q + 1)).2 (hg (q + 1)).1 htr
      have hgz : g (q + 1) ≠ multi.T.Z := multi.T.ne_Z_of_lt hlt
      refine ⟨?_, ?_⟩
      · show lowS f (q + 2) < lowS g (q + 2)
        rw [lowS_two, lowS_two]
        exact ct_append_lt (q + 1) _ _ _ _ (ec_closed (q + 1) _ (hf (q + 1)).1 (hf (q + 1)).2).1
          (ec_closed (q + 1) _ (hg (q + 1)).1 (hg (q + 1)).2).1 he (lowS_closed f hf (q + 1)).2.2
      · show headS f (q + 2) < headS g (q + 2)
        rw [headS_two_ne hgz]
        by_cases hfz : f (q + 1) = multi.T.Z
        · rw [headS_two_Z hfz]
          obtain ⟨p', X, he', hp'⟩ := headS_shape f (q + 1)
          rw [he']
          apply T.Lt.p_head
          rcases hp' with h | h
          · rw [h]; exact Nat.succ_pos q
          · exact h
        · rw [headS_two_ne hfz]
          exact T.Lt.p_mid _ _ _ _ _ (ct_append_lt (q + 1) _ _ _ _ (oneDel_NF _ (hf (q + 1)).1)
            (oneDel_NF _ (hg (q + 1)).1) (oneDel_lt _ _ (hf (q + 1)).1 (tr_ne_Z hfz) htr)
            (lowS_closed f hf (q + 1)).2.2)
  | m + 1 => by
    obtain ⟨ih1, ih2⟩ := headS_lt hf hg hm p heq hlt m
    have e1 : p + 1 + m = p + m + 1 := by omega
    rw [e1] at ih1 ih2
    have hk : multi.compareT (f (p + m + 1)) (g (p + m + 1)) = .eq := heq _ (by omega)
    rw [show p + 1 + (m + 1) = p + m + 2 by omega]
    refine ⟨?_, ?_⟩
    · rw [lowS_two, lowS_two, tr_congr hk]
      exact MT.add_left_lt _ ih1
    · by_cases hfz : f (p + m + 1) = multi.T.Z
      · have hgz : g (p + m + 1) = multi.T.Z := by
          rw [hfz] at hk; exact multi.T.eqv_Z_iff.1 (multi.T.eqv_symm hk)
        rw [headS_two_Z hfz, headS_two_Z hgz]; exact ih2
      · have hgz : g (p + m + 1) ≠ multi.T.Z := ne_Z_of_eqv hk hfz
        rw [headS_two_ne hfz, headS_two_ne hgz, tr_congr hk]
        exact T.Lt.p_mid _ _ _ _ _ (MT.add_left_lt _ ih1)

theorem auxH_lt {v w : multi.V multi.T} (hv : ∀ j, Gd j (multi.V.get0 v j))
    (hw : ∀ j, Gd j (multi.V.get0 w j))
    (hm : ∀ j, multi.V.get0 v j < multi.V.get0 w j → tr (multi.V.get0 v j) < tr (multi.V.get0 w j))
    (hlt : v < w) : auxH v < auxH w ∧ auxL v < auxL w := by
  obtain ⟨p, heq, hp⟩ := (multi.V.lt_iff_pivot v w).1 hlt
  have hpw : p < w.length := by
    apply Nat.lt_of_not_le
    intro h
    rw [multi.V.get0_ge w p h] at hp
    exact multi.T.not_lt_Z _ hp
  obtain ⟨m, hm'⟩ : ∃ m, v.length + w.length = p + 1 + m := ⟨v.length + w.length - (p + 1), by omega⟩
  rw [auxH_eq v (v.length + w.length) (Nat.le_add_right _ _),
    auxH_eq w (v.length + w.length) (Nat.le_add_left _ _),
    auxL_eq v (v.length + w.length) (Nat.le_add_right _ _),
    auxL_eq w (v.length + w.length) (Nat.le_add_left _ _), hm']
  obtain ⟨h1, h2⟩ := headS_lt hv hw hm p heq hp m
  exact ⟨h2, h1⟩

/-! ### Order preservation and normal forms -/

theorem order_preserve_bounded (N : Nat)
    (hgood : ∀ x : multi.T, x.size < N → ∀ u, NFComp u x → Gd u x) :
    ∀ s t : multi.T, s.size ≤ N → t.size ≤ N → NF s → NF t → s < t → tr s < tr t := by
  intro s
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro t hsz htz hs ht hlt
    cases s with
    | Z =>
      cases t with
      | Z => exact absurd hlt (multi.T.not_lt_Z _)
      | P w b => rw [tr_Z]; exact Z_lt_tr (fun h => multi.T.noConfusion h)
    | P v a =>
      cases t with
      | Z => exact absurd hlt (multi.T.not_lt_Z _)
      | P w b =>
        rcases (multi.T.P_lt_P_iff v w a b).1 hlt with hvw | ⟨hvw, hab⟩
        · apply lt_of_head_lt
          rw [head_tr, head_tr]
          refine (auxH_lt (fun j => hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P v j a) hsz)
            j (hs.comp j)) (fun j => hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P w j b) htz)
            j (ht.comp j)) (fun j hj => ?_) hvw).1
          exact ih _ (multi.T.size_get0_lt_P v j a) _
            (Nat.le_trans (Nat.le_of_lt (multi.T.size_get0_lt_P v j a)) hsz)
            (Nat.le_trans (Nat.le_of_lt (multi.T.size_get0_lt_P w j b)) htz)
            (hs.comp j).1 (ht.comp j).1 hj
        · rw [tr_P, tr_P, auxH_congr hvw]
          exact MT.add_left_lt _ (ih a (multi.T.size_lt_P_right v a) b
            (Nat.le_trans (Nat.le_of_lt (multi.T.size_lt_P_right v a)) hsz)
            (Nat.le_trans (Nat.le_of_lt (multi.T.size_lt_P_right w b)) htz) hs.inv.2.1 ht.inv.2.1 hab)

theorem NF_step (v : multi.V multi.T) (a : multi.T) (hs : NF (multi.T.P v a))
    (hnf : ∀ s : multi.T, s.size < (multi.T.P v a).size → NF s → T.isNF1 (tr s))
    (hgood : ∀ s : multi.T, s.size < (multi.T.P v a).size → ∀ u, NFComp u s → Gd u s) :
    T.isNF1 (tr (multi.T.P v a)) := by
  obtain ⟨_, ha, _, hh⟩ := hs.inv
  have hvg : ∀ j, Gd j (multi.V.get0 v j) :=
    fun j => hgood _ (multi.T.size_get0_lt_P v j a) j (hs.comp j)
  have hhead : T.head (tr a) ≤ auxH v := by
    cases a with
    | Z => rw [tr_Z]; exact T.Z_le _
    | P w b =>
      rw [head_tr]
      have hsw : ∀ j, (multi.V.get0 w j).size < (multi.T.P v (multi.T.P w b)).size :=
        fun j => Nat.lt_trans (multi.T.size_get0_lt_P w j b) (multi.T.size_lt_P_right v _)
      rcases (multi.T.P_le_P_iff w v multi.T.Z multi.T.Z).1 hh with hwv | ⟨hwv, _⟩
      · refine Or.inl (auxH_lt (fun j => hgood _ (hsw j) j (ha.comp j)) hvg (fun j hj => ?_) hwv).1
        exact order_preserve_bounded (multi.T.P v (multi.T.P w b)).size hgood _ _
          (Nat.le_of_lt (hsw j)) (Nat.le_of_lt (multi.T.size_get0_lt_P v j _))
          (ha.comp j).1 (hs.comp j).1 hj
      · exact Or.inr (auxH_congr hwv)
  have hprincipal := auxH_closed hvg
  obtain ⟨p, X, he, htr⟩ := tr_P_eq v a
  rw [he] at hprincipal hhead
  rw [htr]
  obtain ⟨hX, _, hgX, _⟩ := T.isNF1_P_inv _ _ _ hprincipal
  exact T.isNF1.p p X (tr a) hX (hnf a (multi.T.size_lt_P_right v a) ha) hgX hhead

/-! ### Supports of the principal summand -/

/-- Bounds on the supports of the contributions of a coordinate at index `i`. -/
def CoordHyp (u : Nat) (C : T) (i : Nat) (x : multi.T) : Prop :=
  (∀ y ∈ T.G1 u (ct i (ec i (tr x))), y < C) ∧
  (u ≤ i → ∀ y ∈ T.G1 u (ct i (oneDel (tr x))), y < C) ∧
  (i = 0 → ∀ y ∈ T.G1 u (ec 0 (tr x)), y < C) ∧
  (i = 0 → u = 0 → ∀ y ∈ T.G1 u (tr x), y < C)

theorem lowS_support (u : Nat) (C : T) (f : Nat → multi.T) (hc : ∀ j, CoordHyp u C j (f j)) :
    ∀ k, ∀ y ∈ T.G1 u (lowS f k), y < C
  | 0 => fun y hy => by cases hy
  | 1 => (hc 0).2.2.1 rfl
  | k + 2 => by
    intro y hy
    rw [lowS_two, MT.G1_add, List.mem_append] at hy
    rcases hy with hy | hy
    · exact (hc (k + 1)).1 y hy
    · exact lowS_support u C f hc (k + 1) y hy

theorem headS_support (u : Nat) (C : T) (f : Nat → multi.T) (hc : ∀ j, CoordHyp u C j (f j)) :
    ∀ k p X, headS f k = T.P p X T.Z → u ≤ p → ∀ y ∈ T.G1 u X, y < C
  | 0, p, X, he, _, y, hy => by
    change T.P 0 T.Z T.Z = T.P p X T.Z at he
    injection he with _ hX _
    rw [← hX] at hy; cases hy
  | 1, p, X, he, hup, y, hy => by
    change T.P 0 (tr (f 0)) T.Z = T.P p X T.Z at he
    injection he with hp hX _
    rw [← hp] at hup
    rw [← hX] at hy
    exact (hc 0).2.2.2 rfl (Nat.eq_zero_of_le_zero hup) y hy
  | k + 2, p, X, he, hup, y, hy => by
    by_cases hz : f (k + 1) = multi.T.Z
    · rw [headS_two_Z hz] at he
      exact headS_support u C f hc (k + 1) p X he hup y hy
    · rw [headS_two_ne hz] at he
      injection he with hp hX _
      rw [← hp] at hup
      rw [← hX, MT.G1_add, List.mem_append] at hy
      rcases hy with hy | hy
      · exact (hc (k + 1)).2.1 hup y hy
      · exact lowS_support u C f hc (k + 1) y hy

theorem coord_hyp_of (u : Nat) (C : T) (i : Nat) (x : multi.T) (hx : Gd i x)
    (hxC : u ≤ i → tr x < C) (hsum : u ≤ i → SumAll (CardCond i u (· < C)) (tr x)) :
    CoordHyp u C i x := by
  have hR : ∀ a b : T, a ≤ b → b < C → a < C := fun a b h1 h2 => lt_of_le_of_lt_thm T _ _ _ h1 h2
  have hec := ec_closed i (tr x) hx.1 hx.2
  by_cases hui : u ≤ i
  · refine ⟨early_card_support_bounded i u hui (· < C) hR (tr x) hx.1 (hxC hui) (hsum hui),
      fun _ => ct_support_bounded i u hui (· < C) hR _ (oneDel_NF _ hx.1)
        (hR _ _ (oneDel_le _ hx.1) (hxC hui)) (SumAll_oneDel _ _ (hsum hui)), ?_, ?_⟩
    · intro hi0 y hy
      subst hi0
      have hu0 : u = 0 := Nat.eq_zero_of_le_zero hui
      subst hu0
      rcases ec_support_exact 0 0 (tr x) (Nat.le_refl 0) hx.1 y hy with h | h
      · rw [h]; exact hR _ _ (part_first_le 0 _ hx.1) (hxC hui)
      · exact lt_trans_thm _ _ _ (hx.2 y h) (hxC hui)
    · intro hi0 hu0 y hy
      subst hi0; subst hu0
      exact lt_trans_thm _ _ _ (hx.2 y hy) (hxC hui)
  · have hui' : i < u := Nat.lt_of_not_le hui
    refine ⟨?_, fun h => absurd h hui, ?_, fun hi0 hu0 => absurd (by rw [hi0, hu0]; exact Nat.le_refl 0) hui⟩
    · rw [index_Prop1_G1_empty i _ (ct_index_self i _ hec.2) u hui']
      intro y hy; cases hy
    · intro hi0
      subst hi0
      rw [index_Prop1_G1_empty 0 _ hec.2 u hui']
      intro y hy; cases hy

/-- The high part of a principal argument is the high part of its top coordinate. -/
theorem headS_high (f : Nat → multi.T) (hf : ∀ j, Gd j (f j)) :
    ∀ k p X, headS f k = T.P p X T.Z →
      (part p X).1 = T.Z ∨ (part p X).1 = (part p (tr (f p))).1
  | 0, p, X, he => by
    change T.P 0 T.Z T.Z = T.P p X T.Z at he
    injection he with _ hX _
    rw [← hX]; exact Or.inl rfl
  | 1, p, X, he => by
    change T.P 0 (tr (f 0)) T.Z = T.P p X T.Z at he
    injection he with hp hX _
    rw [← hp, ← hX]; exact Or.inr rfl
  | k + 2, p, X, he => by
    by_cases hz : f (k + 1) = multi.T.Z
    · rw [headS_two_Z hz] at he
      exact headS_high f hf (k + 1) p X he
    · rw [headS_two_ne hz] at he
      injection he with hp hX _
      subst hp; subst hX
      have hlow := lowS_closed f hf (k + 1)
      refine Or.inr ?_
      rw [part_add_distrib, part_of_index (k + 1) _
        (Rank1Termination.index_mono (Nat.le_succ k) _ hlow.2.1), T.add_Z,
        (part_ct (k + 1) _).1, part_oneDel_fst]

/-! ### Supports of translations -/

theorem deep_bound (N : Nat) (hgood : ∀ x : multi.T, x.size < N → ∀ u, NFComp u x → Gd u x)
    (u : Nat) (C : T) (hC : T.Z < C) :
    ∀ x : multi.T, x.size ≤ N → NF x → (∀ z, z ∈ G u x → tr z < C) →
      SumAll (fun p c => u ≤ p → ∀ y ∈ T.G1 u c, y < C) (tr x) ∧
        SumAll (fun p c => u ≤ p → (part p c).1 = T.Z ∨ (part p c).1 < C) (tr x) := by
  intro x
  induction x using (measure multi.T.size).wf.induction with
  | h x ih =>
    intro hsz hx hsupp
    cases x with
    | Z => rw [tr_Z]; exact ⟨trivial, trivial⟩
    | P w b =>
      have hcoordSz (j : Nat) : (multi.V.get0 w j).size < N :=
        Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P w j b) hsz
      have hgw (j : Nat) : Gd j (multi.V.get0 w j) := hgood _ (hcoordSz j) j (hx.comp j)
      obtain ⟨K, X, he, htr⟩ := tr_P_eq w b
      have ihb := ih b (multi.T.size_lt_P_right w b)
        (Nat.le_trans (Nat.le_of_lt (multi.T.size_lt_P_right w b)) hsz) hx.inv.2.1
        (fun z hz => hsupp z (G_in_tail hz))
      have hcoordC (j : Nat) (huj : u ≤ j) : tr (multi.V.get0 w j) < C := by
        by_cases hz : multi.V.get0 w j = multi.T.Z
        · rw [hz, tr_Z]; exact hC
        · exact hsupp _ (G_coord_mem huj hz)
      rw [htr]
      have hcoord (j : Nat) : CoordHyp u C j (multi.V.get0 w j) := by
        apply coord_hyp_of u C j _ (hgw j) (hcoordC j)
        intro huj
        have ihj := ih (multi.V.get0 w j) (multi.T.size_get0_lt_P w j b)
          (Nat.le_of_lt (hcoordSz j)) (hx.comp j).1
          (fun z hz => hsupp z (G_in_coord huj hz))
        have hself := SumAll_G1_self j (tr (multi.V.get0 w j))
        have h1 : SumAll (fun p c => j ≤ p → c < C) (tr (multi.V.get0 w j)) := by
          apply SumAll_mono _ _ _ _ hself
          intro p c h hjp
          exact lt_trans_thm _ _ _ ((hgw j).2 c (h hjp)) (hcoordC j huj)
        apply SumAll_mono _ _ _ _ (SumAll_and3 _ _ _ _ h1 ihj.1 ihj.2)
        intro p c ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun hup _ => ?_⟩
        rcases h3 hup with h | h
        · rw [h]; exact hC
        · exact h
      refine ⟨⟨fun hup => headS_support u C _ hcoord _ K X
        (by rw [← auxH_eq_length]; exact he) hup, ihb.1⟩, ⟨fun hup => ?_, ihb.2⟩⟩
      rcases headS_high _ hgw w.length K X (by rw [← auxH_eq_length]; exact he) with h | h
      · exact Or.inl h
      · apply Or.inr
        rw [h]
        exact lt_of_le_of_lt_thm T _ _ _ (part_first_le _ _ (hgw K).1) (hcoordC K hup)

theorem summand_args_lt (N : Nat)
    (hgood : ∀ x : multi.T, x.size < N → ∀ u, NFComp u x → Gd u x)
    (u : Nat) (TS : T) (hTS : T.isNF1 TS) (hTSne : T.Z < TS) :
    ∀ b : multi.T, b.size ≤ N → NF b → (∀ z, z ∈ G u b → tr z < TS) →
      (∀ p c, IsSummand p c (tr b) → IsSummand p c TS) →
      SumAll (fun p c => u ≤ p → c < TS) (tr b) := by
  intro b
  induction b using (measure multi.T.size).wf.induction with
  | h b ih =>
    intro hsz hb hsupp hsumm
    cases b with
    | Z => rw [tr_Z]; exact trivial
    | P w b =>
      have hgw (j : Nat) : Gd j (multi.V.get0 w j) :=
        hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P w j b) hsz) j (hb.comp j)
      obtain ⟨K, X, he, htr⟩ := tr_P_eq w b
      have hhead := auxH_closed hgw
      rw [he] at hhead
      obtain ⟨hX, _, hgX, _⟩ := T.isNF1_P_inv K X T.Z hhead
      rw [htr] at hsumm ⊢
      refine ⟨fun hup => ?_, ih b (multi.T.size_lt_P_right w b)
        (Nat.le_trans (Nat.le_of_lt (multi.T.size_lt_P_right w b)) hsz) hb.inv.2.1
        (fun z hz => hsupp z (G_in_tail hz)) (fun p c hs => hsumm p c (Or.inr hs))⟩
      have hsum : IsSummand K X TS := hsumm K X (Or.inl ⟨rfl, rfl⟩)
      have hlow := part_snd_lt_wrap K X T.Z hX hgX
      have hcase : (part K X).1 = T.Z ∨
          ((part K X).1 = (part K (tr (multi.V.get0 w K))).1 ∧ multi.V.get0 w K ≠ multi.T.Z) := by
        rcases headS_high _ hgw w.length K X (by rw [← auxH_eq_length]; exact he) with h | h
        · exact Or.inl h
        · by_cases hz : multi.V.get0 w K = multi.T.Z
          · rw [hz, tr_Z] at h; exact Or.inl h
          · exact Or.inr ⟨h, hz⟩
      rcases hcase with h | ⟨h, hz⟩
      · exact summand_arg_lt K X T.Z TS hTS hX T.isNF1.z hsum hTSne (by rw [h]; rfl) hlow
      · exact summand_arg_lt _ X (tr (multi.V.get0 w K)) TS hTS hX (hgw K).1 hsum
          (hsupp _ (G_coord_mem hup hz)) h.symm hlow

/-! ### The main simultaneous induction -/

theorem good_all : ∀ s : multi.T,
    (NF s → T.isNF1 (tr s)) ∧ (∀ u, NFComp u s → Gd u s) := by
  intro s
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    have hgood : ∀ z : multi.T, z.size < s.size → ∀ u, NFComp u z → Gd u z :=
      fun z hz => (ih z hz).2
    have hNF : NF s → T.isNF1 (tr s) := by
      intro hs
      cases s with
      | Z => rw [tr_Z]; exact T.isNF1.z
      | P v a => exact NF_step v a hs (fun z hz => (ih z hz).1) hgood
    refine ⟨hNF, fun u hs => ⟨hNF hs.1, ?_⟩⟩
    have hsupp : ∀ z, z ∈ G u s → tr z < tr s := by
      intro z hz
      exact order_preserve_bounded s.size hgood z s (Nat.le_of_lt (G_size_lt u s z hz))
        (Nat.le_refl _) (NF_G hs.1 u z hz) hs.1 (hs.2 z hz)
    cases s with
    | Z => intro y hy; rw [tr_Z] at hy; cases hy
    | P v a =>
      have hne : T.Z < tr (multi.T.P v a) := Z_lt_tr (fun h => multi.T.noConfusion h)
      have h1 := summand_args_lt (multi.T.P v a).size hgood u _ (hNF hs.1) hne
        (multi.T.P v a) (Nat.le_refl _) hs.1 hsupp (fun _ _ h => h)
      have h2 := (deep_bound (multi.T.P v a).size hgood u _ hne (multi.T.P v a)
        (Nat.le_refl _) hs.1 hsupp).1
      apply G1_of_SumAll u (· < tr (multi.T.P v a))
      apply SumAll_mono _ _ _ _ (SumAll_and3 _ _ _ _ h1 h2 h2)
      intro p c ⟨h1, h2, _⟩ hup
      exact ⟨h1 hup, h2 hup⟩

theorem NF_good {s : multi.T} (hs : NF s) : T.isNF1 (tr s) := (good_all s).1 hs

theorem Gd_of_NFComp {u : Nat} {s : multi.T} (hs : NFComp u s) : Gd u s := (good_all s).2 u hs

theorem tr_mono {s t : multi.T} (hs : NF s) (ht : NF t) (hst : s < t) : tr s < tr t :=
  order_preserve_bounded (max s.size t.size) (fun _ _ _ hz => Gd_of_NFComp hz) s t
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) hs ht hst

theorem tr_reflect_lt {s t : multi.T} (hs : NF s) (ht : NF t) (h : tr s < tr t) : s < t := by
  rcases multi.T.lt_trichotomy s t with hst | heq | hts
  · exact hst
  · rw [← tr_norm s, ← tr_norm t, heq] at h; exact absurd h (lt_irrefl_thm _)
  · exact absurd (tr_mono ht hs hts) (lt_asymm_thm h)

theorem tr_reflect_le {s t : multi.T} (hs : NF s) (ht : NF t) (h : tr s ≤ tr t) : s ≤ t := by
  rcases h with h | h
  · exact Or.inl (tr_reflect_lt hs ht h)
  · rcases multi.T.lt_trichotomy s t with hst | heq | hts
    · exact Or.inl hst
    · exact Or.inr ((multi.compareT_eq_iff s t).2 heq)
    · have h2 := tr_mono ht hs hts
      rw [h] at h2; exact absurd h2 (lt_irrefl_thm _)

/-! ### The bound `Ω` -/

theorem tr_lt_bound {s : multi.T} (hs : NF s) (hb : s < otb) : tr s < T.P 1 T.Z T.Z := by
  cases s with
  | Z => rw [tr_Z]; exact T.Lt.Z_lt_P _ _ _
  | P v a =>
    have hz := coords_zero_of_lt_otb hb
    obtain ⟨p, X, he, htr⟩ := tr_P_eq v a
    have hp : p = 0 := by
      have h1 := headS_zeros (multi.V.get0 v) 1 (fun j hj => hz j hj) (v.length)
      rw [← auxH_eq v (1 + v.length) (by omega), he] at h1
      change T.P p X T.Z = T.P 0 (tr (multi.V.get0 v 0)) T.Z at h1
      injection h1
    rw [htr, hp]
    exact T.Lt.p_head _ _ _ _ _ _ Nat.one_pos

end old

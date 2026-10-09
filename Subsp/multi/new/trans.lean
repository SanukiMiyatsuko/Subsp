import Subsp.multi.Collapse
import Subsp.multi.new.source

/-! The translation of `new` into Buchholz notation.

`P[a₀] + r ↦ ψ_0(a₀) + r`, and when a coordinate above the lowest is nonzero,
`P[a₀, …, aₙ] + r ↦ ψ_1(Ω·(S - 1) + log a₀) + r` with `S = ∑_{j ≥ 1} Ω^{j-1}·log aⱼ`. -/

namespace new

open MT

/-- Remove a leading summand `ψ_0(0) = 1`. -/
def oneDel : T → T
  | T.P 0 T.Z s2 => s2
  | s => s

mutual
def tr : multi.T → T
  | .Z => .Z
  | .P v a => T.add (if sumN v = .Z then .P 0 (a0N v) .Z
      else .P 1 (T.add (card 1 (oneDel (sumN v))) (collapse (a0N v))) .Z) (tr a)

/-- `∑_{j ≥ 1} Ω^{j-1} · collapse(tr vⱼ)`, the highest coordinate first. -/
def sumN : multi.V multi.T → T
  | .emp => .Z
  | .snoc x xs => match xs with
    | .emp => .Z
    | .snoc _ _ => T.add (card (xs.length - 1) (collapse (tr x))) (sumN xs)

/-- The translation of the lowest coordinate. -/
def a0N : multi.V multi.T → T
  | .emp => .Z
  | .snoc x .emp => tr x
  | .snoc _ (.snoc y ys) => a0N (.snoc y ys)
end

/-- The principal part of the translation. -/
def prin (v : multi.V multi.T) : T :=
  if sumN v = .Z then .P 0 (a0N v) .Z
  else .P 1 (T.add (card 1 (oneDel (sumN v))) (collapse (a0N v))) .Z

theorem tr_Z : tr multi.T.Z = T.Z := by rw [tr]

theorem tr_P (v : multi.V multi.T) (a : multi.T) :
    tr (multi.T.P v a) = T.add (prin v) (tr a) := by
  rw [tr]; rfl

theorem prin_shape (v : multi.V multi.T) : ∃ p m, prin v = T.P p m T.Z ∧ p ≤ 1 := by
  unfold prin
  split
  · exact ⟨0, _, rfl, Nat.zero_le 1⟩
  · exact ⟨1, _, rfl, Nat.le_refl 1⟩

theorem tr_P_eq (v : multi.V multi.T) (a : multi.T) :
    ∃ p m, tr (multi.T.P v a) = T.P p m (tr a) ∧ prin v = T.P p m T.Z ∧ p ≤ 1 := by
  obtain ⟨p, m, h, hp⟩ := prin_shape v
  refine ⟨p, m, ?_, h, hp⟩
  rw [tr_P, h, T.P_add_eq]; rfl

theorem tr_ne_Z {s : multi.T} (h : s ≠ multi.T.Z) : tr s ≠ T.Z := by
  cases s with
  | Z => exact absurd rfl h
  | P v a =>
    obtain ⟨p, m, he, _, _⟩ := tr_P_eq v a
    rw [he]; intro h; cases h

theorem tr_index1 : ∀ s : multi.T, T.index_Prop1 1 (tr s)
  | .Z => by rw [tr_Z]; exact T.index_Prop1.z
  | .P v a => by
    obtain ⟨p, m, he, _, hp⟩ := tr_P_eq v a
    rw [he]; exact T.index_Prop1.p _ _ _ hp (tr_index1 a)

theorem hd_tr (s : multi.T) : T.head (tr s) = tr (multi.T.hd s) := by
  cases s with
  | Z => rw [tr_Z]; rfl
  | P v a =>
    obtain ⟨p, m, he, hpr, _⟩ := tr_P_eq v a
    show T.head (tr (multi.T.P v a)) = tr (multi.T.P v multi.T.Z)
    rw [he, tr_P, hpr, tr_Z, T.add_Z]; rfl

/-! ### Compatibility with normalization -/

theorem sumN_snocZ (xs : multi.V multi.T) : sumN (.snoc .Z xs) = sumN xs := by
  cases xs with
  | emp => rw [sumN, sumN]
  | snoc _ _ => rw [sumN]; simp only [tr_Z, collapse_Z, card_Z, add_Z_left]

theorem a0N_snocZ (xs : multi.V multi.T) : a0N (.snoc .Z xs) = a0N xs := by
  cases xs with
  | emp => rw [a0N, a0N, tr_Z]
  | snoc _ _ => rw [a0N]

theorem sumN_trim : ∀ v : multi.V multi.T, sumN (multi.V.trim v) = sumN v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z => simp only [multi.V.trim]; rw [sumN_trim ax, sumN_snocZ]
    | P _ _ => rfl

theorem a0N_trim : ∀ v : multi.V multi.T, a0N (multi.V.trim v) = a0N v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z => simp only [multi.V.trim]; rw [a0N_trim ax, a0N_snocZ]
    | P _ _ => rfl

mutual
theorem tr_norm : ∀ s : multi.T, tr (multi.T.norm s) = tr s
  | .Z => by rw [multi.T.norm]
  | .P v a => by
    rw [multi.T.norm_P, tr_P, tr_P, tr_norm a]
    unfold prin
    rw [multi.V.norm, sumN_trim, a0N_trim, sumN_mapNorm v, a0N_mapNorm v]

theorem sumN_mapNorm : ∀ v : multi.V multi.T, sumN (multi.V.mapNorm v) = sumN v
  | .emp => by rw [multi.V.mapNorm]
  | .snoc a .emp => by
    show sumN (multi.V.snoc (multi.T.norm a) multi.V.emp) = sumN (multi.V.snoc a multi.V.emp)
    rw [sumN, sumN]
  | .snoc a (.snoc b bx) => by
    show sumN (multi.V.snoc (multi.T.norm a) (multi.V.mapNorm (multi.V.snoc b bx))) = _
    have hm : multi.V.mapNorm (multi.V.snoc b bx) =
        multi.V.snoc (multi.T.norm b) (multi.V.mapNorm bx) := rfl
    rw [hm, sumN, sumN, ← hm, multi.V.length_mapNorm, tr_norm a, sumN_mapNorm (.snoc b bx)]

theorem a0N_mapNorm : ∀ v : multi.V multi.T, a0N (multi.V.mapNorm v) = a0N v
  | .emp => by rw [multi.V.mapNorm]
  | .snoc a .emp => by
    show a0N (multi.V.snoc (multi.T.norm a) multi.V.emp) = a0N (multi.V.snoc a multi.V.emp)
    rw [a0N, a0N, tr_norm a]
  | .snoc a (.snoc b bx) => by
    show a0N (multi.V.snoc (multi.T.norm a) (multi.V.mapNorm (multi.V.snoc b bx))) = _
    have hm : multi.V.mapNorm (multi.V.snoc b bx) =
        multi.V.snoc (multi.T.norm b) (multi.V.mapNorm bx) := rfl
    rw [hm, a0N, a0N, ← hm, a0N_mapNorm (.snoc b bx)]
end

theorem tr_congr {a b : multi.T} (h : multi.compareT a b = .eq) : tr a = tr b := by
  rw [← tr_norm a, ← tr_norm b, (multi.compareT_eq_iff a b).1 h]

theorem prin_congr {v w : multi.V multi.T} (h : multi.compareV v w = .eq) : prin v = prin w := by
  have h1 := tr_congr ((multi.T.P_eqv_iff v w multi.T.Z multi.T.Z).2 ⟨h, multi.compareT_ZZ⟩)
  rw [tr_P, tr_P, tr_Z, T.add_Z, T.add_Z] at h1
  exact h1

/-! ### Coordinatewise description -/

/-- The blocks `Ω^{j-1} · collapse(tr (f j))` for `1 ≤ j < k`. -/
def sUp (f : Nat → multi.T) : Nat → T
  | 0 => T.Z
  | 1 => T.Z
  | k + 2 => T.add (card k (collapse (tr (f (k + 1))))) (sUp f (k + 1))

theorem a0N_eq : ∀ v : multi.V multi.T, a0N v = tr (multi.V.get0 v 0)
  | .emp => by rw [a0N, show multi.V.get0 multi.V.emp 0 = multi.T.Z from rfl, tr_Z]
  | .snoc x .emp => by rw [a0N]; rfl
  | .snoc x (.snoc y ys) => by
    rw [a0N, a0N_eq (.snoc y ys), multi.V.get0_snoc_low x (multi.V.snoc y ys) 0 (Nat.zero_lt_succ _)]

theorem sUp_congr {f g : Nat → multi.T} :
    ∀ k, (∀ j, 1 ≤ j → j < k → multi.compareT (f j) (g j) = .eq) → sUp f k = sUp g k
  | 0, _ => rfl
  | 1, _ => rfl
  | k + 2, h => by
    simp only [sUp]
    rw [tr_congr (h (k + 1) (by omega) (by omega)),
      sUp_congr (k + 1) (fun j hj1 hj => h j hj1 (by omega))]

theorem sUp_zeros (f : Nat → multi.T) (k : Nat) (hk : 1 ≤ k) :
    ∀ m, (∀ j, k ≤ j → f j = multi.T.Z) → sUp f (k + m) = sUp f k
  | 0, _ => rfl
  | m + 1, h => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show k' + 1 + (m + 1) = (k' + m) + 2 from by omega, sUp,
      show k' + m + 1 = k' + 1 + m from by omega, h (k' + 1 + m) (by omega), tr_Z, collapse_Z,
      card_Z, add_Z_left, sUp_zeros f (k' + 1) hk m h]

theorem sumN_eq_length : ∀ v : multi.V multi.T, sumN v = sUp (multi.V.get0 v) v.length
  | .emp => rfl
  | .snoc x .emp => by rw [sumN]; rfl
  | .snoc x (.snoc y ys) => by
    rw [sumN, sumN_eq_length (.snoc y ys)]
    show T.add (card ((multi.V.snoc y ys).length - 1) (collapse (tr x)))
      (sUp (multi.V.get0 (multi.V.snoc y ys)) (multi.V.snoc y ys).length) =
      sUp (multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys))) (ys.length + 1 + 1)
    simp only [multi.V.length, sUp]
    rw [show ys.length + 1 - 1 = ys.length from by omega]
    congr 1
    · rw [show multi.V.get0 (multi.V.snoc x (multi.V.snoc y ys)) (ys.length + 1) = x from
        multi.V.get0_snoc_top x _]
    · apply sUp_congr
      intro j _ hj
      rw [multi.V.get0_snoc_low x (multi.V.snoc y ys) j hj]
      exact multi.T.eqv_refl _

theorem sUp_allZ (f : Nat → multi.T) (hf : ∀ j, f j = multi.T.Z) : ∀ k, sUp f k = T.Z
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by rw [sUp, hf, tr_Z, collapse_Z, card_Z, add_Z_left, sUp_allZ f hf (k + 1)]

theorem sumN_eq (v : multi.V multi.T) (N : Nat) (hN : v.length ≤ N) :
    sumN v = sUp (multi.V.get0 v) N := by
  rw [sumN_eq_length]
  by_cases h1 : 1 ≤ v.length
  · obtain ⟨m, rfl⟩ : ∃ m, N = v.length + m := ⟨N - v.length, by omega⟩
    rw [sUp_zeros _ _ h1 m (fun j hj => multi.V.get0_ge v j hj)]
  · have hz : ∀ j, multi.V.get0 v j = multi.T.Z := fun j => multi.V.get0_ge v j (by omega)
    rw [sUp_allZ _ hz, sUp_allZ _ hz]

/-! ### Block algebra -/

theorem card_add_gen (n : Nat) : ∀ a b : T, card n (T.add a b) = T.add (card n a) (card n b) := by
  intro a b
  induction a with
  | Z => rw [card_Z]; rfl
  | P p x y _ ih =>
    cases n with
    | zero => rw [card_zero, card_zero, card_zero]
    | succ k =>
      rw [T.P_add_eq]
      show (_ + card (k + 1) (T.add y b)) = T.add (_ + card (k + 1) y) (card (k + 1) b)
      rw [ih, hadd_eq, hadd_eq, add_assoc]

theorem card_one_P1 (a b : T) : card 1 (T.P 1 a b) = T.P 1 (shift 1 a) (card 1 b) := by
  show (if (1 : Nat) = 0 then _ else T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) a) T.Z) +
    card 1 b = _
  rw [ite_eq_right (by omega), hadd_eq, T.P_add_eq]
  rfl

theorem shift_one_shift (m : Nat) (x : T) : shift 1 (shift m x) = shift (m + 1) x := by
  rw [shift_succ, shift_succ, shift_zero]

theorem card_one_comp (m : Nat) : ∀ {c : T}, T.index_Prop1 0 c → card 1 (card m c) = card (m + 1) c
  | _, .z => by simp only [card_Z]
  | _, .p p a b hp hb => by
    have hp0 : p = 0 := by omega
    subst p
    cases m with
    | zero => rw [card_zero]
    | succ m =>
      rw [card_P0, card_one_P1, card_one_comp (m + 1) hb, card_P0, shift_one_shift]

/-- Good coordinates: normal translations lying above their own support. -/
def Gd (x : multi.T) : Prop := T.isNF1 (tr x) ∧ ∀ y, y ∈ T.G1 0 (tr x) → y < tr x

theorem Gd.collapse {x : multi.T} (h : Gd x) :
    T.isNF1 (collapse (tr x)) ∧ T.index_Prop1 0 (collapse (tr x)) :=
  collapse_closed h.1 h.2

theorem collapse_tr_ne_Z {x : multi.T} (hx : x ≠ multi.T.Z) : collapse (tr x) ≠ T.Z :=
  collapse_ne_Z (tr_ne_Z hx)

theorem collapse_tr_eq_Z {x : multi.T} (h : collapse (tr x) = T.Z) : x = multi.T.Z := by
  by_cases hx : x = multi.T.Z
  · exact hx
  · exact absurd h (collapse_tr_ne_Z hx)

theorem sUp_lt_card (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) :
    ∀ k {z : T}, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z → sUp f (k + 1) < card k z
  | 0, z, _, _, hz => by rw [card_zero]; exact Z_lt_of_ne hz
  | k + 1, z, hzNF, hzIdx, hz => by
    show T.add (card k (collapse (tr (f (k + 1))))) (sUp f (k + 1)) < card (k + 1) z
    by_cases hc : collapse (tr (f (k + 1))) = T.Z
    · rw [hc, card_Z, add_Z_left]
      have h := card_level_lt T.Z (Nat.lt_succ_self k) hzNF hzIdx hz hzNF hzIdx hz
      rw [T.add_Z] at h
      exact lt_trans_thm _ _ _ (sUp_lt_card f hf k hzNF hzIdx hz) h
    · exact card_level_lt _ (Nat.lt_succ_self k) (hf (k + 1)).collapse.1
        (hf (k + 1)).collapse.2 hc hzNF hzIdx hz

theorem sUp_closed (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) :
    ∀ k, T.isNF1 (sUp f k) ∧ T.index_Prop1 1 (sUp f k) ∧
      (∀ x, x ∈ T.G1 1 (sUp f k) → x < sUp f k)
  | 0 => ⟨T.isNF1.z, T.index_Prop1.z, by intro x hx; cases hx⟩
  | 1 => ⟨T.isNF1.z, T.index_Prop1.z, by intro x hx; cases hx⟩
  | k + 2 => by
    rw [show sUp f (k + 2) = T.add (card k (collapse (tr (f (k + 1))))) (sUp f (k + 1)) from rfl]
    cases k with
    | zero =>
      rw [show sUp f 1 = T.Z from rfl, T.add_Z, card_zero]
      have hc := (hf 1).collapse
      exact ⟨hc.1, Rank1Termination.index_mono (Nat.zero_le 1) _ hc.2,
        by rw [index_Prop1_G1_empty 0 _ hc.2 1 (by omega)]; intro x hx; cases hx⟩
    | succ k =>
      have ih := sUp_closed f hf (k + 2)
      exact card_append_closed k _ (hf (k + 2)).collapse.1 (hf (k + 2)).collapse.2 ih.1 ih.2.1
        ih.2.2 (fun z hzNF hzIdx hz => sUp_lt_card f hf (k + 1) hzNF hzIdx hz)

theorem sUp_ne_Z {f : Nat → multi.T} {k j : Nat} (hj1 : 1 ≤ j) (hjk : j < k)
    (hfj : f j ≠ multi.T.Z) : sUp f k ≠ T.Z := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => omega
    | succ k =>
      show T.add (card k (collapse (tr (f (k + 1))))) (sUp f (k + 1)) ≠ T.Z
      by_cases hjk' : j = k + 1
      · subst hjk'
        cases hcz : card k (collapse (tr (f (k + 1)))) with
        | Z => exact absurd hcz (card_ne_Z k (collapse_tr_ne_Z hfj))
        | P _ _ _ => rw [T.P_add_eq]; intro h; cases h
      · intro h
        have h2 : sUp f (k + 1) = T.Z := by
          cases hcz : card k (collapse (tr (f (k + 1)))) with
          | Z => rw [hcz, add_Z_left] at h; exact h
          | P _ _ _ => rw [hcz, T.P_add_eq] at h; cases h
        exact ih (by omega) h2

theorem sUp_eq_Z_of {f : Nat → multi.T} (hf : ∀ j, 1 ≤ j → f j = multi.T.Z) :
    ∀ k, sUp f k = T.Z
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
    rw [sUp, hf (k + 1) (by omega), tr_Z, collapse_Z, card_Z, add_Z_left, sUp_eq_Z_of hf (k + 1)]

/-- The blocks strictly between coordinate `i` and coordinate `i + 1 + m`. -/
def aboveS (f : Nat → multi.T) (i : Nat) : Nat → T
  | 0 => T.Z
  | m + 1 => T.add (card (i + m) (collapse (tr (f (i + 1 + m))))) (aboveS f i m)

theorem sUp_split (f : Nat → multi.T) (i : Nat) :
    ∀ m, sUp f (i + 2 + m) = T.add (aboveS f (i + 1) m) (sUp f (i + 2))
  | 0 => rfl
  | m + 1 => by
    rw [show i + 2 + (m + 1) = (i + 1 + m) + 2 from by omega, sUp,
      show i + 1 + m + 1 = i + 2 + m from by omega, sUp_split f i m, aboveS, add_assoc]

theorem aboveS_congr {f g : Nat → multi.T} (i : Nat) :
    ∀ m, (∀ j, i < j → multi.compareT (f j) (g j) = .eq) → aboveS f i m = aboveS g i m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [aboveS]
    rw [tr_congr (h (i + 1 + m) (by omega)), aboveS_congr i m h]

/-- Lexicographic comparison of the coordinate sums. -/
theorem sUp_lex {f g : Nat → multi.T} (hf : ∀ j, Gd (f j)) (hg : ∀ j, Gd (g j))
    (hmono : ∀ j, f j < g j → tr (f j) < tr (g j)) {i : Nat}
    (heq : ∀ j, i < j → multi.compareT (f j) (g j) = .eq) (hlt : f i < g i) :
    ∀ N, i < N → sUp f N < sUp g N ∨ (sUp f N = sUp g N ∧ tr (f 0) < tr (g 0)) := by
  intro N hN
  cases i with
  | zero =>
    right
    exact ⟨sUp_congr N (fun j hj1 _ => heq j hj1), hmono 0 hlt⟩
  | succ i =>
    left
    obtain ⟨m, rfl⟩ : ∃ m, N = i + 2 + m := ⟨N - (i + 2), by omega⟩
    rw [sUp_split, sUp_split, aboveS_congr (i + 1) m heq]
    apply add_left_lt
    show T.add (card i (collapse (tr (f (i + 1))))) (sUp f (i + 1)) <
      T.add (card i (collapse (tr (g (i + 1))))) (sUp g (i + 1))
    exact card_append_lt i _ _ (hf (i + 1)).collapse.1 (hf (i + 1)).collapse.2
      (hg (i + 1)).collapse.1 (hg (i + 1)).collapse.2
      (collapse_lt (hf (i + 1)).1 (hf (i + 1)).2 (hg (i + 1)).1 (hmono (i + 1) hlt))
      (fun q hqNF hqIdx hq => sUp_lt_card f hf i hqNF hqIdx hq)

/-! ### Multiplication by `Ω` on index-one terms -/

theorem idx0_lt_P1 {x : T} (m y : T) (hx : T.index_Prop1 0 x) : x < T.P 1 m y := by
  cases hx with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)

theorem card1_append_lt :
    ∀ {s t : T} (x y : T), T.isNF1 s → T.index_Prop1 1 s → T.isNF1 t → T.index_Prop1 1 t →
      s < t → T.index_Prop1 0 x → T.add (card 1 s) x < T.add (card 1 t) y := by
  intro s t x y hsNF hsIdx htNF htIdx hst hx
  induction hst with
  | Z_lt_P q e f =>
    cases htIdx with
    | p _ _ _ hq _ =>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
      · rw [card_Z, add_Z_left, card_P0_add]; exact idx0_lt_P1 _ _ hx
      · rw [card_Z, add_Z_left, card_one_P1, T.P_add_eq]; exact idx0_lt_P1 _ _ hx
  | p_head p q a e b f hpq =>
    cases hsIdx with
    | p _ _ _ hp _ =>
      cases htIdx with
      | p _ _ _ hq _ =>
        have hp0 : p = 0 := by omega
        have hq1 : q = 1 := by omega
        subst p; subst q
        have ha := T.isNF1_P_inv _ _ _ hsNF
        rw [card_P0_add, card_one_P1, T.P_add_eq]
        apply T.Lt.p_mid
        rw [shift_zero, shift_succ, shift_zero]
        exact idx0_lt_P1 _ _ (collapse_closed ha.1 ha.2.2.1).2
  | p_mid p a e b f h _ =>
    cases hsIdx with
    | p _ _ _ hp _ =>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
      · rw [card_P0_add, card_P0_add]
        apply T.Lt.p_mid
        rw [shift_zero, shift_zero]
        exact collapse_lt (T.isNF1_P_inv _ _ _ hsNF).1 (T.isNF1_P_inv _ _ _ hsNF).2.2.1
          (T.isNF1_P_inv _ _ _ htNF).1 h
      · rw [card_one_P1, card_one_P1, T.P_add_eq, T.P_add_eq]
        exact T.Lt.p_mid _ _ _ _ _ (shift_lt_right 1 h)
  | p_tail p a b f h ih =>
    cases hsIdx with
    | p _ _ _ hp hb =>
      cases htIdx with
      | p _ _ _ _ hf =>
        have hr := ih (T.isNF1_P_inv _ _ _ hsNF).2.1 hb (T.isNF1_P_inv _ _ _ htNF).2.1 hf
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
        · rw [card_P0_add, card_P0_add]; exact T.Lt.p_tail _ _ _ _ hr
        · rw [card_one_P1, card_one_P1, T.P_add_eq, T.P_add_eq]; exact T.Lt.p_tail _ _ _ _ hr

/-! ### Removing a leading `1` -/

theorem oneDel_P0 (a b : T) : oneDel (T.P 0 a b) = if a = T.Z then b else T.P 0 a b := by
  cases a <;> rfl

theorem oneDel_P_succ (p : Nat) (a b : T) : oneDel (T.P (p + 1) a b) = T.P (p + 1) a b := rfl

theorem oneDel_Z : oneDel T.Z = T.Z := rfl

theorem oneDel_NF_index0 {s : T} (hs : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    T.isNF1 (oneDel s) ∧ T.index_Prop1 0 (oneDel s) := by
  cases hi with
  | z => exact ⟨hs, T.index_Prop1.z⟩
  | p p a b hp hb =>
    have hp0 : p = 0 := by omega
    subst p
    rw [oneDel_P0]
    split
    · exact ⟨(T.isNF1_P_inv _ _ _ hs).2.1, hb⟩
    · exact ⟨hs, T.index_Prop1.p _ _ _ (Nat.le_refl 0) hb⟩

theorem G1_oneDel_sub (s : T) : ∀ x, x ∈ T.G1 0 (oneDel s) → x ∈ T.G1 0 s := by
  intro x hx
  cases s with
  | Z => exact hx
  | P p a b =>
    cases p with
    | zero =>
      rw [oneDel_P0] at hx
      split at hx
      · exact (G1_P_mem (Nat.le_refl 0)).2 (Or.inr (Or.inr hx))
      · exact hx
    | succ p => exact hx

theorem oneDel_lt_index0 {a b : T} (haNF : T.isNF1 a) (haIdx : T.index_Prop1 0 a)
    (haNe : a ≠ T.Z) (hbIdx : T.index_Prop1 0 b) (hbNe : b ≠ T.Z) (hab : a < b) :
    oneDel a < oneDel b := by
  cases haIdx with
  | z => exact absurd rfl haNe
  | p p a1 a2 hp _ =>
    cases hbIdx with
    | z => exact absurd rfl hbNe
    | p q c d hq _ =>
      have hp0 : p = 0 := by omega
      have hq0 : q = 0 := by omega
      subst p; subst q
      rw [oneDel_P0, oneDel_P0]
      cases hab with
      | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
      | p_mid _ _ _ _ _ h =>
        have hc : c ≠ T.Z := by intro he; rw [he] at h; exact lt_Z_inv h
        rw [ite_eq_right hc]
        split
        · exact lt_of_le_of_lt_thm T _ _ _ (T.isNF1_tail_le _ haNF _ _ _ rfl)
            (T.Lt.p_mid _ _ _ _ _ h)
        · exact T.Lt.p_mid _ _ _ _ _ h
      | p_tail _ _ _ _ h =>
        by_cases ha : a1 = T.Z
        · rw [ite_eq_left ha, ite_eq_left ha]; exact h
        · rw [ite_eq_right ha, ite_eq_right ha]; exact T.Lt.p_tail _ _ _ _ h

theorem P1ZZ_le (c d : T) : T.P 1 T.Z T.Z ≤ T.P 1 c d :=
  partial_order.trans _ _ _ (lift_le 1 (T.Z_le c)) (head_le_self (T.P 1 c d))

theorem oneDel_lt_index1 {s t : T} (hsNF : T.isNF1 s) (hsIdx : T.index_Prop1 1 s) (hsNe : s ≠ T.Z)
    (htNF : T.isNF1 t) (htIdx : T.index_Prop1 1 t) (htNe : t ≠ T.Z) (hst : s < t) :
    oneDel s < oneDel t := by
  cases hsIdx with
  | z => exact absurd rfl hsNe
  | p p a b hp _ =>
    cases htIdx with
    | z => exact absurd rfl htNe
    | p q c d hq _ =>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl <;>
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with rfl | rfl
      · exact oneDel_lt_index0 hsNF (isNF1_index 0 0 a b hsNF (Nat.le_refl 0))
          (fun h => T.noConfusion h) (isNF1_index 0 0 c d htNF (Nat.le_refl 0))
          (fun h => T.noConfusion h) hst
      · have hi := (oneDel_NF_index0 hsNF (isNF1_index 0 0 a b hsNF (Nat.le_refl 0))).2
        rw [oneDel_P_succ]
        exact lt_of_lt_of_le_thm T _ _ _ (index_Prop1_lt_succ 0 _ hi) (P1ZZ_le c d)
      · cases hst with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
      · rw [oneDel_P_succ, oneDel_P_succ]; exact hst

theorem oneDel_NF_index1 {s : T} (hs : T.isNF1 s) (hi : T.index_Prop1 1 s) :
    T.isNF1 (oneDel s) ∧ T.index_Prop1 1 (oneDel s) := by
  cases hi with
  | z => exact ⟨hs, T.index_Prop1.z⟩
  | p p a b hp hb =>
    cases p with
    | zero =>
      rw [oneDel_P0]
      split
      · exact ⟨(T.isNF1_P_inv _ _ _ hs).2.1, hb⟩
      · exact ⟨hs, T.index_Prop1.p _ _ _ hp hb⟩
    | succ p => exact ⟨hs, T.index_Prop1.p _ _ _ hp hb⟩

/-! ### Multiplying the coordinate sums by `Ω` -/

theorem card1_sUp (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) (k : Nat) :
    card 1 (sUp f (k + 2)) = T.add (card (k + 1) (collapse (tr (f (k + 1))))) (card 1 (sUp f (k + 1))) := by
  rw [show sUp f (k + 2) = T.add (card k (collapse (tr (f (k + 1))))) (sUp f (k + 1)) from rfl,
    card_add_gen, card_one_comp k (hf (k + 1)).collapse.2]

/-- `Ω · S + L` for an index-zero `L`. -/
theorem card1_sUp_closed (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) {L : T} (hL : T.isNF1 L)
    (hLi : T.index_Prop1 0 L) :
    ∀ k, (T.isNF1 (T.add (card 1 (sUp f (k + 1))) L) ∧
      T.index_Prop1 1 (T.add (card 1 (sUp f (k + 1))) L) ∧
      (∀ x, x ∈ T.G1 1 (T.add (card 1 (sUp f (k + 1))) L) →
        x < T.add (card 1 (sUp f (k + 1))) L)) ∧
      ∀ {z : T}, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
        T.add (card 1 (sUp f (k + 1))) L < card (k + 1) z
  | 0 => by
    rw [show sUp f 1 = T.Z from rfl, card_Z, add_Z_left]
    refine ⟨⟨hL, Rank1Termination.index_mono (Nat.zero_le 1) _ hLi, ?_⟩, ?_⟩
    · rw [index_Prop1_G1_empty 0 _ hLi 1 (by omega)]; intro x hx; cases hx
    · intro z hzNF hzIdx hz
      cases hzIdx with
      | z => exact absurd rfl hz
      | p p a b hp _ =>
        have hp0 : p = 0 := by omega
        subst p
        rw [card_P0]
        exact idx0_lt_P1 _ _ hLi
  | k + 1 => by
    have ih := card1_sUp_closed f hf hL hLi k
    rw [card1_sUp f hf k, add_assoc]
    refine ⟨card_append_closed k _ (hf (k + 1)).collapse.1 (hf (k + 1)).collapse.2 ih.1.1
      ih.1.2.1 ih.1.2.2 (fun z hzNF hzIdx hz => ih.2 hzNF hzIdx hz), ?_⟩
    intro z hzNF hzIdx hz
    by_cases hc : collapse (tr (f (k + 1))) = T.Z
    · rw [hc, card_Z, add_Z_left]
      have h := card_level_lt T.Z (Nat.lt_succ_self (k + 1)) hzNF hzIdx hz hzNF hzIdx hz
      rw [T.add_Z] at h
      exact lt_trans_thm _ _ _ (ih.2 hzNF hzIdx hz) h
    · exact card_level_lt _ (Nat.lt_succ_self (k + 1)) (hf (k + 1)).collapse.1
        (hf (k + 1)).collapse.2 hc hzNF hzIdx hz

/-- Support of a block `Ω^{k+1} · c`. -/
theorem card_supp (k : Nat) : ∀ {c : T} (s : T), T.isNF1 c → T.index_Prop1 0 c →
    (∀ x, x ∈ T.G1 0 c → x ≤ s) →
    ∀ x, x ∈ T.G1 0 (card (k + 1) c) → x ∈ T.G1 1 (card (k + 1) c) ∨ x = T.Z ∨ x ≤ s := by
  intro c s hc hi hs
  induction hi with
  | z => intro x hx; rw [card_Z] at hx; cases hx
  | p p a b hp _ ih =>
    have hp0 : p = 0 := by omega
    subst p
    obtain ⟨haNF, hbNF, haG, _⟩ := T.isNF1_P_inv _ _ _ hc
    intro x hx
    rw [card_P0] at hx ⊢
    rcases (G1_P_mem (Nat.zero_le 1)).1 hx with rfl | hx | hx
    · exact Or.inl ((G1_P_mem (Nat.le_refl 1)).2 (Or.inl rfl))
    · rcases shift_G1_zero k _ x hx with rfl | hx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (partial_order.trans _ _ _ (collapse_G1_le haNF haG x hx)
          (hs a ((G1_P_mem (Nat.le_refl 0)).2 (Or.inl rfl)))))
    · rcases ih hbNF (fun y hy => hs y ((G1_P_mem (Nat.le_refl 0)).2 (Or.inr (Or.inr hy))))
          x hx with h | h | h
      · exact Or.inl ((G1_P_mem (Nat.le_refl 1)).2 (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

theorem card1_sUp_supp (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) : ∀ k,
    ∀ y, y ∈ T.G1 0 (card 1 (sUp f k)) → y ∈ T.G1 1 (card 1 (sUp f k)) ∨ y = T.Z ∨
      ∃ j, f j ≠ multi.T.Z ∧ y ≤ tr (f j)
  | 0 => by intro y hy; rw [show sUp f 0 = T.Z from rfl, card_Z] at hy; cases hy
  | 1 => by intro y hy; rw [show sUp f 1 = T.Z from rfl, card_Z] at hy; cases hy
  | k + 2 => by
    intro y hy
    rw [card1_sUp f hf k, G1_add] at hy ⊢
    rcases List.mem_append.1 hy with hy | hy
    · by_cases hfz : f (k + 1) = multi.T.Z
      · rw [hfz, tr_Z, collapse_Z, card_Z] at hy; cases hy
      · rcases card_supp k (tr (f (k + 1))) (hf (k + 1)).collapse.1 (hf (k + 1)).collapse.2
            (collapse_G1_le (hf (k + 1)).1 (hf (k + 1)).2) y hy with h | h | h
        · exact Or.inl (List.mem_append_left _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨k + 1, hfz, h⟩)
    · rcases card1_sUp_supp f hf (k + 1) y hy with h | h | h
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-! ### The coordinate sum starting at index zero -/

theorem sUp_index0_high (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) :
    ∀ k, T.index_Prop1 0 (sUp f k) → ∀ j, 2 ≤ j → j < k → f j = multi.T.Z
  | 0, _, j, _, hj => absurd hj (Nat.not_lt_zero _)
  | 1, _, j, h2, hj => absurd hj (by omega)
  | k + 2, hi, j, h2, hj => by
    rw [show sUp f (k + 2) = T.add (card k (collapse (tr (f (k + 1))))) (sUp f (k + 1)) from rfl]
      at hi
    have htop : f (k + 1) = multi.T.Z ∨ k = 0 := by
      cases k with
      | zero => exact Or.inr rfl
      | succ k =>
        left
        by_cases hfz : f (k + 2) = multi.T.Z
        · exact hfz
        · exfalso
          have hc := (hf (k + 2)).collapse
          have hne := collapse_tr_ne_Z hfz
          generalize collapse (tr (f (k + 2))) = c at hc hne hi
          cases hc.2 with
          | z => exact hne rfl
          | p p a b hp _ =>
            have hp0 : p = 0 := by omega
            subst hp0
            rw [card_P0_add] at hi
            cases hi with
            | p _ _ _ h _ => omega
    rcases htop with htop | htop
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | hj'
      · rw [htop, tr_Z, collapse_Z, card_Z, add_Z_left] at hi
        exact sUp_index0_high f hf (k + 1) hi j h2 hj'
      · rw [hj']; exact htop
    · subst htop; omega

theorem sUp_eq_low (f : Nat → multi.T) (hf : ∀ j, 2 ≤ j → f j = multi.T.Z) :
    ∀ k, 2 ≤ k → sUp f k = collapse (tr (f 1))
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by
    rw [show sUp f 2 = T.add (card 0 (collapse (tr (f 1)))) (sUp f 1) from rfl,
      show sUp f 1 = T.Z from rfl, T.add_Z, card_zero]
  | k + 3, _ => by
    rw [show sUp f (k + 3) = T.add (card (k + 1) (collapse (tr (f (k + 2))))) (sUp f (k + 2))
      from rfl, hf (k + 2) (by omega), tr_Z, collapse_Z, card_Z, add_Z_left,
      sUp_eq_low f hf (k + 2) (by omega)]

/-! ### The principal part -/

/-- The middle term `Ω·(S - 1) + log a₀` of a principal translation with `S ≠ 0`. -/
def mid (S A : T) : T := T.add (card 1 (oneDel S)) (collapse A)

theorem mid_closed (f : Nat → multi.T) (hf : ∀ j, Gd (f j)) (N : Nat) (hN : 2 ≤ N)
    (hS : sUp f N ≠ T.Z) :
    T.isNF1 (mid (sUp f N) (tr (f 0))) ∧ T.index_Prop1 1 (mid (sUp f N) (tr (f 0))) ∧
      (∀ x, x ∈ T.G1 1 (mid (sUp f N) (tr (f 0))) → x < mid (sUp f N) (tr (f 0))) := by
  have hL := (hf 0).collapse
  have hSc := sUp_closed f hf N
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  unfold mid
  rcases hSs : sUp f (N' + 1) with _ | ⟨p, a, b⟩
  · exact absurd hSs hS
  · rw [hSs] at hSc
    have hp : p ≤ 1 := by cases hSc.2.1 with | p _ _ _ hp _ => exact hp
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
    · have hS0 := isNF1_index 0 0 a b hSc.1 (Nat.le_refl 0)
      have hd := oneDel_NF_index0 hSc.1 hS0
      exact card_append_closed 0 (collapse (tr (f 0))) hd.1 hd.2 hL.1
        (Rank1Termination.index_mono (Nat.zero_le 1) _ hL.2)
        (by rw [index_Prop1_G1_empty 0 _ hL.2 1 (by omega)]; intro x hx; cases hx)
        (fun z _ hzIdx hz => by
          cases hzIdx with
          | z => exact absurd rfl hz
          | p q c d hq _ =>
            have hq0 : q = 0 := by omega
            subst q
            rw [card_P0]; exact idx0_lt_P1 _ _ hL.2)
    · rw [oneDel_P_succ, ← hSs]
      exact (card1_sUp_closed f hf hL.1 hL.2 N').1

theorem prin_eq (v : multi.V multi.T) (N : Nat) (hN : v.length ≤ N) :
    prin v = if sUp (multi.V.get0 v) N = T.Z then T.P 0 (tr (multi.V.get0 v 0)) T.Z
      else T.P 1 (mid (sUp (multi.V.get0 v) N) (tr (multi.V.get0 v 0))) T.Z := by
  unfold prin mid
  rw [sumN_eq v N hN, a0N_eq]

theorem prin_NF {v : multi.V multi.T} (hv : ∀ j, Gd (multi.V.get0 v j)) : T.isNF1 (prin v) := by
  rw [prin_eq v (v.length + 2) (by omega)]
  split
  · exact T.isNF1.p _ _ _ (hv 0).1 T.isNF1.z (hv 0).2 (T.Z_le _)
  · rename_i hS
    have hm := mid_closed _ hv (v.length + 2) (by omega) hS
    exact T.isNF1.p _ _ _ hm.1 T.isNF1.z hm.2.2 (T.Z_le _)

/-- The principal translation is strictly monotone in the vector. -/
theorem prin_lt {v w : multi.V multi.T} (hv : ∀ j, Gd (multi.V.get0 v j))
    (hw : ∀ j, Gd (multi.V.get0 w j))
    (hmono : ∀ j, multi.V.get0 v j < multi.V.get0 w j →
      tr (multi.V.get0 v j) < tr (multi.V.get0 w j))
    (hvw : v < w) : prin v < prin w := by
  obtain ⟨i, heq, hlt⟩ := (multi.V.lt_iff_pivot v w).1 hvw
  have hiw : i < w.length := by
    apply Nat.lt_of_not_le
    intro h
    rw [multi.V.get0_ge w i h] at hlt
    exact multi.T.not_lt_Z _ hlt
  let N := v.length + w.length + 2
  have hlex := sUp_lex hv hw hmono heq hlt N (by omega)
  rw [prin_eq v N (by omega), prin_eq w N (by omega)]
  by_cases hSv : sUp (multi.V.get0 v) N = T.Z <;> by_cases hSw : sUp (multi.V.get0 w) N = T.Z
  · rw [ite_eq_left hSv, ite_eq_left hSw]
    rcases hlex with h | ⟨_, h⟩
    · rw [hSv, hSw] at h; exact absurd h (lt_irrefl_thm _)
    · exact T.Lt.p_mid _ _ _ _ _ h
  · rw [ite_eq_left hSv, ite_eq_right hSw]
    exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  · exfalso
    rcases hlex with h | ⟨h, _⟩
    · rw [hSw] at h; exact lt_Z_inv h
    · exact hSv (h.trans hSw)
  · rw [ite_eq_right hSv, ite_eq_right hSw]
    apply T.Lt.p_mid
    have hcv := sUp_closed _ hv N
    have hcw := sUp_closed _ hw N
    rcases hlex with h | ⟨h, ha⟩
    · have hdv := oneDel_NF_index1 hcv.1 hcv.2.1
      have hdw := oneDel_NF_index1 hcw.1 hcw.2.1
      exact card1_append_lt _ _ hdv.1 hdv.2 hdw.1 hdw.2
        (oneDel_lt_index1 hcv.1 hcv.2.1 hSv hcw.1 hcw.2.1 hSw h) (hv 0).collapse.2
    · unfold mid
      rw [h]
      exact add_left_lt _ (collapse_lt (hv 0).1 (hv 0).2 (hw 0).1 ha)

theorem prin_le {v w : multi.V multi.T} (hv : ∀ j, Gd (multi.V.get0 v j))
    (hw : ∀ j, Gd (multi.V.get0 w j))
    (hmono : ∀ j, multi.V.get0 v j < multi.V.get0 w j →
      tr (multi.V.get0 v j) < tr (multi.V.get0 w j))
    (hvw : v ≤ w) : prin v ≤ prin w := by
  rcases hvw with h | h
  · exact Or.inl (prin_lt hv hw hmono h)
  · exact Or.inr (prin_congr h)

/-- Support of the principal translation. -/
theorem prin_supp {v : multi.V multi.T} (hv : ∀ j, Gd (multi.V.get0 v j)) :
    ∀ y, y ∈ T.G1 0 (prin v) → y < prin v ∨
      ∃ j, multi.V.get0 v j ≠ multi.T.Z ∧ y ≤ tr (multi.V.get0 v j) := by
  let N := v.length + 2
  have hzero : ∀ y, y ≤ tr (multi.V.get0 v 0) → y < prin v ∨
      ∃ j, multi.V.get0 v j ≠ multi.T.Z ∧ y ≤ tr (multi.V.get0 v j) := by
    intro y hy
    by_cases h0 : multi.V.get0 v 0 = multi.T.Z
    · left
      rw [h0, tr_Z] at hy
      have hyz : y = T.Z := by
        rcases hy with h | h
        · exact absurd h lt_Z_inv
        · exact h
      rw [hyz]
      obtain ⟨p, m, hpm, _⟩ := prin_shape v
      rw [hpm]; exact T.Lt.Z_lt_P _ _ _
    · exact Or.inr ⟨0, h0, hy⟩
  intro y hy
  have hprin := prin_eq v N (by omega)
  rw [hprin] at hy ⊢
  split at hy
  · rename_i hS
    rw [ite_eq_left hS]
    rcases (G1_P_mem (Nat.le_refl 0)).1 hy with rfl | hy | hy
    · rcases hzero _ (Or.inr rfl) with h | h
      · left; rw [hprin, ite_eq_left hS] at h; exact h
      · exact Or.inr h
    · rcases hzero y (Or.inl ((hv 0).2 y hy)) with h | h
      · left; rw [hprin, ite_eq_left hS] at h; exact h
      · exact Or.inr h
    · cases hy
  · rename_i hS
    rw [ite_eq_right hS]
    have hm := mid_closed _ hv N (by omega) hS
    have hwrap := lt_wrap 1 _ T.Z hm.2.1 hm.2.2
    rcases (G1_P_mem (Nat.zero_le 1)).1 hy with rfl | hy | hy
    · exact Or.inl hwrap
    · unfold mid at hy hm hwrap
      rw [G1_add] at hy
      rcases List.mem_append.1 hy with hy | hy
      · -- the multiplied coordinate sum
        have hG1sub : ∀ x, x ∈ T.G1 1 (card 1 (oneDel (sUp (multi.V.get0 v) N))) →
            x < T.P 1 (T.add (card 1 (oneDel (sUp (multi.V.get0 v) N)))
              (collapse (tr (multi.V.get0 v 0)))) T.Z := by
          intro x hx
          exact lt_trans_thm _ _ _ (hm.2.2 x (by rw [G1_add]; exact List.mem_append_left _ hx))
            hwrap
        have hSc := sUp_closed _ hv N
        rcases hSs : sUp (multi.V.get0 v) N with _ | ⟨p, a, b⟩
        · exact absurd hSs hS
        · rw [hSs] at hy hG1sub hSc
          have hp : p ≤ 1 := by cases hSc.2.1 with | p _ _ _ hp _ => exact hp
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
          · -- `S` is the collapse of the first coordinate above the lowest
            have hS0 := isNF1_index 0 0 a b hSc.1 (Nat.le_refl 0)
            have hhigh := sUp_index0_high _ hv N (by rw [hSs]; exact hS0)
            have hz2 : ∀ j, 2 ≤ j → multi.V.get0 v j = multi.T.Z := by
              intro j hj
              by_cases hjN : j < N
              · exact hhigh j hj hjN
              · exact multi.V.get0_ge v j (by omega)
            have hlow : T.P 0 a b = collapse (tr (multi.V.get0 v 1)) := by
              rw [← hSs]
              exact sUp_eq_low _ hz2 N (by omega)
            by_cases hf1 : multi.V.get0 v 1 = multi.T.Z
            · rw [hf1, tr_Z, collapse_Z] at hlow; cases hlow
            · have hd := oneDel_NF_index0 hSc.1 hS0
              rcases card_supp 0 (tr (multi.V.get0 v 1)) hd.1 hd.2
                  (fun x hx => by
                    have hx' := G1_oneDel_sub _ x hx
                    rw [hlow] at hx'
                    exact collapse_G1_le (hv 1).1 (hv 1).2 x hx') y hy with h | h | h
              · exact Or.inl (hG1sub y h)
              · left; rw [h]; exact T.Lt.Z_lt_P _ _ _
              · exact Or.inr ⟨1, hf1, h⟩
          · rw [oneDel_P_succ] at hy hG1sub
            have hsupp := card1_sUp_supp _ hv N y
            rw [hSs] at hsupp
            rcases hsupp hy with h | h | h
            · exact Or.inl (hG1sub y h)
            · left; rw [h]; exact T.Lt.Z_lt_P _ _ _
            · exact Or.inr h
      · by_cases h0 : multi.V.get0 v 0 = multi.T.Z
        · rw [h0, tr_Z, collapse_Z] at hy; cases hy
        · exact Or.inr ⟨0, h0, collapse_G1_le (hv 0).1 (hv 0).2 y hy⟩
    · cases hy

/-! ### Normal forms and monotonicity -/

theorem add_prin_lt {v w : multi.V multi.T} (a b : T) (h : prin v < prin w) :
    T.add (prin v) a < T.add (prin w) b := by
  obtain ⟨p, m, hp, _⟩ := prin_shape v
  obtain ⟨q, n, hq, _⟩ := prin_shape w
  rw [hp, hq] at h ⊢
  rw [T.P_add_eq, T.P_add_eq, add_Z_left, add_Z_left]
  cases h with
  | p_head _ _ _ _ _ _ h => exact T.Lt.p_head _ _ _ _ _ _ h
  | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
  | p_tail _ _ _ _ h => cases h

theorem mono_bounded (N : Nat) (hgood : ∀ x : multi.T, x.size < N → NFComp x → Gd x) :
    ∀ M, ∀ s t : multi.T, s.size + t.size < M → s.size ≤ N → t.size ≤ N →
      NF s → NF t → s < t → tr s < tr t
  | 0, _, _, h, _, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | M + 1, s, t, hM, hsN, htN, hs, ht, hst => by
    cases s with
    | Z =>
      cases t with
      | Z => exact absurd hst (multi.T.lt_irrefl _)
      | P w b => rw [tr_Z]; exact Z_lt_of_ne (tr_ne_Z (fun h => multi.T.noConfusion h))
    | P v a =>
      cases t with
      | Z => exact absurd hst (multi.T.not_lt_Z _)
      | P w b =>
        rw [tr_P, tr_P]
        rcases (multi.T.P_lt_P_iff v w a b).1 hst with hvw | ⟨hvw, hab⟩
        · apply add_prin_lt
          apply prin_lt
          · exact fun j => hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P v j a) hsN)
              (hs.comp j)
          · exact fun j => hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P w j b) htN)
              (ht.comp j)
          · intro j hj
            have h1 := multi.T.size_get0_lt_P v j a
            have h2 := multi.T.size_get0_lt_P w j b
            exact mono_bounded N hgood M _ _ (by omega) (by omega) (by omega)
              (hs.inv.1 j) (ht.inv.1 j) hj
          · exact hvw
        · rw [prin_congr hvw]
          apply add_left_lt
          have h1 := multi.T.size_lt_P_right v a
          have h2 := multi.T.size_lt_P_right w b
          exact mono_bounded N hgood M _ _ (by omega) (by omega) (by omega)
            hs.inv.2.1 ht.inv.2.1 hab

/-- Every support element of the translation lies below it or below the translation of a
support element of the source. -/
def Decomp (s : multi.T) : Prop :=
  ∀ y, y ∈ T.G1 0 (tr s) → y < tr s ∨ ∃ z, z ∈ G s ∧ y ≤ tr z

theorem main (s : multi.T) : (NF s → T.isNF1 (tr s)) ∧ (NF s → Decomp s) ∧ (NFComp s → Gd s) := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    have hgood : ∀ x : multi.T, x.size < s.size → NFComp x → Gd x :=
      fun x hx => (ih x hx).2.2
    have hpres := fun x y (hx : multi.T.size x ≤ s.size) (hy : multi.T.size y ≤ s.size) =>
      mono_bounded s.size hgood (x.size + y.size + 1) x y (Nat.lt_succ_self _) hx hy
    have hNF : NF s → T.isNF1 (tr s) ∧ Decomp s := by
      intro hs
      cases s with
      | Z =>
        refine ⟨by rw [tr_Z]; exact T.isNF1.z, fun y hy => ?_⟩
        rw [tr_Z] at hy; cases hy
      | P v a =>
        obtain ⟨hv, ha, _, hh⟩ := hs.inv
        have hcomp : ∀ j, Gd (multi.V.get0 v j) := fun j =>
          hgood _ (multi.T.size_get0_lt_P v j a) (hs.comp j)
        have hpr := prin_NF hcomp
        have haIH := ih a (multi.T.size_lt_P_right v a)
        obtain ⟨p, m, htr, hpm, _⟩ := tr_P_eq v a
        rw [hpm] at hpr
        obtain ⟨hmNF, _, hmG, _⟩ := T.isNF1_P_inv _ _ _ hpr
        -- the head of the tail lies below the principal part
        have hhead : T.head (tr a) ≤ T.P p m T.Z := by
          rw [← hpm]
          cases a with
          | Z => rw [tr_Z]; exact T.Z_le _
          | P w b =>
            rw [hd_tr]
            show tr (multi.T.P w multi.T.Z) ≤ prin v
            rw [tr_P, tr_Z, T.add_Z]
            have hwv : w ≤ v := by
              rcases (multi.T.P_le_P_iff w v multi.T.Z multi.T.Z).1 hh with h | ⟨h, _⟩
              · exact Or.inl h
              · exact Or.inr h
            have hsa := multi.T.size_lt_P_right v (multi.T.P w b)
            apply prin_le _ hcomp _ hwv
            · intro j
              exact hgood _ (by have := multi.T.size_get0_lt_P w j b; omega) (ha.comp j)
            · intro j hj
              have h1 := multi.T.size_get0_lt_P w j b
              have h2 := multi.T.size_get0_lt_P v j (multi.T.P w b)
              exact hpres _ _ (by omega) (by omega) (ha.inv.1 j) (hv j) hj
        have hNF1 : T.isNF1 (T.P p m (tr a)) := T.isNF1.p _ _ _ hmNF (haIH.1 ha) hmG hhead
        have hprin_mem : ∀ y, y ∈ T.G1 0 (T.P p m T.Z) → y ∈ T.G1 0 (prin v) := by
          rw [hpm]; exact fun y h => h
        have hprin_lt : ∀ y, y < prin v → y < T.P p m (tr a) := by
          intro y h
          rw [hpm] at h
          exact lt_of_lt_of_le_thm T _ _ _ h (head_le_self (T.P p m (tr a)))
        rw [htr]
        refine ⟨hNF1, fun y hy => ?_⟩
        rw [htr] at hy ⊢
        rcases (G1_P_mem (Nat.zero_le p)).1 hy with hy | hy | hy
        · rcases prin_supp hcomp y (hprin_mem y ((G1_P_mem (Nat.zero_le p)).2 (Or.inl hy)))
            with h | ⟨j, hj, h⟩
          · exact Or.inl (hprin_lt y h)
          · exact Or.inr ⟨_, G_coord_mem hj, h⟩
        · rcases prin_supp hcomp y (hprin_mem y ((G1_P_mem (Nat.zero_le p)).2 (Or.inr (Or.inl hy))))
            with h | ⟨j, hj, h⟩
          · exact Or.inl (hprin_lt y h)
          · exact Or.inr ⟨_, G_coord_mem hj, h⟩
        · rcases (haIH.2.1 ha) y hy with h | ⟨z, hz, h⟩
          · exact Or.inl (lt_trans_thm _ _ _ h (tail_lt_of_NF1 hNF1))
          · exact Or.inr ⟨z, G_in_tail hz, h⟩
    refine ⟨fun hs => (hNF hs).1, fun hs => (hNF hs).2, fun hs => ⟨(hNF hs.1).1, ?_⟩⟩
    intro y hy
    rcases (hNF hs.1).2 y hy with h | ⟨z, hz, h⟩
    · exact h
    · exact lt_of_le_of_lt_thm T _ _ _ h (hpres z s (Nat.le_of_lt (G_size_lt s z hz))
        (Nat.le_refl _) (NF_G_comp hs.1 z hz).1 hs.1 (hs.2 z hz))

theorem NF_good {s : multi.T} (hs : NF s) : T.isNF1 (tr s) := (main s).1 hs

theorem tr_mono {s t : multi.T} (hs : NF s) (ht : NF t) (hst : s < t) : tr s < tr t :=
  mono_bounded (s.size + t.size + 1) (fun x _ hx => (main x).2.2 hx) (s.size + t.size + 1) s t
    (Nat.lt_succ_self _) (by omega) (by omega) hs ht hst

/-! ### The bound `ψ_0(Ω^{Ω^ω})` -/

/-- `ψ_1(ψ_1(1)) = Ω^ω`. -/
def vb : T := T.P 1 (T.P 1 (T.P 0 T.Z T.Z) T.Z) T.Z

/-- `ψ_1(ψ_1(ψ_1(1))) = Ω^{Ω^ω}`. -/
def nbound : T := T.P 1 vb T.Z

/-- The target bound `ψ_0(Ω^{Ω^ω})`. -/
def bound : T := T.P 0 nbound T.Z

theorem card1_add_lt_vb : ∀ {X : T} (L : T), T.isNF1 X → T.index_Prop1 1 X →
    T.index_Prop1 0 L → T.add (card 1 X) L < vb := by
  intro X L hX hXi hL
  cases hXi with
  | z => rw [card_Z, add_Z_left]; exact idx0_lt_P1 _ _ hL
  | p p a b hp _ =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
    · rw [card_P0_add, shift_zero]
      apply T.Lt.p_mid
      have hi := (collapse_closed (T.isNF1_P_inv _ _ _ hX).1 (T.isNF1_P_inv _ _ _ hX).2.2.1).2
      exact idx0_lt_P1 _ _ hi
    · rw [card_one_P1, T.P_add_eq, shift_succ, shift_zero]
      exact T.Lt.p_mid _ _ _ _ _ (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))

theorem prin_lt_nbound {v : multi.V multi.T} (hv : ∀ j, Gd (multi.V.get0 v j)) :
    prin v < nbound := by
  rw [prin_eq v (v.length + 2) (by omega)]
  split
  · exact T.Lt.p_head _ _ _ _ _ _ (by omega)
  · apply T.Lt.p_mid
    have hSc := sUp_closed _ hv (v.length + 2)
    have hd := oneDel_NF_index1 hSc.1 hSc.2.1
    exact card1_add_lt_vb _ hd.1 hd.2 (hv 0).collapse.2

theorem tr_lt_nbound {s : multi.T} (hs : NF s) : tr s < nbound := by
  cases s with
  | Z => rw [tr_Z]; exact T.Lt.Z_lt_P _ _ _
  | P v a =>
    obtain ⟨p, m, htr, hpm, _⟩ := tr_P_eq v a
    have h := prin_lt_nbound (fun j => (main _).2.2 (hs.comp j))
    rw [hpm] at h
    rw [htr]
    cases h with
    | p_head _ _ _ _ _ _ h => exact T.Lt.p_head _ _ _ _ _ _ h
    | p_mid _ _ _ _ _ h => exact T.Lt.p_mid _ _ _ _ _ h
    | p_tail _ _ _ _ h => cases h

theorem tr_lt_bound {s : multi.T} (hs : NF s) (hb : s < otb) : tr s < bound := by
  cases s with
  | Z => rw [tr_Z]; exact T.Lt.Z_lt_P _ _ _
  | P v a =>
    have hz := coords_zero_of_lt_otb hb
    have hS : sumN v = T.Z := by
      rw [sumN_eq_length]
      apply sUp_eq_Z_of
      intro j hj
      exact hz j hj
    rw [tr_P]
    unfold prin
    rw [ite_eq_left hS, a0N_eq, T.P_add_eq, add_Z_left]
    exact T.Lt.p_mid _ _ _ _ _ (tr_lt_nbound (hs.inv.1 0))

end new

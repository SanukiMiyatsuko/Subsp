import Subsp.multi.Collapse
import Subsp.multi.emp.source

/-! The translation of `emp` into Buchholz notation:
`P[a₀, …, aₙ] + r ↦ ψ_0(Ω^n·aₙ + ⋯ + Ω·a₁ + a₀) + r`.

Normal forms are sent to normal forms, the translation is strictly monotone on normal forms,
and its values lie below `ψ_0(Ω^ω)`. -/

namespace emp

open MT

mutual
def tr : multi.T → T
  | .Z => .Z
  | .P v a => .P 0 (trV v) (tr a)

/-- `∑ Ω^j · tr(v_j)`, the highest coordinate first. -/
def trV : multi.V multi.T → T
  | .emp => .Z
  | .snoc x xs => T.add (card xs.length (tr x)) (trV xs)
end

theorem tr_Z : tr multi.T.Z = T.Z := by rw [tr]

theorem tr_P (v : multi.V multi.T) (a : multi.T) : tr (multi.T.P v a) = T.P 0 (trV v) (tr a) := by
  rw [tr]

theorem trV_emp : trV (multi.V.emp : multi.V multi.T) = T.Z := by rw [trV]

theorem trV_snoc (x : multi.T) (xs : multi.V multi.T) :
    trV (multi.V.snoc x xs) = T.add (card xs.length (tr x)) (trV xs) := by
  rw [trV]

theorem tr_index0 : ∀ s : multi.T, T.index_Prop1 0 (tr s)
  | .Z => by rw [tr_Z]; exact T.index_Prop1.z
  | .P v a => by rw [tr_P]; exact T.index_Prop1.p _ _ _ (Nat.le_refl 0) (tr_index0 a)

theorem tr_ne_Z {s : multi.T} (h : s ≠ multi.T.Z) : tr s ≠ T.Z := by
  cases s with
  | Z => exact absurd rfl h
  | P v a => rw [tr_P]; intro h; cases h

theorem tr_eq_Z {s : multi.T} (h : tr s = T.Z) : s = multi.T.Z := by
  cases s with
  | Z => rfl
  | P v a => rw [tr_P] at h; cases h

/-! ### Compatibility with normalization -/

theorem trV_trim : ∀ v : multi.V multi.T, trV (multi.V.trim v) = trV v
  | .emp => rfl
  | .snoc a ax => by
    cases a with
    | Z =>
      simp only [multi.V.trim]
      rw [trV_trim ax, trV_snoc, tr_Z, card_Z, add_Z_left]
    | P _ _ => rfl

mutual
theorem tr_norm : ∀ s : multi.T, tr (multi.T.norm s) = tr s
  | .Z => by rw [multi.T.norm]
  | .P v a => by
    rw [multi.T.norm_P, tr_P, tr_P, tr_norm a, multi.V.norm, trV_trim, trV_mapNorm v]

theorem trV_mapNorm : ∀ v : multi.V multi.T, trV (multi.V.mapNorm v) = trV v
  | .emp => by rw [multi.V.mapNorm]
  | .snoc a ax => by
    rw [multi.V.mapNorm, trV_snoc, trV_snoc, multi.V.length_mapNorm, tr_norm a, trV_mapNorm ax]
end

theorem trV_norm (v : multi.V multi.T) : trV (multi.V.norm v) = trV v := by
  rw [multi.V.norm, trV_trim, trV_mapNorm]

theorem tr_congr {a b : multi.T} (h : multi.compareT a b = .eq) : tr a = tr b := by
  rw [← tr_norm a, ← tr_norm b, (multi.compareT_eq_iff a b).1 h]

theorem trV_congr {v w : multi.V multi.T} (h : multi.compareV v w = .eq) : trV v = trV w := by
  rw [← trV_norm v, ← trV_norm w, (multi.compareV_eq_iff v w).1 h]

/-! ### Coordinatewise description of `trV` -/

/-- The blocks of `trV` coming from the coordinates below `k`. -/
def trUpTo (f : Nat → multi.T) : Nat → T
  | 0 => T.Z
  | k + 1 => T.add (card k (tr (f k))) (trUpTo f k)

theorem trUpTo_congr {f g : Nat → multi.T} :
    ∀ k, (∀ j, j < k → multi.compareT (f j) (g j) = .eq) → trUpTo f k = trUpTo g k
  | 0, _ => rfl
  | k + 1, h => by
    simp only [trUpTo]
    rw [tr_congr (h k (Nat.lt_succ_self k)),
      trUpTo_congr k (fun j hj => h j (Nat.lt_succ_of_lt hj))]

theorem trUpTo_zeros (f : Nat → multi.T) (k : Nat) :
    ∀ m, (∀ j, k ≤ j → f j = multi.T.Z) → trUpTo f (k + m) = trUpTo f k
  | 0, _ => rfl
  | m + 1, h => by
    rw [show k + (m + 1) = (k + m) + 1 from rfl, trUpTo, h (k + m) (Nat.le_add_right k m),
      tr_Z, card_Z, add_Z_left, trUpTo_zeros f k m h]

theorem trV_eq_trUpTo_length : ∀ v : multi.V multi.T, trV v = trUpTo (multi.V.get0 v) v.length
  | .emp => rfl
  | .snoc x xs => by
    rw [trV_snoc, trV_eq_trUpTo_length xs]
    simp only [multi.V.length, trUpTo]
    rw [multi.V.get0_snoc_top]
    congr 1
    apply trUpTo_congr
    intro j hj
    rw [multi.V.get0_snoc_low x xs j hj]
    exact multi.T.eqv_refl _

theorem trV_eq_trUpTo (v : multi.V multi.T) (N : Nat) (hN : v.length ≤ N) :
    trV v = trUpTo (multi.V.get0 v) N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = v.length + m := ⟨N - v.length, by omega⟩
  rw [trV_eq_trUpTo_length, trUpTo_zeros _ _ m (fun j hj => multi.V.get0_ge v j hj)]

/-- The blocks strictly between coordinate `i` and coordinate `i + 1 + m`. -/
def above (f : Nat → multi.T) (i : Nat) : Nat → T
  | 0 => T.Z
  | m + 1 => T.add (card (i + 1 + m) (tr (f (i + 1 + m)))) (above f i m)

theorem trUpTo_split (f : Nat → multi.T) (i : Nat) :
    ∀ m, trUpTo f (i + 1 + m) = T.add (above f i m) (trUpTo f (i + 1))
  | 0 => rfl
  | m + 1 => by
    rw [show i + 1 + (m + 1) = (i + 1 + m) + 1 from rfl, trUpTo, trUpTo_split f i m, above,
      add_assoc]

theorem above_congr {f g : Nat → multi.T} (i : Nat) :
    ∀ m, (∀ j, i < j → multi.compareT (f j) (g j) = .eq) → above f i m = above g i m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [above]
    rw [tr_congr (h (i + 1 + m) (by omega)), above_congr i m h]

/-! ### Normal forms of the vector part -/

/-- The Buchholz-side properties of the translation of a coordinate. -/
def Good (x : multi.T) : Prop := T.isNF1 (tr x)

/-- `trUpTo` of good coordinates lies below every nonzero block at the next level. -/
theorem trUpTo_lt_card (f : Nat → multi.T) (hf : ∀ j, Good (f j)) :
    ∀ k {z : T}, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z → trUpTo f k < card k z
  | 0, z, _, _, hz => by rw [trUpTo]; exact Z_lt_of_ne (card_ne_Z 0 hz)
  | k + 1, z, hzNF, hzIdx, hz => by
    rw [trUpTo]
    by_cases hfk : tr (f k) = T.Z
    · rw [hfk, card_Z, add_Z_left]
      have h := card_level_lt T.Z (Nat.lt_succ_self k) hzNF hzIdx hz hzNF hzIdx hz
      rw [T.add_Z] at h
      exact lt_trans_thm _ _ _ (trUpTo_lt_card f hf k hzNF hzIdx hz) h
    · exact card_level_lt _ (Nat.lt_succ_self k) (hf k) (tr_index0 _) hfk hzNF hzIdx hz

theorem trUpTo_closed (f : Nat → multi.T) (hf : ∀ j, Good (f j)) :
    ∀ k, T.isNF1 (trUpTo f k) ∧ T.index_Prop1 1 (trUpTo f k) ∧
      (∀ x, x ∈ T.G1 1 (trUpTo f k) → x < trUpTo f k)
  | 0 => ⟨T.isNF1.z, T.index_Prop1.z, by intro x hx; rw [trUpTo] at hx; cases hx⟩
  | k + 1 => by
    rw [trUpTo]
    cases k with
    | zero =>
      rw [trUpTo, T.add_Z, card_zero]
      exact card_closed 0 (hf 0) (tr_index0 _) |>.imp (by rw [card_zero]; exact id)
        (fun h => by rw [card_zero] at h; exact h)
    | succ k =>
      have ih := trUpTo_closed f hf (k + 1)
      exact card_append_closed k _ (hf (k + 1)) (tr_index0 _) ih.1 ih.2.1 ih.2.2
        (fun z hzNF hzIdx hz => trUpTo_lt_card f hf (k + 1) hzNF hzIdx hz)

theorem trV_closed {v : multi.V multi.T} (hv : ∀ j, Good (multi.V.get0 v j)) :
    T.isNF1 (trV v) ∧ T.index_Prop1 1 (trV v) ∧ (∀ x, x ∈ T.G1 1 (trV v) → x < trV v) := by
  rw [trV_eq_trUpTo_length]
  exact trUpTo_closed _ hv _

/-! ### Monotonicity of the vector part -/

theorem trV_lt {v w : multi.V multi.T} (hv : ∀ j, Good (multi.V.get0 v j))
    (hw : ∀ j, Good (multi.V.get0 w j))
    (hmono : ∀ j, multi.V.get0 v j < multi.V.get0 w j →
      tr (multi.V.get0 v j) < tr (multi.V.get0 w j))
    (hvw : v < w) : trV v < trV w := by
  obtain ⟨i, heq, hlt⟩ := (multi.V.lt_iff_pivot v w).1 hvw
  have hiw : i < w.length := by
    apply Nat.lt_of_not_le
    intro h
    rw [multi.V.get0_ge w i h] at hlt
    exact multi.T.not_lt_Z _ hlt
  let N := v.length + w.length
  obtain ⟨m, hm⟩ : ∃ m, N = i + 1 + m := ⟨N - (i + 1), by omega⟩
  rw [trV_eq_trUpTo v N (by omega), trV_eq_trUpTo w N (by omega), hm,
    trUpTo_split, trUpTo_split, above_congr i m heq]
  apply add_left_lt
  simp only [trUpTo]
  have hvi := hv i
  have hwi := hw i
  exact card_append_lt i _ _ hvi (tr_index0 _) hwi (tr_index0 _) (hmono i hlt)
    (fun q hqNF hqIdx hq => trUpTo_lt_card _ hv i hqNF hqIdx hq)

theorem trV_le {v w : multi.V multi.T} (hv : ∀ j, Good (multi.V.get0 v j))
    (hw : ∀ j, Good (multi.V.get0 w j))
    (hmono : ∀ j, multi.V.get0 v j < multi.V.get0 w j →
      tr (multi.V.get0 v j) < tr (multi.V.get0 w j))
    (hvw : v ≤ w) : trV v ≤ trV w := by
  rcases hvw with h | h
  · exact Or.inl (trV_lt hv hw hmono h)
  · exact Or.inr (trV_congr h)

/-! ### Support of the vector part -/

mutual
/-- The vectors of all principal subterms. -/
def nest : multi.T → List (multi.V multi.T)
  | .Z => []
  | .P w a => w :: (nestV w ++ nest a)

def nestV : multi.V multi.T → List (multi.V multi.T)
  | .emp => []
  | .snoc x xs => nest x ++ nestV xs
end

theorem mem_nest_P {w : multi.V multi.T} {a : multi.T} {u : multi.V multi.T} :
    u ∈ nest (multi.T.P w a) ↔ u = w ∨ u ∈ nestV w ∨ u ∈ nest a := by
  rw [nest]; simp only [List.mem_cons, List.mem_append]

theorem mem_nestV {v : multi.V multi.T} {u : multi.V multi.T} :
    u ∈ nestV v ↔ ∃ j, u ∈ nest (multi.V.get0 v j) := by
  induction v with
  | emp =>
    rw [nestV]
    constructor
    · intro h; cases h
    · rintro ⟨j, hj⟩; rw [show multi.V.get0 multi.V.emp j = multi.T.Z from rfl, nest] at hj
      cases hj
  | snoc x xs ih =>
    rw [nestV, List.mem_append, ih]
    constructor
    · rintro (h | ⟨j, hj⟩)
      · exact ⟨xs.length, by rw [multi.V.get0_snoc_top]; exact h⟩
      · by_cases hjl : j < xs.length
        · exact ⟨j, by rw [multi.V.get0_snoc_low x xs j hjl]; exact hj⟩
        · rw [multi.V.get0_ge xs j (by omega), nest] at hj; cases hj
    · rintro ⟨j, hj⟩
      by_cases hjl : j = xs.length
      · subst hjl; rw [multi.V.get0_snoc_top] at hj; exact Or.inl hj
      · simp only [multi.V.get0, hjl, ite_false] at hj
        exact Or.inr ⟨j, hj⟩

/-- Every nested vector is the vector of a smaller subterm, normal when the term is. -/
theorem nest_sub (x : multi.T) : ∀ u, u ∈ nest x →
    ∃ a, (multi.T.P u a).size ≤ x.size ∧ (NF x → NF (multi.T.P u a)) := by
  induction x using (measure multi.T.size).wf.induction with
  | h x ih =>
    intro u hu
    cases x with
    | Z => rw [nest] at hu; cases hu
    | P w a =>
      rcases mem_nest_P.1 hu with rfl | hu | hu
      · exact ⟨a, Nat.le_refl _, id⟩
      · obtain ⟨j, hj⟩ := mem_nestV.1 hu
        obtain ⟨a', hs, hnf⟩ := ih _ (multi.T.size_get0_lt_P w j a) u hj
        exact ⟨a', Nat.le_trans hs (Nat.le_of_lt (multi.T.size_get0_lt_P w j a)),
          fun h => hnf (h.inv.1 j)⟩
      · obtain ⟨a', hs, hnf⟩ := ih a (multi.T.size_lt_P_right w a) u hu
        exact ⟨a', Nat.le_trans hs (Nat.le_of_lt (multi.T.size_lt_P_right w a)),
          fun h => hnf h.inv.2.1⟩

/-- In a normal form, every nested vector lies at or below the leading vector. -/
theorem nest_le_hd : ∀ {x : multi.T}, NF x → ∀ u, u ∈ nest x →
    multi.T.P u multi.T.Z ≤ multi.T.hd x := by
  intro x hx
  induction hx with
  | z => intro u hu; rw [nest] at hu; cases hu
  | p w a _ _ hh hlt ihw iha =>
    intro u hu
    rcases mem_nest_P.1 hu with rfl | hu | hu
    · exact multi.T.le_refl _
    · obtain ⟨j, hj⟩ := mem_nestV.1 hu
      exact multi.T.le_of_lt (multi.T.lt_of_le_of_lt (ihw j u hj)
        (multi.T.lt_of_le_of_lt (multi.T.hd_le_self _) (hlt j)))
    · exact multi.T.le_trans (iha u hu) hh

theorem nestV_lt {v : multi.V multi.T} {a : multi.T} (h : NF (multi.T.P v a)) :
    ∀ u, u ∈ nestV v → u < v := by
  intro u hu
  obtain ⟨j, hj⟩ := mem_nestV.1 hu
  have h1 := nest_le_hd (h.inv.1 j) u hj
  exact multi.vlt_of_P_lt (multi.T.lt_of_le_of_lt h1
    (multi.T.lt_of_le_of_lt (multi.T.hd_le_self _) (h.inv.2.2.2 j)))

/-- The support of the vector part: every support element lies below it or below the
translation of a nested vector. -/
def Supp (v : multi.V multi.T) : Prop :=
  ∀ y, y ∈ T.G1 0 (trV v) → y < trV v ∨ ∃ u, u ∈ nestV v ∧ y ≤ trV u

theorem block_supp (k : Nat) : ∀ x : multi.T,
    (∀ u, u ∈ nest x → T.isNF1 (trV u) ∧ Supp u) →
    ∀ y, y ∈ T.G1 0 (card k (tr x)) →
      y ∈ T.G1 1 (card k (tr x)) ∨ y = T.Z ∨ ∃ u, u ∈ nest x ∧ y ≤ trV u
  | .Z, _, y, hy => by rw [tr_Z, card_Z] at hy; cases hy
  | .P w a, hx, y, hy => by
    have hw := hx w (mem_nest_P.2 (Or.inl rfl))
    have ha : ∀ u, u ∈ nest a → T.isNF1 (trV u) ∧ Supp u :=
      fun u hu => hx u (mem_nest_P.2 (Or.inr (Or.inr hu)))
    have hsub : ∀ u, u ∈ nestV w → u ∈ nest (multi.T.P w a) :=
      fun u hu => mem_nest_P.2 (Or.inr (Or.inl hu))
    have hpart : ∀ y, y ∈ T.G1 0 (part (trV w)).1 ∨ y ∈ T.G1 0 (part (trV w)).2 →
        y ∈ T.G1 0 (trV w) := by
      intro y hy
      rw [← part_add (trV w), G1_add]
      exact List.mem_append.2 hy
    -- support elements of the translation of `w`
    have hinner : ∀ y, y ∈ T.G1 0 (trV w) → ∃ u, u ∈ nest (multi.T.P w a) ∧ y ≤ trV u := by
      intro y hy
      rcases hw.2 y hy with h | ⟨u, hu, h⟩
      · exact ⟨w, mem_nest_P.2 (Or.inl rfl), Or.inl h⟩
      · exact ⟨u, hsub u hu, h⟩
    rw [tr_P] at hy ⊢
    cases k with
    | zero =>
      rw [card_zero] at hy ⊢
      rcases (G1_P_mem (Nat.le_refl 0)).1 hy with rfl | hy | hy
      · exact Or.inr (Or.inr ⟨w, mem_nest_P.2 (Or.inl rfl), Or.inr rfl⟩)
      · exact Or.inr (Or.inr (hinner y hy))
      · rcases block_supp 0 a ha y (by rw [card_zero]; exact hy) with h | h | ⟨u, hu, h⟩
        · left; rw [card_zero] at h; rw [G1_one_P0]; exact h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨u, mem_nest_P.2 (Or.inr (Or.inr hu)), h⟩)
    | succ j =>
      rw [card_P0] at hy ⊢
      rcases (G1_P_mem (Nat.zero_le 1)).1 hy with rfl | hy | hy
      · exact Or.inl ((G1_P_mem (Nat.le_refl 1)).2 (Or.inl rfl))
      · rcases shift_G1_zero j _ y hy with rfl | hy
        · exact Or.inr (Or.inl rfl)
        · rcases collapse_G1_cases hw.1 y hy with ⟨_, rfl⟩ | hy | hy
          · exact Or.inr (Or.inr ⟨w, mem_nest_P.2 (Or.inl rfl), part_fst_le_self _⟩)
          · exact Or.inr (Or.inr (hinner y (hpart y (Or.inl hy))))
          · exact Or.inr (Or.inr (hinner y (hpart y (Or.inr hy))))
      · rcases block_supp (j + 1) a ha y hy with h | h | ⟨u, hu, h⟩
        · exact Or.inl ((G1_P_mem (Nat.le_refl 1)).2 (Or.inr (Or.inr h)))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨u, mem_nest_P.2 (Or.inr (Or.inr hu)), h⟩)

theorem trV_supp_weak : ∀ v : multi.V multi.T,
    (∀ u, u ∈ nestV v → T.isNF1 (trV u) ∧ Supp u) →
    ∀ y, y ∈ T.G1 0 (trV v) →
      y ∈ T.G1 1 (trV v) ∨ y = T.Z ∨ ∃ u, u ∈ nestV v ∧ y ≤ trV u
  | .emp, _, y, hy => by rw [trV_emp] at hy; cases hy
  | .snoc x xs, hv, y, hy => by
    rw [trV_snoc, G1_add] at hy
    rw [trV_snoc, G1_add]
    have hx : ∀ u, u ∈ nest x → T.isNF1 (trV u) ∧ Supp u :=
      fun u hu => hv u (by rw [nestV]; exact List.mem_append_left _ hu)
    have hxs : ∀ u, u ∈ nestV xs → T.isNF1 (trV u) ∧ Supp u :=
      fun u hu => hv u (by rw [nestV]; exact List.mem_append_right _ hu)
    rcases List.mem_append.1 hy with hy | hy
    · rcases block_supp xs.length x hx y hy with h | h | ⟨u, hu, h⟩
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨u, by rw [nestV]; exact List.mem_append_left _ hu, h⟩)
    · rcases trV_supp_weak xs hxs y hy with h | h | ⟨u, hu, h⟩
      · exact Or.inl (List.mem_append_right _ h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨u, by rw [nestV]; exact List.mem_append_right _ hu, h⟩)

theorem trV_supp {v : multi.V multi.T} (hv : ∀ j, Good (multi.V.get0 v j))
    (hn : ∀ u, u ∈ nestV v → T.isNF1 (trV u) ∧ Supp u) : Supp v := by
  intro y hy
  have hc := trV_closed hv
  rcases trV_supp_weak v hn y hy with h | rfl | h
  · exact Or.inl (hc.2.2 y h)
  · left
    apply Z_lt_of_ne
    intro hz
    rw [hz] at hy
    cases hy
  · exact Or.inr h

/-! ### Normal forms and monotonicity -/

theorem mono_bounded (N : Nat) (hgood : ∀ x : multi.T, x.size < N → NF x → Good x) :
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
        · apply T.Lt.p_mid
          apply trV_lt
          · exact fun j => hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P v j a) hsN)
              (hs.inv.1 j)
          · exact fun j => hgood _ (Nat.lt_of_lt_of_le (multi.T.size_get0_lt_P w j b) htN)
              (ht.inv.1 j)
          · intro j hj
            have h1 := multi.T.size_get0_lt_P v j a
            have h2 := multi.T.size_get0_lt_P w j b
            exact mono_bounded N hgood M _ _ (by omega) (by omega) (by omega)
              (hs.inv.1 j) (ht.inv.1 j) hj
          · exact hvw
        · rw [trV_congr hvw]
          apply T.Lt.p_tail
          have h1 := multi.T.size_lt_P_right v a
          have h2 := multi.T.size_lt_P_right w b
          exact mono_bounded N hgood M _ _ (by omega) (by omega) (by omega)
            hs.inv.2.1 ht.inv.2.1 hab

theorem main : ∀ N, ∀ s : multi.T, s.size < N → NF s →
    Good s ∧ ∀ v a, s = multi.T.P v a → Supp v
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | N + 1, s, hsN, hs => by
    have hgood : ∀ x : multi.T, x.size < N → NF x → Good x :=
      fun x hx hnf => (main N x hx hnf).1
    have hmono := fun s t (hsN : multi.T.size s ≤ N) (htN : multi.T.size t ≤ N) =>
      mono_bounded N hgood (s.size + t.size + 1) s t (Nat.lt_succ_self _) hsN htN
    cases s with
    | Z => exact ⟨by show T.isNF1 (tr multi.T.Z); rw [tr_Z]; exact T.isNF1.z,
        fun v a h => multi.T.noConfusion h⟩
    | P v a =>
      obtain ⟨hv, ha, hh, _⟩ := hs.inv
      have hcomp : ∀ j, Good (multi.V.get0 v j) := fun j =>
        hgood _ (by have := multi.T.size_get0_lt_P v j a; omega) (hv j)
      -- nested vectors of the components
      have hnest : ∀ u, u ∈ nestV v → T.isNF1 (trV u) ∧ Supp u ∧
          (∀ j, Good (multi.V.get0 u j)) ∧ ∀ j, (multi.V.get0 u j).size < N := by
        intro u hu
        obtain ⟨j, hj⟩ := mem_nestV.1 hu
        obtain ⟨a', hsz, hnf⟩ := nest_sub _ u hj
        have hu' := hnf (hv j)
        have hsz' : (multi.T.P u a').size < N := by
          have := multi.T.size_get0_lt_P v j a; omega
        have hm := main N _ hsz' hu'
        have hg : ∀ j, Good (multi.V.get0 u j) := fun j =>
          hgood _ (by have := multi.T.size_get0_lt_P u j a'; omega) (hu'.inv.1 j)
        refine ⟨(trV_closed hg).1, hm.2 u a' rfl, hg, fun j => ?_⟩
        have := multi.T.size_get0_lt_P u j a'; omega
      have hsupp : Supp v := trV_supp hcomp (fun u hu => ⟨(hnest u hu).1, (hnest u hu).2.1⟩)
      refine ⟨?_, fun v' a' h => by injection h with h1 _; subst h1; exact hsupp⟩
      have hc := trV_closed hcomp
      show T.isNF1 (tr (multi.T.P v a))
      rw [tr_P]
      refine T.isNF1.p 0 _ _ hc.1 (hgood a (by have := multi.T.size_lt_P_right v a; omega) ha)
        (fun y hy => ?_) ?_
      · rcases hsupp y hy with h | ⟨u, hu, h⟩
        · exact h
        · have hlt : trV u < trV v := by
            apply trV_lt (hnest u hu).2.2.1 hcomp _ (nestV_lt hs u hu)
            intro j hj
            exact hmono _ _ (Nat.le_of_lt ((hnest u hu).2.2.2 j))
              (by have := multi.T.size_get0_lt_P v j a; omega)
              (by
                obtain ⟨j', hj'⟩ := mem_nestV.1 hu
                obtain ⟨a'', _, hnf⟩ := nest_sub _ u hj'
                exact (hnf (hv j')).inv.1 j)
              (hv j) hj
          exact lt_of_le_of_lt_thm T _ _ _ h hlt
      · cases a with
        | Z => rw [tr_Z]; exact T.Z_le _
        | P w b =>
          rw [tr_P]
          show T.P 0 (trV w) T.Z ≤ T.P 0 (trV v) T.Z
          have hwv : w ≤ v := by
            rcases (multi.T.P_le_P_iff w v multi.T.Z multi.T.Z).1 hh with h | ⟨h, _⟩
            · exact Or.inl h
            · exact Or.inr h
          apply lift_le 0
          apply trV_le _ hcomp _ hwv
          · intro j
            exact hgood _ (by
              have h1 := multi.T.size_get0_lt_P w j b
              have h2 := multi.T.size_lt_P_right v (multi.T.P w b); omega) (ha.inv.1 j)
          · intro j hj
            exact hmono _ _
              (by have h1 := multi.T.size_get0_lt_P w j b
                  have h2 := multi.T.size_lt_P_right v (multi.T.P w b); omega)
              (by have := multi.T.size_get0_lt_P v j (multi.T.P w b); omega)
              (ha.inv.1 j) (hv j) hj

theorem NF_good {s : multi.T} (hs : NF s) : T.isNF1 (tr s) :=
  (main (s.size + 1) s (Nat.lt_succ_self _) hs).1

theorem tr_mono {s t : multi.T} (hs : NF s) (ht : NF t) (hst : s < t) : tr s < tr t :=
  mono_bounded (s.size + t.size + 1) (fun x _ hx => NF_good hx) (s.size + t.size + 1) s t
    (Nat.lt_succ_self _) (by omega) (by omega) hs ht hst

/-! ### The bound `ψ_0(Ω^ω)` -/

/-- The Buchholz bound `ψ_1(ψ_1(1))` of the vector parts. -/
def vbound : T := T.P 1 (T.P 1 (T.P 0 T.Z T.Z) T.Z) T.Z

theorem good_Z : Good multi.T.Z := by unfold Good; rw [tr_Z]; exact T.isNF1.z

theorem trV_lt_bound : ∀ v : multi.V multi.T, (∀ j, Good (multi.V.get0 v j)) → trV v < vbound
  | .emp, _ => by rw [trV_emp]; exact T.Lt.Z_lt_P _ _ _
  | .snoc x xs, hv => by
    have hx : Good x := by have := hv xs.length; rwa [multi.V.get0_snoc_top] at this
    have hxs : ∀ j, Good (multi.V.get0 xs j) := by
      intro j
      by_cases hj : j < xs.length
      · have := hv j; rwa [multi.V.get0_snoc_low x xs j hj] at this
      · rw [multi.V.get0_ge xs j (by omega)]; exact good_Z
    rw [trV_snoc]
    cases x with
    | Z => rw [tr_Z, card_Z, add_Z_left]; exact trV_lt_bound xs hxs
    | P w a =>
      have hx' : T.isNF1 (T.P 0 (trV w) (tr a)) := by
        have h := hx; unfold Good at h; rwa [tr_P] at h
      obtain ⟨hwNF, _, hwG, _⟩ := T.isNF1_P_inv _ _ _ hx'
      rw [tr_P]
      cases xs.length with
      | zero =>
        rw [card_zero, T.P_add_eq]
        exact T.Lt.p_head _ _ _ _ _ _ (by omega)
      | succ k =>
        rw [card_P0_add]
        apply T.Lt.p_mid
        cases k with
        | zero =>
          rw [shift_zero]
          have hi := (collapse_closed hwNF hwG).2
          generalize collapse (trV w) = c at hi ⊢
          cases hi with
          | z => exact T.Lt.Z_lt_P _ _ _
          | p p c d hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)
        | succ k =>
          rw [shift_succ]
          exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)

/-- The target bound `ψ_0(Ω^ω)`. -/
def bound : T := T.P 0 vbound T.Z

theorem tr_lt_bound {s : multi.T} (hs : NF s) : tr s < bound := by
  cases s with
  | Z => rw [tr_Z]; exact T.Lt.Z_lt_P _ _ _
  | P v a =>
    rw [tr_P]
    apply T.Lt.p_mid
    apply trV_lt_bound
    intro j
    exact NF_good (hs.inv.1 j)

end emp

import Subsp.multi.Lex
import Subsp.multi.old.nt

/-! Source-side theory of `old` on `multi.T`: unfolding of `dom` and `fund`, the indexed
support lists `G u`, normal forms, closure of normal forms under fundamental sequences, and
cofinality. -/

open multi
open T

namespace old

/-! ### Unfolding `dom` and `fund` -/

theorem dom_tail (v : V multi.T) {a : multi.T} (ha : a ≠ Z) : T.dom (P v a) = T.dom a := by
  rw [T.dom, ite_eq_right ha]

theorem dom_PZ_none {v : V multi.T} (h : V.fnz v = none) : T.dom (P v Z) = .one := by
  rw [T.dom, ite_eq_left rfl, h]

theorem dom_PZ_one0 {v : V multi.T} (h : V.fnz v = some 0) (hd : T.dom (V.get0 v 0) = .one) :
    T.dom (P v Z) = .omega := by
  rw [T.dom, ite_eq_left rfl, h]; simp only [hd]

theorem dom_PZ_oneS {v : V multi.T} {k : Nat} (h : V.fnz v = some (k + 1))
    (hd : T.dom (V.get0 v (k + 1)) = .one) : T.dom (P v Z) = .Omega (k + 1) := by
  rw [T.dom, ite_eq_left rfl, h]; simp only [hd]

theorem dom_PZ_omega {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .omega) : T.dom (P v Z) = .omega := by
  rw [T.dom, ite_eq_left rfl, h]; simp only [hd]

theorem dom_PZ_Omega_le {v : V multi.T} {i m : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .Omega m) (hm : m ≤ i) : T.dom (P v Z) = .Omega m := by
  rw [T.dom, ite_eq_left rfl, h]; simp only [hd]; rw [ite_eq_left hm]

theorem dom_PZ_Omega_gt {v : V multi.T} {i m : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .Omega m) (hm : ¬ m ≤ i) : T.dom (P v Z) = .omega := by
  rw [T.dom, ite_eq_left rfl, h]; simp only [hd]; rw [ite_eq_right hm]

theorem dom_PZ_zero {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .zero) : T.dom (P v Z) = .omega := by
  rw [T.dom, ite_eq_left rfl, h]; simp only [hd]

theorem dom_P_ne_zero : ∀ (a : multi.T) (v : V multi.T), T.dom (P v a) ≠ .zero
  | Z, v => by
    rcases hf : V.fnz v with _ | i
    · rw [dom_PZ_none hf]; intro h; cases h
    · cases hdi : T.dom (V.get0 v i) with
      | zero => rw [dom_PZ_zero hf hdi]; intro h; cases h
      | one =>
        cases i with
        | zero => rw [dom_PZ_one0 hf hdi]; intro h; cases h
        | succ k => rw [dom_PZ_oneS hf hdi]; intro h; cases h
      | omega => rw [dom_PZ_omega hf hdi]; intro h; cases h
      | Omega m =>
        by_cases hm : m ≤ i
        · rw [dom_PZ_Omega_le hf hdi hm]; intro h; cases h
        · rw [dom_PZ_Omega_gt hf hdi hm]; intro h; cases h
  | P w b, v => by
    rw [dom_tail v (fun h => T.noConfusion h)]
    exact dom_P_ne_zero b w

theorem eq_Z_of_dom_zero {s : multi.T} (h : T.dom s = .zero) : s = Z := by
  cases s with
  | Z => rfl
  | P v a => exact absurd h (dom_P_ne_zero a v)

/-- The shapes of a principal term with domain `Omega m`. -/
theorem dom_PZ_Omega_inv {v : V multi.T} {m : Nat} (hd : T.dom (P v Z) = .Omega m) :
    ∃ i, V.fnz v = some i ∧
      ((T.dom (V.get0 v i) = .one ∧ 0 < i ∧ m = i) ∨ (T.dom (V.get0 v i) = .Omega m ∧ m ≤ i)) := by
  rcases hf : V.fnz v with _ | i
  · rw [dom_PZ_none hf] at hd; cases hd
  · refine ⟨i, rfl, ?_⟩
    cases hdi : T.dom (V.get0 v i) with
    | zero => rw [dom_PZ_zero hf hdi] at hd; cases hd
    | one =>
      cases i with
      | zero => rw [dom_PZ_one0 hf hdi] at hd; cases hd
      | succ k =>
        rw [dom_PZ_oneS hf hdi] at hd
        injection hd with hd
        exact Or.inl ⟨rfl, Nat.succ_pos k, hd.symm⟩
    | omega => rw [dom_PZ_omega hf hdi] at hd; cases hd
    | Omega m' =>
      by_cases hm : m' ≤ i
      · rw [dom_PZ_Omega_le hf hdi hm] at hd
        injection hd with hd
        subst hd
        exact Or.inr ⟨rfl, hm⟩
      · rw [dom_PZ_Omega_gt hf hdi hm] at hd; cases hd

/-- The shapes of a principal term with domain `omega`. -/
theorem dom_PZ_omega_inv {v : V multi.T} (hd : T.dom (P v Z) = .omega) :
    ∃ i, V.fnz v = some i ∧
      ((T.dom (V.get0 v i) = .one ∧ i = 0) ∨ T.dom (V.get0 v i) = .omega ∨
        ∃ m, T.dom (V.get0 v i) = .Omega m ∧ ¬ m ≤ i) := by
  rcases hf : V.fnz v with _ | i
  · rw [dom_PZ_none hf] at hd; cases hd
  · refine ⟨i, rfl, ?_⟩
    cases hdi : T.dom (V.get0 v i) with
    | zero =>
      exact absurd (eq_Z_of_dom_zero hdi) (V.fnz_some_spec v i hf).1
    | one =>
      cases i with
      | zero => exact Or.inl ⟨rfl, rfl⟩
      | succ k => rw [dom_PZ_oneS hf hdi] at hd; cases hd
    | omega => exact Or.inr (Or.inl rfl)
    | Omega m' =>
      by_cases hm : m' ≤ i
      · rw [dom_PZ_Omega_le hf hdi hm] at hd; cases hd
      · exact Or.inr (Or.inr ⟨m', rfl, hm⟩)

theorem dom_Omega_pos : ∀ (s : multi.T) {m : Nat}, T.dom s = .Omega m → 0 < m
  | Z, _, hd => by rw [T.dom] at hd; cases hd
  | P v a, m, hd => by
    by_cases ha : a = Z
    · subst ha
      obtain ⟨i, _, h | h⟩ := dom_PZ_Omega_inv hd
      · rw [h.2.2]; exact h.2.1
      · exact dom_Omega_pos (V.get0 v i) h.1
    · rw [dom_tail v ha] at hd
      exact dom_Omega_pos a hd
termination_by s => s.size
decreasing_by
  · exact T.size_get0_lt_P _ _ _
  · exact T.size_lt_P_right _ _

theorem fund_Z (t : multi.T) : T.fund Z t = Z := by rw [T.fund]

theorem fund_tail (v : V multi.T) {a : multi.T} (ha : a ≠ Z) (t : multi.T) :
    T.fund (P v a) t = P v (T.fund a t) := by
  rw [T.fund, ite_eq_right ha]

theorem fund_PZ_none {v : V multi.T} (h : V.fnz v = none) (t : multi.T) :
    T.fund (P v Z) t = Z := by
  rw [T.fund, ite_eq_left rfl, h]

theorem fund_PZ_one0 {v : V multi.T} (h : V.fnz v = some 0) (hd : T.dom (V.get0 v 0) = .one)
    (t : multi.T) : T.fund (P v Z) t = T.mul (P (V.set v 0 (T.fund (V.get0 v 0) Z)) Z) t := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]

theorem fund_PZ_oneS {v : V multi.T} {k : Nat} (h : V.fnz v = some (k + 1))
    (hd : T.dom (V.get0 v (k + 1)) = .one) (t : multi.T) :
    T.fund (P v Z) t =
      P (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k t) Z := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]

theorem fund_PZ_Omega_lt {v : V multi.T} {i m : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .Omega m) (hm : i < m) (t : multi.T) :
    T.fund (P v Z) t =
      P (V.set v i (T.fund (V.get0 v i) (T.iter (fun x => T.fund (V.get0 v i) x) t))) Z := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]; rw [ite_eq_left hm]

theorem fund_PZ_Omega_ge {v : V multi.T} {i m : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .Omega m) (hm : ¬ i < m) (t : multi.T) :
    T.fund (P v Z) t = P (V.set v i (T.fund (V.get0 v i) t)) Z := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]; rw [ite_eq_right hm]

theorem fund_PZ_omega {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .omega) (t : multi.T) :
    T.fund (P v Z) t = P (V.set v i (T.fund (V.get0 v i) t)) Z := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]

/-! ### Successors -/

theorem dom_one_fnz {v : V multi.T} (hd : T.dom (P v Z) = .one) : V.fnz v = none := by
  rcases hf : V.fnz v with _ | i
  · rfl
  · exfalso
    cases hdi : T.dom (V.get0 v i) with
    | zero => rw [dom_PZ_zero hf hdi] at hd; cases hd
    | one =>
      cases i with
      | zero => rw [dom_PZ_one0 hf hdi] at hd; cases hd
      | succ k => rw [dom_PZ_oneS hf hdi] at hd; cases hd
    | omega => rw [dom_PZ_omega hf hdi] at hd; cases hd
    | Omega m =>
      by_cases hm : m ≤ i
      · rw [dom_PZ_Omega_le hf hdi hm] at hd; cases hd
      · rw [dom_PZ_Omega_gt hf hdi hm] at hd; cases hd

theorem fund_one_irrel : ∀ (s : multi.T), T.dom s = .one → ∀ t, T.fund s t = T.fund s Z
  | Z, hd, _ => by rw [T.dom] at hd; cases hd
  | P v a, hd, t => by
    by_cases ha : a = Z
    · subst ha
      have hf := dom_one_fnz hd
      rw [fund_PZ_none hf, fund_PZ_none hf]
    · rw [fund_tail v ha, fund_tail v ha, fund_one_irrel a (by rwa [dom_tail v ha] at hd) t]

/-- Below a successor means at most its predecessor. -/
theorem fund_one_upper : ∀ (s : multi.T), T.dom s = .one → ∀ b, b < s → b ≤ T.fund s Z
  | Z, hd, _, _ => by rw [T.dom] at hd; cases hd
  | P v a, hd, b, hb => by
    by_cases ha : a = Z
    · subst ha
      have hf := dom_one_fnz hd
      rw [fund_PZ_none hf]
      cases b with
      | Z => exact T.Z_le Z
      | P y e =>
        exfalso
        obtain ⟨p, _, hp⟩ := (V.lt_iff_pivot y v).1 (vlt_of_P_lt hb)
        rw [V.fnz_none_spec v hf p] at hp
        exact T.not_lt_Z _ hp
    · rw [fund_tail v ha]
      cases b with
      | Z => exact T.Z_le _
      | P y e =>
        rcases (T.P_lt_P_iff y v e a).1 hb with hy | ⟨hy, he⟩
        · exact Or.inl (T.P_lt_P_of_vlt _ _ hy)
        · exact (T.P_le_P_iff y v e _).2
            (Or.inr ⟨hy, fund_one_upper a (by rwa [dom_tail v ha] at hd) e he⟩)

/-! ### Fundamental sequences descend -/

theorem fund_lt_self (s : multi.T) : s ≠ Z → ∀ t, T.fund s t < s := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro hs t
    cases s with
    | Z => exact absurd rfl hs
    | P v a =>
      by_cases ha : a = Z
      · subst ha
        rcases hf : V.fnz v with _ | i
        · rw [fund_PZ_none hf]; exact T.Z_lt_P _ _
        · obtain ⟨hne, _⟩ := V.fnz_some_spec v i hf
          have hi := V.lt_length_of_fnz v i hf
          have hrec : ∀ u, T.fund (V.get0 v i) u < V.get0 v i :=
            fun u => ih _ (T.size_get0_lt_P v i Z) hne u
          cases hd : T.dom (V.get0 v i) with
          | zero => exact absurd (eq_Z_of_dom_zero hd) hne
          | one =>
            cases i with
            | zero =>
              rw [fund_PZ_one0 hf hd]
              exact mul_lt_of_vlt (set_lt hi (hrec Z)) t
            | succ k =>
              rw [fund_PZ_oneS hf hd]
              apply T.P_lt_P_of_vlt
              apply V.lt_of_pivot (k + 1)
              · intro j hj
                rw [V.get0_set_ne _ k _ j (by omega)]
                exact V.get0_set_eqv_above v (k + 1) _ j hj
              · rw [V.get0_set_ne _ k _ (k + 1) (by omega), V.get0_set_same v (k + 1) _ hi]
                exact hrec Z
          | omega =>
            rw [fund_PZ_omega hf hd]
            exact T.P_lt_P_of_vlt _ _ (set_lt hi (hrec t))
          | Omega m =>
            by_cases hm : i < m
            · rw [fund_PZ_Omega_lt hf hd hm]
              exact T.P_lt_P_of_vlt _ _ (set_lt hi (hrec _))
            · rw [fund_PZ_Omega_ge hf hd hm]
              exact T.P_lt_P_of_vlt _ _ (set_lt hi (hrec _))
      · rw [fund_tail v ha]
        exact T.P_tail_lt v (ih a (T.size_lt_P_right v a) ha t)

theorem hd_fund_le (s t : multi.T) : T.hd (T.fund s t) ≤ T.hd s := by
  by_cases hs : s = Z
  · subst hs; rw [fund_Z]; exact T.le_refl _
  · exact T.hd_mono (fund_lt_self s hs t)

/-! ### The indexed support lists -/

mutual
/-- The nonzero coordinates of index at least `u` occurring in a term, reached through
coordinates of index at least `u` and through tails. -/
def G (u : Nat) : multi.T → List multi.T
  | .Z => []
  | .P v a => Gv u v ++ G u a

def Gv (u : Nat) : V multi.T → List multi.T
  | .emp => []
  | .snoc x xs => Gv u xs ++ (if x = .Z then [] else if u ≤ xs.length then x :: G u x else [])
end

theorem G_Z (u : Nat) : G u multi.T.Z = [] := by rw [G]

theorem mem_Gv {u : Nat} {v : V multi.T} {y : multi.T} :
    y ∈ Gv u v ↔ ∃ j, u ≤ j ∧ ((V.get0 v j ≠ Z ∧ y = V.get0 v j) ∨ y ∈ G u (V.get0 v j)) := by
  induction v with
  | emp =>
    rw [Gv]
    constructor
    · intro h; cases h
    · rintro ⟨j, _, ⟨h, _⟩ | h⟩
      · exact absurd rfl h
      · rw [show V.get0 V.emp j = Z from rfl, G_Z] at h; cases h
  | snoc x xs ih =>
    rw [Gv, List.mem_append, ih]
    constructor
    · rintro (⟨j, huj, hj⟩ | h)
      · by_cases hjl : j < xs.length
        · exact ⟨j, huj, by rw [V.get0_snoc_low x xs j hjl]; exact hj⟩
        · rw [V.get0_ge xs j (by omega)] at hj
          rcases hj with ⟨h, _⟩ | h
          · exact absurd rfl h
          · rw [G_Z] at h; cases h
      · by_cases hx : x = Z
        · rw [ite_eq_left hx] at h; cases h
        · rw [ite_eq_right hx] at h
          by_cases hu : u ≤ xs.length
          · rw [ite_eq_left hu, List.mem_cons] at h
            refine ⟨xs.length, hu, ?_⟩
            rw [V.get0_snoc_top]
            rcases h with h | h
            · exact Or.inl ⟨hx, h⟩
            · exact Or.inr h
          · rw [ite_eq_right hu] at h; cases h
    · rintro ⟨j, huj, hj⟩
      by_cases hjl : j = xs.length
      · rw [hjl, V.get0_snoc_top] at hj
        right
        have hx : x ≠ Z := by
          rcases hj with ⟨h, _⟩ | h
          · exact h
          · intro hx; rw [hx, G_Z] at h; cases h
        rw [ite_eq_right hx, ite_eq_left (hjl ▸ huj), List.mem_cons]
        rcases hj with ⟨_, h⟩ | h
        · exact Or.inl h
        · exact Or.inr h
      · left
        refine ⟨j, huj, ?_⟩
        simp only [V.get0, hjl, ite_false] at hj
        exact hj

theorem mem_G_P {u : Nat} {v : V multi.T} {a y : multi.T} :
    y ∈ G u (P v a) ↔
      (∃ j, u ≤ j ∧ ((V.get0 v j ≠ Z ∧ y = V.get0 v j) ∨ y ∈ G u (V.get0 v j))) ∨ y ∈ G u a := by
  rw [G, List.mem_append, mem_Gv]

theorem G_coord_mem {u : Nat} {v : V multi.T} {a : multi.T} {j : Nat} (huj : u ≤ j)
    (h : V.get0 v j ≠ Z) : V.get0 v j ∈ G u (P v a) :=
  mem_G_P.2 (Or.inl ⟨j, huj, Or.inl ⟨h, rfl⟩⟩)

theorem G_in_coord {u : Nat} {v : V multi.T} {a y : multi.T} {j : Nat} (huj : u ≤ j)
    (h : y ∈ G u (V.get0 v j)) : y ∈ G u (P v a) :=
  mem_G_P.2 (Or.inl ⟨j, huj, Or.inr h⟩)

theorem G_in_tail {u : Nat} {v : V multi.T} {a y : multi.T} (h : y ∈ G u a) : y ∈ G u (P v a) :=
  mem_G_P.2 (Or.inr h)

theorem G_size_lt (u : Nat) : ∀ s y : multi.T, y ∈ G u s → y.size < s.size := by
  intro s
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro y hy
    cases s with
    | Z => rw [G_Z] at hy; cases hy
    | P v a =>
      rcases mem_G_P.1 hy with ⟨j, _, ⟨_, rfl⟩ | hG⟩ | hG
      · exact T.size_get0_lt_P v j a
      · have hi := T.size_get0_lt_P v j a
        exact Nat.lt_trans (ih _ hi y hG) hi
      · have hi := T.size_lt_P_right v a
        exact Nat.lt_trans (ih _ hi y hG) hi

theorem G_trans (u : Nat) : ∀ a x y : multi.T, x ∈ G u a → y ∈ G u x → y ∈ G u a := by
  intro a
  induction a using (measure multi.T.size).wf.induction with
  | h a ih =>
    intro x y hx hy
    cases a with
    | Z => rw [G_Z] at hx; cases hx
    | P v b =>
      rcases mem_G_P.1 hx with ⟨j, huj, ⟨_, rfl⟩ | hG⟩ | hG
      · exact G_in_coord huj hy
      · exact G_in_coord huj (ih _ (T.size_get0_lt_P v j b) x y hG hy)
      · exact G_in_tail (ih _ (T.size_lt_P_right v b) x y hG hy)

theorem G_ne_Z {u : Nat} {s y : multi.T} (h : y ∈ G u s) : y ≠ Z := by
  induction s using (measure multi.T.size).wf.induction generalizing y with
  | h s ih =>
    cases s with
    | Z => rw [G_Z] at h; cases h
    | P v a =>
      rcases mem_G_P.1 h with ⟨j, _, ⟨hz, rfl⟩ | hG⟩ | hG
      · exact hz
      · exact ih _ (T.size_get0_lt_P v j a) hG
      · exact ih _ (T.size_lt_P_right v a) hG

theorem G_mono {u u' : Nat} (huu : u ≤ u') : ∀ s y : multi.T, y ∈ G u' s → y ∈ G u s := by
  intro s
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro y hy
    cases s with
    | Z => rw [G_Z] at hy; cases hy
    | P v a =>
      rcases mem_G_P.1 hy with ⟨j, huj, ⟨hz, rfl⟩ | hG⟩ | hG
      · exact G_coord_mem (Nat.le_trans huu huj) hz
      · exact G_in_coord (Nat.le_trans huu huj) (ih _ (T.size_get0_lt_P v j a) y hG)
      · exact G_in_tail (ih _ (T.size_lt_P_right v a) y hG)

/-- The support lists commute with normalization. -/
theorem Gv_trim (u : Nat) : ∀ w : V multi.T, Gv u (V.trim w) = Gv u w
  | .emp => rfl
  | .snoc x xs => by
    cases x with
    | Z =>
      show Gv u (V.trim xs) = Gv u xs ++ (if (Z : multi.T) = Z then [] else _)
      rw [Gv_trim u xs, ite_eq_left rfl, List.append_nil]
    | P _ _ => rfl

mutual
theorem G_norm (u : Nat) : ∀ s : multi.T, G u (multi.T.norm s) = (G u s).map multi.T.norm
  | .Z => by rw [multi.T.norm, G_Z]; rfl
  | .P v a => by
    rw [multi.T.norm, G, G, List.map_append, G_norm u a, Gv_trim, Gv_mapNorm u v]

theorem Gv_mapNorm (u : Nat) : ∀ v : V multi.T, Gv u (V.mapNorm v) = (Gv u v).map multi.T.norm
  | .emp => rfl
  | .snoc x xs => by
    rw [V.mapNorm, Gv, Gv, List.map_append, Gv_mapNorm u xs, V.length_mapNorm]
    congr 1
    by_cases hz : x = Z
    · rw [ite_eq_left hz, ite_eq_left (by rw [hz]; rfl)]; rfl
    · rw [ite_eq_right hz, ite_eq_right (fun h => hz (T.norm_eq_Z.1 h))]
      by_cases hu : u ≤ xs.length
      · rw [ite_eq_left hu, ite_eq_left hu, G_norm u x]; rfl
      · rw [ite_eq_right hu, ite_eq_right hu]; rfl
end

/-! ### Normal forms -/

/-- Normal forms: every coordinate lies above its own support at its index. -/
inductive NF : multi.T → Prop
  | z : NF Z
  | p (v : V multi.T) (a : multi.T) (hv : ∀ j, NF (V.get0 v j)) (ha : NF a)
      (hg : ∀ j y, y ∈ G j (V.get0 v j) → y < V.get0 v j) (hh : T.hd a ≤ P v Z) : NF (P v a)

/-- A normal form lying above its own support at index `u`. -/
def NFComp (u : Nat) (x : multi.T) : Prop := NF x ∧ ∀ y, y ∈ G u x → y < x

theorem NF.inv {v : V multi.T} {a : multi.T} (h : NF (P v a)) :
    (∀ j, NF (V.get0 v j)) ∧ NF a ∧ (∀ j y, y ∈ G j (V.get0 v j) → y < V.get0 v j) ∧
      T.hd a ≤ P v Z := by
  cases h with
  | p _ _ hv ha hg hh => exact ⟨hv, ha, hg, hh⟩

theorem NF.comp {v : V multi.T} {a : multi.T} (h : NF (P v a)) (j : Nat) :
    NFComp j (V.get0 v j) := ⟨h.inv.1 j, h.inv.2.2.1 j⟩

theorem NFComp_Z (u : Nat) : NFComp u Z := ⟨NF.z, fun y hy => by rw [G_Z] at hy; cases hy⟩

theorem NFComp_mono {u u' : Nat} (huu : u ≤ u') {s : multi.T} (h : NFComp u s) : NFComp u' s :=
  ⟨h.1, fun y hy => h.2 y (G_mono huu s y hy)⟩

theorem NF_PZ_of_comps {v : V multi.T} (h : ∀ j, NFComp j (V.get0 v j)) : NF (P v Z) :=
  NF.p v Z (fun j => (h j).1) NF.z (fun j => (h j).2) (T.Z_le _)

theorem NF_G : ∀ {s : multi.T}, NF s → ∀ u x, x ∈ G u s → NF x := by
  intro s hs
  induction hs with
  | z => intro u x hx; rw [G_Z] at hx; cases hx
  | p v a hv _ _ _ ihv iha =>
    intro u x hx
    rcases mem_G_P.1 hx with ⟨j, _, ⟨_, rfl⟩ | hG⟩ | hG
    · exact hv j
    · exact ihv j u x hG
    · exact iha u x hG

theorem NF_norm : ∀ {s : multi.T}, NF s → NF (multi.T.norm s) := by
  intro s h
  induction h with
  | z => exact NF.z
  | p v a _ _ hg hh ihv iha =>
    rw [T.norm_P]
    refine NF.p _ _ (fun j => by rw [V.get0_norm]; exact ihv j) iha (fun j y hy => ?_) ?_
    · rw [V.get0_norm, G_norm, List.mem_map] at hy
      rw [V.get0_norm]
      obtain ⟨y', hy', rfl⟩ := hy
      exact (multi.T.lt_norm_iff _ _).1 (hg j y' hy')
    · have hhd : T.hd (multi.T.norm a) = multi.T.norm (T.hd a) := by
        cases a with
        | Z => rfl
        | P w b => rw [T.norm_P]; rfl
      rw [hhd, show P (V.norm v) Z = multi.T.norm (P v Z) from (T.norm_P v Z).symm]
      exact (multi.T.le_norm_iff _ _).1 hh

theorem G_eqv {u : Nat} {x x' : multi.T} (h : compareT x x' = .eq) :
    ∀ y, y ∈ G u x → ∃ y', y' ∈ G u x' ∧ compareT y y' = .eq := by
  intro y hy
  have hn : multi.T.norm x = multi.T.norm x' := (compareT_eq_iff x x').1 h
  have h1 : multi.T.norm y ∈ G u (multi.T.norm x') := by
    rw [← hn, G_norm]; exact List.mem_map_of_mem hy
  rw [G_norm, List.mem_map] at h1
  obtain ⟨y', hy', he⟩ := h1
  exact ⟨y', hy', (compareT_eq_iff y y').2 he.symm⟩

theorem ne_Z_of_eqv {x x' : multi.T} (h : compareT x x' = .eq) (hx : x ≠ Z) : x' ≠ Z :=
  fun h' => hx ((T.eq_Z_iff_of_norm_eq ((compareT_eq_iff x x').1 h)).2 h')

/-! ### Interval domination -/

def GZ (u : Nat) (z : multi.T) : List multi.T := [z] ++ G u z ++ [Z]

/-- Supports of `b` at level `u` lie below `b` or are dominated by the support of each `c`
between `b` and `a`, or by `z` and its support. -/
def IDom (u : Nat) (z b a : multi.T) : Prop :=
  b < a ∧ ∀ c, b ≤ c → c ≤ a → ∀ x, x ∈ G u b → x < b ∨ ∃ y, y ∈ G u c ++ GZ u z ∧ x ≤ y

def WDom (z b a : multi.T) : Prop := ∀ u, IDom u z b a

theorem mem_GZ_self (u : Nat) (z : multi.T) : z ∈ GZ u z :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.2 rfl))

theorem mem_GZ_G {u : Nat} {z y : multi.T} (h : y ∈ G u z) : y ∈ GZ u z := by
  simp only [GZ, List.mem_append, List.mem_singleton]; exact Or.inl (Or.inr h)

theorem mem_GZ_Z (u : Nat) (z : multi.T) : Z ∈ GZ u z :=
  List.mem_append_right _ (List.mem_singleton.2 rfl)

theorem P_not_le_Z {v : V multi.T} {b : multi.T} (h : P v b ≤ Z) : False := by
  rcases h with h | h
  · exact T.not_lt_Z _ h
  · rw [compareT_PZ] at h; cases h

/-- A term sandwiched between two terms with the same leading vector has an equivalent
leading vector, and its tail is sandwiched between the tails. -/
theorem sandwich {v : V multi.T} {b a c : multi.T} (hl : P v b ≤ c) (hu : c ≤ P v a) :
    ∃ w d, c = P w d ∧ compareV w v = .eq ∧ b ≤ d ∧ d ≤ a := by
  cases c with
  | Z => exact (P_not_le_Z hl).elim
  | P w d =>
    refine ⟨w, d, rfl, ?_⟩
    rcases (T.P_le_P_iff v w b d).1 hl with h1 | ⟨h1, hbd⟩
    · rcases (T.P_le_P_iff w v d a).1 hu with h2 | ⟨h2, _⟩
      · exact absurd (V.lt_trans h1 h2) (V.lt_irrefl _)
      · exact absurd (V.lt_of_lt_of_eqv h1 h2) (V.lt_irrefl _)
    · rcases (T.P_le_P_iff w v d a).1 hu with h2 | ⟨h2, hda⟩
      · exact absurd (V.lt_of_eqv_of_lt h1 h2) (V.lt_irrefl _)
      · exact ⟨h2, hbd, hda⟩

theorem IDom_tail {u : Nat} {z b a : multi.T} (v : V multi.T) (hbt : b < P v b)
    (hs : IDom u z b a) : IDom u z (P v b) (P v a) := by
  refine ⟨T.P_tail_lt v hs.1, ?_⟩
  intro c hbc hca x hx
  obtain ⟨w, d, rfl, hwv, hbd, hda⟩ := sandwich hbc hca
  rcases mem_G_P.1 hx with ⟨j, huj, ⟨hne, rfl⟩ | hG⟩ | hG
  · have hj : compareT (V.get0 v j) (V.get0 w j) = .eq :=
      (V.eqv_iff_get0 v w).1 (V.eqv_symm hwv) j
    exact Or.inr ⟨V.get0 w j, List.mem_append_left _ (G_coord_mem huj (ne_Z_of_eqv hj hne)),
      T.le_of_eqv hj⟩
  · have hj : compareT (V.get0 v j) (V.get0 w j) = .eq :=
      (V.eqv_iff_get0 v w).1 (V.eqv_symm hwv) j
    obtain ⟨y', hy', he⟩ := G_eqv hj x hG
    exact Or.inr ⟨y', List.mem_append_left _ (G_in_coord huj hy'), T.le_of_eqv he⟩
  · rcases hs.2 d hbd hda x hG with hxb | ⟨y, hy, hxy⟩
    · exact Or.inl (T.lt_trans hxb hbt)
    · refine Or.inr ⟨y, ?_, hxy⟩
      rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_left _ (G_in_tail hy)
      · exact List.mem_append_right _ hy

/-! ### Normal forms from interval domination -/

theorem exists_G_not_lt (b : multi.T) : ∀ l : List multi.T, ¬ (∀ x, x ∈ l → x < b) →
    ∃ x, x ∈ l ∧ ¬ x < b
  | [], h => absurd (fun x hx => by cases hx) h
  | a :: as, h => by
    by_cases ha : a < b
    · obtain ⟨x, hx, hn⟩ := exists_G_not_lt b as (fun hall => h (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ha
        · exact hall x hx))
      exact ⟨x, List.mem_cons_of_mem a hx, hn⟩
    · exact ⟨a, List.mem_cons_self, ha⟩

theorem decide_all_lt (b : multi.T) : ∀ l : List multi.T,
    (∀ x, x ∈ l → x < b) ∨ ¬ (∀ x, x ∈ l → x < b)
  | [] => Or.inl (fun x hx => by cases hx)
  | a :: as => by
    by_cases ha : a < b
    · rcases decide_all_lt b as with h | h
      · exact Or.inl (fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ha
          · exact h x hx)
      · exact Or.inr (fun hall => h (fun x hx => hall x (List.mem_cons_of_mem a hx)))
    · exact Or.inr (fun hall => ha (hall a List.mem_cons_self))

theorem find_violating_source (u : Nat) (b c₀ : multi.T) :
    ∀ w, w ∈ G u c₀ → b ≤ w → ∃ c, c ∈ G u c₀ ∧ b ≤ c ∧ ∀ x, x ∈ G u c → x < b := by
  intro w
  induction w using (measure multi.T.size).wf.induction with
  | h w ih =>
    intro hw hbw
    rcases decide_all_lt b (G u w) with h | h
    · exact ⟨w, hw, hbw, h⟩
    · obtain ⟨x, hx, hn⟩ := exists_G_not_lt b (G u w) h
      exact ih x (G_size_lt u w x hx) (G_trans u c₀ w x hw hx) (T.le_of_not_lt hn)

theorem NFComp_of_IDom {u : Nat} {z b a : multi.T} (hb : NF b) (ha : NFComp u a)
    (hz : NFComp u z) (hs : IDom u z b a) (hzb : z < b) : NFComp u b := by
  have hZ : ∀ x, x ∈ GZ u z → x < b := by
    intro x hx
    simp only [GZ, List.mem_append, List.mem_singleton] at hx
    rcases hx with (rfl | hx) | rfl
    · exact hzb
    · exact T.lt_trans (hz.2 x hx) hzb
    · exact T.lt_of_le_of_lt (T.Z_le z) hzb
  have hup : ∀ x, x ∈ G u b → x < a := by
    intro x hx
    rcases hs.2 a (Or.inl hs.1) (T.le_refl a) x hx with hx | ⟨y, hy, hxy⟩
    · exact T.lt_trans hx hs.1
    · apply T.lt_of_le_of_lt hxy
      rcases List.mem_append.1 hy with hy | hy
      · exact ha.2 y hy
      · exact T.lt_trans (hZ y hy) hs.1
  refine ⟨hb, fun x hx => ?_⟩
  by_cases hxb : x < b
  · exact hxb
  · obtain ⟨c, hc, hbc, hcut⟩ := find_violating_source u b b x hx (T.le_of_not_lt hxb)
    exfalso
    rcases hs.2 c hbc (Or.inl (hup c hc)) c hc with hcc | ⟨y, hy, hcy⟩
    · exact T.lt_irrefl b (T.lt_of_le_of_lt hbc hcc)
    · have hyb : y < b := (List.mem_append.1 hy).elim (hcut y) (hZ y)
      exact T.lt_irrefl b (T.lt_of_le_of_lt hbc (T.lt_of_le_of_lt hcy hyb))

theorem NFComp_of_IDom_Z {u : Nat} {b a : multi.T} (hb : NF b) (ha : NFComp u a)
    (hs : IDom u Z b a) : NFComp u b := by
  cases b with
  | Z => exact NFComp_Z u
  | P v c => exact NFComp_of_IDom hb ha (NFComp_Z u) hs (T.Z_lt_P _ _)

theorem IDom_eliminate {u : Nat} {z b a : multi.T} (hb : IDom u z b a) (hz : IDom u Z z a)
    (hzb : z < b) : IDom u Z b a := by
  refine ⟨hb.1, fun c hbc hca x hx => ?_⟩
  rcases hb.2 c hbc hca x hx with hxc | ⟨y, hy, hxy⟩
  · exact Or.inl hxc
  · rcases List.mem_append.1 hy with hy | hy
    · exact Or.inr ⟨y, List.mem_append_left _ hy, hxy⟩
    · simp only [GZ, List.mem_append, List.mem_singleton] at hy
      rcases hy with (rfl | hy) | rfl
      · exact Or.inl (T.lt_of_le_of_lt hxy hzb)
      · rcases hz.2 c (Or.inl (T.lt_of_lt_of_le hzb hbc)) hca y hy with hyc | ⟨w, hw, hyw⟩
        · exact Or.inl (T.lt_of_le_of_lt hxy (T.lt_trans hyc hzb))
        · exact Or.inr ⟨w, hw, T.le_trans hxy hyw⟩
      · exact Or.inr ⟨Z, List.mem_append_right _ (mem_GZ_Z u Z), hxy⟩

theorem IDom_Z_mono {u : Nat} {z b a : multi.T} (h : IDom u Z b a) : IDom u z b a := by
  refine ⟨h.1, fun c hbc hca x hx => ?_⟩
  rcases h.2 c hbc hca x hx with hxb | ⟨y, hy, hxy⟩
  · exact Or.inl hxb
  · rcases List.mem_append.1 hy with hy | hy
    · exact Or.inr ⟨y, List.mem_append_left _ hy, hxy⟩
    · have hyZ : y = Z := by
        simp only [GZ, List.mem_append, List.mem_singleton] at hy
        rcases hy with (rfl | hy) | rfl
        · rfl
        · rw [G_Z] at hy; cases hy
        · rfl
      subst hyZ
      exact Or.inr ⟨Z, List.mem_append_right _ (mem_GZ_Z u z), hxy⟩

/-! ### Pivots inside an interval -/

theorem interval_pivot {low mid high : V multi.T} (i : Nat)
    (heqAbove : ∀ j, i < j → compareT (V.get0 low j) (V.get0 high j) = .eq)
    (hpivot : V.get0 low i < V.get0 high i) (hlm : low ≤ mid) (hmh : mid ≤ high) :
    (∀ j, i < j → compareT (V.get0 mid j) (V.get0 high j) = .eq) ∧
      V.get0 low i ≤ V.get0 mid i ∧ V.get0 mid i ≤ V.get0 high i := by
  rcases hlm with hlt | heq
  · obtain ⟨p, hpEq, hpLt⟩ := (V.lt_iff_pivot low mid).1 hlt
    have hpi : p ≤ i := by
      apply Nat.le_of_not_gt
      intro hip
      rcases hmh with h | h
      · obtain ⟨q, hqEq, hqLt⟩ := (V.lt_iff_pivot mid high).1 h
        rcases Nat.lt_trichotomy q p with hqp | rfl | hpq
        · have h1 := T.lt_of_lt_of_eqv hpLt (hqEq p hqp)
          exact T.lt_irrefl _ (T.lt_of_lt_of_eqv h1 (T.eqv_symm (heqAbove _ hip)))
        · have h1 := T.lt_trans hpLt hqLt
          exact T.lt_irrefl _ (T.lt_of_lt_of_eqv h1 (T.eqv_symm (heqAbove q hip)))
        · have h1 := T.lt_of_eqv_of_lt (hpEq q hpq) hqLt
          exact T.lt_irrefl _ (T.lt_of_lt_of_eqv h1 (T.eqv_symm (heqAbove q (by omega))))
      · have h1 := T.lt_of_lt_of_eqv hpLt ((V.eqv_iff_get0 mid high).1 h p)
        exact T.lt_irrefl _ (T.lt_of_lt_of_eqv h1 (T.eqv_symm (heqAbove p hip)))
    have hhigh : ∀ j, i < j → compareT (V.get0 mid j) (V.get0 high j) = .eq :=
      fun j hj => T.eqv_trans (T.eqv_symm (hpEq j (by omega))) (heqAbove j hj)
    refine ⟨hhigh, ?_, ?_⟩
    · rcases Nat.lt_or_eq_of_le hpi with h | h
      · exact T.le_of_eqv (hpEq i h)
      · rw [h] at hpLt; exact Or.inl hpLt
    · rcases hmh with h | h
      · obtain ⟨q, hqEq, hqLt⟩ := (V.lt_iff_pivot mid high).1 h
        have hqi : q ≤ i := by
          apply Nat.le_of_not_gt
          intro hiq
          exact T.lt_irrefl _ (T.lt_of_lt_of_eqv hqLt (T.eqv_symm (hhigh q hiq)))
        rcases Nat.lt_or_eq_of_le hqi with h | h
        · exact T.le_of_eqv (hqEq i h)
        · rw [h] at hqLt; exact Or.inl hqLt
      · exact T.le_of_eqv ((V.eqv_iff_get0 mid high).1 h i)
  · have hj := (V.eqv_iff_get0 low mid).1 heq
    refine ⟨fun j hjj => T.eqv_trans (T.eqv_symm (hj j)) (heqAbove j hjj), T.le_of_eqv (hj i),
      Or.inl (T.lt_of_eqv_of_lt (T.eqv_symm (hj i)) hpivot)⟩

theorem vle_of_P_le {v w : V multi.T} {a b : multi.T} (h : P v a ≤ P w b) : v ≤ w := by
  rcases (T.P_le_P_iff v w a b).1 h with h | ⟨h, _⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Interval domination for a change at a pivot coordinate: coordinates above the pivot are
kept, the pivot coordinate is dominated, and the visited coordinates below it are `Z` or `z`. -/
theorem IDom_pivot (u : Nat) (z : multi.T) {low high : V multi.T} (i : Nat)
    (hAbove : ∀ j, i < j → compareT (V.get0 low j) (V.get0 high j) = .eq)
    (hPivotLt : V.get0 low i < V.get0 high i)
    (hinner : u ≤ i → IDom u z (V.get0 low i) (V.get0 high i))
    (hBelow : ∀ q, u ≤ q → q < i → V.get0 low q = Z ∨ V.get0 low q = z) :
    IDom u z (P low Z) (P high Z) := by
  refine ⟨T.P_lt_P_of_vlt _ _ (V.lt_of_pivot i hAbove hPivotLt), ?_⟩
  intro c hlc hch
  cases c with
  | Z => exact (P_not_le_Z hlc).elim
  | P mid d =>
    have hB := interval_pivot i hAbove hPivotLt (vle_of_P_le hlc) (vle_of_P_le hch)
    intro x hx
    rcases mem_G_P.1 hx with ⟨q, huq, hq⟩ | ht
    · rcases Nat.lt_trichotomy q i with hqi | rfl | hiq
      · refine Or.inr ⟨x, List.mem_append_right _ ?_, T.le_refl x⟩
        rcases hBelow q huq hqi with hz | hz
        · rw [hz] at hq
          rcases hq with ⟨h, _⟩ | h
          · exact absurd rfl h
          · rw [G_Z] at h; cases h
        · rw [hz] at hq
          rcases hq with ⟨_, rfl⟩ | h
          · exact mem_GZ_self _ _
          · exact mem_GZ_G h
      · have hne : V.get0 low q ≠ Z := by
          rcases hq with ⟨h, _⟩ | h
          · exact h
          · intro hz; rw [hz, G_Z] at h; cases h
        have hmidne : V.get0 mid q ≠ Z := by
          intro h
          rw [h] at hB
          rcases hB.2.1 with h1 | h1
          · exact T.not_lt_Z _ h1
          · exact hne (T.eqv_Z_iff.1 h1)
        have hmem : V.get0 mid q ∈ G u (P mid d) ++ GZ u z :=
          List.mem_append_left _ (G_coord_mem huq hmidne)
        rcases hq with ⟨_, rfl⟩ | h
        · exact Or.inr ⟨V.get0 mid q, hmem, hB.2.1⟩
        · rcases (hinner huq).2 (V.get0 mid q) hB.2.1 hB.2.2 x h with hxl | ⟨y, hy, hxy⟩
          · exact Or.inr ⟨V.get0 mid q, hmem, Or.inl (T.lt_of_lt_of_le hxl hB.2.1)⟩
          · refine Or.inr ⟨y, ?_, hxy⟩
            rcases List.mem_append.1 hy with hy | hy
            · exact List.mem_append_left _ (G_in_coord huq hy)
            · exact List.mem_append_right _ hy
      · have he : compareT (V.get0 low q) (V.get0 mid q) = .eq :=
          T.eqv_trans (hAbove q hiq) (T.eqv_symm (hB.1 q hiq))
        rcases hq with ⟨hne, rfl⟩ | h
        · exact Or.inr ⟨V.get0 mid q,
            List.mem_append_left _ (G_coord_mem huq (ne_Z_of_eqv he hne)), T.le_of_eqv he⟩
        · obtain ⟨y', hy', he'⟩ := G_eqv he x h
          exact Or.inr ⟨y', List.mem_append_left _ (G_in_coord huq hy'), T.le_of_eqv he'⟩
    · rw [G_Z] at ht; cases ht

/-- Replacing the lowest nonzero coordinate by a dominated smaller one. -/
theorem IDom_set (u : Nat) (z : multi.T) {v : V multi.T} {i : Nat} (hi : i < v.length)
    (hzero : ∀ j, j < i → V.get0 v j = Z) {x : multi.T} (hx : x < V.get0 v i)
    (hinner : u ≤ i → IDom u z x (V.get0 v i)) : IDom u z (P (V.set v i x) Z) (P v Z) :=
  IDom_pivot u z i (V.get0_set_eqv_above v i x) (by rw [V.get0_set_same v i x hi]; exact hx)
    (by rw [V.get0_set_same v i x hi]; exact hinner)
    (fun q _ hq => Or.inl (by rw [V.get0_set_ne v i x q (Nat.ne_of_lt hq)]; exact hzero q hq))

/-! ### Closure under fundamental sequences -/

theorem NF_set {v : V multi.T} {i : Nat} (hi : i < v.length) (hs : NF (P v Z)) {x : multi.T}
    (hx : NFComp i x) : NF (P (V.set v i x) Z) := by
  apply NF_PZ_of_comps
  intro j
  by_cases hj : j = i
  · rw [hj, V.get0_set_same v i x hi]; exact hx
  · rw [V.get0_set_ne v i x j hj]; exact hs.comp j

theorem NF_mul {w : V multi.T} (hw : NF (P w Z)) : ∀ t, NF (T.mul (P w Z) t)
  | Z => NF.z
  | P _ t => by
    have hr := NF_mul hw t
    obtain ⟨hv, _, hg, _⟩ := hw.inv
    refine NF.p w _ hv hr hg ?_
    cases t with
    | Z => exact T.Z_le _
    | P _ _ => exact T.le_refl _

theorem G_mul_sub {u : Nat} {w : V multi.T} : ∀ t x, x ∈ G u (T.mul (P w Z) t) → x ∈ G u (P w Z)
  | Z, x, hx => by
    have : T.mul (P w Z) Z = Z := rfl
    rw [this, G_Z] at hx; cases hx
  | P y t, x, hx => by
    have : T.mul (P w Z) (P y t) = P w (T.mul (P w Z) t) := rfl
    rw [this] at hx
    rcases mem_G_P.1 hx with hv | ht
    · exact mem_G_P.2 (Or.inl hv)
    · exact G_mul_sub t x ht

theorem P_le_mul {w : V multi.T} (t : multi.T) (ht : t ≠ Z) : P w Z ≤ T.mul (P w Z) t := by
  cases t with
  | Z => exact absurd rfl ht
  | P y t' => exact T.P_tail_le w (T.Z_le _)

theorem IDom_mul {u : Nat} {w v : V multi.T} (t : multi.T) (hvec : w < v)
    (hbase : IDom u Z (P w Z) (P v Z)) : IDom u Z (T.mul (P w Z) t) (P v Z) := by
  refine ⟨mul_lt_of_vlt hvec t, ?_⟩
  intro c hmc hcv x hx
  cases t with
  | Z =>
    have : T.mul (P w Z) Z = Z := rfl
    rw [this, G_Z] at hx; cases hx
  | P ts add =>
    have hle := P_le_mul (w := w) (P ts add) (fun h => T.noConfusion h)
    exact (hbase.2 c (T.le_trans hle hmc) hcv x (G_mul_sub _ x hx)).imp_left
      (fun h => T.lt_of_lt_of_le h hle)

theorem tail_lt_of_NF : ∀ (a : multi.T) (v : V multi.T), NF (P v a) → a < P v a
  | Z, _, _ => T.Z_lt_P _ _
  | P w b, v, hs => by
    obtain ⟨_, ha, _, hh⟩ := hs.inv
    rcases (T.P_le_P_iff w v Z Z).1 hh with h | ⟨h, _⟩
    · exact T.P_lt_P_of_vlt _ _ h
    · exact T.P_lt_P_of_eqv h (tail_lt_of_NF b w ha)

theorem fund_one_master : ∀ s : multi.T, NF s → T.dom s = .one →
    NF (T.fund s Z) ∧ WDom Z (T.fund s Z) s
  | Z, _, hd => by rw [T.dom] at hd; cases hd
  | P v a, hs, hd => by
    obtain ⟨hv, ha, hg, hh⟩ := hs.inv
    by_cases haz : a = Z
    · subst haz
      rw [fund_PZ_none (dom_one_fnz hd)]
      refine ⟨NF.z, fun u => ⟨T.Z_lt_P _ _, ?_⟩⟩
      intro c _ _ x hx; rw [G_Z] at hx; cases hx
    · obtain ⟨hnf, hrel⟩ := fund_one_master a ha (by rwa [dom_tail v haz] at hd)
      rw [fund_tail v haz]
      have hf : NF (P v (T.fund a Z)) := NF.p v _ hv hnf hg (T.le_trans (hd_fund_le a Z) hh)
      exact ⟨hf, fun u => IDom_tail v (tail_lt_of_NF _ v hf) (hrel u)⟩

theorem fund_one_NFComp {u : Nat} {s : multi.T} (hs : NFComp u s) (hd : T.dom s = .one) :
    NFComp u (T.fund s Z) := by
  obtain ⟨hnf, hdom⟩ := fund_one_master s hs.1 hd
  exact NFComp_of_IDom_Z hnf hs (hdom u)

theorem fund_Omega_ne_Z : ∀ (s t : multi.T) {m : Nat}, T.dom s = .Omega m → T.fund s t ≠ Z
  | Z, _, _, hd => by rw [T.dom] at hd; cases hd
  | P v a, t, m, hd => by
    by_cases haz : a = Z
    · subst haz
      obtain ⟨i, hf, ⟨hdi, hi0, _⟩ | ⟨hdi, hmi⟩⟩ := dom_PZ_Omega_inv hd
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi0).symm⟩
        rw [fund_PZ_oneS hf hdi]; intro h; cases h
      · rw [fund_PZ_Omega_ge hf hdi (Nat.not_lt_of_le hmi)]; intro h; cases h
    · rw [fund_tail v haz]; intro h; cases h

theorem fund_Omega_strict_mono (s : multi.T) : ∀ {m : Nat}, T.dom s = .Omega m →
    ∀ x y, x < y → T.fund s x < T.fund s y := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro m hd x y hxy
    cases s with
    | Z => rw [T.dom] at hd; cases hd
    | P v a =>
      by_cases haz : a = Z
      · subst haz
        obtain ⟨i, hf, ⟨hdi, hi0, _⟩ | ⟨hdi, hmi⟩⟩ := dom_PZ_Omega_inv hd
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi0).symm⟩
          have hi := V.lt_length_of_fnz v (k + 1) hf
          rw [fund_PZ_oneS hf hdi, fund_PZ_oneS hf hdi]
          apply T.P_lt_P_of_vlt
          have hlen : k < (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)).length := by
            rw [V.length_set]; omega
          apply V.lt_of_pivot k
          · intro j hj
            rw [V.get0_set_ne _ k _ j (by omega), V.get0_set_ne _ k _ j (by omega)]
            exact T.eqv_refl _
          · rw [V.get0_set_same _ k _ hlen, V.get0_set_same _ k _ hlen]; exact hxy
        · have hi := V.lt_length_of_fnz v i hf
          rw [fund_PZ_Omega_ge hf hdi (Nat.not_lt_of_le hmi),
            fund_PZ_Omega_ge hf hdi (Nat.not_lt_of_le hmi)]
          apply T.P_lt_P_of_vlt
          apply V.lt_of_pivot i
          · intro j hj
            rw [V.get0_set_ne _ i _ j (by omega), V.get0_set_ne _ i _ j (by omega)]
            exact T.eqv_refl _
          · rw [V.get0_set_same _ i _ hi, V.get0_set_same _ i _ hi]
            exact ih _ (T.size_get0_lt_P v i Z) hdi x y hxy
      · rw [fund_tail v haz, fund_tail v haz]
        exact T.P_tail_lt v (ih a (T.size_lt_P_right v a) (by rwa [dom_tail v haz] at hd) x y hxy)

theorem iter_fund_lt_next {s : multi.T} {m : Nat} (hd : T.dom s = .Omega m) :
    ∀ t, T.iter (fun x => T.fund s x) t < T.fund s (T.iter (fun x => T.fund s x) t)
  | Z => by
    show Z < T.fund s Z
    exact T.Z_lt_of_ne (fund_Omega_ne_Z s Z hd)
  | P w t => fund_Omega_strict_mono s hd _ _ (iter_fund_lt_next hd t)

theorem fund_Omega_master (s : multi.T) : ∀ (z : multi.T) (m : Nat), NF s →
    T.dom s = .Omega m → NFComp (m - 1) z →
    NF (T.fund s z) ∧ WDom z (T.fund s z) s ∧ ∀ u, m ≤ u → IDom u Z (T.fund s z) s := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro z m hs hd hz
    cases s with
    | Z => rw [T.dom] at hd; cases hd
    | P v a =>
      obtain ⟨hv, ha, hg, hh⟩ := hs.inv
      by_cases haz : a = Z
      · subst haz
        obtain ⟨i, hf, ⟨hdi, hi0, hmi⟩ | ⟨hdi, hmi⟩⟩ := dom_PZ_Omega_inv hd
        · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi0).symm⟩
          subst hmi
          have hz' : NFComp k z := by
            have h1 := hz; rwa [Nat.add_sub_cancel] at h1
          obtain ⟨hne, hzero⟩ := V.fnz_some_spec v (k + 1) hf
          have hil := V.lt_length_of_fnz v (k + 1) hf
          have hc := fund_one_NFComp (hs.comp (k + 1)) hdi
          have hlt := fund_lt_self _ hne Z
          have hlen : k < (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)).length := by
            rw [V.length_set]; omega
          have hwk : V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z) k = z :=
            V.get0_set_same _ k z hlen
          have hwi : V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z) (k + 1) =
              T.fund (V.get0 v (k + 1)) Z := by
            rw [V.get0_set_ne _ k z (k + 1) (by omega), V.get0_set_same v (k + 1) _ hil]
          have hwo : ∀ j, k + 1 < j → compareT (V.get0 (V.set (V.set v (k + 1)
              (T.fund (V.get0 v (k + 1)) Z)) k z) j) (V.get0 v j) = .eq := by
            intro j hj
            rw [V.get0_set_ne _ k z j (by omega), V.get0_set_ne v (k + 1) _ j (by omega)]
            exact T.eqv_refl _
          have hwb : ∀ q, q < k + 1 →
              V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z) q = Z ∨
              V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z) q = z := by
            intro q hq
            by_cases hqk : q = k
            · right; rw [hqk, hwk]
            · left
              rw [V.get0_set_ne _ k z q hqk, V.get0_set_ne v (k + 1) _ q (by omega)]
              exact hzero q hq
          have hdom1 := fund_one_master _ (hv (k + 1)) hdi
          rw [fund_PZ_oneS hf hdi]
          refine ⟨NF_set hlen (NF_set hil hs hc) hz', fun u => ?_, fun u hu => ?_⟩
          · exact IDom_pivot u z (k + 1) hwo (by rw [hwi]; exact hlt)
              (fun _ => by rw [hwi]; exact IDom_Z_mono (hdom1.2 u)) (fun q _ hq => hwb q hq)
          · exact IDom_pivot u Z (k + 1) hwo (by rw [hwi]; exact hlt)
              (fun _ => by rw [hwi]; exact hdom1.2 u)
              (fun q huq hq => absurd (Nat.lt_of_le_of_lt hu (Nat.lt_of_le_of_lt huq hq))
                (Nat.lt_irrefl _))
        · obtain ⟨hne, hzero⟩ := V.fnz_some_spec v i hf
          have hil := V.lt_length_of_fnz v i hf
          obtain ⟨hnf, hwd, hhigh⟩ := ih _ (T.size_get0_lt_P v i Z) z m (hv i) hdi hz
          have hcomp : NFComp i (T.fund (V.get0 v i) z) :=
            NFComp_of_IDom_Z hnf (hs.comp i) (hhigh i hmi)
          rw [fund_PZ_Omega_ge hf hdi (Nat.not_lt_of_le hmi)]
          exact ⟨NF_set hil hs hcomp, fun u => IDom_set u z hil hzero (hwd u).1 (fun _ => hwd u),
            fun u hu => IDom_set u Z hil hzero (hwd u).1 (fun _ => hhigh u hu)⟩
      · obtain ⟨hnf, hwd, hhigh⟩ :=
          ih a (T.size_lt_P_right v a) z m ha (by rwa [dom_tail v haz] at hd) hz
        rw [fund_tail v haz]
        have hf : NF (P v (T.fund a z)) := NF.p v _ hv hnf hg (T.le_trans (hd_fund_le a z) hh)
        have hbt := tail_lt_of_NF _ v hf
        exact ⟨hf, fun u => IDom_tail v hbt (hwd u), fun u hu => IDom_tail v hbt (hhigh u hu)⟩

theorem fund_iter_NFComp {u m : Nat} {s : multi.T} (hum : u < m) (hs : NFComp u s)
    (hd : T.dom s = .Omega m) : ∀ t,
    NFComp u (T.fund s (T.iter (fun x => T.fund s x) t)) ∧
      WDom Z (T.fund s (T.iter (fun x => T.fund s x) t)) s := by
  have hsne : s ≠ Z := by intro h; rw [h, T.dom] at hd; cases hd
  have step : ∀ r, NFComp u (T.iter (fun x => T.fund s x) r) →
      WDom Z (T.iter (fun x => T.fund s x) r) s →
      NFComp u (T.fund s (T.iter (fun x => T.fund s x) r)) ∧
        WDom Z (T.fund s (T.iter (fun x => T.fund s x) r)) s := by
    intro r hr hw
    obtain ⟨hnf, hwd, _⟩ := fund_Omega_master s _ m hs.1 hd
      (NFComp_mono (Nat.le_pred_of_lt hum) hr)
    have hlt := iter_fund_lt_next hd r
    exact ⟨NFComp_of_IDom hnf hs hr (hwd u) hlt, fun v => IDom_eliminate (hwd v) (hw v) hlt⟩
  intro t
  induction t using (measure multi.T.size).wf.induction with
  | h t ih =>
    cases t with
    | Z =>
      refine step Z (NFComp_Z u) (fun v => ⟨T.Z_lt_of_ne hsne, ?_⟩)
      intro c _ _ x hx
      have : T.iter (fun x => T.fund s x) Z = Z := rfl
      rw [this, G_Z] at hx; cases hx
    | P w t' =>
      obtain ⟨h1, h2⟩ := ih t' (T.size_lt_P_right w t')
      exact step (P w t') h1 h2

theorem fund_omega_master (s : multi.T) : ∀ t : multi.T, NF s → T.dom s = .omega →
    NF (T.fund s t) ∧ WDom Z (T.fund s t) s := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro t hs hd
    cases s with
    | Z => rw [T.dom] at hd; cases hd
    | P v a =>
      obtain ⟨hv, ha, hg, hh⟩ := hs.inv
      by_cases haz : a = Z
      · subst haz
        obtain ⟨i, hf, ⟨hdi, hi0⟩ | hdi | ⟨m, hdi, hmi⟩⟩ := dom_PZ_omega_inv hd
        · subst hi0
          obtain ⟨hne, _⟩ := V.fnz_some_spec v 0 hf
          have hil := V.lt_length_of_fnz v 0 hf
          have hu := fund_one_NFComp (hs.comp 0) hdi
          have hdom1 := fund_one_master _ (hv 0) hdi
          have hlt := fund_lt_self _ hne Z
          rw [fund_PZ_one0 hf hdi]
          refine ⟨NF_mul (NF_set hil hs hu) t, fun u => IDom_mul t (set_lt hil hlt) ?_⟩
          exact IDom_set u Z hil (fun j hj => absurd hj (Nat.not_lt_zero j)) hlt
            (fun _ => hdom1.2 u)
        · obtain ⟨hne, hzero⟩ := V.fnz_some_spec v i hf
          have hil := V.lt_length_of_fnz v i hf
          obtain ⟨hnf, hwd⟩ := ih _ (T.size_get0_lt_P v i Z) t (hv i) hdi
          have hcomp := NFComp_of_IDom_Z hnf (hs.comp i) (hwd i)
          rw [fund_PZ_omega hf hdi]
          exact ⟨NF_set hil hs hcomp, fun u => IDom_set u Z hil hzero (hwd u).1 (fun _ => hwd u)⟩
        · obtain ⟨hne, hzero⟩ := V.fnz_some_spec v i hf
          have hil := V.lt_length_of_fnz v i hf
          have him : i < m := Nat.lt_of_not_le hmi
          obtain ⟨hcomp, hwd⟩ := fund_iter_NFComp him (hs.comp i) hdi t
          rw [fund_PZ_Omega_lt hf hdi him]
          exact ⟨NF_set hil hs hcomp, fun u => IDom_set u Z hil hzero (hwd u).1 (fun _ => hwd u)⟩
      · obtain ⟨hnf, hwd⟩ := ih a (T.size_lt_P_right v a) t ha (by rwa [dom_tail v haz] at hd)
        rw [fund_tail v haz]
        have hf : NF (P v (T.fund a t)) := NF.p v _ hv hnf hg (T.le_trans (hd_fund_le a t) hh)
        exact ⟨hf, fun u => IDom_tail v (tail_lt_of_NF _ v hf) (hwd u)⟩

theorem NF_fund (s t : multi.T) (hs : NF s) (ht : ∀ m, T.dom s = .Omega m → NFComp (m - 1) t) :
    NF (T.fund s t) := by
  cases hd : T.dom s with
  | zero => rw [eq_Z_of_dom_zero hd, fund_Z]; exact NF.z
  | one => rw [fund_one_irrel s hd]; exact (fund_one_master s hs hd).1
  | omega => exact (fund_omega_master s t hs hd).1
  | Omega m => exact (fund_Omega_master s t m hs hd (ht m hd)).1

/-! ### Finite terms -/

theorem G_ofNat (u : Nat) : ∀ n, G u (T.ofNat n) = []
  | 0 => G_Z u
  | n + 1 => by
    show G u (P V.emp (T.ofNat n)) = []
    rw [G, G_ofNat u n]; rfl

theorem NFComp_ofNat (u : Nat) : ∀ n, NFComp u (T.ofNat n)
  | 0 => NFComp_Z u
  | n + 1 => by
    refine ⟨NF.p _ _ (fun _ => NF.z) (NFComp_ofNat u n).1
      (fun j y hy => by rw [show V.get0 V.emp j = Z from rfl, G_Z] at hy; cases hy) ?_, ?_⟩
    · cases n with
      | zero => exact T.Z_le _
      | succ n => exact T.le_refl _
    · intro y hy; rw [G_ofNat] at hy; cases hy

/-! ### Cofinality -/

theorem mul_cofinal {w : V multi.T} :
    ∀ d, NF d → T.hd d ≤ P w Z → ∃ m, d < T.mul (P w Z) (T.ofNat m)
  | Z, _, _ => ⟨1, T.Z_lt_P _ _⟩
  | P y e, hd, hh => by
    obtain ⟨_, he, _, hhe⟩ := hd.inv
    rcases (T.P_le_P_iff y w Z Z).1 hh with hy | ⟨hy, _⟩
    · exact ⟨1, T.P_lt_P_of_vlt _ _ hy⟩
    · have hhe' : T.hd e ≤ P w Z :=
        T.le_trans hhe (Or.inr ((T.P_eqv_iff y w Z Z).2 ⟨hy, compareT_ZZ⟩))
      obtain ⟨m, hm⟩ := mul_cofinal e he hhe'
      exact ⟨m + 1, T.P_lt_P_of_eqv hy hm⟩

/-- Iterates of the fundamental sequence of an `Omega m`-domain term are cofinal below it
among the terms above their support at index `m - 1`. -/
theorem iteration_cofinal {a : multi.T} {m : Nat} (ha : NF a) (hd : T.dom a = .Omega m) :
    ∀ b, NFComp (m - 1) b → b < a →
      ∃ n, b < T.fund a (T.iter (fun x => T.fund a x) (T.ofNat n)) := by
  intro b
  induction b using (measure multi.T.size).wf.induction with
  | h b ih =>
    intro hbcomp hba
    have descend : ∀ cur, NF cur → T.dom cur = .Omega m → ∀ tgt, NF tgt → tgt < cur →
        (∀ x, x ∈ G (m - 1) tgt → x ∈ G (m - 1) b) →
        ∃ n, tgt < T.fund cur (T.iter (fun x => T.fund a x) (T.ofNat n)) := by
      intro cur hcur
      induction hcur with
      | z => intro h; rw [T.dom] at h; cases h
      | p v c _ hc _ _ ihv ihc =>
        intro hcdom tgt htgnf htgc hmem
        by_cases hcz : c = Z
        · subst hcz
          obtain ⟨i, hf, ⟨hdk, hi0, hmi⟩ | ⟨hdi, hmi⟩⟩ := dom_PZ_Omega_inv hcdom
          · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi0).symm⟩
            have hmk : m - 1 = k := by rw [hmi, Nat.add_sub_cancel]
            obtain ⟨_, hzero⟩ := V.fnz_some_spec v (k + 1) hf
            have hi := V.lt_length_of_fnz v (k + 1) hf
            have hlen : k < (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)).length := by
              rw [V.length_set]; omega
            have hwk : ∀ z, V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z) k
                = z := fun z => V.get0_set_same _ k z hlen
            have hwi : ∀ z, V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z)
                (k + 1) = T.fund (V.get0 v (k + 1)) Z := by
              intro z
              rw [V.get0_set_ne _ k z (k + 1) (by omega), V.get0_set_same v (k + 1) _ hi]
            have hwo : ∀ z j, k + 1 < j → compareT (V.get0 (V.set (V.set v (k + 1)
                (T.fund (V.get0 v (k + 1)) Z)) k z) j) (V.get0 v j) = .eq := by
              intro z j hj
              rw [V.get0_set_ne _ k z j (by omega), V.get0_set_ne v (k + 1) _ j (by omega)]
              exact T.eqv_refl _
            simp only [fund_PZ_oneS hf hdk]
            cases tgt with
            | Z => exact ⟨0, T.Z_lt_P _ _⟩
            | P w tail =>
              have hw := vlt_of_P_lt htgc
              obtain ⟨q, hAbove, hLt⟩ := (V.lt_iff_pivot w v).1 hw
              have hmq := pivot_above_zero hzero hLt
              rcases Nat.lt_or_eq_of_le hmq with hmq | hmq
              · refine ⟨0, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot q ?_ ?_)⟩
                · intro j hj; exact T.eqv_trans (hAbove j hj) (T.eqv_symm (hwo _ j (by omega)))
                · exact T.lt_of_lt_of_eqv hLt (T.eqv_symm (hwo _ q hmq))
              · subst hmq
                rcases fund_one_upper _ hdk _ hLt with hstrict | heq
                · refine ⟨0, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot (k + 1) ?_ ?_)⟩
                  · intro j hj; exact T.eqv_trans (hAbove j hj) (T.eqv_symm (hwo _ j hj))
                  · rw [hwi]; exact hstrict
                · have hpiv : ∀ z, V.get0 w k < z → P w tail <
                      P (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k z) Z := by
                    intro z hz
                    apply T.P_lt_P_of_vlt
                    apply V.lt_of_pivot k
                    · intro j hj
                      rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hj' | hj'
                      · exact T.eqv_trans (hAbove j hj') (T.eqv_symm (hwo _ j hj'))
                      · rw [← hj', hwi]; exact heq
                    · rw [hwk]; exact hz
                  by_cases hwz : V.get0 w k = Z
                  · refine ⟨1, hpiv _ ?_⟩
                    rw [hwz]
                    exact T.Z_lt_of_ne (fund_Omega_ne_Z a _ hd)
                  · have hcMem := hmem _ (G_coord_mem (Nat.le_of_eq hmk) hwz)
                    have hcomp : NFComp (m - 1) (V.get0 w k) := by
                      rw [hmk]; exact htgnf.comp k
                    obtain ⟨n, hn⟩ := ih _ (G_size_lt (m - 1) b _ hcMem) hcomp
                      (T.lt_trans (hbcomp.2 _ hcMem) hba)
                    exact ⟨n + 1, hpiv _ (by rw [T.iter_ofNat_succ]; exact hn)⟩
          · obtain ⟨_, hzero⟩ := V.fnz_some_spec v i hf
            have hi := V.lt_length_of_fnz v i hf
            have hmi' : m - 1 ≤ i := Nat.le_trans (Nat.sub_le m 1) hmi
            simp only [fund_PZ_Omega_ge hf hdi (Nat.not_lt_of_le hmi)]
            cases tgt with
            | Z => exact ⟨0, T.Z_lt_P _ _⟩
            | P w tail =>
              have hw := vlt_of_P_lt htgc
              obtain ⟨q, hAbove, hLt⟩ := (V.lt_iff_pivot w v).1 hw
              have hiq := pivot_above_zero hzero hLt
              rcases Nat.lt_or_eq_of_le hiq with hiq | hiq
              · refine ⟨0, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot q ?_ ?_)⟩
                · intro j hj
                  exact T.eqv_trans (hAbove j hj)
                    (T.eqv_symm (V.get0_set_eqv_above v i _ j (by omega)))
                · exact T.lt_of_lt_of_eqv hLt (T.eqv_symm (V.get0_set_eqv_above v i _ q hiq))
              · subst hiq
                obtain ⟨n, hn⟩ := ihv i hdi (V.get0 w i) (htgnf.inv.1 i) hLt
                  (fun x hx => hmem x (G_in_coord hmi' hx))
                refine ⟨n, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot i ?_ ?_)⟩
                · intro j hj
                  exact T.eqv_trans (hAbove j hj) (T.eqv_symm (V.get0_set_eqv_above v i _ j hj))
                · rw [V.get0_set_same v i _ hi]; exact hn
        · have hdc : T.dom c = .Omega m := by rwa [dom_tail v hcz] at hcdom
          simp only [fund_tail v hcz]
          cases tgt with
          | Z => exact ⟨0, T.Z_lt_P _ _⟩
          | P w tail =>
            rcases (T.P_lt_P_iff w v tail c).1 htgc with hwv | ⟨hwv, htl⟩
            · exact ⟨0, T.P_lt_P_of_vlt _ _ hwv⟩
            · obtain ⟨n, hn⟩ := ihc hdc tail htgnf.inv.2.1 htl
                (fun x hx => hmem x (G_in_tail hx))
              exact ⟨n, T.P_lt_P_of_eqv hwv hn⟩
    exact descend a ha hd b hbcomp.1 hba (fun _ hx => hx)

theorem omega_cofinal (a : multi.T) : NF a → T.dom a = .omega →
    ∀ b, NF b → b < a → ∃ n, b < T.fund a (T.ofNat n) := by
  induction a using (measure multi.T.size).wf.induction with
  | h a ih =>
    intro ha hda b hb hba
    cases a with
    | Z => rw [T.dom] at hda; cases hda
    | P v c =>
      obtain ⟨hv, hc, _, _⟩ := ha.inv
      by_cases hcz : c = Z
      · subst hcz
        obtain ⟨i, hf, hcase⟩ := dom_PZ_omega_inv hda
        obtain ⟨hne, hzero⟩ := V.fnz_some_spec v i hf
        have hi := V.lt_length_of_fnz v i hf
        -- cofinality inherited from the lowest nonzero coordinate
        have lift : ∀ f : Nat → multi.T,
            (∀ x, NFComp i x → x < V.get0 v i → ∃ n, x < f n) →
            ∃ n, b < P (V.set v i (f n)) Z := by
          intro f hfc
          cases b with
          | Z => exact ⟨0, T.Z_lt_P _ _⟩
          | P w e =>
            have hy := vlt_of_P_lt hba
            obtain ⟨p, hpeq, hplt⟩ := (V.lt_iff_pivot w v).1 hy
            have hip := pivot_above_zero hzero hplt
            rcases Nat.lt_or_eq_of_le hip with hip | hip
            · refine ⟨0, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot p ?_ ?_)⟩
              · intro j hj
                exact T.eqv_trans (hpeq j hj)
                  (T.eqv_symm (V.get0_set_eqv_above v i _ j (by omega)))
              · exact T.lt_of_lt_of_eqv hplt (T.eqv_symm (V.get0_set_eqv_above v i _ p hip))
            · subst hip
              obtain ⟨n, hn⟩ := hfc _ (hb.comp i) hplt
              refine ⟨n, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot i ?_ ?_)⟩
              · intro j hj
                exact T.eqv_trans (hpeq j hj) (T.eqv_symm (V.get0_set_eqv_above v i _ j hj))
              · rw [V.get0_set_same v i _ hi]; exact hn
        rcases hcase with ⟨hd, hi0⟩ | hd | ⟨m, hd, hmi⟩
        · subst hi0
          simp only [fund_PZ_one0 hf hd]
          cases b with
          | Z => exact ⟨1, T.Z_lt_P _ _⟩
          | P y e =>
            have hy := vlt_of_P_lt hba
            obtain ⟨p, hpeq, hplt⟩ := (V.lt_iff_pivot y v).1 hy
            have hset : ∀ j, 0 < j → compareT (V.get0 (V.set v 0 (T.fund (V.get0 v 0) Z)) j)
                (V.get0 v j) = .eq := V.get0_set_eqv_above v 0 _
            rcases Nat.eq_zero_or_pos p with hp | hp
            · subst hp
              rcases fund_one_upper _ hd _ hplt with h0 | h0
              · refine ⟨1, T.P_lt_P_of_vlt _ _ ?_⟩
                apply V.lt_of_pivot 0
                · intro j hj; exact T.eqv_trans (hpeq j hj) (T.eqv_symm (hset j hj))
                · rw [V.get0_set_same v 0 _ hi]; exact h0
              · have hyv : compareV y (V.set v 0 (T.fund (V.get0 v 0) Z)) = .eq := by
                  rw [V.eqv_iff_get0]
                  intro j
                  rcases Nat.eq_zero_or_pos j with hj | hj
                  · rw [hj, V.get0_set_same v 0 _ hi]; exact h0
                  · exact T.eqv_trans (hpeq j hj) (T.eqv_symm (hset j hj))
                obtain ⟨_, he, _, hhe⟩ := hb.inv
                obtain ⟨m, hm⟩ := mul_cofinal e he
                  (T.le_trans hhe (Or.inr ((T.P_eqv_iff _ _ Z Z).2 ⟨hyv, compareT_ZZ⟩)))
                exact ⟨m + 1, T.P_lt_P_of_eqv hyv hm⟩
            · refine ⟨1, T.P_lt_P_of_vlt _ _ ?_⟩
              apply V.lt_of_pivot p
              · intro j hj; exact T.eqv_trans (hpeq j hj) (T.eqv_symm (hset j (by omega)))
              · exact T.lt_of_lt_of_eqv hplt (T.eqv_symm (hset p hp))
        · simp only [fund_PZ_omega hf hd]
          exact lift (fun n => T.fund (V.get0 v i) (T.ofNat n))
            (fun x hx hxi => ih _ (T.size_get0_lt_P v i Z) (hv i) hd x hx.1 hxi)
        · have him : i < m := Nat.lt_of_not_le hmi
          simp only [fund_PZ_Omega_lt hf hd him]
          exact lift (fun n => T.fund (V.get0 v i)
            (T.iter (fun x => T.fund (V.get0 v i) x) (T.ofNat n)))
            (fun x hx hxi => iteration_cofinal (hv i) hd x
              (NFComp_mono (Nat.le_pred_of_lt him) hx) hxi)
      · simp only [fund_tail v hcz]
        have hdc : T.dom c = .omega := by rwa [dom_tail v hcz] at hda
        cases b with
        | Z => exact ⟨0, T.Z_lt_P _ _⟩
        | P y e =>
          rcases (T.P_lt_P_iff y v e c).1 hba with hy | ⟨hy, he⟩
          · exact ⟨0, T.P_lt_P_of_vlt _ _ hy⟩
          · obtain ⟨n, hn⟩ := ih c (T.size_lt_P_right v c) hc hdc e hb.inv.2.1 he
            exact ⟨n, T.P_lt_P_of_eqv hy hn⟩

/-! ### The countable bound `P[0, 1]` -/

/-- `Ω_1`, the bound of the countable terms. -/
def otb : multi.T := P (V.snoc (P V.emp Z) (V.snoc Z V.emp)) Z

theorem get0_otb_vec (j : Nat) :
    V.get0 (V.snoc (P V.emp Z) (V.snoc Z V.emp) : V multi.T) j =
      if j = 1 then P V.emp Z else Z := by
  show (if j = 1 then P V.emp Z else (if j = 0 then Z else Z)) = _
  by_cases h : j = 1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]; split <;> rfl

/-- Below `Ω_1` only the lowest coordinate can be nonzero. -/
theorem coords_zero_of_lt_otb {v : V multi.T} {a : multi.T} (h : P v a < otb) :
    ∀ j, 0 < j → V.get0 v j = Z := by
  have hv := vlt_of_P_lt h
  obtain ⟨q, hAbove, hLt⟩ := (V.lt_iff_pivot _ _).1 hv
  rw [get0_otb_vec] at hLt
  have hq1 : q = 1 := by
    by_cases hq : q = 1
    · exact hq
    · rw [ite_eq_right hq] at hLt; exact absurd hLt (T.not_lt_Z _)
  subst hq1
  rw [ite_eq_left rfl] at hLt
  have h1 : V.get0 v 1 = Z := by
    cases hc : V.get0 v 1 with
    | Z => rfl
    | P w c =>
      rw [hc] at hLt
      obtain ⟨p, _, hp⟩ := (V.lt_iff_pivot w V.emp).1 (vlt_of_P_lt hLt)
      exact absurd hp (T.not_lt_Z _)
  intro j hj
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hj | hj
  · have := hAbove j hj
    rw [get0_otb_vec, ite_eq_right (by omega)] at this
    exact T.eqv_Z_iff.1 this
  · rw [← hj]; exact h1

theorem dom_not_Omega : ∀ s : multi.T, NF s → s < otb → ∀ m, T.dom s ≠ .Omega m
  | Z, _, _, _, h => by rw [T.dom] at h; cases h
  | P v a, hs, hb, m, hO => by
    by_cases haz : a = Z
    · subst haz
      obtain ⟨i, hf, ⟨_, hi0, _⟩ | ⟨hdi, hmi⟩⟩ := dom_PZ_Omega_inv hO
      · exact (V.fnz_some_spec v i hf).1 (coords_zero_of_lt_otb hb i hi0)
      · rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          exact absurd (Nat.lt_of_lt_of_le (dom_Omega_pos _ hdi) hmi) (Nat.lt_irrefl 0)
        · exact (V.fnz_some_spec v i hf).1 (coords_zero_of_lt_otb hb i hi)
    · exact dom_not_Omega a hs.inv.2.1 (T.lt_trans (tail_lt_of_NF a v hs) hb) m
        (by rwa [dom_tail v haz] at hO)

theorem cofinal (a b : multi.T) (ha : NF a ∧ a < otb) (hb : NF b ∧ b < otb) (hba : b < a) :
    ∃ n, b ≤ T.fund a (T.ofNat n) := by
  cases hd : T.dom a with
  | zero => rw [eq_Z_of_dom_zero hd] at hba; exact absurd hba (T.not_lt_Z _)
  | one => exact ⟨0, fund_one_upper a hd b hba⟩
  | omega =>
    obtain ⟨n, hn⟩ := omega_cofinal a ha.1 hd b hb.1 hba
    exact ⟨n, Or.inl hn⟩
  | Omega m => exact absurd hd (dom_not_Omega a ha.1 ha.2 m)

/-! ### Bases and the invariant -/

theorem get0_LF : ∀ n j, V.get0 (T.LF n) j = if j = n ∧ n ≠ 0 then T.ofNat 1 else Z
  | 0, j => by
    rw [T.LF, ite_eq_right (show ¬(j = 0 ∧ (0 : Nat) ≠ 0) from fun h => h.2 rfl)]; rfl
  | 1, j => by
    rw [T.LF]
    by_cases h : j = 1
    · rw [h, ite_eq_left (show (1 : Nat) = 1 ∧ (1 : Nat) ≠ 0 from ⟨rfl, Nat.one_ne_zero⟩)]; rfl
    · rw [ite_eq_right (show ¬(j = 1 ∧ (1 : Nat) ≠ 0) from fun h' => h h'.1)]
      show (if j = 1 then T.ofNat 1 else (if j = 0 then Z else Z)) = Z
      rw [ite_eq_right h]; split <;> rfl
  | n + 2, j => by
    rw [T.LF, V.get0_append, get0_LF (n + 1)]
    have hlen : (V.snoc Z V.emp : V multi.T).length = 1 := rfl
    rw [hlen]
    by_cases hj : j < 1
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [ite_eq_left hj, ite_eq_right (show ¬((0 : Nat) = n + 2 ∧ n + 2 ≠ 0) from
        fun h => Nat.succ_ne_zero (n + 1) h.1.symm)]
      rfl
    · rw [ite_eq_right hj]
      by_cases hjn : j = n + 2
      · rw [ite_eq_left (show j - 1 = n + 1 ∧ n + 1 ≠ 0 from ⟨by omega, Nat.succ_ne_zero n⟩),
          ite_eq_left (show j = n + 2 ∧ n + 2 ≠ 0 from ⟨hjn, Nat.succ_ne_zero (n + 1)⟩)]
      · rw [ite_eq_right (show ¬ (j - 1 = n + 1 ∧ n + 1 ≠ 0) from
            fun h => hjn (by have := h.1; omega)),
          ite_eq_right (show ¬(j = n + 2 ∧ n + 2 ≠ 0) from fun h => hjn h.1)]
    exact Nat.succ_ne_zero n

theorem emp_lt_LF (n : Nat) (hn : n ≠ 0) : (V.emp : V multi.T) < T.LF n := by
  apply V.lt_of_pivot n
  · intro j hj
    rw [get0_LF, ite_eq_right (fun h => Nat.ne_of_gt hj h.1)]
    exact compareT_ZZ
  · rw [get0_LF, ite_eq_left ⟨rfl, hn⟩]
    exact T.Z_lt_P _ _

theorem NFComp_PLF (u n : Nat) : NFComp u (P (T.LF n) Z) := by
  have hc : ∀ j, NFComp j (V.get0 (T.LF n) j) := by
    intro j; rw [get0_LF]; split
    · exact NFComp_ofNat j 1
    · exact NFComp_Z j
  refine ⟨NF_PZ_of_comps hc, fun y hy => ?_⟩
  rcases mem_G_P.1 hy with ⟨j, _, hj⟩ | ht
  · rw [get0_LF] at hj
    split at hj
    · rename_i h
      rcases hj with ⟨_, rfl⟩ | hj
      · exact T.P_lt_P_of_vlt _ _ (emp_lt_LF n h.2)
      · rw [G_ofNat] at hj; cases hj
    · rcases hj with ⟨hz, _⟩ | hj
      · exact absurd rfl hz
      · rw [G_Z] at hj; cases hj
  · rw [G_Z] at ht; cases ht

theorem get0_single (x : multi.T) (j : Nat) :
    V.get0 (V.snoc x V.emp : V multi.T) j = if j = 0 then x else Z := by
  show (if j = 0 then x else Z) = _
  rfl

theorem Inv_base (n : Nat) : NF (sys.base n) ∧ sys.base n < otb := by
  constructor
  · apply NF_PZ_of_comps
    intro j
    show NFComp j (V.get0 (V.snoc (P (T.LF n) Z) V.emp) j)
    rw [get0_single]; split
    · exact NFComp_PLF j n
    · exact NFComp_Z j
  · apply T.P_lt_P_of_vlt
    apply V.lt_of_pivot 1
    · intro j hj
      show compareT (V.get0 (V.snoc (P (T.LF n) Z) V.emp) j) _ = .eq
      rw [get0_single, ite_eq_right (by omega), get0_otb_vec, ite_eq_right (by omega)]
      exact compareT_ZZ
    · show V.get0 (V.snoc (P (T.LF n) Z) V.emp) 1 < _
      rw [get0_single, ite_eq_right (by omega), get0_otb_vec, ite_eq_left rfl]
      exact T.Z_lt_P _ _

theorem le_base (s : multi.T) (hs : s < otb) : ∃ n, s ≤ sys.base n := by
  cases s with
  | Z => exact ⟨0, T.Z_le _⟩
  | P v a =>
    have hz := coords_zero_of_lt_otb hs
    have h0 : ∃ n, V.get0 v 0 < P (T.LF n) Z := by
      cases hx : V.get0 v 0 with
      | Z => exact ⟨1, T.Z_lt_P _ _⟩
      | P w b =>
        refine ⟨w.length + 1, T.P_lt_P_of_vlt _ _ (V.lt_of_pivot (w.length + 1) ?_ ?_)⟩
        · intro j hj
          rw [V.get0_ge w j (by omega), get0_LF, ite_eq_right (fun h => by omega)]
          exact compareT_ZZ
        · rw [V.get0_ge w _ (by omega), get0_LF, ite_eq_left ⟨rfl, by omega⟩]
          exact T.Z_lt_P _ _
    obtain ⟨n, hn⟩ := h0
    refine ⟨n, Or.inl (T.P_lt_P_of_vlt _ _ (V.lt_of_pivot 0 ?_ ?_))⟩
    · intro j hj
      show compareT _ (V.get0 (V.snoc (P (T.LF n) Z) V.emp) j) = .eq
      rw [hz j hj, get0_single, ite_eq_right (by omega)]
      exact compareT_ZZ
    · show _ < V.get0 (V.snoc (P (T.LF n) Z) V.emp) 0
      rw [get0_single, ite_eq_left rfl]
      exact hn

theorem otb_norm : multi.T.norm otb = otb := rfl

theorem Inv_fund (s : multi.T) (hs : NF s ∧ s < otb) (n : Nat) :
    NF (T.fund s (T.ofNat n)) ∧ T.fund s (T.ofNat n) < otb := by
  refine ⟨NF_fund s _ hs.1 (fun m _ => NFComp_ofNat (m - 1) n), ?_⟩
  by_cases hsz : s = Z
  · subst hsz; rw [fund_Z]; exact T.Z_lt_P _ _
  · exact T.lt_trans (fund_lt_self s hsz _) hs.2

theorem Inv_norm (s : multi.T) (hs : NF s ∧ s < otb) :
    NF (multi.T.norm s) ∧ multi.T.norm s < otb := by
  refine ⟨NF_norm hs.1, ?_⟩
  have := (multi.T.lt_norm_iff s otb).1 hs.2
  rwa [otb_norm] at this

end old

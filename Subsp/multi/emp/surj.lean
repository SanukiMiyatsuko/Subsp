import Subsp.multi.Uncollapse
import Subsp.multi.emp.trans

/-! Surjectivity of the `emp` translation onto the Buchholz normal forms below `ψ_0(Ω^ω)`. -/

namespace emp

open MT

/-- All coordinates are normal forms. -/
def NFc (v : multi.V multi.T) : Prop := ∀ j, NF (multi.V.get0 v j)

theorem NFc.good {v : multi.V multi.T} (h : NFc v) : ∀ j, Good (multi.V.get0 v j) :=
  fun j => NF_good (h j)

theorem NFc.mono {v w : multi.V multi.T} (hv : NFc v) (hw : NFc w) :
    ∀ j, multi.V.get0 v j < multi.V.get0 w j → tr (multi.V.get0 v j) < tr (multi.V.get0 w j) :=
  fun j h => tr_mono (hv j) (hw j) h

/-! ### Reflection of the vector order -/

theorem trV_reflect_lt {v w : multi.V multi.T} (hv : NFc v) (hw : NFc w) (h : trV v < trV w) :
    v < w := by
  rcases multi.V.lt_trichotomy v w with hvw | hvw | hwv
  · exact hvw
  · have he : trV v = trV w := by rw [← trV_norm v, hvw, trV_norm]
    rw [he] at h; exact absurd h (lt_irrefl_thm _)
  · exact absurd h (lt_asymm_thm (trV_lt hw.good hv.good (hw.mono hv) hwv))

theorem trV_reflect_le {v w : multi.V multi.T} (hv : NFc v) (hw : NFc w) (h : trV v ≤ trV w) :
    v ≤ w := by
  rcases multi.V.lt_trichotomy v w with hvw | hvw | hwv
  · exact Or.inl hvw
  · exact Or.inr ((multi.compareV_eq_iff v w).2 hvw)
  · rcases h with h | h
    · exact absurd h (lt_asymm_thm (trV_lt hw.good hv.good (hw.mono hv) hwv))
    · exact absurd (h ▸ trV_lt hw.good hv.good (hw.mono hv) hwv) (lt_irrefl_thm _)

/-! ### The uncountable prefix of a vector translation -/

theorem part_card_succ_fixed (k : Nat) : ∀ {A : T}, T.index_Prop1 0 A →
    part (card (k + 1) A) = (card (k + 1) A, T.Z) := by
  intro A hA
  induction hA with
  | z => rw [card_Z]; rfl
  | p p a b hp _ ih =>
    have hp0 : p = 0 := by omega
    subst p
    rw [card_P0]
    simp only [part, show (1 : Nat) ≠ 0 by omega, ite_false]
    rw [ih]

theorem part_fixed_add : ∀ {a b : T}, part a = (a, T.Z) → part b = (b, T.Z) →
    part (T.add a b) = (T.add a b, T.Z) := by
  intro a
  induction a with
  | Z => intro b _ hb; exact hb
  | P p c d _ ih =>
    intro b ha hb
    have hi := part_fixed_P_inv ha
    rw [T.P_add_eq]
    simp only [part, hi.1, ite_false, ih hi.2 hb]

theorem part_above (f : Nat → multi.T) : ∀ m, part (above f 0 m) = (above f 0 m, T.Z)
  | 0 => rfl
  | m + 1 => by
    rw [above]
    have h1 : part (card (0 + 1 + m) (tr (f (0 + 1 + m)))) =
        (card (0 + 1 + m) (tr (f (0 + 1 + m))), T.Z) := by
      rw [show 0 + 1 + m = m + 1 by omega]
      exact part_card_succ_fixed m (tr_index0 _)
    exact part_fixed_add h1 (part_above f m)

theorem part_trV (v : multi.V multi.T) :
    (part (trV v)).1 = trV (multi.V.set v 0 multi.T.Z) := by
  let N := v.length + 1
  have hsplit : ∀ u : multi.V multi.T, u.length ≤ N →
      trV u = T.add (above (multi.V.get0 u) 0 v.length) (tr (multi.V.get0 u 0)) := by
    intro u hu
    rw [trV_eq_trUpTo u (0 + 1 + v.length) (by omega), trUpTo_split]
    simp only [trUpTo, card_zero, T.add_Z]
  have hset : (multi.V.set v 0 multi.T.Z).length ≤ N := by rw [multi.V.length_set]; omega
  rw [hsplit v (by omega), hsplit _ hset]
  rw [part_add_fixed _ _ (part_above _ _) (part_of_index0 (tr_index0 _))]
  have hab : above (multi.V.get0 (multi.V.set v 0 multi.T.Z)) 0 v.length =
      above (multi.V.get0 v) 0 v.length :=
    above_congr 0 v.length (fun j hj => multi.V.get0_set_eqv_above v 0 _ j hj)
  rw [hab]
  by_cases hv : 0 < v.length
  · rw [multi.V.get0_set_same v 0 _ hv, tr_Z, T.add_Z]
  · rw [multi.V.get0_ge (multi.V.set v 0 multi.T.Z) 0 (by rw [multi.V.length_set]; omega), tr_Z,
      T.add_Z]

/-! ### Coordinates below the term, from the Buchholz support condition -/

theorem G1_block_sub (v : multi.V multi.T) (j : Nat) :
    ∀ y, y ∈ T.G1 0 (card j (tr (multi.V.get0 v j))) → y ∈ T.G1 0 (trV v) := by
  intro y hy
  by_cases hj : j < v.length
  · obtain ⟨m, hm⟩ : ∃ m, v.length = j + 1 + m := ⟨v.length - (j + 1), by omega⟩
    rw [trV_eq_trUpTo v (j + 1 + m) (by omega), trUpTo_split, trUpTo, G1_add, G1_add]
    exact List.mem_append_right _ (List.mem_append_left _ hy)
  · rw [multi.V.get0_ge v j (by omega), tr_Z, card_Z] at hy; cases hy

theorem mem_G1_shift (k : Nat) (c : T) : ∀ y, y ∈ T.G1 0 c → y ∈ T.G1 0 (shift k c) := by
  induction k with
  | zero => exact fun y hy => hy
  | succ k ih =>
    intro y hy
    rw [shift_succ]
    exact (G1_P_mem (Nat.zero_le 1)).2 (Or.inr (Or.inr (ih y hy)))

theorem nsize_coord_lt (y : multi.V multi.T) (e : multi.T) (j : Nat) :
    multi.T.nsize (multi.V.get0 y j) < multi.T.nsize (multi.T.P y e) :=
  multi.T.nsize_get0_lt y j e

/-- If the translation satisfies the Buchholz support condition, every coordinate lies below
the principal term. -/
theorem coord_lt_of_G {w : multi.V multi.T} (hw : NFc w)
    (hG : ∀ g, g ∈ T.G1 0 (trV w) → g < trV w) :
    ∀ j, multi.V.get0 w j < multi.T.P w multi.T.Z := by
  intro j
  have hj := hw j
  cases hx : multi.V.get0 w j with
  | Z => exact multi.T.Z_lt_P _ _
  | P y e =>
    rw [hx] at hj
    have hy : NFc y := hj.inv.1
    apply multi.T.P_lt_P_of_vlt
    have hblock := G1_block_sub w j
    rw [hx, tr_P] at hblock
    cases j with
    | zero =>
      rw [card_zero] at hblock
      exact trV_reflect_lt hy hw (hG _ (hblock _ (by simp [T.G1])))
    | succ k =>
      rw [card_P0] at hblock
      have hy0 : NFc (multi.V.set y 0 multi.T.Z) := by
        intro m
        by_cases hm : m = 0
        · by_cases h0 : 0 < y.length
          · rw [hm, multi.V.get0_set_same y 0 _ h0]; exact NF.z
          · rw [hm, multi.V.get0_ge _ 0 (by rw [multi.V.length_set]; omega)]; exact NF.z
        · rw [multi.V.get0_set_ne y 0 _ m hm]; exact hy m
      have hlt : trV (multi.V.set y 0 multi.T.Z) < trV w := by
        rw [← part_trV]
        by_cases hp : (part (trV y)).1 = T.Z
        · rw [hp]
          apply Z_lt_of_ne
          intro hz
          have := hblock (shift k (collapse (trV y))) (by simp [T.G1])
          rw [hz] at this; cases this
        · obtain ⟨g, hg, hpg⟩ := collapse_cover (trV_closed hy.good).1 hp
          exact lt_of_le_of_lt_thm T _ _ _ hpg (hG _ (hblock _ ((G1_P_mem (Nat.zero_le 1)).2
            (Or.inr (Or.inl (mem_G1_shift k _ g hg))))))
      apply multi.V.lt_transfer (trV_reflect_lt hy0 hw hlt) (k + 1)
      · rw [multi.V.get0_set_ne y 0 _ (k + 1) (by omega), hx]
        exact multi.T.not_eqv_of_nsize_lt (nsize_coord_lt y e (k + 1))
      · intro m hm
        rw [multi.V.get0_set_ne y 0 _ m (by omega)]
        exact multi.T.eqv_refl _
      · intro m _; exact multi.T.eqv_refl _

/-! ### Powers of `Ω` and shapes below them -/

/-- `Ω^L`. -/
def opow (L : Nat) : T := card L (T.P 0 T.Z T.Z)

theorem opow_succ (k : Nat) : opow (k + 1) = T.P 1 (shift k T.Z) T.Z := by
  unfold opow
  rw [card_P0, card_Z, collapse_Z]

theorem shift_decomp_lt : ∀ k' : Nat, ∀ a : T, T.isNF1 a → a < shift k' T.Z →
    ∃ k e, k < k' ∧ a = shift k e ∧ T.index_Prop1 0 e ∧ T.isNF1 e
  | 0, a, _, h => by rw [shift_zero] at h; exact absurd h lt_Z_inv
  | m + 1, a, ha, h => by
    rw [shift_succ] at h
    cases a with
    | Z => exact ⟨0, T.Z, Nat.zero_lt_succ m, rfl, T.index_Prop1.z, T.isNF1.z⟩
    | P p c d =>
      cases h with
      | p_head _ _ _ _ _ _ hp =>
        have hp0 : p = 0 := by omega
        subst p
        exact ⟨0, T.P 0 c d, Nat.zero_lt_succ m, rfl, isNF1_index 0 0 c d ha (Nat.le_refl 0), ha⟩
      | p_mid _ _ _ _ _ hc => exact absurd hc lt_Z_inv
      | p_tail _ _ _ _ hd =>
        obtain ⟨k, e, hk, rfl, he, heNF⟩ := shift_decomp_lt m d (T.isNF1_P_inv _ _ _ ha).2.1 hd
        exact ⟨k + 1, e, Nat.succ_lt_succ hk, (shift_succ k e).symm, he, heNF⟩

theorem lt_opow_of_lt_vbound {x : T} (hx : T.isNF1 x) (h : x < vbound) : ∃ L, x < opow L := by
  cases x with
  | Z => exact ⟨0, T.Lt.Z_lt_P _ _ _⟩
  | P p c d =>
    cases h with
    | p_head _ _ _ _ _ _ hp =>
      have hp0 : p = 0 := by omega
      subst p
      exact ⟨1, by rw [opow_succ, shift_zero]; exact T.Lt.p_head _ _ _ _ _ _ (by omega)⟩
    | p_mid _ _ _ _ _ hc =>
      obtain ⟨k, e, rfl, he⟩ := shift_decomp_omega c (T.isNF1_P_inv _ _ _ hx).1 hc
      exact ⟨k + 2, by rw [opow_succ]; exact T.Lt.p_mid _ _ _ _ _ (shift_level_lt k (k + 1)
        (Nat.lt_succ_self k) he)⟩
    | p_tail _ _ _ _ h => cases h

theorem le_shift (k : Nat) {e : T} (he : T.index_Prop1 0 e) : e ≤ shift k e := by
  cases k with
  | zero => exact Or.inr rfl
  | succ k =>
    rw [shift_succ]
    left
    cases he with
    | z => exact T.Lt.Z_lt_P _ _ _
    | p p a b hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)

theorem deg_shift_ge (k : Nat) (e : T) : deg e ≤ deg (shift k e) := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => rw [shift_succ]; exact Nat.le_trans ih (deg_tail_le 1 T.Z _)

theorem mid_le_of_P_le {p : Nat} {a b : T} (h : T.P p a T.Z ≤ T.P p b T.Z) : a ≤ b := by
  rcases h with h | h
  · cases h with
    | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
    | p_mid _ _ _ _ _ h => exact Or.inl h
    | p_tail _ _ _ _ h => cases h
  · cases h; exact Or.inr rfl

theorem shift_reflect_le {k : Nat} {a b : T} (h : shift k a ≤ shift k b) : a ≤ b := by
  rcases lt_total_thm a b with hab | hba | rfl
  · exact Or.inl hab
  · rcases h with h | h
    · exact absurd h (lt_asymm_thm (shift_lt_right k hba))
    · exact absurd (h ▸ shift_lt_right k hba) (lt_irrefl_thm _)
  · exact Or.inr rfl

theorem collapse_reflect_le {a b : T} (ha : T.isNF1 a) (_hag : ∀ x, x ∈ T.G1 0 a → x < a)
    (hb : T.isNF1 b) (hbg : ∀ x, x ∈ T.G1 0 b → x < b) (h : collapse a ≤ collapse b) : a ≤ b := by
  rcases lt_total_thm a b with hab | hba | rfl
  · exact Or.inl hab
  · rcases h with h | h
    · exact absurd h (lt_asymm_thm (collapse_lt hb hbg ha hba))
    · exact absurd (h ▸ collapse_lt hb hbg ha hba) (lt_irrefl_thm _)
  · exact Or.inr rfl

/-! ### Padding a vector with zero coordinates -/

def padZ (v : multi.V multi.T) : Nat → multi.V multi.T
  | 0 => v
  | m + 1 => .snoc .Z (padZ v m)

theorem padZ_length (v : multi.V multi.T) : ∀ m, (padZ v m).length = v.length + m
  | 0 => rfl
  | m + 1 => by
    show (padZ v m).length + 1 = _
    rw [padZ_length v m]; omega

theorem get0_padZ (v : multi.V multi.T) : ∀ m j, multi.V.get0 (padZ v m) j = multi.V.get0 v j
  | 0, _ => rfl
  | m + 1, j => by
    show (if j = (padZ v m).length then multi.T.Z else multi.V.get0 (padZ v m) j) = _
    by_cases hj : j = (padZ v m).length
    · rw [ite_eq_left hj, multi.V.get0_ge v j (by rw [hj, padZ_length]; omega)]
    · rw [ite_eq_right hj, get0_padZ v m j]

theorem trV_padZ (v : multi.V multi.T) : ∀ m, trV (padZ v m) = trV v
  | 0 => rfl
  | m + 1 => by
    show trV (multi.V.snoc multi.T.Z (padZ v m)) = _
    rw [trV_snoc, tr_Z, card_Z, add_Z_left, trV_padZ v m]

/-! ### The inverse of the translation -/

/-- Level-zero support below `ψ_1(ψ_1(1))`. -/
def SmallB (c : T) : Prop := ∀ y, y ∈ T.G1 0 c → y < vbound

/-- Inverse of the vector translation at exponent depth `n`. -/
def VInv (n : Nat) : Prop :=
  ∀ c, deg c ≤ n → T.isNF1 c → SmallB c → ∀ L, c < opow L →
    ∃ v : multi.V multi.T, v.length ≤ L ∧ NFc v ∧ trV v = c

theorem term_inv (n : Nat) (hV : VInv n) : ∀ u : T, T.index_Prop1 0 u → T.isNF1 u → SmallB u →
    deg u ≤ n + 1 → ∃ s, NF s ∧ tr s = u
  | .Z, _, _, _, _ => ⟨multi.T.Z, NF.z, tr_Z⟩
  | .P p c d, hi, hu, hs, hdeg => by
    have hp : p = 0 := by cases hi with | p _ _ _ hp _ => omega
    subst p
    have hdi : T.index_Prop1 0 d := by cases hi with | p _ _ _ _ h => exact h
    obtain ⟨hcNF, hdNF, hcG, hdh⟩ := T.isNF1_P_inv _ _ _ hu
    have hcB : c < vbound := hs c (by simp [T.G1])
    obtain ⟨L, hL⟩ := lt_opow_of_lt_vbound hcNF hcB
    have hcS : SmallB c := fun y hy => hs y ((G1_P_mem (Nat.le_refl 0)).2 (Or.inr (Or.inl hy)))
    have hcdeg : deg c ≤ n := by have := deg_mid_lt 0 c d; omega
    obtain ⟨v, _, hv, hvc⟩ := hV c hcdeg hcNF hcS L hL
    obtain ⟨a, ha, had⟩ := term_inv n hV d hdi hdNF
      (fun y hy => hs y ((G1_P_mem (Nat.le_refl 0)).2 (Or.inr (Or.inr hy))))
      (Nat.le_trans (deg_tail_le 0 c d) hdeg)
    refine ⟨multi.T.P v a, NF.p v a hv ha ?_ (coord_lt_of_G hv (by rw [hvc]; exact hcG)), ?_⟩
    · cases a with
      | Z => exact multi.T.Z_le _
      | P w b =>
        rw [tr_P] at had
        have hwv : trV w ≤ trV v := by
          rw [hvc]; rw [← had] at hdh; exact P0_head_mid_le hdh
        rcases trV_reflect_le ha.inv.1 hv hwv with h | h
        · exact Or.inl (multi.T.P_lt_P_of_vlt _ _ h)
        · exact Or.inr ((multi.T.P_eqv_iff w v multi.T.Z multi.T.Z).2 ⟨h, multi.compareT_ZZ⟩)
    · rw [tr_P, hvc, had]

theorem part_vbound : part vbound = (vbound, T.Z) := rfl

theorem vinv_step (n : Nat) (hV : VInv n) : ∀ c, deg c ≤ n + 1 → T.isNF1 c → SmallB c →
    ∀ L, c < opow L → ∃ v : multi.V multi.T, v.length ≤ L ∧ NFc v ∧ trV v = c
  | .Z, _, _, _, L, _ => ⟨.emp, Nat.zero_le _, fun _ => NF.z, trV_emp⟩
  | .P p a rest, hdeg, hc, hs, L, hL => by
    cases L with
    | zero =>
      have := lt_one_eq_Z (show T.P p a rest < T.P 0 T.Z T.Z from hL)
      cases this
    | succ k' =>
      rw [opow_succ] at hL
      cases p with
      | zero =>
        have hi := isNF1_index 0 0 a rest hc (Nat.le_refl 0)
        obtain ⟨z, hz, hzc⟩ := term_inv n hV _ hi hc hs hdeg
        refine ⟨.snoc z .emp, Nat.succ_le_succ (Nat.zero_le _), fun j => ?_, ?_⟩
        · show NF (if j = 0 then z else multi.V.get0 multi.V.emp j)
          by_cases hj : j = 0
          · rw [ite_eq_left hj]; exact hz
          · rw [ite_eq_right hj]; exact NF.z
        · rw [trV_snoc, trV_emp, T.add_Z]
          show card 0 (tr z) = _
          rw [card_zero, hzc]
      | succ q =>
        cases q with
        | succ q =>
          cases hL with
          | p_head _ _ _ _ _ _ h => exact absurd h (by omega)
        | zero =>
          have ha_lt : a < shift k' T.Z := by
            cases hL with
            | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
            | p_mid _ _ _ _ _ h => exact h
            | p_tail _ _ _ _ h => cases h
          obtain ⟨haNF, hrNF, haG, hrh⟩ := T.isNF1_P_inv _ _ _ hc
          obtain ⟨k, e, hk, rfl, he0, heNF⟩ := shift_decomp_lt k' a haNF ha_lt
          -- the coefficient of the leading summand
          have hsa : ∀ y, y ∈ T.G1 0 (shift k e) → y < vbound :=
            fun y hy => hs y ((G1_P_mem (Nat.zero_le 1)).2 (Or.inr (Or.inl hy)))
          have heS : SmallB e := fun y hy => hsa y (mem_G1_shift k e y hy)
          have haB : shift k e < vbound := hs _ (by simp [T.G1])
          have heB : e < vbound := lt_of_le_of_lt_thm T _ _ _ (le_shift k he0) haB
          obtain ⟨x, hxNF, hxG, hxc, hxB, hxdeg⟩ := exists_uncollapse e heNF he0
          have hxB' := hxB vbound part_vbound heS heB
          obtain ⟨L'', hL''⟩ := lt_opow_of_lt_vbound hxNF hxB'
          have hxdeg' : deg x ≤ n := by
            have h1 := deg_shift_ge k e
            have h2 := deg_mid_lt (0 + 1) (shift k e) rest
            omega
          obtain ⟨w, _, hw, hwx⟩ :=
            hV x hxdeg' hxNF (fun y hy => lt_trans_thm _ _ _ (hxG y hy) hxB') L'' hL''
          -- the remaining summands
          have hrest : rest < opow (k + 2) := by
            rw [opow_succ]
            exact lt_P_of_head_lt (lt_of_le_of_lt_thm T _ _ _ hrh
              (T.Lt.p_mid _ _ _ _ _ (shift_level_lt k (k + 1) (Nat.lt_succ_self k) he0)))
          obtain ⟨v', hv'len, hv', hv'c⟩ := vinv_step n hV rest
            (Nat.le_trans (deg_tail_le 1 _ rest) hdeg) hrNF
            (fun y hy => hs y ((G1_P_mem (Nat.zero_le 1)).2 (Or.inr (Or.inr hy)))) (k + 2) hrest
          let v'' := padZ v' (k + 2 - v'.length)
          have hlen'' : v''.length = k + 2 := by
            show (padZ v' (k + 2 - v'.length)).length = k + 2
            rw [padZ_length]; omega
          have hget'' : ∀ j, multi.V.get0 v'' j = multi.V.get0 v' j := get0_padZ v' _
          let y := multi.V.get0 v' (k + 1)
          refine ⟨multi.V.set v'' (k + 1) (multi.T.P w y), ?_, fun j => ?_, ?_⟩
          · rw [multi.V.length_set, hlen'']; omega
          · by_cases hj : j = k + 1
            · rw [hj, multi.V.get0_set_same v'' (k + 1) _ (by rw [hlen'']; omega)]
              refine NF.p w y hw (hv' (k + 1)) ?_ (coord_lt_of_G hw (by rw [hwx]; exact hxG))
              -- the leading summands are ordered
              cases hyc : y with
              | Z => exact multi.T.Z_le _
              | P w' b' =>
                have hyNF : NF (multi.T.P w' b') := hyc ▸ hv' (k + 1)
                have htr := NF_good hyNF
                rw [tr_P] at htr
                obtain ⟨hw'NF, _, hw'G, _⟩ := T.isNF1_P_inv _ _ _ htr
                -- the head of the remaining summands
                have hhead : T.head rest = T.P 1 (shift k (collapse (trV w'))) T.Z := by
                  rw [← hv'c, ← trV_padZ v' (k + 2 - v'.length)]
                  show T.head (trV v'') = _
                  rw [trV_eq_trUpTo v'' (k + 2) (Nat.le_of_eq hlen''), trUpTo, hget'',
                    show multi.V.get0 v' (k + 1) = y from rfl, hyc, tr_P, card_P0_add]
                  rfl
                rw [hhead] at hrh
                have h1 : shift k (collapse (trV w')) ≤ shift k (collapse (trV w)) := by
                  rw [hwx, hxc]
                  exact mid_le_of_P_le hrh
                have h2 := collapse_reflect_le hw'NF hw'G (trV_closed hw.good).1
                  (by rw [hwx]; exact hxG) (shift_reflect_le h1)
                rcases trV_reflect_le hyNF.inv.1 hw h2 with h | h
                · exact Or.inl (multi.T.P_lt_P_of_vlt _ _ h)
                · exact Or.inr ((multi.T.P_eqv_iff w' w multi.T.Z multi.T.Z).2 ⟨h, multi.compareT_ZZ⟩)
            · rw [multi.V.get0_set_ne v'' (k + 1) _ j hj, hget'']
              exact hv' j
          · rw [trV_eq_trUpTo _ (k + 2) (Nat.le_of_eq (by rw [multi.V.length_set, hlen''])), trUpTo,
              multi.V.get0_set_same v'' (k + 1) _ (by rw [hlen'']; omega), tr_P, hwx,
              card_P0_add, hxc]
            have hrest' : rest = T.add (card (k + 1) (tr y)) (trUpTo (multi.V.get0 v'') (k + 1)) := by
              rw [← hv'c, ← trV_padZ v' (k + 2 - v'.length)]
              show trV v'' = _
              rw [trV_eq_trUpTo v'' (k + 2) (Nat.le_of_eq hlen'')]
              show T.add (card (k + 1) (tr (multi.V.get0 v'' (k + 1))))
                (trUpTo (multi.V.get0 v'') (k + 1)) = _
              rw [hget'']
            rw [hrest']
            congr 2
            apply trUpTo_congr
            intro j hj
            rw [multi.V.get0_set_ne v'' (k + 1) _ j (by omega)]
            exact multi.T.eqv_refl _

theorem vinv_all : ∀ n, VInv n
  | 0 => by
    intro c hdeg _ _ L _
    cases c with
    | Z => exact ⟨.emp, Nat.zero_le _, fun _ => NF.z, trV_emp⟩
    | P p a b => exact absurd (Nat.le_trans (Nat.le_max_left _ _) hdeg) (Nat.not_succ_le_zero _)
  | n + 1 => vinv_step n (vinv_all n)

/-- Every Buchholz normal form below `ψ_0(Ω^ω)` is the translation of a normal form. -/
theorem surj (u : T) (hu : T.isNF1 u) (hub : u < bound) : ∃ s, NF s ∧ tr s = u := by
  have hi : T.index_Prop1 0 u := by
    cases u with
    | Z => exact T.index_Prop1.z
    | P p c d =>
      have hp : p = 0 := by
        cases hub with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
        | p_mid _ _ _ _ _ _ => rfl
        | p_tail _ _ _ _ _ => rfl
      subst p
      exact isNF1_index 0 0 c d hu (Nat.le_refl 0)
  have hs : SmallB u := by
    cases u with
    | Z => intro y hy; cases hy
    | P p c d =>
      have hc : c < vbound := by
        cases hub with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
        | p_mid _ _ _ _ _ h => exact h
        | p_tail _ _ _ _ h => cases h
      have hp : p = 0 := by
        cases hub with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
        | p_mid _ _ _ _ _ _ => rfl
        | p_tail _ _ _ _ _ => rfl
      subst p
      exact fun y hy => lt_of_le_of_lt_thm T _ _ _ (support_le_of_head hu (Or.inr rfl) y hy) hc
  exact term_inv (deg u) (vinv_all _) u hi hu hs (Nat.le_succ _)

end emp

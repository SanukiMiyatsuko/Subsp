import Subsp.multi.Collapse

/-! Reconstruction before `MT.collapse`, used to invert the translations: every countable
normal form is the collapse of a normal form whose level-zero support lies below it, and the
reconstruction does not increase the exponent depth. -/

namespace MT

open T

/-- Nesting depth through exponents; appending a tail does not add a level. -/
def deg : T → Nat
  | Z => 0
  | P _ a b => max (deg a + 1) (deg b)

theorem deg_add (a b : T) : deg (T.add a b) = max (deg a) (deg b) := by
  induction a with
  | Z => simp [T.add, deg]
  | P p c d _ ih => simp only [T.P_add_eq, deg, ih, Nat.max_assoc]

theorem deg_mid_lt (p : Nat) (a b : T) : deg a < deg (P p a b) :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self (deg a)) (Nat.le_max_left _ _)

theorem deg_tail_le (p : Nat) (a b : T) : deg b ≤ deg (P p a b) := Nat.le_max_right _ _

theorem deg_part_fst (a : T) : deg (part a).1 ≤ deg a := by
  have h := deg_add (part a).1 (part a).2
  rw [part_add] at h
  rw [h]
  exact Nat.le_max_left _ _

/-- A term whose summands lie at or below `ψ_0(a)` has level-zero support at or below `a`. -/
theorem support_le_of_head {s a : T} (hs : T.isNF1 s) (hh : T.head s ≤ P 0 a Z) :
    ∀ x, x ∈ T.G1 0 s → x ≤ a := by
  induction hs with
  | z => intro x hx; cases hx
  | p p c d _ _ hg hhead _ ih =>
    have hp : p = 0 := Nat.eq_zero_of_le_zero (head_le_index p 0 c a hh)
    subst p
    have hca := P0_head_mid_le hh
    intro x hx
    simp only [T.G1, Nat.zero_le, ite_true, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with (rfl | hx) | hx
    · exact hca
    · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (hg x hx) hca)
    · exact ih (partial_order.trans _ _ _ hhead hh) x hx

theorem good_of_mid_lt {a b : T} (hs : T.isNF1 (P 0 a b)) (ha : a < P 0 a b) :
    ∀ x, x ∈ T.G1 0 (P 0 a b) → x < P 0 a b :=
  fun x hx => lt_of_le_of_lt_thm T _ _ _ (support_le_of_head hs (Or.inr rfl) x hx) ha

theorem good_part_fst {s : T} (hg : ∀ x, x ∈ T.G1 0 s → x < s) :
    ∀ x, x ∈ T.G1 0 (part s).1 → x < (part s).1 := by
  intro x hx
  apply lt_add_left_of_size_lt (part s).1 (part s).2 x
  · intro h; rw [h] at hx; cases hx
  · exact G1_size_lt 0 _ x hx
  · rw [part_add]
    apply hg
    rw [← part_add s, G1_add]
    exact List.mem_append_left _ hx

theorem part_snd_lt_wrap {a : T} (_hnf : T.isNF1 a) (hg : ∀ x, x ∈ T.G1 0 a → x < a) :
    (part a).2 < P 0 a Z := by
  rcases part_snd_shape a with h | ⟨e, f, h⟩
  · rw [h]; exact T.Lt.Z_lt_P _ _ _
  · rw [h]; exact T.Lt.p_mid _ _ _ _ _ (remainder_mid_lt h hg)

theorem part_fixed_P_inv {p : Nat} {a b : T} (hfix : part (P p a b) = (P p a b, Z)) :
    p ≠ 0 ∧ part b = (b, Z) := by
  by_cases hp : p = 0
  · simp [part, hp] at hfix
  · simp only [part, hp, ite_false, Prod.mk.injEq, P.injEq, true_and] at hfix
    exact ⟨hp, Prod.ext hfix.1 hfix.2⟩

theorem part_add_fixed : ∀ a b : T, part a = (a, Z) → part b = (Z, b) →
    part (T.add a b) = (a, b) := by
  intro a
  induction a with
  | Z => exact fun b _ hb => hb
  | P p c d _ ih =>
    intro b hf hb
    have hi := part_fixed_P_inv hf
    simp [T.P_add_eq, part, hi.1, ih b hi.2 hb]

theorem add_fixed_index0_NF : ∀ a b : T, T.isNF1 a → T.isNF1 b →
    part a = (a, Z) → T.index_Prop1 0 b → T.isNF1 (T.add a b) := by
  intro a b ha
  induction ha with
  | z => exact fun hb _ _ => hb
  | p p c d hc _ hg hh _ ih =>
    intro hb hf hi
    have hfix := part_fixed_P_inv hf
    rw [T.P_add_eq]
    refine T.isNF1.p _ _ _ hc (ih hb hfix.2 hi) hg ?_
    cases d with
    | Z =>
      cases hi with
      | z => exact T.Z_le _
      | p q e f hq _ => exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (by have := hfix.1; omega))
    | P q e f => simpa [T.P_add_eq, T.head] using hh

theorem index0_lt_fixed {b c : T} (hb : T.index_Prop1 0 b) (hc : part c = (c, Z))
    (hcne : c ≠ Z) : b < c := by
  cases c with
  | Z => exact absurd rfl hcne
  | P q u v =>
    have hq : q ≠ 0 := (part_fixed_P_inv hc).1
    cases hb with
    | z => exact T.Lt.Z_lt_P _ _ _
    | p p a d hp _ => exact T.Lt.p_head _ _ _ _ _ _ (by omega)

theorem add_index0_lt_fixed : ∀ {a c b : T}, part a = (a, Z) → part c = (c, Z) →
    T.index_Prop1 0 b → a < c → T.add a b < c := by
  intro a c b ha hc hb hlt
  induction hlt with
  | Z_lt_P q u v => exact index0_lt_fixed hb hc (by intro h; cases h)
  | p_head p q x u y v h => rw [T.P_add_eq]; exact T.Lt.p_head _ _ _ _ _ _ h
  | p_mid p x u y v h _ => rw [T.P_add_eq]; exact T.Lt.p_mid _ _ _ _ _ h
  | p_tail p x y v h ih =>
    rw [T.P_add_eq]
    exact T.Lt.p_tail _ _ _ _ (ih (part_fixed_P_inv ha).2 (part_fixed_P_inv hc).2)

theorem collapse_of_part {x h t : T} (hx : T.isNF1 x) (hp : part x = (h, t)) :
    collapse x = if h = Z then x else if T.head t ≤ P 0 h Z then P 0 h t else t := by
  have ht : T.isNF1 t := by have := (part_NF1 hx).2; rwa [hp] at this
  rw [collapse_eq x (by rw [hp]; exact ht), hp]
  by_cases hh : h = Z
  · subst hh
    have hxt : t = x := by have := part_add x; rw [hp] at this; exact this
    simp [hxt]
  · simp [hh]

/-- Reconstruction before collapse. -/
theorem exists_uncollapse (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    ∃ x : T, T.isNF1 x ∧ (∀ y, y ∈ T.G1 0 x → y < x) ∧ collapse x = s ∧
      (∀ B : T, part B = (B, Z) → (∀ y, y ∈ T.G1 0 s → y < B) → s < B → x < B) ∧
      deg x ≤ deg s := by
  cases hi with
  | z =>
    exact ⟨Z, hnf, (by intro x hx; cases hx), by rw [collapse]; rfl, fun _ _ _ hb => hb,
      Nat.le_refl _⟩
  | p p a b hp hb =>
    have hp0 : p = 0 := by omega
    subst p
    have hn := T.isNF1_P_inv 0 a b hnf
    have hfix : part (part a).1 = ((part a).1, Z) := part_fst_fixed a
    have hadd : T.add (part a).1 (part a).2 = a := part_add a
    have hparts := part_NF1 hn.1
    have hhgood := good_part_fst hn.2.2.1
    have hidx : T.index_Prop1 0 (part a).2 := part_snd_index0 hn.1
    have hpartb := part_of_index0 hb
    by_cases hz : (part a).1 = Z
    · have hal : (part a).2 = a := by rw [hz] at hadd; exact hadd
      have haidx : T.index_Prop1 0 a := hal ▸ hidx
      refine ⟨P 0 a b, hnf, good_of_mid_lt hnf (lt_wrap 0 a b haidx hn.2.2.1), ?_,
        fun _ _ _ hsB => hsB, Nat.le_refl _⟩
      exact collapse_of_index0 (T.index_Prop1.p _ _ _ (Nat.le_refl 0) hb)
    · by_cases hlz : (part a).2 = Z
      · have hha : (part a).1 = a := by rw [hlz, T.add_Z] at hadd; exact hadd
        have hafix : part a = (a, Z) := by rw [Prod.ext_iff]; exact ⟨hha, hlz⟩
        have hxNF := add_fixed_index0_NF a b hn.1 hn.2.1 hafix hb
        have hpx := part_add_fixed a b hafix hpartb
        have hane : a ≠ Z := by intro h; apply hz; rw [hha]; exact h
        refine ⟨T.add a b, hxNF, ?_, ?_, ?_, ?_⟩
        · intro y hy
          rw [G1_add, List.mem_append] at hy
          rcases hy with hy | hy
          · exact lt_of_lt_of_le_thm T _ _ _ (hn.2.2.1 y hy) (add_self_le a b)
          · have hbne : b ≠ Z := by intro h; rw [h] at hy; cases hy
            exact lt_of_le_of_lt_thm T _ _ _ (support_le_of_head hn.2.1 hn.2.2.2 y hy)
              (add_lt_add_of_ne_Z a b hbne)
        · rw [collapse_of_part hxNF hpx, ite_eq_right hane, ite_eq_left hn.2.2.2]
        · exact fun B hB hG _ => add_index0_lt_fixed hafix hB hb (hG a (by simp [T.G1]))
        · rw [deg_add, deg]
          exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _),
            Nat.le_max_right _ _⟩
      · have hha : (part a).1 < a := by
          have h := add_lt_add_of_ne_Z (part a).1 (part a).2 hlz
          rwa [hadd] at h
        have hl : (part a).2 < P 0 a Z := part_snd_lt_wrap hn.1 hn.2.2.1
        have has : a < T.add (part a).1 (P 0 a b) := by
          have h := add_left_lt (part a).1
            (lt_of_lt_of_le_thm T _ _ _ hl (head_le_self (P 0 a b)))
          rwa [hadd] at h
        have hsidx := T.index_Prop1.p 0 a b (Nat.le_refl 0) hb
        have hxNF := add_fixed_index0_NF _ _ hparts.1 hnf hfix hsidx
        have hpx := part_add_fixed _ _ hfix (part_of_index0 hsidx)
        refine ⟨T.add (part a).1 (P 0 a b), hxNF, ?_, ?_, ?_, ?_⟩
        · intro y hy
          rw [G1_add, List.mem_append] at hy
          rcases hy with hy | hy
          · exact lt_of_lt_of_le_thm T _ _ _ (hhgood y hy) (add_self_le _ _)
          · exact lt_of_le_of_lt_thm T _ _ _ (support_le_of_head hnf (Or.inr rfl) y hy) has
        · rw [collapse_of_part hxNF hpx, ite_eq_right hz]
          apply ite_eq_right
          intro hh
          exact lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ hha (P0_head_mid_le hh))
        · exact fun B hB hG _ => add_index0_lt_fixed hfix hB hsidx
            (lt_trans_thm _ _ _ hha (hG a (by simp [T.G1])))
        · rw [deg_add]
          exact Nat.max_le.mpr ⟨Nat.le_trans (deg_part_fst a) (Nat.le_of_lt (deg_mid_lt 0 a b)),
            Nat.le_refl _⟩

/-- The uncountable prefix of a normal form is dominated by the support of its collapse. -/
theorem collapse_cover {s : T} (hs : T.isNF1 s) (hne : (part s).1 ≠ Z) :
    ∃ g, g ∈ T.G1 0 (collapse s) ∧ (part s).1 ≤ g := by
  rw [collapse_eq s (part_NF1 hs).2, ite_eq_right hne]
  split
  · exact ⟨(part s).1, by simp [T.G1], Or.inr rfl⟩
  · rename_i hh
    have hlt := lt_of_not_le hh
    have hidx := part_snd_index0 hs
    revert hh hlt hidx
    generalize (part s).2 = l
    intro hh hlt hidx
    cases hidx with
    | z => exact absurd (T.Z_le _) hh
    | p p c d hp _ =>
      have hp0 : p = 0 := by omega
      subst p
      cases hlt with
      | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
      | p_mid _ _ _ _ _ h => exact ⟨c, by simp [T.G1], Or.inl h⟩
      | p_tail _ _ _ _ h => cases h

end MT

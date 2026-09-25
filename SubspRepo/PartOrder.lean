import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

theorem part_lt_cases : ∀ s t : T, s < t →
    (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2) := by
  intro s
  induction s with
  | Z =>
    intro t h
    cases t with
    | Z => cases h
    | P q u v =>
      rw [T.part]
      rw [T.part]
      by_cases hq : q = 0
      · rw [ite_eq_left hq]
        exact Or.inr ⟨rfl, T.Lt.Z_lt_P q u v⟩
      · rw [ite_eq_right hq]
        cases hp : T.part v with
        | mk c d =>
          exact Or.inl (T.Lt.Z_lt_P q u c)
  | P p x y ihx ihy =>
    intro t h
    cases t with
    | Z => cases h
    | P q u v =>
      rw [T.part]
      rw [T.part]
      by_cases hp0 : p = 0
      · rw [ite_eq_left hp0]
        by_cases hq0 : q = 0
        · rw [ite_eq_left hq0]
          exact Or.inr ⟨rfl, h⟩
        · rw [ite_eq_right hq0]
          cases hvp : T.part v with
          | mk c d =>
            exact Or.inl (T.Lt.Z_lt_P q u c)
      · rw [ite_eq_right hp0]
        cases hyp : T.part y with
        | mk a b =>
          by_cases hq0 : q = 0
          · rw [ite_eq_left hq0]
            have hinv := lt_inv p x y q u v h
            cases hinv with
            | inl hpq =>
              have hpzero : p < 0 := by rw [hq0] at hpq; exact hpq
              exact False.elim (Nat.not_lt_zero p hpzero)
            | inr hor =>
              cases hor with
              | inl hm =>
                have hpq : p = 0 := by rw [hq0] at hm; exact hm.1
                exact False.elim (hp0 hpq)
              | inr ht =>
                have hpq : p = 0 := by rw [hq0] at ht; exact ht.1
                exact False.elim (hp0 hpq)
          · rw [ite_eq_right hq0]
            cases hvp : T.part v with
            | mk c d =>
              have hinv := lt_inv p x y q u v h
              cases hinv with
              | inl hpq =>
                exact Or.inl (T.Lt.p_head p q x u a c hpq)
              | inr hor =>
                cases hor with
                | inl hm =>
                  cases hm.1
                  exact Or.inl (T.Lt.p_mid p x u a c hm.2)
                | inr ht =>
                  cases ht.1
                  cases ht.2.1
                  have hrec := ihy v ht.2.2
                  rw [hyp, hvp] at hrec
                  cases hrec with
                  | inl hac =>
                    exact Or.inl (T.Lt.p_tail p x a c hac)
                  | inr heq =>
                    apply Or.inr
                    constructor
                    · have hac : a = c := heq.1
                      rw [hac]
                    · exact heq.2

#print axioms part_lt_cases

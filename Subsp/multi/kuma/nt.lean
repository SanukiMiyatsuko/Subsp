import Subsp.multi.kuma.defs

open multi
open T

namespace kumakuma

theorem T.dom_congr : ∀ (s s' : multi.T), multi.T.norm s = multi.T.norm s' → T.dom s = T.dom s'
  | Z, s', h => by
    have : s' = Z := (multi.T.eq_Z_iff_of_norm_eq h).1 rfl
    subst this; rfl
  | P li add, s', h => by
    obtain ⟨li', add', rfl, h1, h2⟩ := multi.T.norm_eq_P h
    rw [T.dom, T.dom]
    have hz := multi.T.eq_Z_iff_of_norm_eq h2
    by_cases ha : add = Z
    · have ha' := hz.1 ha
      simp only [ha, ha', ite_true]
      rcases V.fnz_congr_cases h1 with ⟨hA, hB⟩ | ⟨iv, hA, hB, hiv, hjv, hel⟩
      · simp [hA, hB]
      · simp only [hA, hB]
        rw [T.dom_congr _ _ hel]
        generalize dom (li'.get0 iv) = d
        cases d with
        | one =>
          cases iv with
          | zero => rfl
          | succ k => simp [h1]
        | Omega ri =>
          by_cases hlt : li < ri
          · have hlt' : li' < ri := (V.lt_congr h1 rfl).1 hlt
            simp [hlt, hlt']
          · have hlt' : ¬ li' < ri := fun h => hlt ((V.lt_congr h1 rfl).2 h)
            simp [hlt, hlt']
        | zero => rfl
        | omega => rfl
    · have ha' : ¬ add' = Z := mt hz.2 ha
      simp only [ha, ha', ite_false]
      exact T.dom_congr add add' h2
termination_by s => s.size
decreasing_by
  all_goals
    first
    | exact multi.T.size_lt_P_right _ _
    | exact multi.T.size_get0_lt_P _ _ _

theorem T.fund_congr : ∀ (s s' t t' : multi.T),
    multi.T.norm s = multi.T.norm s' → multi.T.norm t = multi.T.norm t' →
    multi.T.norm (T.fund s t) = multi.T.norm (T.fund s' t')
  | Z, s', t, t', hs, ht => by
    have : s' = Z := (multi.T.eq_Z_iff_of_norm_eq hs).1 rfl
    subst this; simp [T.fund, multi.T.norm]
  | P li add, s', t, t', hs, ht => by
    obtain ⟨li', add', rfl, h1, h2⟩ := multi.T.norm_eq_P hs
    rw [T.fund, T.fund]
    have hz := multi.T.eq_Z_iff_of_norm_eq h2
    by_cases ha : add = Z
    · have ha' := hz.1 ha
      simp only [ha, ha', ite_true]
      rcases V.fnz_congr_cases h1 with ⟨hA, hB⟩ | ⟨iv, hA, hB, hiv, hjv, hel⟩
      · simp [hA, hB]
      · simp only [hA, hB]
        have hfun : ∀ x x' : multi.T, multi.T.norm x = multi.T.norm x' →
            multi.T.norm (fund (li.get0 iv) x) = multi.T.norm (fund (li'.get0 iv) x') :=
          fun x x' hx => T.fund_congr (li.get0 iv) (li'.get0 iv) x x' hel hx
        have hset := V.set_congr h1 (hfun Z Z rfl) hiv hjv
        rw [← T.dom_congr _ _ hel]
        generalize dom (li.get0 iv) = d
        cases d with
        | one =>
          cases iv with
          | zero =>
            simp only
            exact T.mul_congr (multi.T.norm_P_congr hset rfl) ht
          | succ k =>
            simp only
            exact multi.T.norm_P_set_congr hset ht
              (V.lt_length_set_pred hiv) (V.lt_length_set_pred hjv)
        | Omega ri =>
          simp only
          by_cases hlt : li < ri
          · have hlt' : li' < ri := (V.lt_congr h1 rfl).1 hlt
            simp only [hlt, hlt', ite_true]
            exact multi.T.norm_P_set_congr h1 (hfun _ _ (T.iter_congr hfun ht)) hiv hjv
          · have hlt' : ¬ li' < ri := fun h => hlt ((V.lt_congr h1 rfl).2 h)
            simp only [hlt, hlt', ite_false]
            exact multi.T.norm_P_set_congr h1 (hfun t t' ht) hiv hjv
        | zero =>
          simp only
          exact multi.T.norm_P_set_congr h1 (hfun t t' ht) hiv hjv
        | omega =>
          simp only
          exact multi.T.norm_P_set_congr h1 (hfun t t' ht) hiv hjv
    · have ha' : ¬ add' = Z := mt hz.2 ha
      simp only [ha, ha', ite_false]
      exact multi.T.norm_P_congr h1 (T.fund_congr add add' t t' h2 ht)
termination_by s => s.size
decreasing_by
  all_goals
    first
    | exact multi.T.size_lt_P_right _ _
    | exact multi.T.size_get0_lt_P _ _ _

def sys : FundSys := ⟨T.fund, fun n => P (.snoc (P (T.LF n) Z) .emp) Z⟩

theorem sys_cong : sys.Cong := T.fund_congr

end kumakuma

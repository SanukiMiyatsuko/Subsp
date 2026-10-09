import Subsp.multi.emp.defs

open multi
open T

namespace emp

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
      rcases V.fnz_congr_cases h1 with ⟨hA, hB⟩ | ⟨iv, hA, hB, -⟩ <;> simp [hA, hB]
    · have ha' : ¬ add' = Z := mt hz.2 ha
      simp only [ha, ha', ite_false]
      exact T.dom_congr add add' h2

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
            refine T.iter_congr (fun x x' hx => ?_) ht
            exact multi.T.norm_P_set_congr hset hx
              (V.lt_length_set_pred hiv) (V.lt_length_set_pred hjv)
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

def sys : FundSys := ⟨T.fund, fun n => P (T.LF n) Z⟩

theorem sys_cong : sys.Cong := T.fund_congr

end emp

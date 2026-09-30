import Subsp.old.fund_props

namespace new

def Vec.outer0 {lam : Nat} (v : Vec (T lam) lam) : Prop :=
  ∀ i : Fin lam, i.val ≠ 0 → v.idx i = T.Z

def T.outer0 {lam : Nat} : T lam → Prop
| .Z => True
| .P ls _ => Vec.outer0 ls

theorem Vec.outer0_rplc_zero {lam : Nat}
    (v : Vec (T lam) lam) (m : Fin lam) (a : T lam)
    (hv : Vec.outer0 v) (hm : m.val = 0) :
    Vec.outer0 (v.rplc m a) := by
  intro j hj
  rw [Vec.rplc_idx_of_ne v m j a (by omega)]
  exact hv j hj

theorem T.outer0_mul_PZ {lam : Nat}
    (v : Vec (T lam) lam) (t : T lam)
    (hv : Vec.outer0 v) :
    T.outer0 (T.mul (T.P v T.Z) t) := by
  cases t with
  | Z => simp [T.mul, T.outer0]
  | P tls add =>
      change Vec.outer0 v
      exact hv

theorem T.outer0_fund {lam : Nat}
    (s t : T lam) (hs : T.outer0 s) :
    T.outer0 (T.fund s t) := by
  cases s with
  | Z => simp [T.fund, T.outer0]
  | P ls add =>
      simp only [T.outer0] at hs
      by_cases hadd : add = T.Z
      · subst add
        cases hmin : T.domVecMinIdx ls with
        | none => rw [T.fund_PZ_none ls t hmin]; trivial
        | some md =>
            obtain ⟨m, d⟩ := md
            have hspec := T.domVecMinIdx_some_spec ls m d hmin
            have hm0 : m.val = 0 := by
              by_cases hm : m.val = 0
              · exact hm
              · have hz := hs m hm
                have hd := hspec.2.1
                rw [hz] at hd
                exact False.elim (hspec.1 hd.symm)
            have hrplc (u : T lam) : Vec.outer0 (ls.rplc m u) :=
              Vec.outer0_rplc_zero ls m u hs hm0
            cases d with
            | zero => exact False.elim (hspec.1 rfl)
            | one =>
                rw [T.fund, ite_eq_left rfl, hmin]
                obtain ⟨mv, mh⟩ := m
                cases mv with
                | zero =>
                    apply T.outer0_mul_PZ
                    exact hrplc _
                | succ r =>
                    change r + 1 = 0 at hm0
                    exact False.elim (Nat.noConfusion hm0)
            | omega =>
                rw [T.fund, ite_eq_left rfl, hmin]
                exact hrplc _
            | Omega i =>
                rw [T.fund_PZ_Omega ls t m i hmin]
                split <;> exact hrplc _
      · simpa [T.fund, hadd, T.outer0] using hs

theorem T.outer0_dim0 (s : T 0) : T.outer0 s := by
  cases s with
  | Z => trivial
  | P ls add =>
      intro i
      exact i.elim0

theorem T.isOT_outer0 {lam : Nat} {s : T lam} (hs : T.isOT lam s) :
    T.outer0 s := by
  induction hs with
  | base_0 n => exact T.outer0_dim0 (T.LF 0 n)
  | base_succ lam n =>
      simp only [T.outer0, Vec.outer0]
      intro i hi
      rw [Vec.ofFn_idx]
      simp [hi]
  | step lam s hs n ih =>
      exact T.outer0_fund s (T.ofNat n) ih

end new

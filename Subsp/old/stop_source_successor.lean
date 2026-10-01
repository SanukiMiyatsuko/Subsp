import Subsp.old.stop_indexed_nf

/-! Finite terms and successor steps preserve indexed source normal forms. -/

namespace new

theorem T.le_refl {lam : Nat} (s : T lam) : s ≤ s := Or.inr (T_refl s)

theorem T.P_le_P_same {lam : Nat} (v : Vec (T lam) lam) (a b : T lam) (h : a ≤ b) :
    T.P v a ≤ T.P v b := by
  simpa only [LE.le, T.le, compareT, Vec_refl] using h

theorem T.lt_Z_false {lam : Nat} (s : T lam) : ¬ s < T.Z := by
  cases s <;> intro h <;> cases h

theorem T.dom_PZ_one_iff {lam : Nat} (v : Vec (T lam) lam) :
    T.dom (T.P v T.Z) = .one ↔ T.domVecMinIdx v = none := by
  simp only [T.dom, ite_true]
  cases T.domVecMinIdx v with
  | none => simp
  | some md =>
      obtain ⟨m, d⟩ := md
      cases d with
      | zero | omega => simp
      | one => by_cases hm : m.val = 0 <;> simp [hm]
      | Omega i => by_cases hi : i ≤ m <;> simp [hi]

theorem T.fund_PZ_none {lam : Nat} (v : Vec (T lam) lam) (t : T lam)
    (h : T.domVecMinIdx v = none) : T.fund (T.P v T.Z) t = T.Z := by
  rw [T.fund, ite_eq_left rfl, h]

theorem T.vector_lt_of_P_lt_PZ {lam : Nat} (v w : Vec (T lam) lam) (a : T lam)
    (h : T.P v a < T.P w T.Z) : compareVec v w = .lt := by
  change (match compareVec v w with | .eq => compareT a T.Z | ord => ord) = .lt at h
  cases hc : compareVec v w with
  | lt => rfl
  | eq => rw [hc] at h; exact False.elim (T.lt_Z_false a h)
  | gt => simp [hc] at h

theorem T.fund_one_upper {lam : Nat} (s : T lam) (hd : T.dom s = .one) :
    ∀ b : T lam, b < s → b ≤ T.fund s T.Z := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => cases hd
  | P v a _ ih =>
      intro b hb
      by_cases haz : a = T.Z
      · subst a
        have hnone := (T.dom_PZ_one_iff v).mp hd
        rw [T.fund_PZ_none v T.Z hnone]
        cases b with
        | Z => exact T.le_refl _
        | P w c =>
            obtain ⟨i, _, hi⟩ := Vec.compare_lt_has_pivot w v (T.vector_lt_of_P_lt_PZ w v c hb)
            rw [T.dom_zero_eq_Z _ (T.domVecMinIdx_none_all_zero v hnone i)] at hi
            exact False.elim (T.lt_Z_false _ hi)
      · rw [T.fund, ite_eq_right haz]
        have hda : T.dom a = .one := by simpa only [T.dom, haz, ite_false] using hd
        cases b with
        | Z => exact T.Z_le _
        | P w c =>
            change (match compareVec w v with | .eq => compareT c a | ord => ord) = .lt at hb
            cases hc : compareVec w v with
            | lt => exact Or.inl (T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
            | eq =>
                rw [hc] at hb
                obtain rfl := Vec_eq_sound w v hc
                exact T.P_le_P_same _ _ _ (ih hda c hb)
            | gt => simp [hc] at hb
  | nil => trivial
  | snoc => trivial

theorem T.fund_one_arg_irrel {lam : Nat} (s t : T lam) (hd : T.dom s = .one) :
    T.fund s t = T.fund s T.Z := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => cases hd
  | P v a _ ih =>
      by_cases haz : a = T.Z
      · subst a
        have hnone := (T.dom_PZ_one_iff v).mp hd
        rw [T.fund_PZ_none v t hnone, T.fund_PZ_none v T.Z hnone]
      · rw [T.fund, ite_eq_right haz, T.fund, ite_eq_right haz]
        rw [ih (by simpa only [T.dom, haz, ite_false] using hd)]
  | nil => trivial
  | snoc => trivial

theorem T.fund_one_NF {lam : Nat} (s : T lam) (hs : T.isNF s) (hd : T.dom s = .one) :
    T.isNF (T.fund s T.Z) := by
  induction hs with
  | z => cases hd
  | p v a hv _ hg hh _ ih =>
      by_cases haz : a = T.Z
      · subst a
        rw [T.fund_PZ_none v T.Z ((T.dom_PZ_one_iff v).mp hd)]
        exact .z
      · rw [T.fund, ite_eq_right haz]
        exact .p v _ hv (ih (by simpa only [T.dom, haz, ite_false] using hd)) hg
          (T.le_trans _ _ _ (T.head_mono _ _ (T.fund_lt_self a T.Z haz)) hh)

theorem T.Gi_fund_one_subset {lam : Nat} (u : Nat) (s : T lam) (hd : T.dom s = .one) :
    ∀ x ∈ T.Gi u (T.fund s T.Z), x ∈ T.Gi u s := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => cases hd
  | P v a _ ih =>
      by_cases haz : a = T.Z
      · subst a
        rw [T.fund_PZ_none v T.Z ((T.dom_PZ_one_iff v).mp hd)]
        intro x hx; cases hx
      · rw [T.fund, ite_eq_right haz]
        intro x hx
        rcases (T.mem_Gi_P u v _ x).mp hx with hv | hx
        · exact (T.mem_Gi_P u v a x).mpr (Or.inl hv)
        · exact (T.mem_Gi_P u v a x).mpr
            (Or.inr (ih (by simpa only [T.dom, haz, ite_false] using hd) x hx))
  | nil => trivial
  | snoc => trivial

theorem T.fund_one_NFComp {lam : Nat} (u : Nat) (s t : T lam)
    (hs : T.isNFComp u s) (hd : T.dom s = .one) : T.isNFComp u (T.fund s t) := by
  rw [T.fund_one_arg_irrel s t hd]
  refine ⟨T.fund_one_NF s hs.1 hd, ?_⟩
  intro x hx
  have hlt := hs.2 x (T.Gi_fund_one_subset u s hd x hx)
  rcases T.fund_one_upper s hd x hlt with h | h
  · exact h
  · have he := T_eq_sound _ _ h
    have hsize := T.Gi_size_lt u _ x hx
    rw [he] at hsize
    exact False.elim (Nat.lt_irrefl _ hsize)

theorem T.Gi_ofNat_zero {lam : Nat} (u n : Nat) :
    ∀ x ∈ T.Gi u (T.ofNat (lam := lam) n), x = T.Z := by
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
      intro x hx
      rcases (T.mem_Gi_P u _ _ x).mp hx with ⟨i, _, hx⟩ | hx
      · simp only [Vec.ofFn_idx] at hx
        rcases hx with rfl | hx
        · rfl
        · cases hx
      · exact ih x hx

theorem T.ofNat_isNF {lam : Nat} (n : Nat) : T.isNF (T.ofNat (lam := lam) n) := by
  induction n with
  | zero => exact .z
  | succ n ih =>
      refine .p _ _ ?_ ih ?_ ?_
      · intro i; rw [Vec.ofFn_idx]; exact .z
      · intro i; rw [Vec.ofFn_idx]; intro x hx; cases hx
      · cases n with
        | zero => exact T.Z_le _
        | succ n => exact T.le_refl _

theorem T.ofNat_isNFComp {lam : Nat} (u n : Nat) : T.isNFComp u (T.ofNat (lam := lam) n) := by
  refine ⟨T.ofNat_isNF n, ?_⟩
  intro x hx
  rw [T.Gi_ofNat_zero u n x hx]
  cases n with
  | zero => cases hx
  | succ n => rfl

end new

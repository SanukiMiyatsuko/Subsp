import Subsp.multi.Lex
import Subsp.multi.emp.nt

/-! Source-side theory of `emp`: unfolding of `dom` and `fund`, normal forms (every coordinate
lies below the term), closure of normal forms under fundamental sequences, and cofinality of
fundamental sequences. -/

open multi
open T

namespace emp

/-! ### Unfolding `dom` and `fund` -/

theorem dom_tail (v : V multi.T) {a : multi.T} (ha : a ≠ Z) : T.dom (P v a) = T.dom a := by
  rw [T.dom, ite_eq_right ha]

theorem dom_PZ_none {v : V multi.T} (h : V.fnz v = none) : T.dom (P v Z) = .one := by
  rw [T.dom, ite_eq_left rfl, h]

theorem dom_PZ_some {v : V multi.T} {i : Nat} (h : V.fnz v = some i) :
    T.dom (P v Z) = .omega := by
  rw [T.dom, ite_eq_left rfl, h]

theorem dom_P_ne_zero : ∀ (a : multi.T) (v : V multi.T), T.dom (P v a) ≠ .zero
  | Z, v => by
    rcases hf : V.fnz v with _ | i
    · rw [dom_PZ_none hf]; intro h; cases h
    · rw [dom_PZ_some hf]; intro h; cases h
  | P w b, v => by
    rw [dom_tail v (fun h => T.noConfusion h)]
    exact dom_P_ne_zero b w

theorem eq_Z_of_dom_zero {s : multi.T} (h : T.dom s = .zero) : s = Z := by
  cases s with
  | Z => rfl
  | P v a => exact absurd h (dom_P_ne_zero a v)

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
      T.iter (fun x => P (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k x) Z) t := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]

theorem fund_PZ_omega {v : V multi.T} {i : Nat} (h : V.fnz v = some i)
    (hd : T.dom (V.get0 v i) = .omega) (t : multi.T) :
    T.fund (P v Z) t = P (V.set v i (T.fund (V.get0 v i) t)) Z := by
  rw [T.fund, ite_eq_left rfl, h]; simp only [hd]

/-! ### Successors -/

theorem fund_one_irrel : ∀ (s : multi.T), T.dom s = .one → ∀ t, T.fund s t = T.fund s Z
  | Z, hd, _ => by rw [T.dom] at hd; cases hd
  | P v a, hd, t => by
    by_cases ha : a = Z
    · subst ha
      rcases hf : V.fnz v with _ | i
      · rw [fund_PZ_none hf, fund_PZ_none hf]
      · rw [dom_PZ_some hf] at hd; cases hd
    · rw [fund_tail v ha, fund_tail v ha, fund_one_irrel a (by rwa [dom_tail v ha] at hd) t]

/-- Below a successor means at most its predecessor. -/
theorem fund_one_upper : ∀ (s : multi.T), T.dom s = .one → ∀ b, b < s → b ≤ T.fund s Z
  | Z, hd, _, _ => by rw [T.dom] at hd; cases hd
  | P v a, hd, b, hb => by
    by_cases ha : a = Z
    · subst ha
      rcases hf : V.fnz v with _ | i
      · rw [fund_PZ_none hf]
        cases b with
        | Z => exact T.Z_le Z
        | P y e =>
          exfalso
          rcases (T.P_lt_P_iff y v e Z).1 hb with hy | ⟨_, he⟩
          · obtain ⟨p, _, hp⟩ := (V.lt_iff_pivot y v).1 hy
            rw [V.fnz_none_spec v hf p] at hp
            exact T.not_lt_Z _ hp
          · exact T.not_lt_Z _ he
      · rw [dom_PZ_some hf] at hd; cases hd
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
              cases t with
              | Z => exact T.Z_lt_P _ _
              | P _ t' =>
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
      · rw [fund_tail v ha]
        exact T.P_tail_lt v (ih a (T.size_lt_P_right v a) ha t)

theorem hd_fund_le (s t : multi.T) : T.hd (T.fund s t) ≤ T.hd s := by
  by_cases hs : s = Z
  · subst hs; rw [fund_Z]; exact T.le_refl _
  · exact T.hd_mono (fund_lt_self s hs t)

/-! ### Normal forms -/

/-- Normal forms: every coordinate of a principal term lies below the term. -/
inductive NF : multi.T → Prop
  | z : NF Z
  | p (v : V multi.T) (a : multi.T) (hv : ∀ j, NF (V.get0 v j)) (ha : NF a)
      (hh : T.hd a ≤ P v Z) (hlt : ∀ j, V.get0 v j < P v Z) : NF (P v a)

theorem NF.inv {v : V multi.T} {a : multi.T} (h : NF (P v a)) :
    (∀ j, NF (V.get0 v j)) ∧ NF a ∧ T.hd a ≤ P v Z ∧ ∀ j, V.get0 v j < P v Z := by
  cases h with
  | p _ _ hv ha hh hlt => exact ⟨hv, ha, hh, hlt⟩

theorem NF.coord_lt_hd {v : V multi.T} {a : multi.T} (h : NF (P v a)) (j : Nat) :
    V.get0 v j < P v a :=
  T.lt_of_lt_of_le (h.inv.2.2.2 j) (T.hd_le_self (P v a))

theorem NF_ofNat : ∀ n, NF (T.ofNat n)
  | 0 => NF.z
  | n + 1 => by
    refine NF.p _ _ (fun _ => NF.z) (NF_ofNat n) ?_ (fun _ => T.Z_lt_P _ _)
    cases n with
    | zero => exact T.Z_le _
    | succ n => exact T.le_refl _

theorem NF_mul {u : V multi.T} (hu : NF (P u Z)) : ∀ t, NF (T.mul (P u Z) t)
  | Z => NF.z
  | P w t => by
    have hr := NF_mul hu t
    obtain ⟨hv, _, _, hlt⟩ := hu.inv
    refine NF.p u _ hv hr ?_ hlt
    cases t with
    | Z => exact T.Z_le _
    | P _ _ => exact T.le_refl _

theorem NF_norm : ∀ {s : multi.T}, NF s → NF (multi.T.norm s) := by
  intro s h
  induction h with
  | z => exact NF.z
  | p v a _ _ hh hlt ihv iha =>
    rw [T.norm_P]
    refine NF.p _ _ (fun j => by rw [V.get0_norm]; exact ihv j) iha ?_ (fun j => ?_)
    · have hhd : T.hd (multi.T.norm a) = multi.T.norm (T.hd a) := by
        cases a with
        | Z => rfl
        | P w b => rw [T.norm_P]; rfl
      rw [hhd, show P (V.norm v) Z = multi.T.norm (P v Z) from (T.norm_P v Z).symm]
      exact (multi.T.le_norm_iff _ _).1 hh
    · rw [V.get0_norm, show P (V.norm v) Z = multi.T.norm (P v Z) from (T.norm_P v Z).symm]
      exact (multi.T.lt_norm_iff _ _).1 (hlt j)

/-- A normal form placed at coordinate `i` of a vector that vanishes below `i` lies below the
new principal term, provided its leading vector lies below the old one. -/
theorem NF_lt_P_set {x : multi.T} (hx : NF x) {v w : V multi.T} (i : Nat)
    (hz : ∀ j, j < i → V.get0 v j = Z)
    (hw : ∀ j, i < j → compareT (V.get0 w j) (V.get0 v j) = .eq)
    (hwi : V.get0 w i = x) (hhd : T.hd x < P v Z) : x < P w Z := by
  cases x with
  | Z => exact T.Z_lt_P _ _
  | P y e =>
    have hy : y < v := by
      rcases (T.P_lt_P_iff y v Z Z).1 hhd with h | ⟨_, h⟩
      · exact h
      · exact absurd h (T.not_lt_Z _)
    apply T.P_lt_P_of_vlt
    apply V.lt_of_zero_below hy i hz hw
    rw [hwi]
    exact hx.coord_lt_hd i

theorem hd_lt_of_lt {x c : multi.T} {v : V multi.T} (hxc : x < c) (hc : c < P v Z) :
    T.hd x < P v Z :=
  T.lt_of_le_of_lt (T.hd_mono hxc) (T.lt_of_le_of_lt (T.hd_le_self c) hc)

/-! ### Closure of normal forms under fundamental sequences -/

/-- Changing one coordinate of a normal principal term. -/
theorem NF_set {v : V multi.T} {i : Nat} (hi : i < v.length) (hv : ∀ j, NF (V.get0 v j))
    (hzero : ∀ j, j < i → V.get0 v j = Z) (hlt : ∀ j, V.get0 v j < P v Z)
    {x : multi.T} (hx : NF x) (hxi : x < V.get0 v i) : NF (P (V.set v i x) Z) := by
  refine NF.p _ _ (fun j => ?_) NF.z (T.Z_le _) (fun j => ?_)
  · by_cases hj : j = i
    · rw [hj, V.get0_set_same v i x hi]; exact hx
    · rw [V.get0_set_ne v i x j hj]; exact hv j
  · rcases Nat.lt_trichotomy j i with hji | hji | hji
    · rw [V.get0_set_ne v i x j (Nat.ne_of_lt hji), hzero j hji]; exact T.Z_lt_P _ _
    · rw [hji, V.get0_set_same v i x hi]
      exact NF_lt_P_set hx i hzero (V.get0_set_eqv_above v i x) (V.get0_set_same v i x hi)
        (hd_lt_of_lt hxi (hlt i))
    · rw [V.get0_set_ne v i x j (Nat.ne_of_gt hji)]
      exact T.get0_lt_P_of_agree (hlt j) (fun m hm => V.get0_set_eqv_above v i x m (by omega))

/-- The iterates of a successor coordinate above the lowest are normal forms. -/
theorem NF_iter {v : V multi.T} {k : Nat} (hi : k + 1 < v.length) (hv : ∀ j, NF (V.get0 v j))
    (hzero : ∀ j, j < k + 1 → V.get0 v j = Z) (hlt : ∀ j, V.get0 v j < P v Z)
    {c : multi.T} (hc : NF c) (hcl : c < V.get0 v (k + 1)) :
    ∀ n, NF (T.iter (fun x => P (V.set (V.set v (k + 1) c) k x) Z) (T.ofNat n)) := by
  have hlen : k < (V.set v (k + 1) c).length := by rw [V.length_set]; omega
  have hwk : ∀ x, V.get0 (V.set (V.set v (k + 1) c) k x) k = x :=
    fun x => V.get0_set_same _ k x hlen
  have hwi : ∀ x, V.get0 (V.set (V.set v (k + 1) c) k x) (k + 1) = c := by
    intro x
    rw [V.get0_set_ne _ k x (k + 1) (by omega), V.get0_set_same v (k + 1) c hi]
  have hwo : ∀ x j, j ≠ k → j ≠ k + 1 →
      V.get0 (V.set (V.set v (k + 1) c) k x) j = V.get0 v j := by
    intro x j hjk hji
    rw [V.get0_set_ne _ k x j hjk, V.get0_set_ne v (k + 1) c j hji]
  have hwa : ∀ x j, k + 1 < j →
      compareT (V.get0 (V.set (V.set v (k + 1) c) k x) j) (V.get0 v j) = .eq := by
    intro x j hj
    rw [hwo x j (by omega) (by omega)]
    exact T.eqv_refl _
  have hstep : ∀ x, NF x → x < P (V.set (V.set v (k + 1) c) k x) Z →
      NF (P (V.set (V.set v (k + 1) c) k x) Z) := by
    intro x hx hxlt
    refine NF.p _ _ (fun j => ?_) NF.z (T.Z_le _) (fun j => ?_)
    · by_cases hjk : j = k
      · rw [hjk, hwk]; exact hx
      · by_cases hji : j = k + 1
        · rw [hji, hwi]; exact hc
        · rw [hwo x j hjk hji]; exact hv j
    · by_cases hjk : j = k
      · rw [hjk, hwk]; exact hxlt
      · by_cases hji : j = k + 1
        · rw [hji, hwi]
          exact NF_lt_P_set hc (k + 1) hzero (hwa x) (hwi x) (hd_lt_of_lt hcl (hlt (k + 1)))
        · rw [hwo x j hjk hji]
          rcases Nat.lt_or_gt_of_ne hji with hlt' | hgt
          · rw [hzero j hlt']; exact T.Z_lt_P _ _
          · exact T.get0_lt_P_of_agree (hlt j) (fun m hm => hwa x m (by omega))
  suffices H : ∀ n, NF (T.iter (fun x => P (V.set (V.set v (k + 1) c) k x) Z) (T.ofNat n)) ∧
      T.iter (fun x => P (V.set (V.set v (k + 1) c) k x) Z) (T.ofNat n) <
        P (V.set (V.set v (k + 1) c) k
          (T.iter (fun x => P (V.set (V.set v (k + 1) c) k x) Z) (T.ofNat n))) Z from
    fun n => (H n).1
  intro n
  induction n with
  | zero => exact ⟨NF.z, T.Z_lt_P _ _⟩
  | succ n ih =>
    rw [T.iter_ofNat_succ]
    refine ⟨hstep _ ih.1 ih.2, T.P_lt_P_of_vlt _ _ ?_⟩
    apply V.lt_of_pivot k
    · intro j hj
      rw [V.get0_set_ne _ k _ j (by omega), V.get0_set_ne _ k _ j (by omega)]
      exact T.eqv_refl _
    · rw [hwk, hwk]; exact ih.2

theorem NF_fund (s : multi.T) : NF s → ∀ n, NF (T.fund s (T.ofNat n)) := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro hs n
    cases s with
    | Z => rw [fund_Z]; exact NF.z
    | P v a =>
      obtain ⟨hv, ha, hh, hlt⟩ := hs.inv
      by_cases haz : a = Z
      · subst haz
        rcases hf : V.fnz v with _ | i
        · rw [fund_PZ_none hf]; exact NF.z
        · obtain ⟨hne, hzero⟩ := V.fnz_some_spec v i hf
          have hi := V.lt_length_of_fnz v i hf
          have hrecNF : ∀ m, NF (T.fund (V.get0 v i) (T.ofNat m)) :=
            ih _ (T.size_get0_lt_P v i Z) (hv i)
          have hrecLt : ∀ u, T.fund (V.get0 v i) u < V.get0 v i := fund_lt_self _ hne
          cases hd : T.dom (V.get0 v i) with
          | zero => exact absurd (eq_Z_of_dom_zero hd) hne
          | one =>
            have hc : NF (T.fund (V.get0 v i) Z) := hrecNF 0
            cases i with
            | zero =>
              rw [fund_PZ_one0 hf hd]
              exact NF_mul (NF_set hi hv hzero hlt hc (hrecLt Z)) _
            | succ k =>
              rw [fund_PZ_oneS hf hd]
              exact NF_iter hi hv hzero hlt hc (hrecLt Z) n
          | omega =>
            rw [fund_PZ_omega hf hd]
            exact NF_set hi hv hzero hlt (hrecNF n) (hrecLt _)
      · rw [fund_tail v haz]
        refine NF.p v _ hv (ih a (T.size_lt_P_right v a) ha n) ?_ hlt
        exact T.le_trans (hd_fund_le a _) hh

/-! ### Cofinality of fundamental sequences -/

theorem mul_cofinal {u : V multi.T} :
    ∀ d, NF d → T.hd d ≤ P u Z → ∃ m, d < T.mul (P u Z) (T.ofNat m)
  | Z, _, _ => ⟨1, T.Z_lt_P _ _⟩
  | P y e, hd, hh => by
    obtain ⟨_, he, hhe, _⟩ := hd.inv
    rcases (T.P_le_P_iff y u Z Z).1 hh with hy | ⟨hy, _⟩
    · exact ⟨1, T.P_lt_P_of_vlt _ _ hy⟩
    · have hhe' : T.hd e ≤ P u Z :=
        T.le_trans hhe (Or.inr ((T.P_eqv_iff y u Z Z).2 ⟨hy, compareT_ZZ⟩))
      obtain ⟨m, hm⟩ := mul_cofinal e he hhe'
      exact ⟨m + 1, T.P_lt_P_of_eqv hy hm⟩

theorem iter_cofinal {v : V multi.T} {k : Nat} (hi : k + 1 < v.length)
    (hzero : ∀ j, j < k + 1 → V.get0 v j = Z) (hd : T.dom (V.get0 v (k + 1)) = .one) :
    ∀ b, NF b → b < P v Z → ∃ n, b < T.iter
      (fun x => P (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k x) Z) (T.ofNat n) := by
  have hlen : k < (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)).length := by
    rw [V.length_set]; omega
  have hwo : ∀ x j, k + 1 < j → compareT (V.get0 (V.set (V.set v (k + 1)
      (T.fund (V.get0 v (k + 1)) Z)) k x) j) (V.get0 v j) = .eq := by
    intro x j hj
    rw [V.get0_set_ne _ k x j (by omega), V.get0_set_ne v (k + 1) _ j (by omega)]
    exact T.eqv_refl _
  have hwi : ∀ x, V.get0 (V.set (V.set v (k + 1) (T.fund (V.get0 v (k + 1)) Z)) k x)
      (k + 1) = T.fund (V.get0 v (k + 1)) Z := by
    intro x
    rw [V.get0_set_ne _ k x (k + 1) (by omega), V.get0_set_same v (k + 1) _ hi]
  intro b
  induction b using (measure multi.T.size).wf.induction with
  | h b ih =>
    intro hb hbv
    cases b with
    | Z => exact ⟨1, T.Z_lt_P _ _⟩
    | P y e =>
      have hy := vlt_of_P_lt hbv
      obtain ⟨p, hpeq, hplt⟩ := (V.lt_iff_pivot y v).1 hy
      have hip := pivot_above_zero hzero hplt
      rcases Nat.lt_or_eq_of_le hip with hip | hip
      · refine ⟨1, T.P_lt_P_of_vlt _ _ ?_⟩
        apply V.lt_of_pivot p
        · intro j hj; exact T.eqv_trans (hpeq j hj) (T.eqv_symm (hwo Z j (by omega)))
        · exact T.lt_of_lt_of_eqv hplt (T.eqv_symm (hwo Z p hip))
      · subst hip
        rcases fund_one_upper _ hd _ hplt with hc | hc
        · refine ⟨1, T.P_lt_P_of_vlt _ _ ?_⟩
          apply V.lt_of_pivot (k + 1)
          · intro j hj; exact T.eqv_trans (hpeq j hj) (T.eqv_symm (hwo Z j hj))
          · rw [hwi]; exact hc
        · obtain ⟨hyv, _, _, _⟩ := hb.inv
          have hyk : V.get0 y k < P v Z := T.lt_trans (hb.coord_lt_hd k) hbv
          obtain ⟨n, hn⟩ := ih _ (T.size_get0_lt_P y k e) (hyv k) hyk
          refine ⟨n + 1, ?_⟩
          rw [T.iter_ofNat_succ]
          apply T.P_lt_P_of_vlt
          apply V.lt_of_pivot k
          · intro j hj
            rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hj' | hj'
            · exact T.eqv_trans (hpeq j hj') (T.eqv_symm (hwo _ j hj'))
            · rw [← hj', hwi]; exact hc
          · rw [V.get0_set_same _ k _ hlen]; exact hn

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
        rcases hf : V.fnz v with _ | i
        · rw [dom_PZ_none hf] at hda; cases hda
        · obtain ⟨hne, hzero⟩ := V.fnz_some_spec v i hf
          have hi := V.lt_length_of_fnz v i hf
          cases hd : T.dom (V.get0 v i) with
          | zero => exact absurd (eq_Z_of_dom_zero hd) hne
          | one =>
            cases i with
            | zero =>
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
                    obtain ⟨_, he, hhe, _⟩ := hb.inv
                    obtain ⟨m, hm⟩ := mul_cofinal e he
                      (T.le_trans hhe (Or.inr ((T.P_eqv_iff _ _ Z Z).2 ⟨hyv, compareT_ZZ⟩)))
                    exact ⟨m + 1, T.P_lt_P_of_eqv hyv hm⟩
                · refine ⟨1, T.P_lt_P_of_vlt _ _ ?_⟩
                  apply V.lt_of_pivot p
                  · intro j hj; exact T.eqv_trans (hpeq j hj) (T.eqv_symm (hset j (by omega)))
                  · exact T.lt_of_lt_of_eqv hplt (T.eqv_symm (hset p hp))
            | succ k =>
              simp only [fund_PZ_oneS hf hd]
              exact iter_cofinal hi hzero hd b hb hba
          | omega =>
            simp only [fund_PZ_omega hf hd]
            cases b with
            | Z => exact ⟨0, T.Z_lt_P _ _⟩
            | P y e =>
              have hy := vlt_of_P_lt hba
              obtain ⟨p, hpeq, hplt⟩ := (V.lt_iff_pivot y v).1 hy
              have hip := pivot_above_zero hzero hplt
              rcases Nat.lt_or_eq_of_le hip with hip | hip
              · refine ⟨0, T.P_lt_P_of_vlt _ _ ?_⟩
                apply V.lt_of_pivot p
                · intro j hj
                  exact T.eqv_trans (hpeq j hj)
                    (T.eqv_symm (V.get0_set_eqv_above v i _ j (by omega)))
                · exact T.lt_of_lt_of_eqv hplt (T.eqv_symm (V.get0_set_eqv_above v i _ p hip))
              · subst hip
                obtain ⟨hyv, _, _, _⟩ := hb.inv
                obtain ⟨n, hn⟩ := ih _ (T.size_get0_lt_P v i Z) (hv i) hd _ (hyv i) hplt
                refine ⟨n, T.P_lt_P_of_vlt _ _ ?_⟩
                apply V.lt_of_pivot i
                · intro j hj
                  exact T.eqv_trans (hpeq j hj) (T.eqv_symm (V.get0_set_eqv_above v i _ j hj))
                · rw [V.get0_set_same v i _ hi]; exact hn
      · simp only [fund_tail v hcz]
        have hdc : T.dom c = .omega := by rwa [dom_tail v hcz] at hda
        cases b with
        | Z => exact ⟨0, T.Z_lt_P _ _⟩
        | P y e =>
          rcases (T.P_lt_P_iff y v e c).1 hba with hy | ⟨hy, he⟩
          · exact ⟨0, T.P_lt_P_of_vlt _ _ hy⟩
          · obtain ⟨n, hn⟩ := ih c (T.size_lt_P_right v c) hc hdc e hb.inv.2.1 he
            exact ⟨n, T.P_lt_P_of_eqv hy hn⟩

theorem cofinal (a b : multi.T) (ha : NF a) (hb : NF b) (hba : b < a) :
    ∃ n, b ≤ T.fund a (T.ofNat n) := by
  cases hd : T.dom a with
  | zero => rw [eq_Z_of_dom_zero hd] at hba; exact absurd hba (T.not_lt_Z _)
  | one => exact ⟨0, fund_one_upper a hd b hba⟩
  | omega =>
    obtain ⟨n, hn⟩ := omega_cofinal a ha hd b hb hba
    exact ⟨n, Or.inl hn⟩

/-! ### Bases -/

theorem get0_LF : ∀ n j, V.get0 (T.LF n) j = if j = n then T.ofNat 1 else Z
  | 0, j => by
    rw [T.LF]
    rfl
  | n + 1, j => by
    rw [T.LF, V.get0_append, get0_LF n]
    have hlen : (V.snoc Z V.emp : V multi.T).length = 1 := rfl
    rw [hlen]
    by_cases hj : j < 1
    · rw [ite_eq_left hj]
      have hj0 : j = 0 := by omega
      subst hj0
      rw [ite_eq_right (fun h => Nat.succ_ne_zero n h.symm)]
      rfl
    · rw [ite_eq_right hj]
      by_cases hjn : j = n + 1
      · rw [ite_eq_left (show j - 1 = n by omega), ite_eq_left hjn]
      · rw [ite_eq_right (show ¬ j - 1 = n by omega), ite_eq_right hjn]

theorem emp_lt_LF (n : Nat) : (V.emp : V multi.T) < T.LF n := by
  apply V.lt_of_pivot n
  · intro j hj
    rw [get0_LF, ite_eq_right (Nat.ne_of_gt hj)]
    exact compareT_ZZ
  · rw [get0_LF, ite_eq_left rfl]
    exact T.Z_lt_P _ _

theorem NF_base (n : Nat) : NF (sys.base n) := by
  refine NF.p _ _ (fun j => ?_) NF.z (T.Z_le _) (fun j => ?_)
  · show NF (V.get0 (T.LF n) j)
    rw [get0_LF]; split
    · exact NF_ofNat 1
    · exact NF.z
  · show V.get0 (T.LF n) j < P (T.LF n) Z
    rw [get0_LF]; split
    · exact T.P_lt_P_of_vlt _ _ (emp_lt_LF n)
    · exact T.Z_lt_P _ _

theorem le_base (s : multi.T) : ∃ n, s ≤ sys.base n := by
  cases s with
  | Z => exact ⟨0, T.Z_le _⟩
  | P v a =>
    refine ⟨v.length, Or.inl (T.P_lt_P_of_vlt _ _ ?_)⟩
    apply V.lt_of_pivot v.length
    · intro j hj
      rw [V.get0_ge v j (Nat.le_of_lt hj), get0_LF, ite_eq_right (Nat.ne_of_gt hj)]
      exact compareT_ZZ
    · rw [V.get0_ge v _ (Nat.le_refl _), get0_LF, ite_eq_left rfl]
      exact T.Z_lt_P _ _

end emp

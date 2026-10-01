import Subsp.old.stop_source_dim

/-! Source-side bounds for legacy OT terms. -/

namespace new

def T.otBound (lam : Nat) : T lam :=
  T.P
    (Vec.ofFn lam
      (fun x => if x.val = 1 then
        T.P (Vec.ofFn lam (fun _ => T.Z)) T.Z
      else T.Z))
    T.Z

theorem T.base_succ_lt_otBound (k n : Nat) (hk : 1 < k + 1) :
    T.P
      (Vec.ofFn (k + 1)
        (fun i => if i.val = 0 then T.LF (k + 1) n else T.Z))
      T.Z <
    T.otBound (k + 1) := by
  apply T.P_lt_P_of_compareVec_lt
  apply Vec.compare_lt_of_pivot _ _ ⟨1, hk⟩
  · intro j hj
    change 1 < j.val at hj
    simp only [T.otBound, Vec.ofFn_idx, show j.val ≠ 0 by omega,
      show j.val ≠ 1 by omega, ite_false]
  · simp only [T.otBound, Vec.ofFn_idx, Nat.one_ne_zero, ite_false, ite_true]
    rfl

theorem T.isOT_sound_bound (lam : Nat) (s : T lam)
    (hs : T.isOT lam s) :
    T.isNF s ∧ (1 < lam → s < T.otBound lam) := by
  induction hs with
  | base_0 n =>
      exact ⟨T.LF_isNF 0 n, by intro h; omega⟩
  | base_succ k n =>
      exact ⟨T.base_succ_isNF k n, T.base_succ_lt_otBound k n⟩
  | step lam a _ n ih =>
      refine ⟨T.fund_NF_closed a (T.ofNat n) ih.1 (T.ofNat_isNFComp 0 n), ?_⟩
      intro hlam
      by_cases haz : a = T.Z
      · subst a
        rw [T.fund]
        rfl
      · exact strict_partial_order.trans _ _ _
          (T.fund_lt_self a (T.ofNat n) haz) (ih.2 hlam)

end new

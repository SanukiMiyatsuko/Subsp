import Subsp.old.stop_source_nf

/-! Weak-normal-form closure for the legacy fundamental sequences. -/

namespace new

theorem T.le_trans {lam : Nat} (a b c : T lam)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with h | h
  · rcases hbc with h' | h'
    · exact Or.inl (T_trans _ _ _ h h')
    · rw [← T_eq_sound _ _ h']
      exact Or.inl h
  · rw [T_eq_sound _ _ h]
    exact hbc

theorem T.iter_isWNF {lam : Nat} (F : T lam → T lam)
    (hF : ∀ x, T.isWNF x → T.isWNF (F x)) :
    ∀ t : T lam, T.isWNF (T.iter F t) := by
  intro t
  induction t using (measure T.size).wf.induction with
  | h t ih =>
      cases t with
      | Z => exact .z
      | P ls add =>
          rw [T.iter]
          exact hF _ (ih add (T.add_size_lt_P ls add))

theorem T.fund_isWNF {lam : Nat} :
    ∀ s : T lam, T.isWNF s →
      ∀ t : T lam, T.isWNF t → T.isWNF (T.fund s t) := by
  intro s
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      intro hs t ht
      cases s with
      | Z =>
          rw [T.fund]
          exact .z
      | P ls add =>
          obtain ⟨hls, haddNF, hhead⟩ := T.isWNF_P_inv ls add hs
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none =>
                rw [T.fund, ite_eq_left rfl, hmin]
                exact .z
            | some md =>
                obtain ⟨m, d⟩ := md
                have hrec (u : T lam) (hu : T.isWNF u) :
                    T.isWNF (T.fund (ls.idx m) u) :=
                  ih (ls.idx m) (T.idx_size_lt_P ls T.Z m) (hls m) u hu
                rw [T.fund, ite_eq_left rfl, hmin]
                cases d with
                | zero =>
                    apply T.isWNF_PZ_of_coords
                    exact T.isWNF_rplc ls m _ hls (hrec t ht)
                | omega =>
                    apply T.isWNF_PZ_of_coords
                    exact T.isWNF_rplc ls m _ hls (hrec t ht)
                | Omega i =>
                    split
                    · apply T.isWNF_PZ_of_coords
                      exact T.isWNF_rplc ls m _ hls (hrec t ht)
                    · apply T.isWNF_PZ_of_coords
                      apply T.isWNF_rplc ls m _ hls
                      apply hrec
                      apply T.iter_isWNF
                      intro x hx
                      exact hrec x hx
                | one =>
                    obtain ⟨mv, mh⟩ := m
                    cases mv with
                    | zero =>
                        apply T.principal_mul_isWNF
                        exact T.isWNF_rplc ls ⟨0, mh⟩ _ hls (hrec T.Z .z)
                    | succ r =>
                        apply T.isWNF_PZ_of_coords
                        apply T.isWNF_rplc
                          (ls.rplc ⟨r + 1, mh⟩
                            (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z))
                          ⟨r, Nat.lt_of_succ_lt mh⟩ t
                        · exact T.isWNF_rplc ls ⟨r + 1, mh⟩ _ hls (hrec T.Z .z)
                        · exact ht
          · rw [T.fund, ite_eq_right hadd]
            refine .p ls _ hls
              (ih add (T.add_size_lt_P ls add) haddNF t ht) ?_
            exact T.le_trans _ _ _ (T.head_mono _ _ (T.fund_lt_self add t hadd)) hhead

theorem T.LF_isWNF (lam n : Nat) :
    T.isWNF (T.LF lam n) := by
  induction n generalizing lam with
  | zero =>
      rw [T.LF]
      exact .z
  | succ n ih =>
      cases lam with
      | zero =>
          rw [T.LF]
          refine .p new.Vec.nil _ (fun i => i.elim0) (ih 0) ?_
          cases n with
          | zero => exact T.Z_le _
          | succ n =>
              exact Or.inr (by simp only [T.LF, T.head, compareT, Vec_refl, T_refl])
      | succ k =>
          rw [T.LF]
          apply T.isWNF_PZ_of_coords
          intro i
          rw [Vec.ofFn_idx]
          split
          · exact ih (k + 1)
          · exact .z

theorem T.isOT_isWNF {lam : Nat} (s : T lam)
    (hs : T.isOT lam s) : T.isWNF s := by
  induction hs with
  | base_0 n => exact T.LF_isWNF 0 n
  | base_succ k n =>
      apply T.isWNF_PZ_of_coords
      intro i
      rw [Vec.ofFn_idx]
      split
      · exact T.LF_isWNF (k + 1) n
      · exact .z
  | step lam s _ n ih =>
      exact T.fund_isWNF s ih (T.ofNat n) (T.ofNat_isWNF n)

end new

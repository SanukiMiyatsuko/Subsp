import Subsp.old.stop_ot_shape

/-! A stronger outer-chain invariant for legacy OT terms: every exposed vector
coordinate is a level-zero normal component. -/

namespace new

def T.outerComp0Chain {lam : Nat} : T lam → Prop
  | .Z => True
  | .P ls add =>
      Vec.outer0 ls ∧
      (∀ i : Fin lam, T.isNFComp 0 (ls.idx i)) ∧
      T.outerComp0Chain add

theorem T.LF_isNFComp0 (lam n : Nat) :
    T.isNFComp 0 (T.LF lam n) :=
  ⟨T.LF_isNF lam n, T.LF_support lam n 0⟩

theorem T.outerComp0Chain_mul_PZ {lam : Nat}
    (v : Vec (T lam) lam) (t : T lam)
    (hv0 : Vec.outer0 v)
    (hvc : ∀ i : Fin lam, T.isNFComp 0 (v.idx i)) :
    T.outerComp0Chain (T.mul (T.P v T.Z) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => trivial
  | P tv add _ ih =>
      rw [T.mul]
      exact ⟨hv0, hvc, ih⟩
  | nil => trivial
  | snoc => trivial

theorem T.outerComp0Chain_fund {lam : Nat}
    (s t : T lam) (hs : T.outerComp0Chain s) :
    T.outerComp0Chain (T.fund s t) := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z => simp [T.fund, T.outerComp0Chain]
      | P ls add =>
          have hls0 : Vec.outer0 ls := hs.1
          have hlsc : ∀ i : Fin lam, T.isNFComp 0 (ls.idx i) := hs.2.1
          have haddChain : T.outerComp0Chain add := hs.2.2
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none =>
                rw [T.fund, ite_eq_left rfl, hmin]
                trivial
            | some md =>
                obtain ⟨m, d⟩ := md
                have hm0 := Vec.outer0_min_index_zero ls hls0 m d hmin
                have hcoord0 : T.isNFComp 0 (ls.idx m) := hlsc m
                have hrplc0 (z : T lam) :
                    Vec.outer0 (ls.rplc m z) :=
                  Vec.outer0_rplc_zero ls m z hls0 hm0
                have hrplcComp (z : T lam) (hz : T.isNFComp 0 z) :
                    ∀ i : Fin lam, T.isNFComp 0 ((ls.rplc m z).idx i) := by
                  intro i
                  by_cases him : i.val = m.val
                  · rw [Fin.eq_of_val_eq him, Vec.rplc_idx_same]
                    exact hz
                  · rw [Vec.rplc_idx_of_ne _ _ _ _ him]
                    exact hlsc i
                rw [T.fund, ite_eq_left rfl, hmin]
                cases d with
                | zero =>
                    exact False.elim ((T.domVecMinIdx_some_spec ls m .zero hmin).1 rfl)
                | one =>
                    obtain ⟨mv, mh⟩ := m
                    cases mv with
                    | zero =>
                        have hc :
                            T.isNFComp 0
                              (T.fund (ls.idx ⟨0, mh⟩) T.Z) :=
                          T.fund_one_NFComp 0 _ T.Z (hlsc ⟨0, mh⟩)
                            (T.domVecMinIdx_some_spec ls ⟨0, mh⟩ .one hmin).2.1
                        exact T.outerComp0Chain_mul_PZ _ t
                          (hrplc0 _) (hrplcComp _ hc)
                    | succ r =>
                        change r + 1 = 0 at hm0
                        exact False.elim (Nat.noConfusion hm0)
                | omega =>
                    have hc :
                        T.isNFComp 0 (T.fund (ls.idx m) t) :=
                      T.fund_omega_NFComp_closed 0 _ t hcoord0
                        (T.domVecMinIdx_some_spec ls m .omega hmin).2.1
                    exact ⟨hrplc0 _, hrplcComp _ hc, trivial⟩
                | Omega i =>
                    have hd : T.dom (ls.idx m) = .Omega i :=
                      (T.domVecMinIdx_some_spec ls m (.Omega i) hmin).2.1
                    have hi : 0 < i.val := T.dom_Omega_pos (ls.idx m) i hd
                    have hc :
                        T.isNFComp 0
                          (T.fund (ls.idx m)
                            (T.iter (T.fund (ls.idx m)) t)) :=
                      (T.fund_iter_NFComp 0 (ls.idx m) t i hi hcoord0 hd).1
                    have hnot := T.outer0_Omega_not_le ls hls0 m i hmin
                    simp only [hnot, ite_false]
                    exact ⟨hrplc0 _, hrplcComp _ hc, trivial⟩
          · rw [T.fund, ite_eq_right hadd]
            exact ⟨hls0, hlsc,
              ih add (T.add_size_lt_P ls add) t haddChain⟩

theorem T.base_succ_outerComp0Chain (k n : Nat) :
    T.outerComp0Chain
      (T.P (Vec.ofFn (k + 1)
        (fun i => if i.val = 0 then T.LF (k + 1) n else T.Z)) T.Z) := by
  refine ⟨?_, ?_, trivial⟩
  · intro i hi
    rw [Vec.ofFn_idx]
    simp [hi]
  · intro i
    rw [Vec.ofFn_idx]
    split
    · exact T.LF_isNFComp0 (k + 1) n
    · exact T.isNFComp_Z 0

theorem T.isOT_outerComp0Chain {lam : Nat} {s : T lam}
    (hs : T.isOT lam s) : T.outerComp0Chain s := by
  induction hs with
  | base_0 n =>
      induction n with
      | zero => trivial
      | succ n ih =>
          rw [T.LF]
          exact ⟨fun i => i.elim0, fun i => i.elim0, ih⟩
  | base_succ k n => exact T.base_succ_outerComp0Chain k n
  | step lam s hs n ih =>
      exact T.outerComp0Chain_fund s (T.ofNat n) ih

end new

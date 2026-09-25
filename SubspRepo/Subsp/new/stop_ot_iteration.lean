import Subsp.new.stop_ot_char

open T

theorem ot_iter_ofNat_succ {lam : Nat} (a : new.T lam) (n : Nat) :
    new.T.iter (fun x => new.T.fund a x) (new.T.ofNat (n + 1)) =
      new.T.fund a (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
  rw [new.T.ofNat, new.T.iter]

#print axioms ot_iter_ofNat_succ

theorem ot_iteration_cofinal {lam : Nat} (a : new.T lam)
    (ha : new.T.isNFComp a) (hd : new.T.dom a = .Omega) :
    ∀ b : new.T lam, new.T.isNFComp b → b < a →
      ∃ n : Nat,
        b < new.T.fund a
          (new.T.iter (fun x => new.T.fund a x) (new.T.ofNat n)) := by
  let F := fun x : new.T lam => new.T.fund a x
  let motive : Nat → Prop := fun n =>
    ∀ b : new.T lam, new.T.size b = n → new.T.isNFComp b → b < a →
      ∃ k : Nat, b < F (new.T.iter F (new.T.ofNat k))
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro b hbsize hbcomp hba
      have descend :
          ∀ cur : new.T lam, new.T.size cur ≤ new.T.size a →
            new.T.isNF cur → new.T.dom cur = .Omega →
            ∀ tgt : new.T lam, new.T.isNF tgt → tgt < cur →
              (∀ x : new.T lam, x ∈ new.T.G tgt → x ∈ new.T.G b) →
              ∃ k : Nat, tgt < new.T.fund cur
                (new.T.iter F (new.T.ofNat k)) := by
        intro cur hcurSize
        let dmotive : Nat → Prop := fun m =>
          ∀ c : new.T lam, new.T.size c = m → new.T.isNF c →
            new.T.dom c = .Omega →
            ∀ tgt : new.T lam, new.T.isNF tgt → tgt < c →
              (∀ x : new.T lam, x ∈ new.T.G tgt → x ∈ new.T.G b) →
              ∃ k : Nat, tgt < new.T.fund c
                (new.T.iter F (new.T.ofNat k))
        have dmain : ∀ m : Nat, dmotive m := by
          intro m
          exact Nat.strongRecOn m (motive := dmotive) (fun m dih => by
            intro c hcsize hcnf hcdom tgt htgnf htgc hmem
            cases c with
            | Z =>
                change new.Dom.zero = new.Dom.Omega at hcdom
                cases hcdom
            | P ls add =>
                by_cases hadd : add = new.T.Z
                · subst add
                  cases hmin : new.T.domVecMinIdx ls with
                  | none =>
                      have hh := hcdom
                      rw [new.T.dom, ite_eq_left rfl, hmin] at hh
                      change new.Dom.one = new.Dom.Omega at hh
                      cases hh
                  | some md =>
                      obtain ⟨mi, d⟩ := md
                      have hh := hcdom
                      rw [new.T.dom, ite_eq_left rfl, hmin] at hh
                      change
                        (if d = new.Dom.one then
                          if mi.val = 0 then new.Dom.omega else new.Dom.Omega
                        else new.Dom.omega) = new.Dom.Omega at hh
                      have hd1 : d = new.Dom.one := by
                        by_cases h : d = new.Dom.one
                        · exact h
                        · rw [ite_eq_right h] at hh
                          cases hh
                      have hmi0 : mi.val ≠ 0 := by
                        rw [ite_eq_left hd1] at hh
                        intro hz
                        rw [ite_eq_left hz] at hh
                        cases hh
                      have hspec := new.T.domVecMinIdx_some_spec ls mi d hmin
                      have hchildDom : new.T.dom (ls.idx mi) = new.Dom.one := by
                        rw [hspec.2.1, hd1]
                      cases mi with
                      | mk mv mh =>
                          cases mv with
                          | zero => exact False.elim (hmi0 rfl)
                          | succ r =>
                              let mi' : Fin lam := ⟨r + 1, mh⟩
                              let mj : Fin lam := ⟨r, Nat.lt_of_succ_lt mh⟩
                              let base := ls.rplc mi'
                                (new.T.fund (ls.idx mi') new.T.Z)
                              have hmiEq : mi' = ⟨r + 1, mh⟩ := rfl
                              cases tgt with
                              | Z =>
                                  refine ⟨0, ?_⟩
                                  have hne :
                                      new.T.fund (new.T.P ls new.T.Z)
                                          (new.T.iter F (new.T.ofNat 0)) ≠ new.T.Z :=
                                    new.T.fund_Omega_ne_Z (new.T.P ls new.T.Z)
                                      (new.T.iter F (new.T.ofNat 0)) hcdom
                                  cases new.T.Z_le
                                      (new.T.fund (new.T.P ls new.T.Z)
                                        (new.T.iter F (new.T.ofNat 0))) with
                                  | inl hlt => exact hlt
                                  | inr heq =>
                                      have hz := new.T_eq_sound new.T.Z
                                        (new.T.fund (new.T.P ls new.T.Z)
                                          (new.T.iter F (new.T.ofNat 0))) heq
                                      exact False.elim (hne hz.symm)
                              | P ws tail =>
                                  have hvec : new.compareVec ws ls = Ordering.lt := by
                                    change
                                      (match new.compareVec ws ls with
                                      | Ordering.eq => new.compareT tail new.T.Z
                                      | ord => ord) = Ordering.lt at htgc
                                    cases hc : new.compareVec ws ls with
                                    | lt => exact rfl
                                    | eq =>
                                        rw [hc] at htgc
                                        exact False.elim (ot_lt_Z_inv tail htgc)
                                    | gt =>
                                        rw [hc] at htgc
                                        cases htgc
                                  obtain ⟨q, hqAbove, hqLt⟩ :=
                                    new.Vec.compare_lt_has_pivot ws ls hvec
                                  have hfundShape : ∀ z : new.T lam,
                                      new.T.fund (new.T.P ls new.T.Z) z =
                                        new.T.P (base.rplc mj z) new.T.Z := by
                                    intro z
                                    conv =>
                                      lhs
                                      rw [new.T.fund, ite_eq_left rfl, hmin]
                                      change (if d = new.Dom.one then _ else _)
                                      rw [ite_eq_left hd1]
                                    change
                                      new.T.P
                                        ((ls.rplc mi'
                                          (new.T.fund (ls.idx mi') new.T.Z)).rplc mj z)
                                        new.T.Z =
                                      new.T.P (base.rplc mj z) new.T.Z
                                    rfl
                                  cases Nat.lt_trichotomy q.val (r + 1) with
                                  | inl hqmi =>
                                      have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                                        hspec.2.2 q hqmi
                                      have hqz := new.T.dom_zero_eq_Z (ls.idx q) hqDom
                                      rw [hqz] at hqLt
                                      exact False.elim (ot_lt_Z_inv (ws.idx q) hqLt)
                                  | inr hrel =>
                                      cases hrel with
                                      | inr hmiq =>
                                          refine ⟨0, ?_⟩
                                          rw [hfundShape]
                                          apply new.T.P_lt_P_of_compareVec_lt
                                          apply new.Vec.compare_lt_of_pivot ws
                                            (base.rplc mj
                                              (new.T.iter F (new.T.ofNat 0))) q
                                          · intro j hqj
                                            have hjmi : j.val ≠ r + 1 :=
                                              Nat.ne_of_gt (Nat.lt_trans hmiq hqj)
                                            have hjmj : j.val ≠ r :=
                                              Nat.ne_of_gt
                                                (Nat.lt_trans (Nat.lt_succ_self r)
                                                  (Nat.lt_trans hmiq hqj))
                                            unfold base
                                            rw [new.Vec.rplc_idx_of_ne _ mj j _ hjmj]
                                            rw [new.Vec.rplc_idx_of_ne ls mi' j _ hjmi]
                                            exact hqAbove j hqj
                                          · have hqmiNe : q.val ≠ r + 1 := Nat.ne_of_gt hmiq
                                            have hqmjNe : q.val ≠ r := by
                                              intro hqr
                                              rw [hqr] at hmiq
                                              exact Nat.lt_irrefl r
                                                (Nat.lt_trans (Nat.lt_succ_self r) hmiq)
                                            unfold base
                                            rw [new.Vec.rplc_idx_of_ne _ mj q _ hqmjNe]
                                            rw [new.Vec.rplc_idx_of_ne ls mi' q _ hqmiNe]
                                            exact hqLt
                                      | inl hqmiEq =>
                                          have hqEq : q = mi' := by
                                            apply Fin.eq_of_val_eq
                                            exact hqmiEq
                                          subst q
                                          have hupper : ws.idx mi' ≤
                                              new.T.fund (ls.idx mi') new.T.Z :=
                                            ot_fund_one_upper (ls.idx mi') hchildDom
                                              (ws.idx mi') hqLt
                                          cases hupper with
                                          | inl hstrict =>
                                              refine ⟨0, ?_⟩
                                              rw [hfundShape]
                                              apply new.T.P_lt_P_of_compareVec_lt
                                              apply new.Vec.compare_lt_of_pivot ws
                                                (base.rplc mj
                                                  (new.T.iter F (new.T.ofNat 0))) mi'
                                              · intro j hmij
                                                have hjmj : j.val ≠ r := by
                                                  exact Nat.ne_of_gt
                                                    (Nat.lt_trans (Nat.lt_succ_self r) hmij)
                                                have hjmi : j.val ≠ r + 1 := Nat.ne_of_gt hmij
                                                unfold base
                                                rw [new.Vec.rplc_idx_of_ne _ mj j _ hjmj]
                                                rw [new.Vec.rplc_idx_of_ne ls mi' j _ hjmi]
                                                exact hqAbove j hmij
                                              · have hmjmi : mi'.val ≠ mj.val := by
                                                  change r + 1 ≠ r
                                                  exact Nat.ne_of_gt (Nat.lt_succ_self r)
                                                rw [new.Vec.rplc_idx_of_ne base mj mi' _ hmjmi]
                                                unfold base
                                                rw [new.Vec.rplc_idx_same]
                                                exact hstrict
                                          | inr heq =>
                                              have hcoordEq : ws.idx mi' =
                                                  new.T.fund (ls.idx mi') new.T.Z :=
                                                new.T_eq_sound _ _ heq
                                              let c0 := ws.idx mj
                                              have hcMemTgt : c0 ∈ new.T.G (new.T.P ws tail) := by
                                                apply (new.T.mem_G_P ws tail c0).mpr
                                                exact Or.inl ⟨mj, Or.inl rfl⟩
                                              have hcMemB : c0 ∈ new.T.G b :=
                                                hmem c0 hcMemTgt
                                              have hcComp : new.T.isNFComp c0 :=
                                                new.T.isNF_G_isNFComp b hbcomp.1 c0 hcMemB
                                              have hcLtB : c0 < b := hbcomp.2 c0 hcMemB
                                              have hcLtA : c0 < a :=
                                                strict_partial_order.trans c0 b a hcLtB hba
                                              have hcSize : new.T.size c0 < n := by
                                                have hs := new.T.G_size_lt b c0 hcMemB
                                                rw [hbsize] at hs
                                                exact hs
                                              obtain ⟨k, hk⟩ :=
                                                ih (new.T.size c0) hcSize c0 rfl hcComp hcLtA
                                              refine ⟨k + 1, ?_⟩
                                              rw [hfundShape]
                                              apply new.T.P_lt_P_of_compareVec_lt
                                              apply new.Vec.compare_lt_of_pivot ws
                                                (base.rplc mj
                                                  (new.T.iter F (new.T.ofNat (k + 1)))) mj
                                              · intro j hmjj
                                                have hmiLeJ : r + 1 ≤ j.val :=
                                                  Nat.succ_le_of_lt hmjj
                                                cases Nat.eq_or_lt_of_le hmiLeJ with
                                                | inl hEq =>
                                                    have hjmi : j = mi' := by
                                                      apply Fin.eq_of_val_eq
                                                      exact hEq.symm
                                                    subst j
                                                    have hmjmi : mi'.val ≠ mj.val := by
                                                      change r + 1 ≠ r
                                                      exact Nat.ne_of_gt (Nat.lt_succ_self r)
                                                    rw [new.Vec.rplc_idx_of_ne base mj mi' _ hmjmi]
                                                    unfold base
                                                    rw [new.Vec.rplc_idx_same]
                                                    exact hcoordEq
                                                | inr hmiJ =>
                                                    have hjmj : j.val ≠ r :=
                                                      Nat.ne_of_gt (Nat.lt_trans
                                                        (Nat.lt_succ_self r) hmiJ)
                                                    have hjmi : j.val ≠ r + 1 := Nat.ne_of_gt hmiJ
                                                    unfold base
                                                    rw [new.Vec.rplc_idx_of_ne _ mj j _ hjmj]
                                                    rw [new.Vec.rplc_idx_of_ne ls mi' j _ hjmi]
                                                    exact hqAbove j hmiJ
                                              · rw [new.Vec.rplc_idx_same]
                                                change c0 < new.T.iter F (new.T.ofNat (k + 1))
                                                rw [ot_iter_ofNat_succ a k]
                                                exact hk
                · have haddDom : new.T.dom add = new.Dom.Omega := by
                    rw [new.T.dom, ite_eq_right hadd] at hcdom
                    exact hcdom
                  have haddNF : new.T.isNF add := by
                    cases hcnf with
                    | p _ _ _ haTail _ _ => exact haTail
                  cases tgt with
                  | Z =>
                      refine ⟨0, ?_⟩
                      rw [new.T.fund_P_tail_eq ls add
                        (new.T.iter F (new.T.ofNat 0)) hadd]
                      rfl
                  | P ws tail =>
                      change
                        (match new.compareVec ws ls with
                        | Ordering.eq => new.compareT tail add
                        | ord => ord) = Ordering.lt at htgc
                      cases hc : new.compareVec ws ls with
                      | lt =>
                          refine ⟨0, ?_⟩
                          rw [new.T.fund_P_tail_eq ls add
                            (new.T.iter F (new.T.ofNat 0)) hadd]
                          exact new.T.P_lt_P_of_compareVec_lt ws ls tail
                            (new.T.fund add (new.T.iter F (new.T.ofNat 0))) hc
                      | gt =>
                          rw [hc] at htgc
                          cases htgc
                      | eq =>
                          rw [hc] at htgc
                          have hws : ws = ls := new.Vec_eq_sound ws ls hc
                          subst ws
                          have htailNF : new.T.isNF tail := by
                            cases htgnf with
                            | p _ _ _ ht _ _ => exact ht
                          have haddSize : new.T.size add < m := by
                            have hs := new.T.add_size_lt_P ls add
                            rw [hcsize] at hs
                            exact hs
                          have hmemTail :
                              ∀ x : new.T lam, x ∈ new.T.G tail → x ∈ new.T.G b := by
                            intro x hx
                            apply hmem x
                            apply (new.T.mem_G_P ls tail x).mpr
                            exact Or.inr hx
                          obtain ⟨k, hk⟩ :=
                            dih (new.T.size add) haddSize add rfl haddNF haddDom
                              tail htailNF htgc hmemTail
                          refine ⟨k, ?_⟩
                          rw [new.T.fund_P_tail_eq ls add
                            (new.T.iter F (new.T.ofNat k)) hadd]
                          exact new.T.P_tail_lt ls tail
                            (new.T.fund add (new.T.iter F (new.T.ofNat k))) hk)
        exact dmain (new.T.size cur) cur rfl
      exact descend a (Nat.le_refl _) ha.1 hd b hbcomp.1 hba
        (fun x hx => hx))
  intro b hb hba
  exact main (new.T.size b) b rfl hb hba

#print axioms ot_iteration_cofinal

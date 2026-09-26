import Subsp.new.stop_ot_iteration

open T

theorem ot_fund_omega_cofinal {lam : Nat} :
    ∀ a : new.T lam, new.T.isNF a → new.T.dom a = .omega →
      ∀ b : new.T lam, new.T.isNF b → b < a →
        ∃ n : Nat, b < new.T.fund a (new.T.ofNat n) := by
  let motive : Nat → Prop := fun n =>
    ∀ a : new.T lam, new.T.size a = n → new.T.isNF a →
      new.T.dom a = .omega →
      ∀ b : new.T lam, new.T.isNF b → b < a →
        ∃ k : Nat, b < new.T.fund a (new.T.ofNat k)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a hasize ha hdom b hb hba
      cases a with
      | Z =>
          change new.Dom.zero = new.Dom.omega at hdom
          cases hdom
      | P ls add =>
          have hcoords := new.T.isNF_P_coord_NFComp ls add ha
          apply Decidable.byCases (p := add = new.T.Z)
          · intro hadd
            cases hadd
            cases hmin : new.T.domVecMinIdx ls with
            | none =>
                have hh := hdom
                rw [new.T.dom, ite_eq_left rfl, hmin] at hh
                change new.Dom.one = new.Dom.omega at hh
                cases hh
            | some md =>
                cases md with
                | mk m d =>
                  have hspec := new.T.domVecMinIdx_some_spec ls m d hmin
                  have hh := hdom
                  rw [new.T.dom, ite_eq_left rfl, hmin] at hh
                  cases d with
                  | zero =>
                      exact False.elim (hspec.1 rfl)
                  | one =>
                      change
                        (if m.val = 0 then new.Dom.omega else new.Dom.Omega) =
                          new.Dom.omega at hh
                      have hm0 : m.val = 0 := by
                        apply Decidable.byCases (p := m.val = 0)
                        · intro hm
                          exact hm
                        · intro hm
                          rw [ite_eq_right hm] at hh
                          cases hh
                      have hhead := ot_head_le_one_base ls m hmin hm0 b hb hba
                      let ⟨k, hk⟩ :=
                        ot_mul_cofinal
                          (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) b hb hhead
                      refine ⟨k, ?_⟩
                      cases m with
                      | mk mv mh =>
                          change mv = 0 at hm0
                          cases hm0
                          rw [new.T.fund, ite_eq_left rfl, hmin]
                          exact hk
                  | omega =>
                      have hchildDom : new.T.dom (ls.idx m) = new.Dom.omega :=
                        hspec.2.1
                      have hchildNF : new.T.isNF (ls.idx m) := (hcoords m).1
                      have hchildSize : new.T.size (ls.idx m) < n := by
                        have hs := new.T.idx_size_lt_P ls new.T.Z m
                        rw [new.Vec.getElem_eq_idx, hasize] at hs
                        exact hs
                      cases b with
                      | Z =>
                          refine ⟨0, ?_⟩
                          rw [new.T.fund, ite_eq_left rfl, hmin]
                          rfl
                      | P ws tail =>
                          have hvec : new.compareVec ws ls = Ordering.lt := by
                            change
                              (match new.compareVec ws ls with
                              | Ordering.eq => new.compareT tail new.T.Z
                              | ord => ord) = Ordering.lt at hba
                            cases hc : new.compareVec ws ls with
                            | lt => exact rfl
                            | eq =>
                                rw [hc] at hba
                                exact False.elim (ot_lt_Z_inv tail hba)
                            | gt =>
                                rw [hc] at hba
                                cases hba
                          let ⟨q, hqAbove, hqLt⟩ :=
                            new.Vec.compare_lt_has_pivot ws ls hvec
                          cases Nat.lt_trichotomy q.val m.val with
                          | inl hqm =>
                              have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                                hspec.2.2 q hqm
                              have hqz := new.T.dom_zero_eq_Z (ls.idx q) hqDom
                              rw [hqz] at hqLt
                              exact False.elim (ot_lt_Z_inv (ws.idx q) hqLt)
                          | inr hrel =>
                              cases hrel with
                              | inr hmq =>
                                  refine ⟨0, ?_⟩
                                  rw [new.T.fund, ite_eq_left rfl, hmin]
                                  apply new.T.P_lt_P_of_compareVec_lt
                                  apply new.Vec.compare_lt_of_pivot ws
                                    (ls.rplc m (new.T.fund (ls.idx m) (new.T.ofNat 0))) q
                                  · intro j hqj
                                    have hjm : j.val ≠ m.val :=
                                      Nat.ne_of_gt (Nat.lt_trans hmq hqj)
                                    rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                    exact hqAbove j hqj
                                  · have hqmNe : q.val ≠ m.val := Nat.ne_of_gt hmq
                                    rw [new.Vec.rplc_idx_of_ne ls m q _ hqmNe]
                                    exact hqLt
                              | inl hqmEq =>
                                  have hqEq : q = m := Fin.eq_of_val_eq hqmEq
                                  cases hqEq
                                  have htargetComp : new.T.isNFComp (ws.idx m) :=
                                    new.T.isNF_P_coord_NFComp ws tail hb m
                                  let ⟨k, hk⟩ :=
                                    ih (new.T.size (ls.idx m)) hchildSize
                                      (ls.idx m) rfl hchildNF hchildDom
                                      (ws.idx m) htargetComp.1 hqLt
                                  refine ⟨k, ?_⟩
                                  rw [new.T.fund, ite_eq_left rfl, hmin]
                                  apply new.T.P_lt_P_of_compareVec_lt
                                  apply new.Vec.compare_lt_of_pivot ws
                                    (ls.rplc m (new.T.fund (ls.idx m) (new.T.ofNat k))) m
                                  · intro j hmj
                                    have hjm : j.val ≠ m.val := Nat.ne_of_gt hmj
                                    rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                    exact hqAbove j hmj
                                  · rw [new.Vec.rplc_idx_same]
                                    exact hk
                  | Omega =>
                      have hchildDom : new.T.dom (ls.idx m) = new.Dom.Omega :=
                        hspec.2.1
                      have hchildComp : new.T.isNFComp (ls.idx m) := hcoords m
                      cases b with
                      | Z =>
                          refine ⟨0, ?_⟩
                          rw [new.T.fund, ite_eq_left rfl, hmin]
                          rfl
                      | P ws tail =>
                          have hvec : new.compareVec ws ls = Ordering.lt := by
                            change
                              (match new.compareVec ws ls with
                              | Ordering.eq => new.compareT tail new.T.Z
                              | ord => ord) = Ordering.lt at hba
                            cases hc : new.compareVec ws ls with
                            | lt => exact rfl
                            | eq =>
                                rw [hc] at hba
                                exact False.elim (ot_lt_Z_inv tail hba)
                            | gt =>
                                rw [hc] at hba
                                cases hba
                          let ⟨q, hqAbove, hqLt⟩ :=
                            new.Vec.compare_lt_has_pivot ws ls hvec
                          cases Nat.lt_trichotomy q.val m.val with
                          | inl hqm =>
                              have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                                hspec.2.2 q hqm
                              have hqz := new.T.dom_zero_eq_Z (ls.idx q) hqDom
                              rw [hqz] at hqLt
                              exact False.elim (ot_lt_Z_inv (ws.idx q) hqLt)
                          | inr hrel =>
                              cases hrel with
                              | inr hmq =>
                                  refine ⟨0, ?_⟩
                                  rw [new.T.fund, ite_eq_left rfl, hmin]
                                  apply new.T.P_lt_P_of_compareVec_lt
                                  apply new.Vec.compare_lt_of_pivot ws
                                    (ls.rplc m
                                      (new.T.fund (ls.idx m)
                                        (new.T.iter (fun x => new.T.fund (ls.idx m) x)
                                          (new.T.ofNat 0)))) q
                                  · intro j hqj
                                    have hjm : j.val ≠ m.val :=
                                      Nat.ne_of_gt (Nat.lt_trans hmq hqj)
                                    rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                    exact hqAbove j hqj
                                  · have hqmNe : q.val ≠ m.val := Nat.ne_of_gt hmq
                                    rw [new.Vec.rplc_idx_of_ne ls m q _ hqmNe]
                                    exact hqLt
                              | inl hqmEq =>
                                  have hqEq : q = m := Fin.eq_of_val_eq hqmEq
                                  cases hqEq
                                  have htargetComp : new.T.isNFComp (ws.idx m) :=
                                    new.T.isNF_P_coord_NFComp ws tail hb m
                                  let ⟨k, hk⟩ :=
                                    ot_iteration_cofinal (ls.idx m) hchildComp hchildDom
                                      (ws.idx m) htargetComp hqLt
                                  refine ⟨k, ?_⟩
                                  rw [new.T.fund, ite_eq_left rfl, hmin]
                                  apply new.T.P_lt_P_of_compareVec_lt
                                  apply new.Vec.compare_lt_of_pivot ws
                                    (ls.rplc m
                                      (new.T.fund (ls.idx m)
                                        (new.T.iter (fun x => new.T.fund (ls.idx m) x)
                                          (new.T.ofNat k)))) m
                                  · intro j hmj
                                    have hjm : j.val ≠ m.val := Nat.ne_of_gt hmj
                                    rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                                    exact hqAbove j hmj
                                  · rw [new.Vec.rplc_idx_same]
                                    exact hk
          · intro hadd
            have haddDom : new.T.dom add = new.Dom.omega := by
              rw [new.T.dom, ite_eq_right hadd] at hdom
              exact hdom
            have haddNF : new.T.isNF add := by
              cases ha with
              | p _ _ _ htail _ _ => exact htail
            have haddSize : new.T.size add < n := by
              have hs := new.T.add_size_lt_P ls add
              rw [hasize] at hs
              exact hs
            cases b with
            | Z =>
                refine ⟨0, ?_⟩
                rw [new.T.fund_P_tail_eq ls add (new.T.ofNat 0) hadd]
                rfl
            | P ws tail =>
                change
                  (match new.compareVec ws ls with
                  | Ordering.eq => new.compareT tail add
                  | ord => ord) = Ordering.lt at hba
                cases hc : new.compareVec ws ls with
                | lt =>
                    refine ⟨0, ?_⟩
                    rw [new.T.fund_P_tail_eq ls add (new.T.ofNat 0) hadd]
                    exact new.T.P_lt_P_of_compareVec_lt ws ls tail
                      (new.T.fund add (new.T.ofNat 0)) hc
                | gt =>
                    rw [hc] at hba
                    cases hba
                | eq =>
                    rw [hc] at hba
                    have hws : ws = ls := new.Vec_eq_sound ws ls hc
                    cases hws
                    have htailNF : new.T.isNF tail := by
                      cases hb with
                      | p _ _ _ ht _ _ => exact ht
                    let ⟨k, hk⟩ :=
                      ih (new.T.size add) haddSize add rfl haddNF haddDom
                        tail htailNF hba
                    refine ⟨k, ?_⟩
                    rw [new.T.fund_P_tail_eq ls add (new.T.ofNat k) hadd]
                    exact new.T.P_tail_lt ls tail (new.T.fund add (new.T.ofNat k)) hk)
  intro a ha hd b hb hba
  exact main (new.T.size a) a rfl ha hd b hb hba

#print axioms ot_fund_omega_cofinal

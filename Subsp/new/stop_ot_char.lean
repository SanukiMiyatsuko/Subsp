import Subsp.new.stop_ot_iter

open T

theorem ot_tail_lt_of_NF {lam : Nat} :
    ∀ (ls : new.Vec (new.T lam) lam) (add : new.T lam),
      new.T.isNF (new.T.P ls add) → add ≠ new.T.Z →
        add < new.T.P ls add := by
  let motive : Nat → Prop := fun n =>
    ∀ (ls : new.Vec (new.T lam) lam) (add : new.T lam),
      new.T.size (new.T.P ls add) = n →
      new.T.isNF (new.T.P ls add) → add ≠ new.T.Z →
        add < new.T.P ls add
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro ls add hsize hnf hne
      cases add with
      | Z => exact False.elim (hne rfl)
      | P ws tail =>
          cases hnf with
          | p _ _ hcoords hadd hG hhead =>
              have hrel := new.T.vector_rel_of_P_le_P ws ls new.T.Z new.T.Z hhead
              cases hrel with
              | inl hvec =>
                  exact new.T.P_lt_P_of_compareVec_lt ws ls tail (new.T.P ws tail) hvec
              | inr hveq =>
                  cases hveq
                  apply Decidable.byCases (p := tail = new.T.Z)
                  · intro htz
                    cases htz
                    change new.T.P ls new.T.Z < new.T.P ls (new.T.P ls new.T.Z)
                    exact new.T.P_tail_lt ls new.T.Z (new.T.P ls new.T.Z) (by rfl)
                  · intro htz
                    have hsza : new.T.size (new.T.P ls tail) < n := by
                      have hh := new.T.add_size_lt_P ls (new.T.P ls tail)
                      rw [hsize] at hh
                      exact hh
                    have hrec := ih (new.T.size (new.T.P ls tail)) hsza
                      ls tail rfl hadd htz
                    exact new.T.P_tail_lt ls tail (new.T.P ls tail) hrec)
  intro ls add hnf hne
  exact main (new.T.size (new.T.P ls add)) ls add rfl hnf hne

#print axioms ot_tail_lt_of_NF

def ot_unit (lam : Nat) : new.T lam :=
  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z


theorem ot_unit_le_P {lam : Nat} (ls : new.Vec (new.T lam) lam)
    (add : new.T lam) : ot_unit lam ≤ new.T.P ls add := by
  cases hc : new.compareVec (new.Vec.ofFn lam (fun _ => new.T.Z)) ls with
  | lt =>
      exact Or.inl (new.T.P_lt_P_of_compareVec_lt
        (new.Vec.ofFn lam (fun _ => new.T.Z)) ls new.T.Z add hc)
  | eq =>
      have hv : new.Vec.ofFn lam (fun _ => new.T.Z) = ls :=
        new.Vec_eq_sound _ _ hc
      rw [← hv]
      exact new.T.P_same_le_iff
        (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z add |>.mpr (new.T.Z_le add)
  | gt =>
      exact False.elim ((oti_zeroVec_not_gt ls) hc)

#print axioms ot_unit_le_P

theorem ot_unit_le_of_ne_Z {lam : Nat} (s : new.T lam)
    (hne : s ≠ new.T.Z) : ot_unit lam ≤ s := by
  cases s with
  | Z => exact False.elim (hne rfl)
  | P ls add => exact ot_unit_le_P ls add

#print axioms ot_unit_le_of_ne_Z

def ot_bound (lam : Nat) : new.T lam :=
  new.T.P
    (new.Vec.ofFn lam (fun x =>
      if x.val = 1 then ot_unit lam else new.T.Z))
    new.T.Z


theorem ot_dom_Omega_not_countable {lam : Nat} :
    ∀ s : new.T lam, new.T.isNF s →
      (1 < lam → s < ot_bound lam) →
      new.T.dom s ≠ .Omega := by
  let motive : Nat → Prop := fun n =>
    ∀ s : new.T lam, new.T.size s = n → new.T.isNF s →
      (1 < lam → s < ot_bound lam) →
      new.T.dom s ≠ .Omega
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s hsize hnf hbound hOmega
      cases s with
      | Z =>
          change new.Dom.zero = new.Dom.Omega at hOmega
          cases hOmega
      | P ls add =>
          apply Decidable.byCases (p := add = new.T.Z)
          · intro hadd
            cases hadd
            cases hmin : new.T.domVecMinIdx ls with
            | none =>
                have hd := hOmega
                rw [new.T.dom, ite_eq_left rfl, hmin] at hd
                change new.Dom.one = new.Dom.Omega at hd
                cases hd
            | some md =>
                let ⟨m, d⟩ := md
                have hd := hOmega
                rw [new.T.dom, ite_eq_left rfl, hmin] at hd
                change
                  (if d = new.Dom.one then
                    if m.val = 0 then new.Dom.omega else new.Dom.Omega
                  else new.Dom.omega) = new.Dom.Omega at hd
                have hd1 : d = new.Dom.one := by
                  apply Decidable.byCases (p := d = new.Dom.one)
                  · intro h
                    exact h
                  · intro h
                    rw [ite_eq_right h] at hd
                    cases hd
                have hm0 : m.val ≠ 0 := by
                  rw [ite_eq_left hd1] at hd
                  intro hm
                  rw [ite_eq_left hm] at hd
                  cases hd
                have hspec := new.T.domVecMinIdx_some_spec ls m d hmin
                have hchildDom : new.T.dom (ls.idx m) = new.Dom.one := by
                  rw [hspec.2.1, hd1]
                have hchildNe : ls.idx m ≠ new.T.Z := by
                  intro hz
                  rw [hz] at hchildDom
                  change new.Dom.zero = new.Dom.one at hchildDom
                  cases hchildDom
                have hunit : ot_unit lam ≤ ls.idx m :=
                  ot_unit_le_of_ne_Z (ls.idx m) hchildNe
                have hlam : 1 < lam := by
                  have hmpos : 0 < m.val := Nat.pos_of_ne_zero hm0
                  exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hmpos) m.isLt
                have hb := hbound hlam
                change
                  (match
                    new.compareVec ls
                      (new.Vec.ofFn lam (fun x =>
                        if x.val = 1 then ot_unit lam else new.T.Z))
                  with
                  | Ordering.eq => new.compareT new.T.Z new.T.Z
                  | ord => ord) = Ordering.lt at hb
                have hvec :
                    new.compareVec ls
                      (new.Vec.ofFn lam (fun x =>
                        if x.val = 1 then ot_unit lam else new.T.Z)) = Ordering.lt := by
                  cases hc : new.compareVec ls
                      (new.Vec.ofFn lam (fun x =>
                        if x.val = 1 then ot_unit lam else new.T.Z)) with
                  | lt => exact rfl
                  | eq =>
                      rw [hc] at hb
                      change Ordering.eq = Ordering.lt at hb
                      cases hb
                  | gt =>
                      rw [hc] at hb
                      cases hb
                let ⟨q, hqAbove, hqLt⟩ :=
                  new.Vec.compare_lt_has_pivot ls
                    (new.Vec.ofFn lam (fun x =>
                      if x.val = 1 then ot_unit lam else new.T.Z)) hvec
                cases Nat.lt_trichotomy q.val m.val with
                | inl hqm =>
                    apply Decidable.byCases (p := m.val = 1)
                    · intro hm1
                      have hq0 : q.val = 0 := by
                        rw [hm1] at hqm
                        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hqm)
                      have hqDom : new.T.dom (ls.idx q) = new.Dom.zero :=
                        hspec.2.2 q hqm
                      have hqz : ls.idx q = new.T.Z :=
                        new.T.dom_zero_eq_Z (ls.idx q) hqDom
                      rw [new.Vec.ofFn_idx] at hqLt
                      have hq1 : q.val ≠ 1 := by
                        rw [hq0]
                        intro h
                        cases h
                      rw [ite_eq_right hq1, hqz] at hqLt
                      exact ot_lt_Z_inv new.T.Z hqLt
                    · intro hm1
                      have heqm := hqAbove m hqm
                      rw [new.Vec.ofFn_idx, ite_eq_right hm1] at heqm
                      exact hchildNe heqm
                | inr hmq =>
                    cases hmq with
                    | inl heqVal =>
                        have hqmEq : q = m := Fin.eq_of_val_eq heqVal
                        cases hqmEq
                        rw [new.Vec.ofFn_idx] at hqLt
                        apply Decidable.byCases (p := m.val = 1)
                        · intro hm1
                          rw [ite_eq_left hm1] at hqLt
                          have hbad : ot_unit lam < ot_unit lam :=
                            new.T.lt_of_le_of_lt (ot_unit lam) (ls.idx m)
                              (ot_unit lam) hunit hqLt
                          exact strict_partial_order.irrefl (ot_unit lam) hbad
                        · intro hm1
                          rw [ite_eq_right hm1] at hqLt
                          exact ot_lt_Z_inv (ls.idx m) hqLt
                    | inr hmqLt =>
                        have hq1 : q.val ≠ 1 := by
                          intro hqv
                          have hmLt1 : m.val < 1 := by
                            rw [← hqv]
                            exact hmqLt
                          have hmz : m.val = 0 :=
                            Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hmLt1)
                          exact hm0 hmz
                        rw [new.Vec.ofFn_idx, ite_eq_right hq1] at hqLt
                        exact ot_lt_Z_inv (ls.idx q) hqLt
          · intro hadd
            have haddNF : new.T.isNF add := by
              cases hnf with
              | p _ _ _ ha _ _ => exact ha
            have haddLt : add < new.T.P ls add :=
              ot_tail_lt_of_NF ls add hnf hadd
            have haddBound : 1 < lam → add < ot_bound lam := by
              intro hlam
              exact strict_partial_order.trans add (new.T.P ls add) (ot_bound lam)
                haddLt (hbound hlam)
            have haddSize : new.T.size add < n := by
              have hh := new.T.add_size_lt_P ls add
              rw [hsize] at hh
              exact hh
            have hrec := ih (new.T.size add) haddSize add rfl haddNF haddBound
            have hdadd : new.T.dom add = new.Dom.Omega := by
              rw [new.T.dom, ite_eq_right hadd] at hOmega
              exact hOmega
            exact hrec hdadd)
  intro s hnf hbound
  exact main (new.T.size s) s rfl hnf hbound

#print axioms ot_dom_Omega_not_countable

theorem ot_vec_ext {lam m : Nat} (v w : new.Vec (new.T lam) m)
    (h : ∀ i : Fin m, v.idx i = w.idx i) : v = w := by
  induction m with
  | zero =>
      cases v
      cases w
      rfl
  | succ k ih =>
      cases v with
      | snoc _ vs vx =>
        cases w with
        | snoc _ ws wx =>
          have hlast := h (Fin.last k)
          change
            (if hlt : k < k then vs.idx ⟨k, hlt⟩ else vx) =
            (if hlt : k < k then ws.idx ⟨k, hlt⟩ else wx) at hlast
          rw [dite_eq_right (Nat.lt_irrefl k), dite_eq_right (Nat.lt_irrefl k)] at hlast
          have hpref : ∀ i : Fin k, vs.idx i = ws.idx i := by
            intro i
            have hi := h i.castSucc
            change
              (if hlt : i.val < k then vs.idx ⟨i.val, hlt⟩ else vx) =
              (if hlt : i.val < k then ws.idx ⟨i.val, hlt⟩ else wx) at hi
            rw [dite_eq_left i.isLt, dite_eq_left i.isLt] at hi
            exact hi
          have hvw := ih vs ws hpref
          rw [hvw, hlast]

#print axioms ot_vec_ext

theorem ot_head_le_one_base {lam : Nat}
    (ls : new.Vec (new.T lam) lam) (m : Fin lam)
    (hmin : new.T.domVecMinIdx ls = some (m, new.Dom.one))
    (hm0 : m.val = 0)
    (b : new.T lam) (hb : new.T.isNF b)
    (hba : b < new.T.P ls new.T.Z) :
    new.T.head b ≤
      new.T.P (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) new.T.Z := by
  cases b with
  | Z =>
      exact new.T.Z_le _
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
      let ⟨q, hqAbove, hqLt⟩ := new.Vec.compare_lt_has_pivot ws ls hvec
      apply Decidable.byCases (p := q.val = m.val)
      · intro hqm
        have hqeq : q = m := Fin.eq_of_val_eq hqm
        cases hqeq
        have hchildDom : new.T.dom (ls.idx m) = new.Dom.one :=
          (new.T.domVecMinIdx_some_spec ls m new.Dom.one hmin).2.1
        have hupper : ws.idx m ≤ new.T.fund (ls.idx m) new.T.Z :=
          ot_fund_one_upper (ls.idx m) hchildDom (ws.idx m) hqLt
        cases hupper with
        | inl hlt =>
            apply Or.inl
            apply new.T.P_lt_P_of_compareVec_lt
            apply new.Vec.compare_lt_of_pivot ws
              (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) m
            · intro j hmj
              have hjm : j.val ≠ m.val := Nat.ne_of_gt hmj
              rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
              exact hqAbove j hmj
            · rw [new.Vec.rplc_idx_same]
              exact hlt
        | inr heq =>
            have htermEq : ws.idx m = new.T.fund (ls.idx m) new.T.Z :=
              new.T_eq_sound _ _ heq
            have hvecEq : ws = ls.rplc m (new.T.fund (ls.idx m) new.T.Z) := by
              apply ot_vec_ext
              intro j
              apply Decidable.byCases (p := j.val = m.val)
              · intro hjm
                have hjEq : j = m := Fin.eq_of_val_eq hjm
                cases hjEq
                rw [new.Vec.rplc_idx_same]
                exact htermEq
              · intro hjm
                have hmj : m.val < j.val := by
                  have hmzero : m.val = 0 := hm0
                  rw [hmzero]
                  have hjpos : 0 < j.val := Nat.pos_of_ne_zero (by
                    intro hjz
                    apply hjm
                    rw [hmzero, hjz])
                  exact hjpos
                rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
                exact hqAbove j hmj
            rw [hvecEq]
            exact new.T.le_refl _
      · intro hqm
        have hmq : m.val < q.val := by
          rw [hm0]
          have hq0 : q.val ≠ 0 := by
            intro hqz
            apply hqm
            rw [hm0, hqz]
          exact Nat.pos_of_ne_zero hq0
        apply Or.inl
        apply new.T.P_lt_P_of_compareVec_lt
        apply new.Vec.compare_lt_of_pivot ws
          (ls.rplc m (new.T.fund (ls.idx m) new.T.Z)) q
        · intro j hqj
          have hjm : j.val ≠ m.val := by
            exact Nat.ne_of_gt (Nat.lt_trans hmq hqj)
          rw [new.Vec.rplc_idx_of_ne ls m j _ hjm]
          exact hqAbove j hqj
        · have hqmne : q.val ≠ m.val := hqm
          rw [new.Vec.rplc_idx_of_ne ls m q _ hqmne]
          exact hqLt

#print axioms ot_head_le_one_base

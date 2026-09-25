import Subsp.new.stop_ot_omega

open T

theorem ot_fund_countable_cofinal {lam : Nat}
    (a b : new.T lam) (ha : new.T.isNF a) (hb : new.T.isNF b)
    (hbound : 1 < lam → a < ot_bound lam) (hba : b < a) :
    ∃ n : Nat,
      new.T.fund a (new.T.ofNat n) < a ∧
        b ≤ new.T.fund a (new.T.ofNat n) := by
  cases hd : new.T.dom a with
  | zero =>
      have haz : a = new.T.Z := new.T.dom_zero_eq_Z a hd
      rw [haz] at hba
      exact False.elim (ot_lt_Z_inv b hba)
  | one =>
      have hane : a ≠ new.T.Z := by
        intro haz
        rw [haz] at hd
        cases hd
      refine ⟨0, new.T.fund_lt_self a (new.T.ofNat 0) hane, ?_⟩
      rw [new.T.fund_one_arg_irrel a (new.T.ofNat 0) hd]
      exact ot_fund_one_upper a hd b hba
  | omega =>
      obtain ⟨n, hn⟩ := ot_fund_omega_cofinal a ha hd b hb hba
      have hane : a ≠ new.T.Z := by
        intro haz
        rw [haz] at hd
        cases hd
      exact ⟨n, new.T.fund_lt_self a (new.T.ofNat n) hane, Or.inl hn⟩
  | Omega =>
      exact False.elim ((ot_dom_Omega_not_countable a ha hbound) hd)

#print axioms ot_fund_countable_cofinal

theorem ot_new_well_founded_NF (lam : Nat) :
    WellFounded (fun s t : {x : new.T lam // new.T.isNF x} => s.1 < t.1) := by
  let R := fun s t : {x : new.T lam // new.T.isNF x} => s.1 < t.1
  have hacc :
      ∀ a : T.NF1, ∀ s : {x : new.T lam // new.T.isNF x},
        trans s.1 = a.1 → Acc R s := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
        intro s heq
        constructor
        intro t hts
        have htrans : trans t.1 < trans s.1 :=
          (gnf_order_embedding t.1 s.1 t.2 s.2).mp hts
        have htrans' : trans t.1 < a.1 := by
          rw [← heq]
          exact htrans
        let ta : T.NF1 := ⟨trans t.1, gnf_NF_is_NF1 t.1 t.2⟩
        exact ih ta htrans' t rfl
  constructor
  intro s
  let a : T.NF1 := ⟨trans s.1, gnf_NF_is_NF1 s.1 s.2⟩
  exact hacc a s rfl

#print axioms ot_new_well_founded_NF

theorem ot_new_isOT_downward {lam : Nat}
    (a b : new.T lam) (ha : new.T.isOT lam a)
    (hb : new.T.isNF b) (hba : b ≤ a) :
    new.T.isOT lam b := by
  let NF := {x : new.T lam // new.T.isNF x}
  have main :
      ∀ a0 : NF, new.T.isOT lam a0.1 →
        ∀ b0 : new.T lam, new.T.isNF b0 → b0 ≤ a0.1 →
          new.T.isOT lam b0 := by
    intro a0
    induction a0 using (ot_new_well_founded_NF lam).induction with
    | h a0 ih =>
        intro ha0 b0 hb0 hba0
        cases hba0 with
        | inl hlt =>
            have hsound := ot_new_isOT_sound lam a0.1 ha0
            obtain ⟨n, hfall, hupper⟩ :=
              ot_fund_countable_cofinal a0.1 b0 a0.2 hb0
                hsound.2 hlt
            have hn : new.T.isOT lam (new.T.fund a0.1 (new.T.ofNat n)) :=
              new.T.isOT.step lam a0.1 ha0 n
            have hfnf : new.T.isNF (new.T.fund a0.1 (new.T.ofNat n)) :=
              (ot_new_isOT_sound lam _ hn).1
            exact ih ⟨new.T.fund a0.1 (new.T.ofNat n), hfnf⟩
              hfall hn b0 hb0 hupper
        | inr heq =>
            have hterm : b0 = a0.1 := new.T_eq_sound b0 a0.1 heq
            rw [hterm]
            exact ha0
  have hanf : new.T.isNF a := (ot_new_isOT_sound lam a ha).1
  exact main ⟨a, hanf⟩ ha b hb hba

#print axioms ot_new_isOT_downward

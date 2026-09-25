import Subsp.new.stop_nf_core

open T

theorem sg_add_interval_size_le (a b x : T)
    (hax : a ≤ x) (hxu : x < T.add a b) :
    a.size ≤ x.size := by
  induction a generalizing x with
  | Z => exact Nat.zero_le x.size
  | P p c d ihc ihd =>
      cases hax with
      | inr heq =>
          rw [heq]
          exact Nat.le_refl x.size
      | inl hlt =>
          have hu : T.add (T.P p c d) b = T.P p c (T.add d b) :=
            T.P_add_eq p c d b
          rw [hu] at hxu
          obtain ⟨e, hex, hde, heu⟩ :=
            sandwich_tail p c d x (T.add d b) hlt hxu
          rw [hex]
          have hsz : d.size ≤ e.size :=
            ihd e (Or.inl hde) heu
          change c.size + d.size + 1 ≤ c.size + e.size + 1
          exact Nat.add_le_add_right (Nat.add_le_add_left hsz c.size) 1

#print axioms sg_add_interval_size_le

theorem sg_good0_part_fst (s : T) (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.part s).1 → x < (T.part s).1 := by
  intro x hx
  let a := (T.part s).1
  let b := (T.part s).2
  have hadd : T.add a b = s := by
    unfold a b
    exact bridge_part_add s
  have hxadd : x ∈ T.G1 0 (T.add a b) := by
    rw [bridge_G1_add_eq]
    exact List.mem_append_left (T.G1 0 b) hx
  have hxsin : x ∈ T.G1 0 s := by
    rw [← hadd]
    exact hxadd
  have hxs : x < s := hg x hxsin
  have hxsz : x.size < a.size := G1_size_lt 0 a x hx
  cases lt_total_thm x a with
  | inl hxa => exact hxa
  | inr hor =>
      cases hor with
      | inl hax =>
          have hsz : a.size ≤ x.size := by
            apply sg_add_interval_size_le a b x (Or.inl hax)
            rw [hadd]
            exact hxs
          exact False.elim ((Nat.not_lt_of_ge hsz) hxsz)
      | inr heq =>
          rw [heq] at hxsz
          exact False.elim (Nat.lt_irrefl a.size hxsz)

#print axioms sg_good0_part_fst

theorem sg_early_G0_le (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.early_collapse s) → x ≤ s := by
  intro x hx
  cases hp : T.part s with
  | mk a b =>
      have hadd := bridge_part_add s
      rw [hp] at hadd
      have hparts := nfaux_part_NF1 s hs
      rw [hp] at hparts
      have hbNF : T.isNF1 b := hparts.2
      have hec := bridge_early_collapse_part s a b hp hbNF
      have haLe : a ≤ s := by
        have h := bridge_part_fst_le_self s
        rw [hp] at h
        exact h
      have hmemB : ∀ y : T, y ∈ T.G1 0 b → y < s := by
        intro y hy
        apply hg y
        rw [← hadd, bridge_G1_add_eq]
        exact List.mem_append_right _ hy
      by_cases ha : a = T.Z
      · rw [hec, ite_eq_left ha] at hx
        exact Or.inl (hmemB x hx)
      · rw [hec, ite_eq_right ha] at hx
        by_cases hkeep : T.head b ≤ T.P 0 a T.Z
        · rw [ite_eq_left hkeep] at hx
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)] at hx
          cases List.mem_append.mp hx with
          | inl hleft =>
              cases List.mem_append.mp hleft with
              | inl hsingle =>
                  have hxa : x = a := List.mem_singleton.mp hsingle
                  rw [hxa]
                  exact haLe
              | inr hGa =>
                  have hgoodA := sg_good0_part_fst s hs hg
                  rw [hp] at hgoodA
                  exact Or.inl (lt_of_lt_of_le_thm T x a s
                    (hgoodA x hGa) haLe)
          | inr hGb =>
              exact Or.inl (hmemB x hGb)
        · rw [ite_eq_right hkeep] at hx
          exact Or.inl (hmemB x hx)

#print axioms sg_early_G0_le

theorem sg_tail_le_principal_add (i : Nat) (m b : T)
    (hb : T.isNF1 b)
    (hh : T.head b ≤ T.P i m T.Z) :
    b ≤ T.P i m b := by
  cases b with
  | Z => exact T.Z_le (T.P i m T.Z)
  | P q e f =>
      rw [T.head] at hh
      cases hh with
      | inl hlt =>
          cases lt_inv q e T.Z i m T.Z hlt with
          | inl hqi =>
              exact Or.inl (T.Lt.p_head q i e m f (T.P q e f) hqi)
          | inr hor =>
              cases hor with
              | inl hmid =>
                  have hqi : q = i := hmid.1
                  subst i
                  exact Or.inl (T.Lt.p_mid q e m f (T.P q e f) hmid.2)
              | inr htail =>
                  exact False.elim (lt_Z_inv htail.2.2)
      | inr heq =>
          injection heq with hqi hem
          subst i
          subst m
          have hfle : f ≤ T.P q e f :=
            T.isNF1_tail_le (T.P q e f) hb q e f rfl
          cases hfle with
          | inl hflt =>
              exact Or.inl (T.Lt.p_tail q e f (T.P q e f) hflt)
          | inr hfeq =>
              exact Or.inr (congrArg (fun z => T.P q e z) hfeq)

#print axioms sg_tail_le_principal_add

theorem sg_lt_principal_add (i : Nat) (m b x : T)
    (hb : T.isNF1 b)
    (hh : T.head b ≤ T.P i m T.Z)
    (hxb : x < b) :
    x < T.P i m b := by
  have hble := sg_tail_le_principal_add i m b hb hh
  exact lt_of_lt_of_le_thm T x b (T.P i m b) hxb hble

#print axioms sg_lt_principal_add

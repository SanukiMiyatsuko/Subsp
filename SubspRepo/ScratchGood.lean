import Subsp.new.stop_ec

open T

theorem sg_early_G0_le (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    ∀ x : T, x ∈ T.G1 0 (T.early_collapse s) → x ≤ s := by
  intro x hx
  cases hp : T.part s with
  | mk a b =>
      have hadd := bridge_part_add s
      rw [hp] at hadd
      have hparts := test_part_NF1 s hs
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
                  have hgoodA := test_good0_part_fst s hs hg
                  rw [hp] at hgoodA
                  exact Or.inl (lt_of_lt_of_le_thm T x a s
                    (hgoodA x hGa) haLe)
          | inr hGb =>
              exact Or.inl (hmemB x hGb)
        · rw [ite_eq_right hkeep] at hx
          exact Or.inl (hmemB x hx)

#print axioms sg_early_G0_le

import Subsp.multi.kuma.WF

/-! Omega-domain sources: coefficients, invariants, relative predecessors and contexts (the
`multi` version of `Subsp/Support/Omega.lean`). -/

namespace kumakuma.GeneralImageOmegaCoefficients

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageRawOrder
open kumakuma.GeneralImageCoefficients kumakuma.GeneralImageTopPair
open kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageLayerOrder
open kumakuma.GeneralImageWFInvariant kumakuma.GeneralImageLimitSupport
open kumakuma.SourceRecursiveDescending kumakuma.SourceSubtermBounds

universe u

inductive Coefficient (d : Nat) : multi.T → multi.T → Prop
  | root (xs : V multi.T) (b : multi.T) (i : Nat)
      (hi : i + 1 < d) (hn : V.get0 xs i ≠ .Z) : Coefficient d (V.get0 xs i) (.P xs b)
  | coordinate (xs : V multi.T) (b : multi.T) (i : Nat) (hi : i < d)
      {a : multi.T} : Coefficient d a (V.get0 xs i) → Coefficient d a (.P xs b)
  | tail (xs : V multi.T) (b : multi.T) {a : multi.T} :
      Coefficient d a b → Coefficient d a (.P xs b)

theorem Coefficient.subterm {d : Nat} {a s : multi.T} (h : Coefficient d a s) :
    Subterm a s := by
  induction h with
  | root xs b i => exact Subterm.coordinate xs b i
  | coordinate xs b i _ _ ih => exact Subterm.trans ih (Subterm.coordinate xs b i)
  | tail xs b _ ih => exact Subterm.trans ih (Subterm.tail xs b)

theorem Coefficient.ne_zero {d : Nat} {a s : multi.T} (h : Coefficient d a s) : a ≠ .Z := by
  induction h with
  | root _ _ _ _ hn => exact hn
  | coordinate _ _ _ _ _ ih | tail _ _ _ ih => exact ih

theorem Coefficient.parent_ne_zero {d : Nat} {a s : multi.T} (h : Coefficient d a s) :
    s ≠ .Z := by cases h <;> intro he <;> cases he

theorem convert_eq_zero_iff (d : Nat) (s : multi.T) :
    convert d (code s) = .zero ↔ s = .Z :=
  ⟨fun h => (code_eq_zero_iff _).1 ((kumakuma.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp h),
    fun h => by rw [h]; exact convert_Z d⟩

theorem H_topPair_precise (u : Term) (n : Nat) (a b : Term) {z : Term}
    (hz : z ∈ Term.H u (topPair n a b)) :
    z = .zero ∨ z ∈ Term.H u a ∨ ArgCoefficient u z b := by
  unfold topPair at hz
  by_cases hb : b = .zero
  · rw [ite_eq_left hb] at hz
    by_cases ha : a = .zero
    · rw [ite_eq_left ha, Term.H] at hz; cases hz
    · rw [ite_eq_right ha] at hz
      rcases H_inacc_support n (dropOne a) hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl (kumakuma.OT2.mem_H_dropOne hz))
  · rw [ite_eq_right hb] at hz
    rcases H_psi_support hz with hz | hz | hz
    · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (kumakuma.OT2.mem_H_dropOne hz))))
    · rcases H_inacc_support n _ hz with hz | hz
      · exact Or.inl hz
      · by_cases ha : a = .zero
        · rw [ite_eq_left ha, Term.H] at hz; cases hz
        · rw [ite_eq_right ha] at hz
          rcases H_succ_support (dropOne a) hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (Or.inl (kumakuma.OT2.mem_H_dropOne hz))

theorem H_principal_precise (u : Term) (k : Nat) (xs : List Term) {z : Term}
    (hz : z ∈ Term.H u (principal (k + 3) xs)) :
    z = .zero ∨
      (∃ i, i < k + 2 ∧ (z = xs[i]?.getD .zero ∨ z = dropOne (xs[i]?.getD .zero))) ∨
      ∃ i, i < k + 3 ∧ z ∈ Term.H u (xs[i]?.getD .zero) := by
  rw [principal_as_layers] at hz
  have direct : ∀ i, i < k + 2 → ArgCoefficient u z (xs[i]?.getD .zero) →
      (∃ i, i < k + 2 ∧ (z = xs[i]?.getD .zero ∨ z = dropOne (xs[i]?.getD .zero))) ∨
        ∃ i, i < k + 3 ∧ z ∈ Term.H u (xs[i]?.getD .zero) := by
    intro i hi h
    rcases h with h | h | h
    · exact Or.inl ⟨i, hi, Or.inl h⟩
    · exact Or.inl ⟨i, hi, Or.inr h⟩
    · exact Or.inr ⟨i, by omega, h⟩
  rcases H_lower_support u (k + 1) xs _ hz with hz | hz | ⟨i, hi, hz⟩
  · exact Or.inl hz
  · rcases H_topPair_precise u (k + 1) _ _ hz with hz | hz | hz
    · exact Or.inl hz
    · exact Or.inr (Or.inr ⟨k + 2, by omega, hz⟩)
    · exact Or.inr (direct (k + 1) (by omega) hz)
  · exact Or.inr (direct i (by omega) hz)


theorem H_convert_coefficient (k : Nat) (u : Term) : ∀ (s : multi.T) {z : Term},
    z ∈ Term.H u (convert (k + 3) (code s)) →
    z = .zero ∨ ∃ a, Coefficient (k + 3) a s ∧
      (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a)))
  | .Z, z, hz => by rw [convert_Z, Term.H] at hz; cases hz
  | .P xs b, z, hz => by
    rw [convert_P] at hz
    rcases H_assemble_support u _ _ hz with hz | hz
    · rcases H_principal_precise u k _ hz with hz | ⟨i, hi, hz⟩ | ⟨i, hi, hz⟩
      · exact Or.inl hz
      · rw [converted_coordinate xs i] at hz
        by_cases hn : V.get0 xs i = .Z
        · rw [hn, convert_Z] at hz
          rcases hz with hz | hz
          · exact Or.inl hz
          · exact Or.inl hz
        · exact Or.inr ⟨V.get0 xs i,
            Coefficient.root (d := k + 3) xs b i (show i + 1 < k + 3 by omega) hn, hz⟩
      · rw [converted_coordinate xs i] at hz
        rcases H_convert_coefficient k u (V.get0 xs i) hz with hz | ⟨a, ha, hz⟩
        · exact Or.inl hz
        · exact Or.inr ⟨a, Coefficient.coordinate xs b _ hi ha, hz⟩
    · rcases H_convert_coefficient k u b hz with hz | ⟨a, ha, hz⟩
      · exact Or.inl hz
      · exact Or.inr ⟨a, Coefficient.tail xs b ha, hz⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem H_nonzero_drop (u t : Term) {z : Term} (hz : z ∈ Term.H u t) (hn : z ≠ .zero) :
    z ∈ Term.H u (dropOne t) := by
  cases t with
  | zero => cases hz
  | inacc => exact hz
  | add a b =>
    by_cases ha : a = Term.one
    · rw [Term.H, ha] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact False.elim (hn (H_one_mem hz))
      · simpa only [dropOne, ha, ↓reduceIte] using hz
    · simpa only [dropOne, ha, ↓reduceIte] using hz
  | psi v b =>
    by_cases ht : Term.psi v b = Term.one
    · rw [ht] at hz
      exact False.elim (hn (H_one_mem hz))
    · simpa only [dropOne, ht, ↓reduceIte] using hz

theorem H_omega_step_coordinate (n : Nat) (a c : Term) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega c) (hn : z ≠ .zero) :
    z ∈ Term.H Term.bigOmega (step n a c) := by
  have hc : c ≠ .zero := by intro he; rw [he, Term.H] at hz; cases hz
  have hd := H_nonzero_drop Term.bigOmega c hz hn
  unfold step
  by_cases ha : a = .zero
  · rw [ite_eq_left ha]
    by_cases h0 : n = 0
    · rw [ite_eq_left h0]
      change z ∈ Term.H Term.bigOmega (.psi (.inacc 0 .zero) c)
      rw [H_omega_psi_inacc]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
    · rw [ite_eq_right h0, ite_eq_right hc, H_omega_psi_inacc]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)
  · rw [ite_eq_right ha, ite_eq_right hc, regular, H_omega_psi_inacc]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)

theorem H_omega_topPair_high (n : Nat) (a b : Term) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega a) (hn : z ≠ .zero) :
    z ∈ Term.H Term.bigOmega (topPair n a b) := by
  have ha : a ≠ .zero := by intro he; rw [he, Term.H] at hz; cases hz
  have hd := H_nonzero_drop Term.bigOmega a hz hn
  unfold topPair
  by_cases hb : b = .zero
  · rw [ite_eq_left hb, ite_eq_right ha, Term.H]
    exact List.mem_append_right _ hd
  · rw [ite_eq_right hb, ite_eq_right ha, H_omega_psi_inacc]
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    rw [Term.H]
    apply List.mem_append_right
    rw [kumakuma.OT2.H_succTerm]
    exact List.mem_append_left _ hd

theorem H_omega_topPair_middle (n : Nat) (a b : Term) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega b) (hn : z ≠ .zero) :
    z ∈ Term.H Term.bigOmega (topPair n a b) := by
  have hb : b ≠ .zero := by intro he; rw [he, Term.H] at hz; cases hz
  rw [topPair, ite_eq_right hb, H_omega_psi_inacc]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (H_nonzero_drop Term.bigOmega b hz hn))

theorem H_omega_lower_coordinate_recursive (j : Nat) (xs : List Term) (a : Term)
    (i : Nat) (hi : i < j) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega (xs[i]?.getD .zero)) (hn : z ≠ .zero) :
    z ∈ Term.H Term.bigOmega (lower j xs a) := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    rw [lower_succ]
    by_cases hij : i < j
    · exact ih _ hij
    · have he : i = j := by omega
      subst i
      exact H_omega_lower_context j xs _ (H_omega_step_coordinate j a _ hz hn)

theorem H_omega_principal_coordinate_recursive (k : Nat) (xs : List Term)
    (i : Nat) (hi : i < k + 3) {z : Term}
    (hz : z ∈ Term.H Term.bigOmega (xs[i]?.getD .zero)) (hn : z ≠ .zero) :
    z ∈ Term.H Term.bigOmega (principal (k + 3) xs) := by
  rw [principal_as_layers]
  by_cases hil : i < k + 1
  · exact H_omega_lower_coordinate_recursive (k + 1) xs _ i hil hz hn
  · apply H_omega_lower_context
    by_cases him : i = k + 1
    · rw [him] at hz
      exact H_omega_topPair_middle _ _ _ hz hn
    · have he : i = k + 2 := by omega
      rw [he] at hz
      exact H_omega_topPair_high _ _ _ hz hn

theorem H_assemble_left (u p t : Term) {z : Term} (hz : z ∈ Term.H u p) :
    z ∈ Term.H u (kumakuma.OT2.assemble p t) := by
  unfold kumakuma.OT2.assemble
  split
  · exact hz
  · rw [Term.H]; exact List.mem_append_left _ hz

theorem H_assemble_right (u p t : Term) {z : Term} (hz : z ∈ Term.H u t) :
    z ∈ Term.H u (kumakuma.OT2.assemble p t) := by
  unfold kumakuma.OT2.assemble
  by_cases ht : t = .zero
  · rw [ht, Term.H] at hz; cases hz
  · rw [ite_eq_right ht, Term.H]; exact List.mem_append_right _ hz


theorem Coefficient.image_mem_H_omega (k : Nat) {a s : multi.T}
    (h : Coefficient (k + 3) a s)
    (hh : Term.head (convert (k + 3) (code a)) ≠ Term.one) :
    convert (k + 3) (code a) ∈ Term.H Term.bigOmega (convert (k + 3) (code s)) := by
  have hn : convert (k + 3) (code a) ≠ .zero := fun he => h.ne_zero ((convert_eq_zero_iff _ _).1 he)
  induction h with
  | root xs b i hi hz =>
    rw [convert_P]
    apply H_assemble_left
    have hm := H_omega_principal_coordinate k (arguments (k + 3) (trim (codes xs))) i
      (by omega) (by rwa [converted_coordinate xs i])
    rw [converted_coordinate xs i] at hm
    rcases hm with hm | hm
    · exact hm
    · rwa [dropOne_of_head_ne hh] at hm
  | coordinate xs b i hik h ih =>
    rw [convert_P]
    apply H_assemble_left
    exact H_omega_principal_coordinate_recursive k _ i hik
      (by rw [converted_coordinate xs i]; exact ih hh hn) hn
  | tail xs b h ih =>
    rw [convert_P]
    exact H_assemble_right _ _ _ (ih hh hn)

theorem Coefficient.parent_image_head_ne_one [LargeCardinals.{u}] (k : Nat)
    {a s : multi.T} (h : Coefficient (k + 3) a s) (hsD : Dim (k + 3) s)
    (hs : RecursiveWF (k + 3) s) :
    Term.head (convert (k + 3) (code s)) ≠ Term.one := by
  induction h with
  | root xs b i hi hn =>
    rw [convert_head]
    exact principal_image_ne_one k xs i (Dim_hd hsD) (recursive_head (.P xs b) hs) hn
  | coordinate xs b i _ h ih =>
    rw [convert_head]
    exact principal_image_ne_one k xs i (Dim_hd hsD) (recursive_head (.P xs b) hs)
      h.parent_ne_zero
  | tail xs b h ih =>
    have hb : RecursiveWF (k + 3) b := (RecursiveWF_P.1 hs).2.1
    have hbn : convert (k + 3) (code b) ≠ .zero :=
      fun he => h.parent_ne_zero ((convert_eq_zero_iff _ _).1 he)
    have hhead := ih hsD.tail hb
    intro hh
    have hwp := hs.wf
    rw [convert_P, kumakuma.OT2.assemble, ite_eq_right hbn] at hwp hh
    have hle := ((Term.wf_add_iff _ _).mp hwp).2.2.2.2
    have hh' : principal (k + 3) (arguments (k + 3) (trim (codes xs))) = Term.one := hh
    rw [hh'] at hle
    have ht := kumakuma.CountableTarget.head_properties hb.wf hbn
    exact hhead ((principal_le_one_iff ht.1 ht.2).mp hle)

theorem Coefficient.lt_of_H_omega [LargeCardinals.{u}] (k : Nat)
    {a s : multi.T} (h : Coefficient (k + 3) a s) (hsD : Dim (k + 3) s)
    (hs : RecursiveWF (k + 3) s)
    (hH : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true) : a < s := by
  have har := h.subterm.recursiveWF hs
  apply (convert_order k a s (h.subterm.dim hsD) hsD har hs).mpr
  by_cases hh : Term.head (convert (k + 3) (code a)) = Term.one
  · obtain ⟨n, he⟩ := head_one_nat har.wf hh
    rw [he]
    have hs0 : convert (k + 3) (code s) ≠ .zero :=
      fun hz => h.parent_ne_zero ((convert_eq_zero_iff _ _).1 hz)
    exact nat_lt_of_head_ne hs.wf hs0 (h.parent_image_head_ne_one k hsD hs) (n + 1)
  · exact (Term.allLt_iff _ _).mp hH _ (h.image_mem_H_omega k hh)

theorem H_convert_bound_of_coefficients [LargeCardinals.{u}] (k : Nat) (u : Term)
    (s : multi.T) (hsD : Dim (k + 3) s) (hs : RecursiveWF (k + 3) s)
    (hc : ∀ a, Coefficient (k + 3) a s → a < s) :
    Term.allLt (Term.H u (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true := by
  by_cases hs0 : s = .Z
  · subst s; simp only [convert_Z, Term.H, Term.allLt, List.all_nil]
  · have hn : convert (k + 3) (code s) ≠ .zero := fun hz => hs0 ((convert_eq_zero_iff _ _).1 hz)
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    rcases H_convert_coefficient k u s hz with rfl | ⟨a, ha, he⟩
    · exact (zero_lt_iff _).mpr hn
    · have har := ha.subterm.recursiveWF hs
      have hlt := (convert_order k a s (ha.subterm.dim hsD) hsD har hs).mp (hc a ha)
      rcases he with rfl | rfl
      · exact hlt
      · exact dropOne_lt_of_lt har.wf hs.wf hlt

theorem H_omega_bound_iff [LargeCardinals.{u}] (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hs : RecursiveWF (k + 3) s) :
    Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true ↔
        ∀ a, Coefficient (k + 3) a s → a < s := by
  constructor
  · intro hH a ha; exact ha.lt_of_H_omega k hsD hs hH
  · exact H_convert_bound_of_coefficients k Term.bigOmega s hsD hs

theorem childrenBelow_of_coefficients (k : Nat) : ∀ (s bound : multi.T), Dim (k + 3) s →
    Recursive s → s ≤ bound → (∀ a, Coefficient (k + 3) a s → a < bound) →
    ChildrenBelow bound s
  | .Z, _, _, _, _, _ => trivial
  | .P xs b, bound, hsD, hr, hle, hc => by
    have hr' := Recursive_P.1 hr
    have lift : ∀ a, a < .P xs b → a < bound := fun a ha => T.lt_of_lt_of_le ha hle
    refine ⟨?_, ?_⟩
    · intro i
      have hlt : V.get0 xs i < bound := by
        by_cases hi : i < k + 2
        · by_cases hn : V.get0 xs i = .Z
          · rw [hn]; exact lift .Z (T.Z_lt_P _ _)
          · exact hc _ (Coefficient.root (d := k + 3) xs b i (by omega) hn)
        · by_cases he : i = k + 2
          · rw [he]; exact lift _ (last_coordinate_lt xs b hsD)
          · rw [V.get0_ge xs i (by rw [hsD.length]; omega)]
            exact lift .Z (T.Z_lt_P _ _)
      apply (treeBelow_iff _ _).mpr
      refine ⟨hlt, ?_⟩
      by_cases hik : i < k + 3
      · exact childrenBelow_of_coefficients k (V.get0 xs i) bound (hsD.coord i) (hr'.1 i)
          (Or.inl hlt) (fun a ha => hc a (Coefficient.coordinate xs b i hik ha))
      · rw [V.get0_ge xs i (by rw [hsD.length]; omega)]; trivial
    · have hlt := lift b (descending_tail_lt xs b hr'.2.2)
      apply (treeBelow_iff _ _).mpr
      refine ⟨hlt, ?_⟩
      exact childrenBelow_of_coefficients k b bound hsD.tail hr'.2.1 (Or.inl hlt)
        (fun a ha => hc a (Coefficient.tail xs b ha))
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem coefficients_iff_subterms (k : Nat) (s : multi.T) (hsD : Dim (k + 3) s)
    (hr : Recursive s) :
    (∀ a, Coefficient (k + 3) a s → a < s) ↔ ∀ a, Subterm a s → a < s := by
  constructor
  · intro hc
    exact (childrenBelow_iff s s).mp
      (childrenBelow_of_coefficients k s s hsD hr (T.le_refl _) hc)
  · intro hs a ha; exact hs a ha.subterm

theorem H_omega_bound_iff_subterms [LargeCardinals.{u}] (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hs : RecursiveWF (k + 3) s) (hr : Recursive s) :
    Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true ↔ ∀ a, Subterm a s → a < s :=
  (H_omega_bound_iff k s hsD hs).trans (coefficients_iff_subterms k s hsD hr)

end kumakuma.GeneralImageOmegaCoefficients

namespace kumakuma.SourceOmegaTail

open multi OTQuotient DimensionCut SourceFundOrder
open SourceSubtermBounds SourceFundGap SourceRecursiveDescending
open GeneralImageCoefficients

theorem Omega_head_mass_pos (xs : V multi.T) (b : multi.T)
    (hr : Recursive (.P xs b)) {v : V multi.T} (hd : domF (.P xs b) = .Omega v) :
    0 < vectorMass xs := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hx : ∀ i, V.get0 xs i = .Z := by
    intro i
    by_cases hi : V.get0 xs i = .Z
    · exact hi
    · have hh := mass_positive hi
      have hu := vectorMass_get0_le xs i
      omega
  obtain ⟨i, _, hfv, _⟩ := domOmega_regular (.P xs b) hd
  have hh := domain_principal_le_head (.P xs b) hr hd
  change multi.T.P v .Z ≤ .P xs .Z at hh
  rcases hh with hh | hh
  · exact absurd ((lt_one_iff hx).1 hh) (by intro he; cases he)
  · have hv := ((T.P_eqv_iff _ _ _ _).1 hh).1
    have hvi := (V.eqv_iff_get0 v xs).1 hv i
    rw [hx i] at hvi
    exact (V.fnz_some_spec v i hfv).1 (T.eqv_Z_iff.1 hvi)

theorem fund_tail_subterms (xs : V multi.T) (b t : multi.T)
    (hb : b ≠ .Z) (hx : 0 < vectorMass xs)
    (hs : ∀ a, Subterm a (.P xs b) → a < .P xs b)
    (ht : ∀ a, Subterm a t → a < t) (hinc : t < T.fund (.P xs b) t) :
    ∀ a, Subterm a (T.fund (.P xs b) t) → a < T.fund (.P xs b) t := by
  by_cases ht0 : t = .Z
  · subst t; exact fund_zero_subterms (.P xs b) hs
  · have hc := (childrenBelow_iff (.P xs b) (.P xs b)).mpr hs
    have hm := mass_positive hb
    have hgap : gap (.P xs b) t = vectorMass xs + mass b := by
      rw [gap, ite_eq_right ht0, mass_P]
      omega
    have hcoords : ∀ i, TreeBelow (T.fund (.P xs b) t) (V.get0 xs i) := by
      intro i
      apply treeBelow_fund_of_small (.P xs b) t _ (hc.1 i)
      rw [hgap]
      have hi := vectorMass_get0_le xs i
      omega
    have hbtree : TreeBelow (T.fund (.P xs b) t) b := by
      apply treeBelow_fund_of_small (.P xs b) t b hc.2
      rw [hgap]
      omega
    have harg : TreeBelow (T.fund (.P xs b) t) t :=
      treeBelow_of_subterms _ t hinc (fun a ha => T.lt_trans (ht a ha) hinc)
    apply (childrenBelow_iff _ _).mp
    rw [fund_tail xs hb] at hcoords hbtree harg ⊢
    exact ⟨hcoords, hbtree.fund harg⟩

end kumakuma.SourceOmegaTail

namespace kumakuma.GeneralImageRegularLimit

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder
open kumakuma.GeneralImageTopPair kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.SourceFundOrder kumakuma.SourceSubtermBounds kumakuma.GeneralImageOmegaCoefficients
open kumakuma.CountableSource
open kumakuma.SourceOmegaTail

universe u

theorem topPair_context (n : Nat) (a b : Term) : Context n (topPair n a b) := by
  rcases topPair_shape n a b with hz | ⟨hp, hf⟩
  · exact Or.inl hz
  · exact Or.inr ⟨hp, Nat.le_of_eq hf.symm⟩

theorem inacc_image_drop_wf (k : Nat) (a : multi.T) (ha : RecursiveWF (k + 3) a) :
    Term.wf (.inacc (k + 1) (dropOne (convert (k + 3) (code a)))) = true := by
  apply (Term.wf_inacc_iff _ _).mpr
  refine ⟨dropOne_wf ha.wf, ?_⟩
  have hi := indices_drop (indices_convert (k + 3) (by omega) (code a))
  exact Nat.le_of_lt_succ (kumakuma.TargetIndexCuts.IndicesBelow.fT_lt (by omega : 0 < k + 2) hi)

theorem step_zero_wf (n : Nat) (a : Term) (ha : Term.wf a = true) :
    Term.wf (step n a .zero) = true := by
  by_cases ha0 : a = .zero
  · subst a
    by_cases hn : n = 0
    · subst n; rfl
    · simp only [step, ↓reduceIte, hn, Term.wf]
  · simpa only [step, ha0, ↓reduceIte] using ha

theorem lower_zero_wf (j : Nat) (xs : List Term) (a : Term)
    (hz : ∀ i, i < j → xs[i]?.getD .zero = .zero) (ha : Term.wf a = true) :
    Term.wf (lower j xs a) = true := by
  induction j generalizing a with
  | zero => exact ha
  | succ j ih =>
    rw [lower_succ, hz j (by omega)]
    exact ih _ (fun i hi => hz i (by omega)) (step_zero_wf j a ha)

theorem step_wf_of_omega_closed (n : Nat) (a c : Term) (ha : Above n a)
    (hwa : Term.wf a = true) (hc : Term.wf c = true)
    (hH : Term.allLt (Term.H Term.bigOmega c) c = true) :
    Term.wf (step n a c) = true := by
  by_cases ha0 : a = .zero
  · subst a
    by_cases hn : n = 0
    · subst n
      simp only [step, ↓reduceIte]
      exact (Term.wf_psi_iff _ _).mpr ⟨by decide +kernel, Term.wf_bigOmega, hc, hH⟩
    · by_cases hc0 : c = .zero
      · simp only [step, ↓reduceIte, hn, hc0, Term.wf]
      · simp only [step, ↓reduceIte, hn, hc0]
        exact (Term.wf_psi_iff _ _).mpr ⟨by simp [Term.isRT, Term.isLimT],
          (Term.wf_inacc_iff _ _).mpr ⟨rfl, by simp [Term.fT]⟩, dropOne_wf hc,
          H_drop_bound_of_omega _ c hc hH⟩
  · by_cases hc0 : c = .zero
    · simpa only [step, ha0, hc0, ↓reduceIte] using hwa
    · simp only [step, ha0, hc0, ↓reduceIte]
      exact (Term.wf_psi_iff _ _).mpr ⟨regular_isRT n a,
        regular_wf n hwa (above_principal (ha.resolve_left ha0)), dropOne_wf hc,
        H_drop_bound_of_omega _ c hc hH⟩

theorem topPair_successor_predecessor (n : Nat) (a c : Term)
    (hi : Term.wf (.inacc n (dropOne a)) = true) (hc : Term.wf c = true)
    (hw : Term.wf (topPair n a (succTerm c)) = true) :
    Term.wf (topPair n a c) = true := by
  by_cases hc0 : c = .zero
  · subst c
    by_cases ha0 : a = .zero
    · simp only [topPair, ↓reduceIte, ha0, Term.wf]
    · simpa only [topPair, ↓reduceIte, ha0] using hi
  · have hdrop := drop_succ c hc0
    by_cases ha0 : a = .zero
    · simp only [topPair, hc0, succTerm_ne_zero, ha0, hdrop, ↓reduceIte] at hw ⊢
      exact psi_wf_of_succ (.inacc n .zero) (dropOne c) (dropOne_wf hc) hw
    · simp only [topPair, hc0, succTerm_ne_zero, ha0, hdrop, ↓reduceIte] at hw ⊢
      exact psi_wf_of_succ (.inacc n (succTerm (dropOne a))) (dropOne c) (dropOne_wf hc) hw

theorem topPair_wf_of_omega_closed (n : Nat) (a b : Term) (ha : Term.wf a = true)
    (hi : Term.wf (.inacc n (dropOne a)) = true) (hb : Term.wf b = true)
    (hH : Term.allLt (Term.H Term.bigOmega b) b = true) :
    Term.wf (topPair n a b) = true := by
  by_cases hb0 : b = .zero
  · subst b
    by_cases ha0 : a = .zero
    · simp only [topPair, ↓reduceIte, ha0, Term.wf]
    · simpa only [topPair, ↓reduceIte, ha0] using hi
  · by_cases ha0 : a = .zero
    · simp only [topPair, hb0, ha0, ↓reduceIte]
      exact (Term.wf_psi_iff _ _).mpr ⟨by simp [Term.isRT, Term.isLimT],
        (Term.wf_inacc_iff _ _).mpr ⟨rfl, by simp [Term.fT]⟩, dropOne_wf hb,
        H_drop_bound_of_omega _ b hb hH⟩
    · simp only [topPair, hb0, ha0, ↓reduceIte]
      exact (Term.wf_psi_iff _ _).mpr ⟨by simp [Term.isRT, Term.isLimT, succTerm_ne_zero, succTerm_isSucc],
        (Term.wf_inacc_iff _ _).mpr ⟨succTerm_wf (dropOne_wf ha),
          by cases dropOne a <;> simp [succTerm, Term.fT, Term.one, Term.bigOmega]⟩,
        dropOne_wf hb, H_drop_bound_of_omega _ b hb hH⟩

theorem lower_regular_update (j m : Nat) (xs ys : List Term) (a c t : Term)
    (him : m + 1 < j) (hctx : Context j a)
    (hc : Term.wf c = true) (ht : Term.wf t = true)
    (hHt : Term.allLt (Term.H Term.bigOmega t) t = true)
    (hx : xs[m + 1]?.getD .zero = succTerm c)
    (hy : ys[m + 1]?.getD .zero = c) (hyt : ys[m]?.getD .zero = t)
    (hzero : ∀ i, i < m → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, m + 1 < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero)
    (hw : Term.wf (lower j xs a) = true) : Term.wf (lower j ys a) = true := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    rw [lower_succ] at hw ⊢
    have hshape : Context j (step j a (xs[j]?.getD .zero)) :=
      step_shape _ (context_above hctx)
    by_cases hij : m + 1 < j
    · rw [hsame j hij (by omega)]
      exact ih _ hij hshape (fun i hi hj => hsame i hi (by omega)) hw
    · have he : j = m + 1 := by omega
      subst j
      rw [hx] at hw hshape
      have hwstep := lower_context_wf (m + 1) xs _ hshape hw
      have hnew := step_successor_predecessor (m + 1) a c (context_above hctx) hc hwstep
      have hnewctx : Context (m + 1) (step (m + 1) a c) := step_shape _ (context_above hctx)
      rw [hy, lower_succ, hyt]
      exact lower_zero_wf m ys _ hzero
        (step_wf_of_omega_closed m _ t (context_above hnewctx) hnew ht hHt)


theorem fund_regular_recursiveWF (k m : Nat) (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hv : V.fnz xs = some (m + 1)) (hdom : domF (V.get0 xs (m + 1)) = .one) (t : multi.T)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (ht : RecursiveWF (k + 3) t)
    (hH : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code t)))
      (convert (k + 3) (code t)) = true) :
    RecursiveWF (k + 3) (T.fund (.P xs .Z) t) := by
  have hml : m + 1 < k + 3 := by have := fnz_lt_length hv; rw [hsD.length] at this; exact this
  have hlow := (V.fnz_some_spec xs _ hv).2
  have hcoords : ∀ i, RecursiveWF (k + 3) (V.get0 xs i) := (RecursiveWF_P.1 hs).1
  let p := T.fund (V.get0 xs (m + 1)) .Z
  have hp : RecursiveWF (k + 3) p :=
    fund_one_recursiveWF _ _ (hsD.coord (m + 1)) (hcoords _) hdom
  have hsucc : convert (k + 3) (code (V.get0 xs (m + 1))) =
      succTerm (convert (k + 3) (code p)) := by
    obtain ⟨a, he⟩ := dom_one_succ (V.get0 xs (m + 1)) (hsD.coord (m + 1)) hdom
    show _ = succTerm (convert (k + 3) (code (T.fund (V.get0 xs (m + 1)) .Z)))
    rw [he, kumakuma.SourceSuccessor.fund_succ, convert_succ]
  let zs := V.set (V.set xs (m + 1) p) m t
  have hlen : xs.length = k + 3 := hsD.length
  have zidx (i : Nat) : V.get0 zs i =
      if i = m then t else if i = m + 1 then p else V.get0 xs i := by
    show V.get0 (V.set (V.set xs (m + 1) p) m t) i = _
    rw [V.get0_set _ m t i (by rw [V.length_set]; omega), V.get0_set xs (m + 1) p i (by omega)]
  have zhigh (i : Nat) (hi : m + 1 < i) : V.get0 zs i = V.get0 xs i := by
    rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
  have zlow (i : Nat) (hi : i < m) : V.get0 zs i = .Z := by
    rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hlow i (by omega)
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes zs))
  have oldGet (i : Nat) : oldArgs[i]?.getD .zero =
      convert (k + 3) (code (V.get0 xs i)) := converted_coordinate xs i
  have newGet (i : Nat) : newArgs[i]?.getD .zero =
      convert (k + 3) (code (V.get0 zs i)) := converted_coordinate zs i
  have newP : newArgs[m + 1]?.getD .zero = convert (k + 3) (code p) := by
    rw [newGet (m + 1), zidx, ite_eq_right (by omega), ite_eq_left rfl]
  have newT : newArgs[m]?.getD .zero = convert (k + 3) (code t) := by
    rw [newGet m, zidx, ite_eq_left rfl]
  have oldSucc : oldArgs[m + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by
    rw [oldGet (m + 1)]; exact hsucc
  have newZero : ∀ i, i < m → newArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [newGet i, zlow i hi, convert_Z]
  have newSame : ∀ i, m + 1 < i → i < k + 3 →
      newArgs[i]?.getD .zero = oldArgs[i]?.getD .zero := by
    intro i hi _
    rw [newGet i, oldGet i, zhigh i hi]
  rw [fund_one_succ hv hdom]
  change RecursiveWF (k + 3) (.P zs .Z)
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
  · intro i
    rw [zidx]
    split
    · exact ht
    · split
      · exact hp
      · exact hcoords i
  · rw [convert_principal, principal_as_layers]
    change Term.wf (lower (k + 1) newArgs
      (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) = true
    have hold : Term.wf (lower (k + 1) oldArgs
        (topPair (k + 1) (oldArgs[k + 2]?.getD .zero) (oldArgs[k + 1]?.getD .zero))) = true := by
      have hh := hs.wf
      rwa [convert_principal, principal_as_layers] at hh
    by_cases hhighest : m + 1 = k + 2
    · have he : m = k + 1 := by omega
      subst m
      rw [newP, newT]
      exact lower_zero_wf (k + 1) newArgs _ newZero
        (topPair_wf_of_omega_closed (k + 1) _ _ hp.wf (inacc_image_drop_wf k p hp) ht.wf hH)
    · by_cases hmiddle : m + 1 = k + 1
      · have he : m = k := by omega
        subst m
        have hhigh := newSame (k + 2) (by omega) (by omega)
        rw [hhigh, newP, lower_succ, newT]
        apply lower_zero_wf k newArgs _ newZero
        have htopold := lower_context_wf (k + 1) oldArgs _ (topPair_context _ _ _) hold
        rw [oldSucc] at htopold
        have hi : Term.wf (.inacc (k + 1) (dropOne (oldArgs[k + 2]?.getD .zero))) = true := by
          rw [oldGet (k + 2)]
          exact inacc_image_drop_wf k _ (hcoords _)
        have htop := topPair_successor_predecessor (k + 1) _ _ hi hp.wf htopold
        exact step_wf_of_omega_closed k _ _ (context_above (topPair_context _ _ _)) htop ht.wf hH
      · have hi : m + 1 < k + 1 := by omega
        rw [newSame (k + 2) (by omega) (by omega), newSame (k + 1) (by omega) (by omega)]
        exact lower_regular_update (k + 1) m oldArgs newArgs _ _ _ hi (topPair_context _ _ _)
          hp.wf ht.wf hH oldSucc newP newT newZero
          (fun i him hik => newSame i him (by omega)) hold

end kumakuma.GeneralImageRegularLimit

namespace kumakuma.SourceOmegaHighest

open multi OTQuotient DimensionCut SourceFundOrder
open SourceSubtermBounds SourceFundGap SourceRecursiveDescending
open GeneralImageCoefficients

theorem Dim_lastVec {m : Nat} {a : multi.T} (ha : Dim (m + 1) a) :
    Dim (m + 1) (.P (lastVec m a) .Z) := by
  refine Dim_P (lastVec_length _ _) (fun i => ?_) (Dim_Z _)
  rw [get0_lastVec]
  split
  · exact ha
  · exact Dim_Z _

theorem highest_not_diagonal (m : Nat) (a : multi.T) (haD : Dim (m + 1) a) (hr : Recursive a)
    {v : V multi.T} (hd : domF a = .Omega v) : ¬ lastVec m a < v := by
  intro hv
  have hl := last_coordinate_lt (lastVec m a) .Z (Dim_lastVec haD)
  rw [get0_lastVec, ite_eq_left rfl] at hl
  have hrlt := diagonal_principal_lt_argument (lastVec m a) a hr hd hv
  exact T.lt_irrefl _ (T.lt_trans hl hrlt)

theorem highest_Omega_domain (m : Nat) (a : multi.T) (haD : Dim (m + 1) a) (hr : Recursive a)
    {v : V multi.T} (hd : domF a = .Omega v) :
    domF (.P (lastVec m a) .Z) = .Omega v := by
  have hn := highest_not_diagonal m a haD hr hd
  have ha : a ≠ .Z := by intro h; rw [h, domF_Z] at hd; cases hd
  exact domF_nondiag (fnz_lastVec m ha) (by rw [get0_lastVec, ite_eq_left rfl]; exact hd) hn

theorem lastVec_replace_last (m : Nat) (a b : multi.T) :
    V.set (lastVec m a) m b = lastVec m b := by
  apply V.eq_of_get0 _ _ (by rw [V.length_set, lastVec_length, lastVec_length])
  intro i
  rw [V.get0_set _ m b i (by rw [lastVec_length]; omega), get0_lastVec, get0_lastVec]
  split <;> rfl

theorem highest_Omega_fund (m : Nat) (a t : multi.T) (haD : Dim (m + 1) a) (hr : Recursive a)
    {v : V multi.T} (hd : domF a = .Omega v) :
    T.fund (.P (lastVec m a) .Z) t = .P (lastVec m (T.fund a t)) .Z := by
  have hn := highest_not_diagonal m a haD hr hd
  have ha : a ≠ .Z := by intro h; rw [h, domF_Z] at hd; cases hd
  have hg : V.get0 (lastVec m a) m = a := by rw [get0_lastVec, ite_eq_left rfl]
  rw [fund_nondiag (fnz_lastVec m ha) (by rw [hg]; exact hd) hn, hg, lastVec_replace_last]

theorem vectorMass_lastVec (m : Nat) (a : multi.T) :
    vectorMass (lastVec m a) = mass a := by
  have hz : vectorMass (zeros m) = 0 := vectorMass_eq_zero _ (get0_zeros m)
  rw [lastVec, vectorMass_snoc, hz, Nat.zero_add]

end kumakuma.SourceOmegaHighest

namespace kumakuma.SourceOmegaInvariant

open multi OTQuotient DimensionCut SourceFundOrder
open SourceSubtermBounds SourceFundGap SourceRecursiveDescending
open GeneralImageCoefficients SourceOmegaTail SourceOmegaHighest

def CutSpine (i : Nat) : multi.T → Prop
  | .Z => True
  | .P xs b => (∀ j, i < j → V.get0 xs j = .Z) ∧ CutSpine i (V.get0 xs i) ∧ CutSpine i b
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem CutSpine.zero (i : Nat) : CutSpine i .Z := by rw [CutSpine]; trivial

theorem CutSpine_P {i : Nat} {xs : V multi.T} {b : multi.T} :
    CutSpine i (.P xs b) ↔
      (∀ j, i < j → V.get0 xs j = .Z) ∧ CutSpine i (V.get0 xs i) ∧ CutSpine i b := by
  rw [CutSpine]

theorem CutSpine.coordinate_lt (i : Nat) : ∀ (xs : V multi.T) (b : multi.T),
    CutSpine i (.P xs b) → V.get0 xs i < .P xs b
  | xs, b, hs => by
    have hs' := CutSpine_P.1 hs
    cases he : V.get0 xs i with
    | Z => exact T.Z_lt_P _ _
    | P ys c =>
      have hcut := hs'.2.1
      rw [he] at hcut
      have hcut' := CutSpine_P.1 hcut
      have harg := CutSpine.coordinate_lt i ys c hcut
      apply T.P_lt_P_of_vlt
      apply V.lt_of_pivot i
      · intro j hj
        rw [hcut'.1 j hj, hs'.1 j hj]
        exact compareT_ZZ
      · rw [he]; exact harg
termination_by xs b => (multi.T.P xs b).size
decreasing_by
  have hh := multi.T.size_get0_lt_P xs i b
  rw [he] at hh
  exact hh

theorem CutSpine.principal_replace (i j : Nat) (xs : V multi.T)
    (a : multi.T) (hs : CutSpine i (.P xs .Z)) (hji : j ≤ i)
    (ha : j = i → CutSpine i a) : CutSpine i (.P (V.set xs j a) .Z) := by
  have hs' := CutSpine_P.1 hs
  refine CutSpine_P.2 ⟨?_, ?_, CutSpine.zero i⟩
  · intro l hl
    rw [V.get0_set_ne xs j a l (by omega)]
    exact hs'.1 l hl
  · by_cases hj : j = i
    · subst hj
      by_cases hil : j < xs.length
      · rw [V.get0_set_same xs j a hil]; exact ha rfl
      · rw [set_of_ge xs j a (Nat.le_of_not_lt hil)]; exact hs'.2.1
    · rw [V.get0_set_ne xs j a i (Ne.symm hj)]
      exact hs'.2.1

theorem CutSpine.mul_principal (i : Nat) (xs : V multi.T)
    (hs : CutSpine i (.P xs .Z)) : ∀ t : multi.T, CutSpine i (multi.T.mul (.P xs .Z) t)
  | .Z => CutSpine.zero i
  | .P ys b => by
    show CutSpine i (.P xs (multi.T.mul (.P xs .Z) b))
    have hs' := CutSpine_P.1 hs
    exact CutSpine_P.2 ⟨hs'.1, hs'.2.1, CutSpine.mul_principal i xs hs b⟩

theorem CutSpine.fund (i : Nat) : ∀ (s t : multi.T), CutSpine i s → CutSpine i (T.fund s t)
  | .Z, _, _ => by rw [fund_Z]; exact CutSpine.zero i
  | .P xs b, t, hs => by
    have hs' := CutSpine_P.1 hs
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | j
      · rw [fund_none hf]; exact CutSpine.zero i
      · have hji : j ≤ i := by
          apply Nat.le_of_not_lt
          intro hij
          exact (V.fnz_some_spec xs j hf).1 (hs'.1 j hij)
        have update (a : multi.T) : CutSpine i (.P (V.set xs j (T.fund (V.get0 xs j) a)) .Z) := by
          apply CutSpine.principal_replace i j xs _ hs hji
          intro he
          subst he
          exact CutSpine.fund j _ a hs'.2.1
        cases hd : domF (V.get0 xs j) with
        | zero => rw [fund_zero hf hd]; exact update t
        | omega => rw [fund_omega hf hd]; exact update t
        | Omega v =>
          by_cases hv : xs < v
          · rw [fund_diag hf hd hv]; exact update _
          · rw [fund_nondiag hf hd hv]; exact update t
        | one =>
          cases j with
          | zero =>
            rw [fund_one_zero hf hd]
            exact CutSpine.mul_principal i _ (update .Z) t
          | succ m =>
            rw [fund_one_succ hf hd]
            apply CutSpine.principal_replace i m _ t (update .Z) (by omega)
            intro he
            omega
    · rw [fund_tail xs hb]
      exact CutSpine_P.2 ⟨hs'.1, hs'.2.1, CutSpine.fund i b t hs'.2.2⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem above_zero_of_vec_le (i : Nat) (xs ys : V multi.T)
    (hy : ∀ j, i < j → V.get0 ys j = .Z) (hxy : xs ≤ ys) :
    ∀ j, i < j → V.get0 xs j = .Z := by
  intro j hj
  rcases hxy with hxy | hxy
  · obtain ⟨p, habove, hp⟩ := (V.lt_iff_pivot xs ys).1 hxy
    have hpi : p ≤ i := by
      apply Nat.le_of_not_lt
      intro hip
      rw [hy p hip] at hp
      exact T.not_lt_Z _ hp
    have he := habove j (by omega)
    rw [hy j hj] at he
    exact T.eqv_Z_iff.1 he
  · have he := (V.eqv_iff_get0 xs ys).1 hxy j
    rw [hy j hj] at he
    exact T.eqv_Z_iff.1 he

theorem above_zero_of_lt_principal (i : Nat)
    (xs ys : V multi.T) (b c : multi.T)
    (hx : ∀ j, i < j → V.get0 xs j = .Z) (h : multi.T.P ys c < .P xs b) :
    ∀ j, i < j → V.get0 ys j = .Z := by
  have hv : ys ≤ xs := by
    rcases (T.P_lt_P_iff ys xs c b).1 h with h | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  exact above_zero_of_vec_le i ys xs hx hv

theorem TreeBelow.cutSpine (i : Nat) (xs : V multi.T) (b : multi.T)
    (hx : ∀ j, i < j → V.get0 xs j = .Z) : ∀ s : multi.T, TreeBelow (.P xs b) s → CutSpine i s
  | .Z, _ => CutSpine.zero i
  | .P ys c, hs => by
    have hs' := TreeBelow_P.1 hs
    exact CutSpine_P.2 ⟨above_zero_of_lt_principal i xs ys b c hx hs'.1,
      TreeBelow.cutSpine i xs b hx _ (hs'.2.1 i), TreeBelow.cutSpine i xs b hx c hs'.2.2⟩
termination_by s => s.size
decreasing_by
  all_goals first
    | exact multi.T.size_get0_lt_P _ _ _
    | exact multi.T.size_lt_P_right _ _

theorem treeBelow_mul_of_root_lt (xs : V multi.T) (bound : multi.T)
    (hx : ∀ i, TreeBelow bound (V.get0 xs i)) (hz : TreeBelow bound .Z) :
    ∀ t : multi.T, multi.T.mul (.P xs .Z) t < bound → TreeBelow bound (multi.T.mul (.P xs .Z) t)
  | .Z, _ => hz
  | .P ys b, hroot => by
    show TreeBelow bound (.P xs (multi.T.mul (.P xs .Z) b))
    refine TreeBelow_P.2 ⟨hroot, hx, ?_⟩
    apply treeBelow_mul_of_root_lt xs bound hx hz b
    exact T.lt_trans
      (descending_tail_lt xs _ (SourceDescending.mul_principal_descending xs (.P ys b))) hroot

theorem ChildrenBelow.fund_of_root_lt {s t bound : multi.T}
    (hs : ChildrenBelow bound s) (ht : TreeBelow bound t) (hroot : T.fund s t < bound) :
    ChildrenBelow bound (T.fund s t) := by
  cases s with
  | Z => rw [fund_Z]; trivial
  | P xs b =>
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [fund_none hf]; trivial
      · have hfu : ∀ a, TreeBelow bound a → TreeBelow bound (T.fund (V.get0 xs i) a) :=
          fun a ha => (hs.1 i).fund ha
        cases hd : domF (V.get0 xs i) with
        | zero => rw [fund_zero hf hd]; exact ⟨treeBelow_set xs i _ bound hs.1 (hfu t ht), hs.2⟩
        | omega => rw [fund_omega hf hd]; exact ⟨treeBelow_set xs i _ bound hs.1 (hfu t ht), hs.2⟩
        | Omega ys =>
          by_cases hv : xs < ys
          · rw [fund_diag hf hd hv]
            exact ⟨treeBelow_set xs i _ bound hs.1
              (hfu _ (treeBelow_iter (T.fund (V.get0 xs i)) bound ht.zero hfu t)), hs.2⟩
          · rw [fund_nondiag hf hd hv]
            exact ⟨treeBelow_set xs i _ bound hs.1 (hfu t ht), hs.2⟩
        | one =>
          cases i with
          | zero =>
            rw [fund_one_zero hf hd] at hroot ⊢
            apply TreeBelow.children
            exact treeBelow_mul_of_root_lt _ bound
              (treeBelow_set xs 0 _ bound hs.1 (hfu .Z ht.zero)) ht.zero t hroot
          | succ m =>
            rw [fund_one_succ hf hd]
            exact ⟨treeBelow_set _ m t bound
              (treeBelow_set xs (m + 1) _ bound hs.1 (hfu .Z ht.zero)) ht, hs.2⟩
    · rw [fund_tail xs hb]
      exact ⟨hs.1, hs.2.fund ht⟩

theorem coordinate_fund_subterms (xs : V multi.T) (i : Nat) (t : multi.T)
    (ha0 : V.get0 xs i ≠ .Z)
    (hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z)
    (ht : ∀ a, Subterm a t → a < t)
    (hinc : t < T.fund (.P xs .Z) t) :
    ∀ a, Subterm a (T.fund (.P xs .Z) t) → a < T.fund (.P xs .Z) t := by
  by_cases ht0 : t = .Z
  · subst t; exact fund_zero_subterms (.P xs .Z) hs
  · have hil : i < xs.length := by
      apply Nat.lt_of_not_le; intro h; exact ha0 (V.get0_ge xs i h)
    let s : multi.T := .P xs .Z
    let a : multi.T := V.get0 xs i
    have ham : 0 < mass a := mass_positive ha0
    have ham' : 0 < mass (V.get0 xs i) := mass_positive ha0
    have hgap : gap s t = vectorMass xs := by
      show gap (.P xs .Z) t = _
      rw [gap, ite_eq_right ht0, mass_P, mass_Z]
      omega
    have hsource := (childrenBelow_iff s s).mpr hs
    have harg : TreeBelow (T.fund s t) t :=
      treeBelow_of_subterms _ t hinc (fun c hc => T.lt_trans (ht c hc) hinc)
    have hchildren : ChildrenBelow (T.fund s t) a := by
      apply (childrenBelow_iff _ _).mpr
      intro c hc
      apply small_lt_fund_all s t c (hs c (Subterm.trans hc (Subterm.coordinate xs .Z i)))
      rw [hgap]
      exact Nat.lt_of_lt_of_le (kumakuma.SourceCoefficientGap.mass_lt_of_subterm hc)
        (vectorMass_get0_le xs i)
    have hcoords : ∀ j, j ≠ i → TreeBelow (T.fund s t) (V.get0 xs j) := by
      intro j hj
      apply treeBelow_fund_of_small s t _ (hsource.1 j)
      rw [hgap]
      have hp := vectorMass_pair_le xs j i hj
      omega
    have hupdated : TreeBelow (T.fund s t) (T.fund a t) := by
      by_cases hsmall : mass a < vectorMass xs
      · exact (treeBelow_fund_of_small s t a (hsource.1 i) (by rw [hgap]; exact hsmall)).fund harg
      · have hsmall' : ¬ mass (V.get0 xs i) < vectorMass xs := hsmall
        have hsingle : ∀ j, j ≠ i → V.get0 xs j = .Z := by
          intro j hj
          have hp := vectorMass_pair_le xs j i hj
          by_cases hz : V.get0 xs j = .Z
          · exact hz
          · have hmpos := mass_positive hz
            omega
        have hhigh : ∀ j, i < j → V.get0 xs j = .Z :=
          fun j hj => hsingle j (by omega)
        have hcut : CutSpine i a := TreeBelow.cutSpine i xs .Z hhigh a (hsource.1 i)
        have hcut' := CutSpine.fund i a t hcut
        have hparent : CutSpine i (.P (V.set xs i (T.fund a t)) .Z) := by
          refine CutSpine_P.2 ⟨?_, ?_, CutSpine.zero i⟩
          · intro j hj
            rw [V.get0_set_ne xs i _ j (by omega)]
            exact hhigh j hj
          · rw [V.get0_set_same xs i _ hil]
            exact hcut'
        have hroot : T.fund a t < T.fund s t := by
          show _ < T.fund (.P xs .Z) t
          rw [hfund]
          have hh := CutSpine.coordinate_lt i (V.set xs i (T.fund a t)) .Z hparent
          rwa [V.get0_set_same xs i _ hil] at hh
        exact (treeBelow_iff _ _).mpr ⟨hroot, ChildrenBelow.fund_of_root_lt hchildren harg hroot⟩
    apply (childrenBelow_iff _ _).mp
    show ChildrenBelow (T.fund (.P xs .Z) t) (T.fund (.P xs .Z) t)
    have hfund' : T.fund s t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z := hfund
    rw [hfund'] at harg hupdated hcoords
    rw [hfund]
    refine ⟨?_, harg.zero⟩
    intro j
    rw [V.get0_set xs i _ j hil]
    split
    · exact hupdated
    · rename_i hj
      exact hcoords j hj

theorem inherited_fund_subterms (xs : V multi.T) (i : Nat)
    (t : multi.T) {v : V multi.T}
    (hf : V.fnz xs = some i) (hd : domF (V.get0 xs i) = .Omega v) (hn : ¬ xs < v)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z)
    (ht : ∀ a, Subterm a t → a < t)
    (hinc : t < T.fund (.P xs .Z) t) :
    ∀ a, Subterm a (T.fund (.P xs .Z) t) → a < T.fund (.P xs .Z) t :=
  coordinate_fund_subterms xs i t (V.fnz_some_spec xs i hf).1 (fund_nondiag hf hd hn t) hs ht hinc

theorem fund_Omega_subterms (s t : multi.T) (hr : Recursive s)
    {v : V multi.T} (hd : domF s = .Omega v)
    (hs : ∀ a, Subterm a s → a < s)
    (ht : ∀ a, Subterm a t → a < t) (hinc : t < T.fund s t) :
    ∀ a, Subterm a (T.fund s t) → a < T.fund s t := by
  cases s with
  | Z => rw [domF_Z] at hd; cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst hb
      rcases hf : V.fnz xs with _ | i
      · rw [domF_none hf] at hd; cases hd
      · cases hc : domF (V.get0 xs i) with
        | zero => rw [domF_zero hf hc] at hd; cases hd
        | omega => rw [domF_omega hf hc] at hd; cases hd
        | one =>
          cases i with
          | zero => rw [domF_one_zero hf hc] at hd; cases hd
          | succ m => exact regular_fund_subterms xs m hf hc t hs ht hinc
        | Omega ys =>
          by_cases hv : xs < ys
          · rw [domF_diag hf hc hv] at hd; cases hd
          · exact inherited_fund_subterms xs i t hf hc hv hs ht hinc
    · exact fund_tail_subterms xs b t hb (Omega_head_mass_pos xs b hr hd) hs ht hinc

theorem Omega_iter_subterms (s : multi.T) (hr : Recursive s)
    {v : V multi.T} (hd : domF s = .Omega v)
    (hs : ∀ a, Subterm a s → a < s) (lam : Nat) : ∀ n : Nat,
    ∀ a, Subterm a (multi.T.iter (T.fund s) (ofNatD lam n)) →
      a < multi.T.iter (T.fund s) (ofNatD lam n)
  | 0 => by
    intro a ha
    have hh := ha.size_lt
    have : (multi.T.iter (T.fund s) (ofNatD lam 0)).size = 0 := rfl
    omega
  | n + 1 => by
    rw [iter_ofNat_succ]
    exact fund_Omega_subterms s _ hr hd hs (Omega_iter_subterms s hr hd hs lam n)
      (domOmega_iter_lt_next s hd lam n)

end kumakuma.SourceOmegaInvariant

namespace kumakuma.GeneralImageHighOmega

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageRegularLimit

universe u

theorem high_recursive_image (k : Nat) (a : multi.T)
    (hs : RecursiveWF (k + 3) (topNode k a)) : RecursiveWF (k + 3) a := by
  have hh := (RecursiveWF_P.1 hs).1 (k + 2)
  rwa [get0_lastVec, ite_eq_left rfl] at hh

end kumakuma.GeneralImageHighOmega

namespace kumakuma.SourceCountableInvariant

open multi OTQuotient DimensionCut SourceFundOrder
open SourceSubtermBounds SourceFundGap SourceRecursiveDescending
open GeneralImageCoefficients SourceOmegaTail SourceOmegaInvariant

theorem TreeBelow.mono_le {s a b : multi.T} (hs : TreeBelow a s) (hab : a ≤ b) :
    TreeBelow b s :=
  treeBelow_of_subterms b s (T.lt_of_lt_of_le hs.root_lt hab)
    (fun c hc => T.lt_of_lt_of_le (Subterm.treeBelow hc hs).root_lt hab)

theorem ofNat_lt_succ (lam n : Nat) : ofNatD lam n < ofNatD lam (n + 1) := by
  rw [← SourceSuccessor.nat_succ]
  exact (SourceSuccessor.lt_succ_iff_le lam _ _).mpr (T.le_refl _)

theorem treeBelow_ofNat (lam : Nat) : ∀ (n : Nat) (bound : multi.T), ofNatD lam n < bound →
    TreeBelow bound (ofNatD lam n)
  | 0, _, h => TreeBelow_Z.2 h
  | n + 1, bound, h => by
    have hb := T.lt_trans (ofNat_lt_succ lam n) h
    have hz : TreeBelow bound .Z := (treeBelow_ofNat lam n bound hb).zero
    exact TreeBelow_P.2 ⟨h, fun i => by rw [get0_zeros]; exact hz, treeBelow_ofNat lam n bound hb⟩

theorem ofNat_subterms (lam n : Nat) :
    ∀ a, Subterm a (ofNatD lam n) → a < ofNatD lam n := by
  cases n with
  | zero =>
    intro a ha
    have hh := ha.size_lt
    have : (ofNatD lam 0).size = 0 := rfl
    omega
  | succ n =>
    apply (childrenBelow_iff _ _).mp
    show ChildrenBelow (ofNatD lam (n + 1)) (.P (zeros lam) (ofNatD lam n))
    have ht := treeBelow_ofNat lam n _ (ofNat_lt_succ lam n)
    exact ⟨fun i => by rw [get0_zeros]; exact ht.zero, ht⟩

theorem succ_le_of_lt (lam : Nat) {a b : multi.T} (h : a < b) :
    SourceSuccessor.succ lam a ≤ b := by
  rcases T.le_total (SourceSuccessor.succ lam a) b with hh | hh
  · exact hh
  · rcases hh with hh | hh
    · have hb := (SourceSuccessor.lt_succ_iff_le lam b a).mp hh
      exact absurd (T.lt_of_lt_of_le h hb) (T.lt_irrefl _)
    · exact Or.inr (T.eqv_symm hh)

theorem ofNat_le_countable_fund (s : multi.T) (hd : domF s = .omega) (lam : Nat) :
    ∀ n : Nat, ofNatD lam n ≤ T.fund s (ofNatD lam n)
  | 0 => T.Z_le _
  | n + 1 => by
    have hn : ofNatD lam n < T.fund s (ofNatD lam (n + 1)) :=
      T.lt_of_le_of_lt (ofNat_le_countable_fund s hd lam n) (countable_fund_lt_next s hd lam n)
    have h := succ_le_of_lt lam hn
    rwa [SourceSuccessor.nat_succ] at h

theorem coordinate_update_root_lt (xs : V multi.T) (i : Nat) (t : multi.T)
    (ha0 : V.get0 xs i ≠ .Z)
    (hfund : T.fund (.P xs .Z) t = .P (V.set xs i (T.fund (V.get0 xs i) t)) .Z)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z) :
    T.fund (V.get0 xs i) t < T.fund (.P xs .Z) t := by
  have hil : i < xs.length := by
    apply Nat.lt_of_not_le; intro h; exact ha0 (V.get0_ge xs i h)
  by_cases ht0 : t = .Z
  · subst t
    have hh : Subterm (V.get0 (V.set xs i (T.fund (V.get0 xs i) .Z)) i) (T.fund (.P xs .Z) .Z) := by
      rw [hfund]; exact Subterm.coordinate _ .Z i
    have hb := fund_zero_subterms (.P xs .Z) hs _ hh
    rwa [V.get0_set_same xs i _ hil] at hb
  · have hgap : gap (.P xs .Z) t = vectorMass xs := by
      rw [gap, ite_eq_right ht0, mass_P, mass_Z]; omega
    by_cases hsmall : mass (V.get0 xs i) < vectorMass xs
    · have hroot := small_lt_fund_all (.P xs .Z) t (V.get0 xs i)
        (hs _ (Subterm.coordinate xs .Z i)) (by rw [hgap]; exact hsmall)
      exact T.lt_trans (fund_lt _ t ha0) hroot
    · have hsingle : ∀ j, j ≠ i → V.get0 xs j = .Z := by
        intro j hj
        have hp := vectorMass_pair_le xs j i hj
        by_cases hz : V.get0 xs j = .Z
        · exact hz
        · have hmpos := mass_positive hz
          omega
      have hhigh : ∀ j, i < j → V.get0 xs j = .Z := fun j hj => hsingle j (by omega)
      have hc := (childrenBelow_iff _ _).mpr hs
      have hcut := CutSpine.fund i _ t (TreeBelow.cutSpine i xs .Z hhigh _ (hc.1 i))
      have hp : CutSpine i (.P (V.set xs i (T.fund (V.get0 xs i) t)) .Z) := by
        refine CutSpine_P.2 ⟨?_, ?_, CutSpine.zero i⟩
        · intro j hj; rw [V.get0_set_ne xs i _ j (by omega)]; exact hhigh j hj
        · rw [V.get0_set_same xs i _ hil]; exact hcut
      rw [hfund]
      have hh := CutSpine.coordinate_lt i _ .Z hp
      rwa [V.get0_set_same xs i _ hil] at hh

theorem mul_nat_subterms (xs : V multi.T)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z) (lam : Nat) (n : Nat) :
    ∀ a, Subterm a (multi.T.mul (.P xs .Z) (ofNatD lam n)) →
      a < multi.T.mul (.P xs .Z) (ofNatD lam n) := by
  cases n with
  | zero =>
    intro a ha
    have hh := ha.size_lt
    have : (multi.T.mul (.P xs .Z) (ofNatD lam 0)).size = 0 := rfl
    omega
  | succ n =>
    rw [mul_principal_ofNat_succ]
    apply (childrenBelow_iff _ _).mp
    have hp : multi.T.P xs .Z ≤ .P xs (multi.T.mul (.P xs .Z) (ofNatD lam n)) :=
      T.hd_le_self (.P xs (multi.T.mul (.P xs .Z) (ofNatD lam n)))
    have hc := (childrenBelow_iff _ _).mpr hs
    have hx : ∀ i, TreeBelow (.P xs (multi.T.mul (.P xs .Z) (ofNatD lam n))) (V.get0 xs i) :=
      fun i => TreeBelow.mono_le (hc.1 i) hp
    have hz : TreeBelow (.P xs (multi.T.mul (.P xs .Z) (ofNatD lam n))) .Z :=
      TreeBelow_Z.2 (T.Z_lt_P _ _)
    refine ⟨hx, treeBelow_mul_of_root_lt xs _ hx hz _ ?_⟩
    exact descending_tail_lt xs _
      (SourceDescending.mul_principal_descending xs (ofNatD lam (n + 1)))

theorem zero_vector_recursive_dom_one {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) :
    ∀ b : multi.T, Recursive (.P w b) → domF (.P w b) = .one
  | .Z, _ => domF_none (fnz_eq_none hw)
  | .P ys c, hr => by
    have hr' := Recursive_P.1 hr
    have hh := hr'.2.2.2
    change multi.T.P ys .Z ≤ .P w .Z at hh
    have hy : ∀ i, V.get0 ys i = .Z := by
      rcases hh with hh | hh
      · exact absurd ((lt_one_iff hw).1 hh) (by intro he; cases he)
      · intro i
        have he := (V.eqv_iff_get0 ys w).1 ((T.P_eqv_iff _ _ _ _).1 hh).1 i
        rw [hw i] at he
        exact T.eqv_Z_iff.1 he
    rw [domF_tail w (by intro he; cases he)]
    exact zero_vector_recursive_dom_one hy c hr'.2.1

theorem omega_head_mass_pos (xs : V multi.T) (b : multi.T)
    (hr : Recursive (.P xs b)) (hd : domF (.P xs b) = .omega) : 0 < vectorMass xs := by
  apply Nat.pos_of_ne_zero
  intro hm
  have hx : ∀ i, V.get0 xs i = .Z := by
    intro i
    by_cases hz : V.get0 xs i = .Z
    · exact hz
    · have hh := vectorMass_get0_le xs i
      have hp := mass_positive hz
      omega
  rw [zero_vector_recursive_dom_one hx b hr] at hd
  cases hd

theorem zeros_lt_of_nonzero {w xs : V multi.T} (hw : ∀ i, V.get0 w i = .Z)
    (hx : ∃ i, V.get0 xs i ≠ .Z) : w < xs := by
  obtain ⟨i, hi⟩ := hx
  rcases V.lt_trichotomy w xs with h | h | h
  · exact h
  · have he := (V.eqv_iff_get0 w xs).1 ((compareV_eq_iff w xs).2 h) i
    rw [hw i] at he
    exact absurd (T.eqv_Z_iff.1 (T.eqv_symm he)) hi
  · exact absurd h (not_lt_zeros xs hw)

theorem numeral_lt_nonzero_head (lam : Nat) (xs : V multi.T) (b : multi.T)
    (hx : 0 < vectorMass xs) (n : Nat) : ofNatD lam n < .P xs b := by
  have hnz : ∃ i, V.get0 xs i ≠ .Z := by
    apply Classical.byContradiction
    intro h
    have hz : ∀ i, V.get0 xs i = .Z := fun i => Classical.byContradiction (fun hi => h ⟨i, hi⟩)
    rw [vectorMass_eq_zero xs hz] at hx
    exact Nat.lt_irrefl 0 hx
  cases n with
  | zero => exact T.Z_lt_P _ _
  | succ n =>
    exact T.P_lt_P_of_vlt _ _ (zeros_lt_of_nonzero (get0_zeros lam) hnz)

theorem zero_principal_subterms {w : V multi.T} (hw : ∀ i, V.get0 w i = .Z) :
    ∀ a, Subterm a (.P w .Z) → a < .P w .Z := by
  apply (childrenBelow_iff _ _).mp
  exact ⟨fun i => by rw [hw i]; exact TreeBelow_Z.2 (T.Z_lt_P _ _), TreeBelow_Z.2 (T.Z_lt_P _ _)⟩

theorem zero_successor_fund_subterms (xs : V multi.T)
    (hf : V.fnz xs = some 0) (hd : domF (V.get0 xs 0) = .one)
    (hs : ∀ a, Subterm a (.P xs .Z) → a < .P xs .Z) (lam n : Nat) :
    ∀ a, Subterm a (T.fund (.P xs .Z) (ofNatD lam n)) →
      a < T.fund (.P xs .Z) (ofNatD lam n) := by
  have hl0 := fnz_lt_length hf
  let p := T.fund (V.get0 xs 0) .Z
  let ys := V.set xs 0 p
  have hfund (t : multi.T) : T.fund (.P xs .Z) t = multi.T.mul (.P ys .Z) t :=
    fund_one_zero hf hd t
  have hfone : T.fund (.P xs .Z) (ofNatD lam 1) = .P ys .Z := by
    rw [hfund]; rfl
  have hchild : T.fund (V.get0 xs 0) (ofNatD lam 1) = p := fund_dom_one _ hd _
  have hplain : T.fund (.P xs .Z) (ofNatD lam 1) =
      .P (V.set xs 0 (T.fund (V.get0 xs 0) (ofNatD lam 1))) .Z := by
    rw [hfone, hchild]
  have hq : ∀ a, Subterm a (.P ys .Z) → a < .P ys .Z := by
    by_cases hone : ∀ i, V.get0 ys i = .Z
    · exact zero_principal_subterms hone
    · have hnz : ∃ i, V.get0 ys i ≠ .Z :=
        Classical.byContradiction (fun h => hone (fun i => Classical.byContradiction (fun hi => h ⟨i, hi⟩)))
      have hinc : ofNatD lam 1 < T.fund (.P xs .Z) (ofNatD lam 1) := by
        rw [hfone]
        exact T.P_lt_P_of_vlt _ _ (zeros_lt_of_nonzero (get0_zeros lam) hnz)
      have ha0 : V.get0 xs 0 ≠ .Z := (V.fnz_some_spec xs 0 hf).1
      have hh := coordinate_fund_subterms xs 0 (ofNatD lam 1) ha0 hplain hs
        (ofNat_subterms lam 1) hinc
      rwa [hfone] at hh
  rw [hfund]
  exact mul_nat_subterms ys hq lam n

theorem fund_omega_subterms (s : multi.T) (hr : Recursive s)
    (hd : domF s = .omega) (hs : ∀ a, Subterm a s → a < s) (lam n : Nat) :
    ∀ a, Subterm a (T.fund s (ofNatD lam n)) → a < T.fund s (ofNatD lam n) := by
  cases s with
  | Z => rw [domF_Z] at hd; cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rcases omega_selector_of_subterms xs hr hs hd with ⟨hf, hc⟩ | ⟨i, hf, hchild⟩
      · exact zero_successor_fund_subterms xs hf hc hs lam n
      · have ha0 : V.get0 xs i ≠ .Z := (V.fnz_some_spec xs i hf).1
        have hfund := fund_omega hf hchild (ofNatD lam n)
        have hroot := coordinate_update_root_lt xs i (ofNatD lam n) ha0 hfund hs
        have hinc : ofNatD lam n < T.fund (.P xs .Z) (ofNatD lam n) :=
          T.lt_of_le_of_lt (ofNat_le_countable_fund _ hchild lam n) hroot
        exact coordinate_fund_subterms xs i (ofNatD lam n) ha0 hfund hs (ofNat_subterms _ n) hinc
    · have hx := omega_head_mass_pos xs b hr hd
      apply fund_tail_subterms xs b (ofNatD lam n) hb hx hs (ofNat_subterms _ n)
      rw [fund_tail xs hb]
      exact numeral_lt_nonzero_head lam xs _ hx n

end kumakuma.SourceCountableInvariant

namespace kumakuma.GeneralImageHeadCuts

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients

universe u

theorem inacc_zero_le (n : Nat) (a : Term) : Term.le (.inacc n .zero) (.inacc n a) = true := by
  cases a <;> simp [Term.le, Term.lt]

theorem hOne_positive_cut (cut : Nat) (hc : 0 < cut) : Term.hOne (.inacc cut .zero) = [] := by
  simp [Term.hOne, Term.predR, Term.le, Term.lt, Term.bigOmega,
    kumakuma.CountableTarget.lt_zero, show 0 < cut from hc]

theorem no_coeff_eq_nil {α : Type} (xs : List α) (h : ∀ z, z ∈ xs → False) : xs = [] := by
  cases xs with
  | nil => rfl
  | cons x ys => exact False.elim (h x List.mem_cons_self)

theorem lower_clear_above_cut (j cut : Nat) (hcut : 0 < cut) (hj : cut ≤ j) (xs : List Term)
    (hz : ∀ i, cut ≤ i → i < j → xs[i]?.getD .zero = .zero) : lower j xs .zero = lower cut xs .zero := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : cut = j + 1
    · rw [he]
    · rw [lower_succ, hz j (by omega) (by omega)]
      have hj0 : j ≠ 0 := by omega
      simp only [step, ↓reduceIte, hj0]
      exact ih (by omega) (fun i hi hij => hz i hi (by omega))

end kumakuma.GeneralImageHeadCuts

namespace kumakuma.GeneralImageRelativePredecessor

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open OCF.Jaeger.Term

universe u

theorem H_eq_nil_of_le_pred [LargeCardinals.{u}] (v t : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (ht : Term.wf t = true)
    (hle : Term.le t (Term.predR v) = true) : Term.H v t = [] := by
  have sv := sem_of_wf.{u} hv
  have sp := sv.isR_pred hvR
  have hval : V.{u} t ≤ regPred (V v) := by
    rw [← sp.2.1]
    exact (le_iff_V ht sp.1).mp hle
  apply kumakuma.GeneralImageHeadCuts.no_coeff_eq_nil
  intro z hz
  have hH : HMem (V.{u} v) (V t) (V z) :=
    (H_iff hvR hv ht _).mpr ⟨z, hz, rfl⟩
  have hC : C (V.{u} v) 0 (V t) := C_of_le_regPred hval
  have hbad := (lemma_5_6 ⟨sv.isR_iff.mp hvR, sv.lt_Λ₀⟩ (sem_of_wf ht).T 0).mp hC _ hH
  exact OCF.Ordinal.not_lt_zero _ hbad

theorem H_psi_successor_support [LargeCardinals.{u}] (v w b : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (hb : Term.wf b = true)
    (hw : Term.wf (.psi w (succTerm b)) = true) {z : Term}
    (hz : z ∈ Term.H v (.psi w b)) :
    z ∈ Term.H v (.psi w (succTerm b)) ∨
      z = b ∧ succTerm b ∈ Term.H v (.psi w (succTerm b)) := by
  have hn := psi_wf_of_succ w b hb hw
  have hp := (sem_of_wf.{u} hv).isR_pred hvR
  have hlt : Term.lt (.psi w b) (.psi w (succTerm b)) = true := by
    have hbs : Term.lt b (succTerm b) = true := by
      rw [lt_succTerm_eq_le hb hb]; simp [Term.le]
    rw [Term.lt]
    simp only [lt_self, decide_true, Bool.false_and, Bool.true_and, Bool.false_or, Bool.or_false, hbs]
  by_cases hskip : Term.le (.psi w (succTerm b)) (Term.predR v) = true
  · have hnew : Term.le (.psi w b) (Term.predR v) = true :=
      target_le_trans hn hw hp.1 (by simp [Term.le, hlt]) hskip
    rw [Term.H, hnew] at hz
    cases hz
  · have hskipF : Term.le (.psi w (succTerm b)) (Term.predR v) = false := by
      cases he : Term.le (.psi w (succTerm b)) (Term.predR v) <;> simp_all
    rw [Term.H, hskipF]
    rw [Term.H] at hz
    split at hz
    · cases hz
    · by_cases hwu : Term.lt w v = true
      · simp only [hwu, ↓reduceIte] at hz ⊢
        exact Or.inl hz
      · have hwuF : Term.lt w v = false := by cases he : Term.lt w v <;> simp_all
        simp only [hwuF, Bool.false_eq_true, ↓reduceIte] at hz ⊢
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inr ⟨rfl, List.mem_cons_self⟩
        · apply Or.inl
          apply List.mem_cons_of_mem
          rcases List.mem_append.mp hz with hz | hz
          · apply List.mem_append_left
            rw [kumakuma.OT2.H_succTerm]
            exact List.mem_append_left _ hz
          · exact List.mem_append_right _ hz

theorem H_step_context_of_wf [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (n : Nat) (a c : Term)
    (ha : Above n a) (hw : Term.wf (step n a c) = true) {z : Term}
    (hz : z ∈ Term.H v a) : z ∈ Term.H v (step n a c) := by
  by_cases ha0 : a = .zero
  · rw [ha0, Term.H] at hz; cases hz
  · by_cases hc0 : c = .zero
    · simpa only [step, ha0, hc0, ↓reduceIte] using hz
    · have hwa := step_context_wf ha hw
      have hfa := ha.resolve_left ha0
      have hpa := above_principal hfa
      simp only [step, ha0, hc0, ↓reduceIte] at hw ⊢
      by_cases hskip : Term.le (.psi (regular n a) (dropOne c)) (Term.predR v) = true
      · have hlt : Term.lt a (.psi (regular n a) (dropOne c)) = true := by
          rw [context_lt_psi_regular _ hwa hpa hwa hfa hw]
          simp [Term.le]
        have hp := (sem_of_wf.{u} hv).isR_pred hvR
        have hle := target_le_trans hwa hw hp.1 (by simp [Term.le, hlt]) hskip
        rw [H_eq_nil_of_le_pred v a hvR hv hwa hle] at hz
        cases hz
      · have hskipF : Term.le (.psi (regular n a) (dropOne c)) (Term.predR v) = false := by
          cases he : Term.le (.psi (regular n a) (dropOne c)) (Term.predR v) <;> simp_all
        rw [Term.H, hskipF]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hzv : z ∈ Term.H v (regular n a) := by
          rw [regular, Term.H]
          apply List.mem_append_right
          rw [kumakuma.OT2.H_succTerm]
          exact List.mem_append_left _ hz
        split
        · exact hzv
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hzv)

theorem zero_step_relative_support [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (a b : Term)
    (ha : Above 0 a) (hb : Term.wf b = true)
    (hw : Term.wf (step 0 a (succTerm b)) = true) {z : Term}
    (hz : z ∈ Term.H v (step 0 a b)) :
    z ∈ Term.H v (step 0 a (succTerm b)) ∨
      (z = b ∨ z = dropOne b) ∧
        (succTerm b ∈ Term.H v (step 0 a (succTerm b)) ∨
          dropOne (succTerm b) ∈ Term.H v (step 0 a (succTerm b))) := by
  by_cases ha0 : a = .zero
  · subst a
    simp only [step, ↓reduceIte] at hz hw ⊢
    rcases H_psi_successor_support v Term.bigOmega b hvR hv hb hw hz with h | ⟨h, hs⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl h, Or.inl hs⟩
  · by_cases hb0 : b = .zero
    · have hz' : z ∈ Term.H v a := by simpa only [step, ha0, hb0, ↓reduceIte] using hz
      exact Or.inl (H_step_context_of_wf v hvR hv 0 a (succTerm b) ha hw hz')
    · have hd := drop_succ b hb0
      simp only [step, ha0, hb0, succTerm_ne_zero, ↓reduceIte, hd] at hz hw ⊢
      rcases H_psi_successor_support v (regular 0 a) (dropOne b) hvR hv (dropOne_wf hb) hw hz
        with h | ⟨h, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨Or.inr h, Or.inr hs⟩

theorem lower_zero_relative_support [LargeCardinals.{u}] (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true) (j : Nat) (hj : 0 < j)
    (xs ys : List Term) (a b : Term) (ha : Context j a) (hb : Term.wf b = true)
    (hx : xs[0]?.getD .zero = succTerm b) (hy : ys[0]?.getD .zero = b)
    (he : ∀ i, 0 < i → i < j → xs[i]?.getD .zero = ys[i]?.getD .zero)
    (hw : Term.wf (lower j xs a) = true) {z : Term} (hz : z ∈ Term.H v (lower j ys a)) :
    z ∈ Term.H v (lower j xs a) ∨
      (z = b ∨ z = dropOne b) ∧
        (succTerm b ∈ Term.H v (lower j xs a) ∨ dropOne (succTerm b) ∈ Term.H v (lower j xs a)) := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero =>
      simp only [lower, hx, hy] at hw hz ⊢
      exact zero_step_relative_support v hvR hv a b (context_above ha) hb hw hz
    | succ j =>
      rw [lower_succ] at hw hz ⊢
      rw [← he (j + 1) (by omega) (by omega)] at hz
      exact ih (by omega) _ (step_shape _ (context_above ha))
        (fun i hi hij => he i hi (by omega)) hw hz


open multi in
theorem Dim_of_oplus {d : Nat} : ∀ {s t : multi.T}, Dim d (s + t) → Dim d s
  | .Z, _, _ => Dim_Z d
  | .P v a, t, h => by
    have h' : Dim d (multi.T.P v (a + t)) := h
    exact Dim_P h'.length h'.coord (Dim_of_oplus h'.tail)

open multi in
theorem zero_coordinate_relative_support [LargeCardinals.{u}] (k : Nat) (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (xs : V multi.T) (b : multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hx : V.get0 xs 0 = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (.P (V.set xs 0 b) .Z)))) :
    z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
      (z = convert (k + 3) (code b) ∨ z = dropOne (convert (k + 3) (code b))) ∧
        (convert (k + 3) (code (kumakuma.SourceSuccessor.succ (k + 3) b)) ∈
            Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
          dropOne (convert (k + 3) (code (kumakuma.SourceSuccessor.succ (k + 3) b))) ∈
            Term.H v (convert (k + 3) (code (.P xs .Z)))) := by
  have hl0 : 0 < xs.length := by rw [hsD.length]; omega
  let us := arguments (k + 3) (trim (codes xs))
  let vs := arguments (k + 3) (trim (codes (V.set xs 0 b)))
  have hb : RecursiveWF (k + 3) b := by
    have := (RecursiveWF_P.1 hs).1 0
    rw [hx] at this
    exact (recursive_succ_iff _ _ _).mp this
  have he : ∀ i, 0 < i → i < k + 3 → us[i]?.getD .zero = vs[i]?.getD .zero := by
    intro i hi _
    show (arguments (k + 3) (trim (codes xs)))[i]?.getD .zero =
      (arguments (k + 3) (trim (codes (V.set xs 0 b))))[i]?.getD .zero
    rw [converted_coordinate xs i, converted_coordinate (V.set xs 0 b) i,
      V.get0_set_ne xs 0 b i (by omega)]
  have htop : topPair (k + 1) (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero) =
      topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero) := by
    rw [he (k + 2) (by omega) (by omega), he (k + 1) (by omega) (by omega)]
  have hctx := kumakuma.GeneralImageRegularLimit.topPair_context (k + 1)
    (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero)
  have h0 : us[0]?.getD .zero = succTerm (convert (k + 3) (code b)) := by
    show (arguments (k + 3) (trim (codes xs)))[0]?.getD .zero = _
    rw [converted_coordinate xs 0, hx, convert_succ]
  have h0' : vs[0]?.getD .zero = convert (k + 3) (code b) := by
    show (arguments (k + 3) (trim (codes (V.set xs 0 b))))[0]?.getD .zero = _
    rw [converted_coordinate (V.set xs 0 b) 0, V.get0_set_same xs 0 b hl0]
  have hw := hs.wf
  rw [convert_principal, principal_as_layers] at hw
  rw [convert_principal, principal_as_layers] at hz
  change z ∈ Term.H v (lower (k + 1) vs
    (topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero))) at hz
  rw [← htop] at hz
  have h := lower_zero_relative_support v hvR hv (k + 1) (by omega) us vs _ _ hctx hb.wf h0 h0'
    (fun i hi hik => he i hi (by omega)) hw hz
  rw [convert_succ, convert_principal, principal_as_layers]
  exact h

open multi in
theorem zero_coordinate_relative_closed [LargeCardinals.{u}] (k : Nat) (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (xs : V multi.T) (b : multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hx : V.get0 xs 0 = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (.P (V.set xs 0 b) .Z))))
      (convert (k + 3) (code (.P (V.set xs 0 b) .Z))) = true := by
  have hl0 : 0 < xs.length := by rw [hsD.length]; omega
  obtain ⟨hn, _⟩ := zero_coordinate_predecessor k xs b hsD hx hs
  have hbD : Dim (k + 3) b := by
    have h0 := hsD.coord 0
    rw [hx] at h0
    exact Dim_of_oplus h0
  have hnD : Dim (k + 3) (.P (V.set xs 0 b) .Z) := Dim_set hsD 0 hbD _ (Dim_Z _)
  have hb : RecursiveWF (k + 3) b := by
    have := (RecursiveWF_P.1 hs).1 0
    rw [hx] at this
    exact (recursive_succ_iff _ _ _).mp this
  have hbs := (recursive_succ_iff (k + 3) (k + 3) b).mpr hb
  have hnon : V.get0 xs 0 ≠ .Z := by
    rw [hx]; exact kumakuma.SourceSuccessor.succ_ne_zero _ b
  have hp : Term.isPrin (convert (k + 3) (code (.P xs .Z))) = true := by
    rw [convert_principal]; exact kumakuma.GeneralImageEmbedding.principal_isPrin _ _
  have hone := principal_image_ne_one k xs 0 hsD hs hnon
  have hfund : T.fund (.P xs .Z) (ofNatD (k + 3) 1) = .P (V.set xs 0 b) .Z := by
    rw [fund_zero_coordinate_successor k xs b _ hx]; rfl
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  have hzold : Term.lt z (convert (k + 3) (code (.P xs .Z))) = true := by
    rcases zero_coordinate_relative_support k v hvR hv xs b hsD hx hs hz with h | ⟨he, hmem⟩
    · exact (Term.allLt_iff _ _).mp hH z h
    · have hslt : Term.lt (convert (k + 3) (code (kumakuma.SourceSuccessor.succ (k + 3) b)))
          (convert (k + 3) (code (.P xs .Z))) = true := by
        rcases hmem with h | h
        · exact (Term.allLt_iff _ _).mp hH _ h
        · exact undrop_lt_principal _ _ hbs.wf hs.wf hp hone ((Term.allLt_iff _ _).mp hH _ h)
      have hbl : Term.lt (convert (k + 3) (code b))
          (convert (k + 3) (code (.P xs .Z))) = true := by
        apply lemma_6_1.{u}.2.1 _ _ _ hb.wf hbs.wf hs.wf _ hslt
        rw [convert_succ, lt_succTerm_eq_le hb.wf hb.wf]; simp [Term.le]
      rcases he with rfl | rfl
      · exact hbl
      · exact dropOne_lt_of_lt hb.wf hs.wf hbl
  rcases H_convert_source k v (.P (V.set xs 0 b) .Z) hz with rfl | ⟨a, ha, he⟩
  · apply (zero_lt_iff _).mpr
    rw [convert_principal]; exact kumakuma.GeneralImageEmbedding.principal_ne_zero _ _
  · have har := ha.recursiveWF hn
    have haD := ha.dim hnD
    have hal : a < .P xs .Z := by
      apply (convert_order k _ _ haD hsD har hs).mpr
      rcases he with rfl | rfl
      · exact hzold
      · exact undrop_lt_principal _ _ har.wf hs.wf hp hone hzold
    have ham := kumakuma.SourceCoefficientGap.mass_lt_of_subterm ha
    have hmass : kumakuma.SourceFundGap.mass (.P (V.set xs 0 b) .Z) + 1 =
        kumakuma.SourceFundGap.mass (.P xs .Z) := by
      have hbalance := kumakuma.SourceFundGap.vectorMass_set xs 0 hl0 b
      rw [hx, kumakuma.SourceFundGap.mass_succ] at hbalance
      rw [kumakuma.SourceFundGap.mass_P, kumakuma.SourceFundGap.mass_P,
        kumakuma.SourceFundGap.mass_Z]
      omega
    have hgap : kumakuma.SourceFundGap.mass a <
        kumakuma.SourceFundGap.gap (.P xs .Z) (ofNatD (k + 3) 1) := by
      rw [kumakuma.SourceFundGap.gap_nonzero _ _ (ofNatD_succ_ne _ _)]; omega
    have ha' := kumakuma.SourceFundGap.small_lt_fund_all (.P xs .Z) (ofNatD (k + 3) 1) a hal hgap
    rw [hfund] at ha'
    have hlt := (convert_order k _ _ haD hnD har hn).mp ha'
    rcases he with rfl | rfl
    · exact hlt
    · exact dropOne_lt_of_lt har.wf hn.wf hlt

open multi in
theorem H_drop_bound (v t : Term) (ht : Term.wf t = true)
    (hH : Term.allLt (Term.H v t) t = true) :
    Term.allLt (Term.H v (dropOne t)) (dropOne t) = true := by
  by_cases hh : Term.head t = Term.one
  · obtain ⟨n, rfl⟩ := head_one_nat ht hh
    rw [dropOne_nat]; exact H_nat_bound v n
  · simpa only [dropOne_of_head_ne hh] using hH

open multi in
theorem H_mul_principal_bound [LargeCardinals.{u}] (k : Nat) (v : Term)
    (xs : V multi.T) (hsD : Dim (k + 3) (.P xs .Z)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) (n : Nat) :
    Term.allLt (Term.H v (convert (k + 3) (code (multi.T.mul (.P xs .Z) (ofNatD (k + 3) n)))))
      (convert (k + 3) (code (multi.T.mul (.P xs .Z) (ofNatD (k + 3) n)))) = true := by
  cases n with
  | zero =>
    show Term.allLt (Term.H v (convert (k + 3) (code .Z))) (convert (k + 3) (code .Z)) = true
    simp [convert_Z, Term.H, Term.allLt]
  | succ n =>
    have hm := mul_principal_recursiveWF xs hs (ofNatD (k + 3) (n + 1))
    have hmD := Dim_mul hsD (Dim_ofNatD (k + 3) (n + 1))
    have hle : multi.T.P xs .Z ≤ multi.T.mul (.P xs .Z) (ofNatD (k + 3) (n + 1)) :=
      T.hd_le_self (.P xs (multi.T.mul (.P xs .Z) (ofNatD (k + 3) n)))
    have hle' := image_le_of_le k _ _ hsD hmD hs hm hle
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    have ho := H_mul_principal_support (k + 3) xs (k + 3) v (n + 1) hz
    have hl := (Term.allLt_iff _ _).mp hH z ho
    rcases (Term.le_iff_eq_or_lt _ _).mp hle' with he | he
    · simpa only [← he] using hl
    · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf v _ hs.wf ho) hs.wf hm.wf hl he

open multi in
theorem fund_zero_successor_relative [LargeCardinals.{u}] (k : Nat)
    (xs : V multi.T) (b : multi.T) (hsD : Dim (k + 3) (.P xs .Z))
    (hx : V.get0 xs 0 = kumakuma.SourceSuccessor.succ (k + 3) b)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) :
    RecursiveWF (k + 3) (T.fund (.P xs .Z) (ofNatD (k + 3) n)) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))))
          (convert (k + 3) (code (T.fund (.P xs .Z) (ofNatD (k + 3) n)))) = true := by
  obtain ⟨hn, _⟩ := zero_coordinate_predecessor k xs b hsD hx hs
  have hbD : Dim (k + 3) b := by
    have h0 := hsD.coord 0
    rw [hx] at h0
    exact Dim_of_oplus h0
  have hnD : Dim (k + 3) (.P (V.set xs 0 b) .Z) := Dim_set hsD 0 hbD _ (Dim_Z _)
  rw [fund_zero_coordinate_successor k xs b _ hx]
  refine ⟨mul_principal_recursiveWF _ hn _, ?_⟩
  intro v hvR hv hH
  exact H_mul_principal_bound k v _ hnD hn
    (zero_coordinate_relative_closed k v hvR hv xs b hsD hx hs hH) n

end kumakuma.GeneralImageRelativePredecessor

namespace kumakuma.GeneralImageCountableLayers

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.GeneralImageRelativePredecessor

universe u

theorem step_replace_relative_wf (n : Nat) (a c t : Term) (ha : Above n a)
    (hc : Term.wf c = true) (ht : Term.wf t = true) (hdrop : dropOne c = c)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v c) c = true → Term.allLt (Term.H v t) t = true)
    (hw : Term.wf (step n a c) = true) : Term.wf (step n a t) = true := by
  by_cases ht0 : t = .zero
  · rw [ht0]; exact step_zero_wf n a (step_context_wf ha hw)
  · by_cases hc0 : c = .zero
    · subst c
      have h := hrel Term.bigOmega (by decide +kernel) Term.wf_bigOmega (by rfl)
      exact step_wf_of_omega_closed n a t ha (step_context_wf ha hw) ht h
    · by_cases ha0 : a = .zero
      · subst a
        by_cases hn : n = 0
        · subst n
          simp only [step, ↓reduceIte] at hw ⊢
          have hp := (Term.wf_psi_iff _ _).mp hw
          exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, ht, hrel _ hp.1 hp.2.1 hp.2.2.2⟩
        · simp only [step, ↓reduceIte, hn, hc0, ht0, hdrop] at hw ⊢
          have hp := (Term.wf_psi_iff _ _).mp hw
          exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ht,
            H_drop_bound _ t ht (hrel _ hp.1 hp.2.1 hp.2.2.2)⟩
      · simp only [step, ha0, hc0, ht0, hdrop, ↓reduceIte] at hw ⊢
        have hp := (Term.wf_psi_iff _ _).mp hw
        exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ht,
          H_drop_bound _ t ht (hrel _ hp.1 hp.2.1 hp.2.2.2)⟩

theorem topPair_replace_relative_wf (n : Nat) (a c t : Term)
    (hi : Term.wf (.inacc n (dropOne a)) = true) (ht : Term.wf t = true)
    (hc0 : c ≠ .zero) (hdrop : dropOne c = c)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v c) c = true → Term.allLt (Term.H v t) t = true)
    (hw : Term.wf (topPair n a c) = true) : Term.wf (topPair n a t) = true := by
  by_cases ht0 : t = .zero
  · by_cases ha0 : a = .zero
    · simp only [topPair, ht0, ha0, ↓reduceIte, Term.wf]
    · simpa only [topPair, ht0, ha0, ↓reduceIte] using hi
  · simp only [topPair, ht0, hc0, hdrop, ↓reduceIte] at hw ⊢
    have hp := (Term.wf_psi_iff _ _).mp hw
    exact (Term.wf_psi_iff _ _).mpr ⟨hp.1, hp.2.1, dropOne_wf ht,
      H_drop_bound _ t ht (hrel _ hp.1 hp.2.1 hp.2.2.2)⟩

theorem lower_replace_relative_wf (j cut : Nat) (hj : cut < j)
    (xs ys : List Term) (a c t : Term) (hctx : Context j a)
    (hc : Term.wf c = true) (ht : Term.wf t = true) (hdrop : dropOne c = c)
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v c) c = true → Term.allLt (Term.H v t) t = true)
    (hx : xs[cut]?.getD .zero = c) (hy : ys[cut]?.getD .zero = t)
    (hzero : ∀ i, i < cut → ys[i]?.getD .zero = .zero)
    (hsame : ∀ i, cut < i → i < j → ys[i]?.getD .zero = xs[i]?.getD .zero)
    (hw : Term.wf (lower j xs a) = true) : Term.wf (lower j ys a) = true := by
  induction j generalizing a with
  | zero => omega
  | succ j ih =>
    by_cases hlt : cut < j
    · rw [lower_succ] at hw ⊢
      rw [hsame j hlt (by omega)]
      exact ih hlt _ (step_shape _ (context_above hctx))
        (fun i hi hij => hsame i hi (by omega)) hw
    · have he : j = cut := by omega
      subst j
      rw [lower_succ, hx] at hw
      have hshape : Context cut (step cut a c) := step_shape c (context_above hctx)
      have hstep := lower_context_wf cut xs _ hshape hw
      rw [lower_succ, hy]
      exact lower_zero_wf cut ys _ hzero
        (step_replace_relative_wf cut a c t (context_above hctx) hc ht hdrop hrel hstep)


open multi in
theorem principal_replace_relative_recursiveWF (k : Nat)
    (xs : V multi.T) (i : Nat) (hib : i ≤ k + 1) (hsD : Dim (k + 3) (.P xs .Z))
    (hlow : ∀ j, j < i → V.get0 xs j = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (a : multi.T)
    (ha : RecursiveWF (k + 3) a) (hc0 : V.get0 xs i ≠ .Z)
    (hdrop : dropOne (convert (k + 3) (code (V.get0 xs i))) = convert (k + 3) (code (V.get0 xs i)))
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v (convert (k + 3) (code (V.get0 xs i)))) (convert (k + 3) (code (V.get0 xs i))) = true →
      Term.allLt (Term.H v (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    RecursiveWF (k + 3) (.P (V.set xs i a) .Z) := by
  have hil : i < xs.length := by rw [hsD.length]; omega
  let ys := V.set xs i a
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have hold (j : Nat) : oldArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 xs j)) :=
    converted_coordinate xs j
  have hnew (j : Nat) : newArgs[j]?.getD .zero = convert (k + 3) (code (V.get0 ys j)) :=
    converted_coordinate ys j
  have hnewa : newArgs[i]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew i]; show convert (k + 3) (code (V.get0 (V.set xs i a) i)) = _
    rw [V.get0_set_same xs i a hil]
  have hzero : ∀ j, j < i → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew j]
    show convert (k + 3) (code (V.get0 (V.set xs i a) j)) = _
    rw [V.get0_set_ne xs i a j (by omega), hlow j hj, convert_Z]
  have hsame : ∀ j, i < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj _
    rw [hnew j, hold j]
    show convert (k + 3) (code (V.get0 (V.set xs i a) j)) = _
    rw [V.get0_set_ne xs i a j (by omega)]
  have hcoords : ∀ j, RecursiveWF (k + 3) (V.get0 xs j) := (RecursiveWF_P.1 hs).1
  have hc := (hcoords i).wf
  refine RecursiveWF_P.2 ⟨?_, recursive_zero _, ?_⟩
  · intro j
    show RecursiveWF (k + 3) (V.get0 (V.set xs i a) j)
    rw [V.get0_set xs i a j hil]
    split
    · exact ha
    · exact hcoords j
  · rw [convert_principal, principal_as_layers]
    change Term.wf (lower (k + 1) newArgs
      (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) = true
    rw [hsame (k + 2) (by omega) (by omega)]
    have hw := hs.wf
    rw [convert_principal, principal_as_layers] at hw
    by_cases he : i = k + 1
    · subst he
      rw [hnewa]
      apply lower_zero_wf (k + 1) newArgs _ hzero
      have htop := lower_context_wf (k + 1) oldArgs _ (topPair_context _ _ _) hw
      rw [hold (k + 1)] at htop
      apply topPair_replace_relative_wf (k + 1) _ _ _ _ ha.wf _ hdrop hrel htop
      · rw [hold (k + 2)]; exact inacc_image_drop_wf k _ (hcoords _)
      · intro hz
        exact hc0 ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 hz)
    · rw [hsame (k + 1) (by omega) (by omega)]
      exact lower_replace_relative_wf (k + 1) i (by omega) oldArgs newArgs _ _ _
        (topPair_context _ _ _) hc ha.wf hdrop hrel (hold i) hnewa hzero
        (fun j hj hjk => hsame j hj (by omega)) hw

end kumakuma.GeneralImageCountableLayers

namespace kumakuma.GeneralImageCountableRecursion

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageCountableLayers kumakuma.GeneralImageRelativePredecessor
open kumakuma.GeneralImageOmegaCoefficients
open kumakuma.GeneralImageCoefficients kumakuma.SourceRecursiveDescending kumakuma.SourceFundOrder
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic

universe u

theorem psi_argument_lt_iff [LargeCardinals.{u}] (v a : Term)
    (hw : Term.wf (.psi v a) = true) :
    Term.lt a (.psi v a) = true ↔ Term.lt a v = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  have hs := (sem_of_wf.{u} hw).psi_ok v a rfl
  rw [lt_iff_V hp.2.2.1 hw, lt_iff_V hp.2.2.1 hp.2.1]
  constructor
  · intro h
    exact OCF.Ordinal.lt_trans _ _ _ h (Ψ_lt hs.1 _)
  · intro h
    exact (theorem_4_9 hs.1 _ _).mp ⟨hs.2, h⟩


open multi in
theorem H_low_empty_above_Omega (v : Term) (hOmega : Term.lt Term.bigOmega v = true)
    (d m : Nat) (a : multi.T) :
    Term.H v (convert d (code (.P (lowVec m a) .Z))) = [] := by
  rw [convert_low_principal, Term.H]
  split
  · rfl
  · simp only [Term.bigOmega, Term.H, ↓reduceIte, List.nil_append]

open multi in
theorem numeral_recursiveWF (d lam n : Nat) : RecursiveWF d (ofNatD lam n) := by
  induction n with
  | zero => exact recursive_zero d
  | succ n ih =>
    rw [← kumakuma.SourceSuccessor.nat_succ]
    exact (recursive_succ_iff d _ _).mpr ih

open multi in
theorem convert_numeral (d lam n : Nat) :
    convert d (code (ofNatD lam n)) = kumakuma.FiniteCorrespondence.natTerm n := by
  have hp : principal d [] = Term.one := by
    simpa only [kumakuma.UserImage.oneCode, convert, arguments, kumakuma.OT2.assemble,
      ↓reduceIte] using convert_one d
  rw [kumakuma.FiniteCorrespondence.code_ofNatD]
  induction n with
  | zero => rw [kumakuma.FiniteCorrespondence.natCode, convert]; rfl
  | succ n ih =>
    rw [kumakuma.FiniteCorrespondence.natCode, convert, arguments, hp, ih]
    cases n with
    | zero => rfl
    | succ n =>
      simp only [kumakuma.OT2.assemble, kumakuma.FiniteCorrespondence.natTerm_ne_zero,
        ↓reduceIte, kumakuma.FiniteCorrespondence.natTerm]

open multi in
theorem drop_image_of_omega [LargeCardinals.{u}] (k : Nat) (s : multi.T)
    (hsD : Dim (k + 3) s) (hs : RecursiveWF (k + 3) s) (hd : domF s = .omega) :
    dropOne (convert (k + 3) (code s)) = convert (k + 3) (code s) := by
  apply dropOne_of_head_ne
  intro hh
  obtain ⟨n, he⟩ := head_one_nat hs.wf hh
  have hn := numeral_recursiveWF (k + 3) (k + 3) (n + 1)
  have hsNat : s = ofNatD (k + 3) (n + 1) := convert_injective k s _ hsD (Dim_ofNatD _ _) hs hn
    (he.trans (convert_numeral _ _ _).symm)
  rw [hsNat, ← kumakuma.SourceSuccessor.nat_succ, kumakuma.SourceSuccessor.dom_succ] at hd
  cases hd

end kumakuma.GeneralImageCountableRecursion

namespace kumakuma.GeneralImageOmegaContext

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.BinaryTranslation kumakuma.TargetArithmetic
open kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant
open kumakuma.GeneralImageHighOmega kumakuma.SourceOmegaHighest
open OCF.Jaeger.Term

universe u

theorem psi_above_predR [LargeCardinals.{u}] (v a : Term)
    (hw : Term.wf (.psi v a) = true) : Term.lt (Term.predR v) (.psi v a) = true := by
  have hp := (Term.wf_psi_iff _ _).mp hw
  have sv := sem_of_wf.{u} hp.2.1
  have sp := sv.isR_pred hp.1
  have hs := (sem_of_wf.{u} hw).psi_ok v a rfl
  rw [lt_iff_V sp.1 hw, sp.2.1]
  exact (theorem_4_2 hs.1 (V a)).1

theorem lower_zero_nonzero (j : Nat) (xs : List Term) (a : Term) (ha : a ≠ .zero)
    (hz : ∀ i, i < j → xs[i]?.getD .zero = .zero) : lower j xs a = a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [lower_succ, hz j (by omega)]
    simp only [step, ha, ↓reduceIte]
    exact ih (fun i hi => hz i (by omega))


open multi in
theorem convert_positive_layers (k : Nat) (xs : V multi.T)
    (i : Nat) (hi : 0 < i) (hib : i ≤ k + 1)
    (hhigh : ∀ j, i < j → V.get0 xs j = .Z) :
    convert (k + 3) (code (.P xs .Z)) =
      lower i (arguments (k + 3) (trim (codes xs)))
        (step i .zero (convert (k + 3) (code (V.get0 xs i)))) := by
  let args := arguments (k + 3) (trim (codes xs))
  have hget (j : Nat) : args[j]?.getD .zero = convert (k + 3) (code (V.get0 xs j)) :=
    converted_coordinate xs j
  have hzero (j : Nat) (hj : i < j) : args[j]?.getD .zero = .zero := by
    rw [hget j, hhigh j hj, convert_Z]
  rw [convert_principal, principal_as_layers]
  change lower (k + 1) args (topPair (k + 1) (args[k + 2]?.getD .zero)
    (args[k + 1]?.getD .zero)) = _
  rw [hzero (k + 2) (by omega)]
  by_cases he : i = k + 1
  · subst he
    rw [hget (k + 1)]
    congr 1
  · rw [hzero (k + 1) (by omega)]
    simp only [topPair, ↓reduceIte]
    rw [lower_clear_above_cut (k + 1) (i + 1) (by omega) (by omega) args
      (fun j hj hjk => hzero j (by omega)), lower_succ, hget i]

open multi in
theorem convert_positive_single (k : Nat) (xs : V multi.T)
    (i : Nat) (hi : 0 < i) (hib : i ≤ k + 1)
    (hlow : ∀ j, j < i → V.get0 xs j = .Z)
    (hhigh : ∀ j, i < j → V.get0 xs j = .Z) (hne : V.get0 xs i ≠ .Z) :
    convert (k + 3) (code (.P xs .Z)) =
      .psi (.inacc i .zero) (dropOne (convert (k + 3) (code (V.get0 xs i)))) := by
  rw [convert_positive_layers k xs i hi hib hhigh]
  have ha0 : convert (k + 3) (code (V.get0 xs i)) ≠ .zero :=
    fun h => hne ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 h)
  simp only [step, ↓reduceIte, Nat.ne_of_gt hi, ha0]
  apply lower_zero_nonzero _ _ _ (by intro h; cases h)
  intro j hj
  rw [converted_coordinate xs j, hlow j hj, convert_Z]

end kumakuma.GeneralImageOmegaContext

namespace kumakuma.GeneralImageSharedContext

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant
open OCF.Jaeger.Term

universe u

def layerCut (n : Nat) (a : Term) : Term := .inacc n (if a = .zero then .zero else succTerm a)

theorem H_one_empty_above_Omega (v : Term) (hOmega : Term.lt Term.bigOmega v = true) :
    Term.H v Term.one = [] := by
  rw [Term.one, Term.H]
  split
  · rfl
  · simp only [↓reduceIte, Term.bigOmega, Term.H, List.nil_append]

theorem regular_H_context_empty_of_wf [LargeCardinals.{u}] (n : Nat) (a : Term)
    (hwa : Term.wf a = true) (hu : Term.wf (regular n a) = true) : Term.H (regular n a) a = [] := by
  have hpred : Term.predR (regular n a) = if Term.fT a ≤ n then .inacc n a else a := by
    simp only [regular, Term.predR, succTerm_ne_zero, ↓reduceIte, predT_succTerm hwa]
  have sp := (sem_of_wf.{u} hu).isR_pred (regular_isRT n a)
  apply H_eq_nil_of_le_pred _ a (regular_isRT n a) hu hwa
  by_cases hf : Term.fT a ≤ n
  · have hi : Term.wf (.inacc n a) = true := by simpa only [hpred, hf, ↓reduceIte] using sp.1
    have hlt : Term.lt a (.inacc n a) = true := by
      rw [lt_iff_V hwa hi]
      exact (sem_of_wf.{u} hi).inacc_ok n a rfl
    simp only [hpred, hf, ↓reduceIte, Term.le, hlt, Bool.or_true]
  · simp only [hpred, hf, ↓reduceIte, Term.le, decide_true, Bool.true_or]

theorem regular_H_self_empty_of_wf [LargeCardinals.{u}] (n : Nat) (a : Term)
    (hwa : Term.wf a = true) (hu : Term.wf (regular n a) = true) : Term.H (regular n a) (regular n a) = [] := by
  have hOmega : Term.lt Term.bigOmega (regular n a) = true := by
    cases n with
    | zero => simp [Term.bigOmega, regular, Term.lt, (zero_lt_iff _).mpr (succTerm_ne_zero a)]
    | succ n => simp [Term.bigOmega, regular, Term.lt]
  have hOne : Term.hOne (regular n a) = [] := by simp [Term.hOne, hOmega]
  change (if n = 0 then [] else Term.hOne (regular n a)) ++ Term.H (regular n a) (succTerm a) = []
  rw [kumakuma.OT2.H_succTerm, regular_H_context_empty_of_wf n a hwa hu, H_one_empty_above_Omega _ hOmega]
  simp only [hOne, ite_self, List.nil_append]

theorem regular_H_self_empty [LargeCardinals.{u}] (n : Nat) (a : Term)
    (ha : Above n a) (hwa : Term.wf a = true) : Term.H (regular n a) (regular n a) = [] := by
  have hu : Term.wf (regular n a) = true := by
    by_cases ha0 : a = .zero
    · simp only [ha0, regular, succTerm]
      exact (Term.wf_inacc_iff _ _).mpr ⟨Term.wf_one, by simp [Term.fT, Term.one, Term.bigOmega]⟩
    · exact regular_wf n hwa (above_principal (ha.resolve_left ha0))
  exact regular_H_self_empty_of_wf n a hwa hu

theorem layerCut_wf (n : Nat) (a : Term) (ha : Above n a) (hwa : Term.wf a = true) :
    Term.wf (layerCut n a) = true := by
  by_cases ha0 : a = .zero
  · simp [layerCut, ha0, Term.wf, Term.fT]
  · simpa only [layerCut, ha0, ↓reduceIte, regular] using
      regular_wf n hwa (above_principal (ha.resolve_left ha0))

theorem layerCut_regular (n : Nat) (a : Term) : Term.isRT (layerCut n a) = true := by
  by_cases ha0 : a = .zero
  · simp [layerCut, ha0, Term.isRT, Term.isLimT, Term.isSucc]
  · simpa only [layerCut, ha0, ↓reduceIte, regular] using regular_isRT n a

theorem layerCut_above_Omega (n : Nat) (hn : 0 < n) (a : Term) :
    Term.lt Term.bigOmega (layerCut n a) = true := by simp [layerCut, Term.bigOmega, Term.lt, hn]

theorem layerCut_H_self_empty [LargeCardinals.{u}] (n : Nat) (hn : 0 < n) (a : Term)
    (ha : Above n a) (hwa : Term.wf a = true) : Term.H (layerCut n a) (layerCut n a) = [] := by
  by_cases ha0 : a = .zero
  · simp [layerCut, ha0, Term.H, hOne_positive_cut n hn]
  · simpa only [layerCut, ha0, ↓reduceIte, regular] using regular_H_self_empty n a ha hwa

theorem layerCut_H_context_empty [LargeCardinals.{u}] (n : Nat) (a : Term)
    (ha : Above n a) (hwa : Term.wf a = true) : Term.H (layerCut n a) a = [] := by
  by_cases ha0 : a = .zero
  · simp [ha0, Term.H]
  · have hp : Term.predR (layerCut n a) = a := by
      simp only [layerCut, ha0, ↓reduceIte, Term.predR, succTerm_ne_zero,
        predT_succTerm hwa, show ¬Term.fT a ≤ n from Nat.not_le.mpr (ha.resolve_left ha0)]
    exact H_eq_nil_of_le_pred _ a (layerCut_regular n a) (layerCut_wf n a ha hwa) hwa
      (by rw [hp]; simp [Term.le, lt_self])

theorem step_positive_nonzero (n : Nat) (hn : 0 < n) (a c : Term) (hc : c ≠ .zero) :
    step n a c ≠ .zero := by
  by_cases ha0 : a = .zero <;> simp [step, ha0, hc, Nat.ne_of_gt hn]

end kumakuma.GeneralImageSharedContext

namespace kumakuma.GeneralImageSharedTopPair

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant
open OCF.Jaeger.Term

universe u

def pairCut (n : Nat) (h : Term) : Term := .inacc n (if h = .zero then .zero else succTerm (dropOne h))

theorem pairCut_regular (n : Nat) (h : Term) : Term.isRT (pairCut n h) = true := by
  by_cases hh0 : h = .zero
  · simp [pairCut, hh0, Term.isRT, Term.isLimT, Term.isSucc]
  · simp only [pairCut, hh0, ↓reduceIte]
    exact regular_isRT n (dropOne h)

theorem pairCut_above_Omega (n : Nat) (hn : 0 < n) (h : Term) :
    Term.lt Term.bigOmega (pairCut n h) = true := by simp [pairCut, Term.bigOmega, Term.lt, hn]

theorem pairCut_H_self_empty [LargeCardinals.{u}] (n : Nat) (hn : 0 < n) (h : Term)
    (hh : Term.wf h = true) (hu : Term.wf (pairCut n h) = true) :
    Term.H (pairCut n h) (pairCut n h) = [] := by
  by_cases hh0 : h = .zero
  · simp [pairCut, hh0, Term.H, hOne_positive_cut n hn]
  · simpa only [pairCut, hh0, ↓reduceIte, regular] using
      regular_H_self_empty_of_wf n (dropOne h) (dropOne_wf hh)
        (by simpa only [pairCut, hh0, ↓reduceIte, regular] using hu)

theorem topPair_zero_bound [LargeCardinals.{u}] (n : Nat) (hn : 0 < n) (h : Term)
    (hh : Term.wf h = true) (hu : Term.wf (pairCut n h) = true) :
    Term.lt (topPair n h .zero) (pairCut n h) = true ∧
      Term.H (pairCut n h) (topPair n h .zero) = [] := by
  by_cases hh0 : h = .zero
  · simp [topPair, pairCut, hh0, Term.lt, Term.H]
  · have hwD := dropOne_wf hh
    have hreg : Term.wf (regular n (dropOne h)) = true := by
      simpa only [pairCut, hh0, ↓reduceIte, regular] using hu
    have hHD := regular_H_context_empty_of_wf n (dropOne h) hwD hreg
    have hOne : Term.hOne (pairCut n h) = [] := by simp [Term.hOne, pairCut_above_Omega n hn h]
    refine ⟨?_, ?_⟩
    · simp only [topPair, hh0, ↓reduceIte, pairCut, inacc_same_lt]
      rw [lt_succTerm_eq_le hwD hwD]
      simp [Term.le]
    · rw [topPair, ite_eq_left rfl, ite_eq_right hh0, Term.H]
      have hd : Term.H (pairCut n h) (dropOne h) = [] := by
        simpa only [pairCut, hh0, ↓reduceIte, regular] using hHD
      simp only [hOne, hd, ite_self, List.nil_append]

end kumakuma.GeneralImageSharedTopPair

namespace kumakuma.GeneralImageMiddleRecursion

open OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant

universe u


open multi in
theorem pairCut_image_pred (k : Nat) (h : multi.T) (hne : h ≠ .Z)
    (hw : RecursiveWF (k + 3) h) :
    Term.predR (pairCut (k + 1) (convert (k + 3) (code h))) =
      convert (k + 3) (code (topNode k h)) := by
  have hz : convert (k + 3) (code h) ≠ .zero :=
    fun he => hne ((kumakuma.GeneralImageOmegaCoefficients.convert_eq_zero_iff _ _).1 he)
  have hi := indices_drop (indices_convert (k + 3) (by omega) (code h))
  have hf : Term.fT (dropOne (convert (k + 3) (code h))) ≤ k + 1 := by
    have hf := kumakuma.TargetIndexCuts.IndicesBelow.fT_lt (by omega : 0 < k + 2) hi
    omega
  rw [convert_topNode k h hne]
  simp only [pairCut, hz, ↓reduceIte, Term.predR, succTerm_ne_zero,
    predT_succTerm (dropOne_wf hw.wf), hf, ↓reduceIte]

open multi in
theorem highest_principal_lt {m : Nat} (xs ys : V multi.T)
    (hxl : xs.length ≤ m + 1) (hyl : ys.length ≤ m + 1)
    (hh : V.get0 xs m < V.get0 ys m) : multi.T.P xs .Z < .P ys .Z := by
  apply T.P_lt_P_of_vlt
  apply V.lt_of_pivot m
  · intro j hj
    rw [V.get0_ge xs j (by omega), V.get0_ge ys j (by omega)]
    exact compareT_ZZ
  · exact hh

end kumakuma.GeneralImageMiddleRecursion

namespace kumakuma.GeneralImageChangingMiddle

open multi OCF.Jaeger kumakuma.OTQuotient kumakuma.DimensionImage kumakuma.CountableSource
open kumakuma.GeneralImageRawOrder kumakuma.GeneralImageWFInvariant
open kumakuma.GeneralImageLimitBranches kumakuma.GeneralImageLimitSupport kumakuma.GeneralImageRegularLimit
open kumakuma.GeneralImageLayerOrder kumakuma.GeneralImagePrincipalOrder kumakuma.GeneralImageTopPair
open kumakuma.GeneralImageRelativePredecessor kumakuma.GeneralImageCountableRecursion
open kumakuma.GeneralImageHeadCuts kumakuma.GeneralImageOmegaContext kumakuma.GeneralImageSharedContext
open kumakuma.GeneralImageSharedTopPair kumakuma.GeneralImageMiddleRecursion
open kumakuma.BinaryTranslation kumakuma.TargetArithmetic kumakuma.GeneralImageCoefficients
open kumakuma.SourceFundOrder kumakuma.SourceRecursiveDescending kumakuma.GeneralImageOmegaCoefficients
open kumakuma.SourceOmegaInvariant

universe u

theorem pairCut_convert_wf (k : Nat) (h : multi.T) (hh : RecursiveWF (k + 3) h) :
    Term.wf (pairCut (k + 1) (convert (k + 3) (code h))) = true := by
  by_cases hz : convert (k + 3) (code h) = .zero
  · simp [pairCut, hz, Term.wf, Term.fT]
  · simp only [pairCut, hz, ↓reduceIte]
    apply (Term.wf_inacc_iff _ _).mpr
    refine ⟨succTerm_wf (dropOne_wf hh.wf), ?_⟩
    cases he : dropOne (convert (k + 3) (code h)) <;> simp [succTerm, Term.fT, Term.one, Term.bigOmega]

end kumakuma.GeneralImageChangingMiddle

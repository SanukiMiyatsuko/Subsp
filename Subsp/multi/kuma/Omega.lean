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

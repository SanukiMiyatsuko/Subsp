import Subsp.Support.WF

/-! Omega-domain sources: coefficients, invariants, relative predecessors and contexts. -/

namespace Support.GeneralImageOmegaCoefficients

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageRawOrder
open Support.GeneralImageCoefficients Support.GeneralImageTopPair
open Support.GeneralImagePrincipalOrder Support.GeneralImageLayerOrder
open Support.GeneralImageWFInvariant Support.GeneralImageLimitSupport
open Support.SourceRecursiveDescending Support.SourceSubtermBounds

universe u

inductive Coefficient (d : Nat) {lam : Nat} : new.T lam → new.T lam → Prop
  | root (xs : Vec (new.T lam) lam) (b : new.T lam) (i : Fin lam)
      (hi : i.val + 1 < d) (hn : xs.idx i ≠ .Z) : Coefficient d (xs.idx i) (.P xs b)
  | coordinate (xs : Vec (new.T lam) lam) (b : new.T lam) (i : Fin lam)
      {a : new.T lam} : Coefficient d a (xs.idx i) → Coefficient d a (.P xs b)
  | tail (xs : Vec (new.T lam) lam) (b : new.T lam) {a : new.T lam} :
      Coefficient d a b → Coefficient d a (.P xs b)

theorem Coefficient.subterm {d lam : Nat} {a s : new.T lam} (h : Coefficient d a s) :
    Subterm a s := by
  induction h with
  | root xs b i => exact Subterm.coordinate xs b i
  | coordinate xs b i _ ih => exact Subterm.trans ih (Subterm.coordinate xs b i)
  | tail xs b _ ih => exact Subterm.trans ih (Subterm.tail xs b)

theorem Coefficient.ne_zero {d lam : Nat} {a s : new.T lam} (h : Coefficient d a s) : a ≠ .Z := by
  induction h with
  | root _ _ _ _ hn => exact hn
  | coordinate _ _ _ _ ih | tail _ _ _ ih => exact ih

theorem Coefficient.parent_ne_zero {d lam : Nat} {a s : new.T lam} (h : Coefficient d a s) :
    s ≠ .Z := by cases h <;> intro he <;> cases he

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
      · exact Or.inr (Or.inl (Support.OT2.mem_H_dropOne hz))
  · rw [ite_eq_right hb] at hz
    rcases H_psi_support hz with hz | hz | hz
    · exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Support.OT2.mem_H_dropOne hz))))
    · rcases H_inacc_support n _ hz with hz | hz
      · exact Or.inl hz
      · by_cases ha : a = .zero
        · rw [ite_eq_left ha, Term.H] at hz; cases hz
        · rw [ite_eq_right ha] at hz
          rcases H_succ_support (dropOne a) hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (Or.inl (Support.OT2.mem_H_dropOne hz))

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

theorem H_convert_coefficient (k : Nat) (u : Term) (s : new.T (k + 3)) {z : Term}
    (hz : z ∈ Term.H u (convert (k + 3) (code s))) :
    z = .zero ∨ ∃ a, Coefficient (k + 3) a s ∧
      (z = convert (k + 3) (code a) ∨ z = dropOne (convert (k + 3) (code a))) := by
  cases he : s with
  | Z => rw [he, code, convert, Term.H] at hz; cases hz
  | P xs b =>
    rw [he, code, convert] at hz
    rcases H_assemble_support u _ _ hz with hz | hz
    · rcases H_principal_precise u k _ hz with hz | ⟨i, hi, hz⟩ | ⟨i, hi, hz⟩
      · exact Or.inl hz
      · rw [converted_coordinate xs ⟨i, by omega⟩] at hz
        by_cases hn : xs.idx ⟨i, by omega⟩ = .Z
        · rw [hn] at hz
          simp only [code, convert, dropOne] at hz
          rcases hz with hz | hz <;> exact Or.inl hz
        · exact Or.inr ⟨xs.idx ⟨i, by omega⟩,
            Coefficient.root (d := k + 3) xs b ⟨i, by omega⟩ (show i + 1 < k + 3 by omega) hn, hz⟩
      · rw [converted_coordinate xs ⟨i, hi⟩] at hz
        rcases H_convert_coefficient k u (xs.idx ⟨i, hi⟩) hz with hz | ⟨a, ha, hz⟩
        · exact Or.inl hz
        · exact Or.inr ⟨a, Coefficient.coordinate xs b _ ha, hz⟩
    · rcases H_convert_coefficient k u b hz with hz | ⟨a, ha, hz⟩
      · exact Or.inl hz
      · exact Or.inr ⟨a, Coefficient.tail xs b ha, hz⟩
termination_by new.T.size s
decreasing_by
  all_goals simp only [he]
  all_goals first
    | (have hi := Vec.idx_size_lt xs (⟨i, hi⟩ : Fin (k + 3)); simp only [new.T.size]; omega)
    | exact new.T.add_size_lt_P _ _

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
    rw [Support.OT2.H_succTerm]
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
    z ∈ Term.H u (Support.OT2.assemble p t) := by
  unfold Support.OT2.assemble
  split
  · exact hz
  · rw [Term.H]; exact List.mem_append_left _ hz

theorem H_assemble_right (u p t : Term) {z : Term} (hz : z ∈ Term.H u t) :
    z ∈ Term.H u (Support.OT2.assemble p t) := by
  unfold Support.OT2.assemble
  by_cases ht : t = .zero
  · rw [ht, Term.H] at hz; cases hz
  · rw [ite_eq_right ht, Term.H]; exact List.mem_append_right _ hz

theorem Coefficient.image_mem_H_omega (k : Nat) {a s : new.T (k + 3)}
    (h : Coefficient (k + 3) a s)
    (hh : Term.head (convert (k + 3) (code a)) ≠ Term.one) :
    convert (k + 3) (code a) ∈ Term.H Term.bigOmega (convert (k + 3) (code s)) := by
  have hn : convert (k + 3) (code a) ≠ .zero := by
    intro he
    exact h.ne_zero (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  induction h with
  | root xs b i hi hz =>
    simp only [code, convert]
    apply H_assemble_left
    have hm := H_omega_principal_coordinate k (arguments (k + 3) (trim (codes xs))) i.val
      (by omega) (by rwa [converted_coordinate xs i])
    rw [converted_coordinate xs i] at hm
    rcases hm with hm | hm
    · exact hm
    · rwa [dropOne_of_head_ne hh] at hm
  | coordinate xs b i h ih =>
    simp only [code, convert]
    apply H_assemble_left
    exact H_omega_principal_coordinate_recursive k _ i.val i.isLt
      (by rw [converted_coordinate xs i]; exact ih hh hn) hn
  | tail xs b h ih =>
    simp only [code, convert]
    exact H_assemble_right _ _ _ (ih hh hn)

theorem Coefficient.parent_image_head_ne_one [LargeCardinals.{u}] (k : Nat)
    {a s : new.T (k + 3)} (h : Coefficient (k + 3) a s) (hs : RecursiveWF (k + 3) s) :
    Term.head (convert (k + 3) (code s)) ≠ Term.one := by
  induction h with
  | root xs b i hi hn =>
    rw [convert_head]
    exact principal_image_ne_one k xs i (recursive_head (.P xs b) hs) hn
  | coordinate xs b i h ih =>
    rw [convert_head]
    exact principal_image_ne_one k xs i (recursive_head (.P xs b) hs) h.parent_ne_zero
  | tail xs b h ih =>
    have hb : RecursiveWF (k + 3) b := by rw [RecursiveWF] at hs; exact hs.2.1
    have hbn : convert (k + 3) (code b) ≠ .zero := by
      intro he
      exact h.parent_ne_zero (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
    have hhead := ih hb
    intro hh
    have hwp := hs.wf
    simp only [code, convert, Support.OT2.assemble, ite_eq_right hbn] at hwp hh
    have hle := ((Term.wf_add_iff _ _).mp hwp).2.2.2.2
    have hh' : principal (k + 3) (arguments (k + 3) (trim (codes xs))) = Term.one := hh
    rw [hh'] at hle
    have ht := Support.CountableTarget.head_properties hb.wf hbn
    exact hhead ((principal_le_one_iff ht.1 ht.2).mp hle)

theorem Coefficient.lt_of_H_omega [LargeCardinals.{u}] (k : Nat)
    {a s : new.T (k + 3)} (h : Coefficient (k + 3) a s) (hs : RecursiveWF (k + 3) s)
    (hH : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true) : new.T.lt a s := by
  have har := h.subterm.recursiveWF hs
  apply (convert_order k a s har hs).mpr
  by_cases hh : Term.head (convert (k + 3) (code a)) = Term.one
  · obtain ⟨n, he⟩ := head_one_nat har.wf hh
    rw [he]
    have hs0 : convert (k + 3) (code s) ≠ .zero := by
      intro hz
      exact h.parent_ne_zero (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp hz))
    exact nat_lt_of_head_ne hs.wf hs0 (h.parent_image_head_ne_one k hs) (n + 1)
  · exact (Term.allLt_iff _ _).mp hH _ (h.image_mem_H_omega k hh)

theorem H_convert_bound_of_coefficients [LargeCardinals.{u}] (k : Nat) (u : Term)
    (s : new.T (k + 3)) (hs : RecursiveWF (k + 3) s)
    (hc : ∀ a, Coefficient (k + 3) a s → new.T.lt a s) :
    Term.allLt (Term.H u (convert (k + 3) (code s))) (convert (k + 3) (code s)) = true := by
  by_cases hs0 : s = .Z
  · subst s; simp only [code, convert, Term.H, Term.allLt, List.all_nil]
  · have hn : convert (k + 3) (code s) ≠ .zero := by
      intro hz
      exact hs0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp hz))
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    rcases H_convert_coefficient k u s hz with rfl | ⟨a, ha, he⟩
    · exact (zero_lt_iff _).mpr hn
    · have har := ha.subterm.recursiveWF hs
      have hlt := (convert_order k a s har hs).mp (hc a ha)
      rcases he with rfl | rfl
      · exact hlt
      · exact dropOne_lt_of_lt har.wf hs.wf hlt

theorem H_omega_bound_iff [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) :
    Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true ↔
        ∀ a, Coefficient (k + 3) a s → new.T.lt a s := by
  constructor
  · intro hH a ha; exact ha.lt_of_H_omega k hs hH
  · exact H_convert_bound_of_coefficients k Term.bigOmega s hs

theorem childrenBelow_of_coefficients (k : Nat) (s bound : new.T (k + 3))
    (hr : Recursive s) (hle : new.T.le s bound)
    (hc : ∀ a, Coefficient (k + 3) a s → new.T.lt a bound) : ChildrenBelow bound s := by
  cases s with
  | Z => trivial
  | P xs b =>
    rw [Recursive] at hr
    have lift : ∀ a, new.T.lt a (.P xs b) → new.T.lt a bound := by
      intro a ha
      rcases hle with hle | hle
      · exact new.T_trans _ _ _ ha hle
      · rw [← new.T_eq_sound _ _ hle]; exact ha
    refine ⟨?_, ?_⟩
    · intro i
      have hlt : new.T.lt (xs.idx i) bound := by
        by_cases hi : i.val < k + 2
        · by_cases hn : xs.idx i = .Z
          · rw [hn]
            exact lift .Z rfl
          · exact hc _ (Coefficient.root (d := k + 3) xs b i (by omega) hn)
        · have he : i = Fin.last (k + 2) := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
          rw [he]
          exact lift _ (last_coordinate_lt xs b)
      apply (treeBelow_iff _ _).mpr
      refine ⟨hlt, ?_⟩
      exact childrenBelow_of_coefficients k (xs.idx i) bound (hr.1 i) (Or.inl hlt)
        (fun a ha => hc a (Coefficient.coordinate xs b i ha))
    · have hlt := lift b (descending_tail_lt xs b hr.2.2)
      apply (treeBelow_iff _ _).mpr
      refine ⟨hlt, ?_⟩
      exact childrenBelow_of_coefficients k b bound hr.2.1 (Or.inl hlt)
        (fun a ha => hc a (Coefficient.tail xs b ha))
termination_by new.T.size s
decreasing_by
  all_goals simp_all only [new.T.size]
  all_goals first | (have hi := Vec.idx_size_lt xs i; omega) | omega

theorem coefficients_iff_subterms (k : Nat) (s : new.T (k + 3)) (hr : Recursive s) :
    (∀ a, Coefficient (k + 3) a s → new.T.lt a s) ↔
      ∀ a, Subterm a s → new.T.lt a s := by
  constructor
  · intro hc
    exact (childrenBelow_iff s s).mp
      (childrenBelow_of_coefficients k s s hr (Or.inr (new.T_refl _)) hc)
  · intro hs a ha; exact hs a ha.subterm

theorem H_omega_bound_iff_subterms [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (hr : Recursive s) :
    Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code s)))
      (convert (k + 3) (code s)) = true ↔ ∀ a, Subterm a s → new.T.lt a s :=
  (H_omega_bound_iff k s hs).trans (coefficients_iff_subterms k s hr)

end Support.GeneralImageOmegaCoefficients

namespace Support.SourceOmegaTail

open new Support.OTQuotient Support.DimensionCut Support.SourceFundOrder
open Support.SourceSubtermBounds Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageCoefficients

theorem Omega_head_mass_pos {lam : Nat} (xs : Vec (T lam) lam) (b : T lam)
    (hr : Recursive (.P xs b)) {v : Vec (T lam) lam} (hd : T.dom (.P xs b) = .Omega v) :
    0 < vectorMass xs := by
  by_cases hn : 0 < vectorMass xs
  · exact hn
  have hm : vectorMass xs = 0 := by omega
  have hx : xs = zeros lam := by
    apply vec_ext
    intro i
    rw [zeros, Vec.ofFn_idx]
    by_cases hi : xs.idx i = .Z
    · exact hi
    · have hh := mass_positive hi
      have hu := vectorMass_idx_le xs i
      omega
  have hv := domOmega_regular (.P xs b) hd
  have hh := domain_principal_le_head (.P xs b) hr hd
  change T.le (.P v .Z) (.P xs .Z) at hh
  rw [hx] at hh
  rcases hh with hh | hh
  · exact False.elim (nonzero_not_below_one (s := .P v .Z) (by intro he; cases he) hh)
  · have he := (T.P.inj (T_eq_sound _ _ hh)).1
    obtain ⟨i, hi, hv⟩ := hv
    rw [he, zeros_minIdx] at hv
    cases hv

theorem fund_tail_subterms {lam : Nat} (xs : Vec (T lam) lam) (b t : T lam)
    (hb : b ≠ .Z) (hx : 0 < vectorMass xs)
    (hs : ∀ a, Subterm a (.P xs b) → T.lt a (.P xs b))
    (ht : ∀ a, Subterm a t → T.lt a t) (hinc : T.lt t (T.fund (.P xs b) t)) :
    ∀ a, Subterm a (T.fund (.P xs b) t) → T.lt a (T.fund (.P xs b) t) := by
  by_cases ht0 : t = .Z
  · subst t; exact fund_zero_subterms (.P xs b) hs
  · have hc := (childrenBelow_iff (.P xs b) (.P xs b)).mpr hs
    have hm := mass_positive hb
    have hgap : gap (.P xs b) t = vectorMass xs + mass b := by
      rw [gap, ite_eq_right ht0, mass]
      omega
    have hcoords : ∀ i, TreeBelow (T.fund (.P xs b) t) (xs.idx i) := by
      intro i
      apply treeBelow_fund_of_small (.P xs b) t _ (hc.1 i)
      rw [hgap]
      have hi := vectorMass_idx_le xs i
      omega
    have hbtree : TreeBelow (T.fund (.P xs b) t) b := by
      apply treeBelow_fund_of_small (.P xs b) t b hc.2
      rw [hgap]
      omega
    have harg : TreeBelow (T.fund (.P xs b) t) t :=
      treeBelow_of_subterms _ t hinc (fun a ha => T_trans _ _ _ (ht a ha) hinc)
    apply (childrenBelow_iff _ _).mp
    have he : T.fund (.P xs b) t = .P xs (T.fund b t) := by rw [T.fund, ite_eq_right hb]
    rw [he] at hcoords hbtree harg ⊢
    exact ⟨hcoords, hbtree.fund harg⟩

end Support.SourceOmegaTail

namespace Support.GeneralImageRegularLimit

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder
open Support.GeneralImageTopPair Support.BinaryTranslation Support.TargetArithmetic
open Support.SourceFundOrder Support.SourceSubtermBounds Support.GeneralImageOmegaCoefficients
open Support.CountableSource
open Support.SourceOmegaTail

universe u

theorem topPair_context (n : Nat) (a b : Term) : Context n (topPair n a b) := by
  rcases topPair_shape n a b with hz | ⟨hp, hf⟩
  · exact Or.inl hz
  · exact Or.inr ⟨hp, Nat.le_of_eq hf.symm⟩

theorem inacc_image_drop_wf (k : Nat) (a : new.T (k + 3)) (ha : RecursiveWF (k + 3) a) :
    Term.wf (.inacc (k + 1) (dropOne (convert (k + 3) (code a)))) = true := by
  apply (Term.wf_inacc_iff _ _).mpr
  refine ⟨dropOne_wf ha.wf, ?_⟩
  have hi := indices_drop (indices_convert (k + 3) (by omega) (code a))
  exact Nat.le_of_lt_succ (Support.TargetIndexCuts.IndicesBelow.fT_lt (by omega : 0 < k + 2) hi)

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

theorem fund_regular_recursiveWF (k m : Nat) (xs : Vec (new.T (k + 3)) (k + 3))
    (hml : m + 1 < k + 3)
    (hv : new.T.domVecMinIdx xs = some (⟨m + 1, hml⟩, .one)) (t : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (ht : RecursiveWF (k + 3) t)
    (hH : Term.allLt (Term.H Term.bigOmega (convert (k + 3) (code t)))
      (convert (k + 3) (code t)) = true) :
    RecursiveWF (k + 3) (new.T.fund (.P xs .Z) t) := by
  have hdom := (Support.DimensionCut.minIdx_spec xs hv).1.symm
  have hlow := (Support.DimensionCut.minIdx_spec xs hv).2.2
  have hcoords : ∀ i, RecursiveWF (k + 3) (xs.idx i) := by rw [RecursiveWF] at hs; exact hs.1
  let p := new.T.fund (xs.idx ⟨m + 1, hml⟩) .Z
  have hp : RecursiveWF (k + 3) p := fund_one_recursiveWF _ _ (hcoords _) hdom
  have hsucc : convert (k + 3) (code (xs.idx ⟨m + 1, hml⟩)) =
      succTerm (convert (k + 3) (code p)) := by
    obtain ⟨a, he⟩ := dom_one_succ (xs.idx ⟨m + 1, hml⟩) hdom
    simp only [p, he, Support.SourceSuccessor.fund_succ, convert_succ]
  let zs := (xs.rplc ⟨m + 1, hml⟩ p).rplc ⟨m, by omega⟩ t
  have zidx (i : Fin (k + 3)) : zs.idx i =
      if i.val = m then t else if i.val = m + 1 then p else xs.idx i := by
    simp only [zs, vec_rplc_idx]
  have zhigh (i : Fin (k + 3)) (hi : m + 1 < i.val) : zs.idx i = xs.idx i := by
    rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
  have zlow (i : Fin (k + 3)) (hi : i.val < m) : zs.idx i = .Z := by
    rw [zidx, ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hlow i (by change i.val < m + 1; omega)
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes zs))
  have oldGet (i : Fin (k + 3)) : oldArgs[i.val]?.getD .zero =
      convert (k + 3) (code (xs.idx i)) := converted_coordinate xs i
  have newGet (i : Fin (k + 3)) : newArgs[i.val]?.getD .zero =
      convert (k + 3) (code (zs.idx i)) := converted_coordinate zs i
  have newP : newArgs[m + 1]?.getD .zero = convert (k + 3) (code p) := by
    rw [newGet ⟨m + 1, hml⟩, zidx, ite_eq_right (by simp), ite_eq_left rfl]
  have newT : newArgs[m]?.getD .zero = convert (k + 3) (code t) := by
    rw [newGet ⟨m, by omega⟩, zidx, ite_eq_left rfl]
  have oldSucc : oldArgs[m + 1]?.getD .zero = succTerm (convert (k + 3) (code p)) := by
    rw [oldGet ⟨m + 1, hml⟩]; exact hsucc
  have newZero : ∀ i, i < m → newArgs[i]?.getD .zero = .zero := by
    intro i hi
    rw [newGet ⟨i, by omega⟩, zlow ⟨i, by omega⟩ hi, code, convert]
  have newSame : ∀ i, m + 1 < i → i < k + 3 →
      newArgs[i]?.getD .zero = oldArgs[i]?.getD .zero := by
    intro i hi hik
    rw [newGet ⟨i, hik⟩, oldGet ⟨i, hik⟩, zhigh ⟨i, hik⟩ hi]
  rw [fund_regular_bound xs hml hv t]
  change RecursiveWF (k + 3) (.P zs .Z)
  rw [RecursiveWF]
  refine ⟨?_, recursive_zero _ _, ?_⟩
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
          rw [oldGet ⟨k + 2, by omega⟩]
          exact inacc_image_drop_wf k _ (hcoords _)
        have htop := topPair_successor_predecessor (k + 1) _ _ hi hp.wf htopold
        exact step_wf_of_omega_closed k _ _ (context_above (topPair_context _ _ _)) htop ht.wf hH
      · have hi : m + 1 < k + 1 := by omega
        rw [newSame (k + 2) (by omega) (by omega), newSame (k + 1) (by omega) (by omega)]
        exact lower_regular_update (k + 1) m oldArgs newArgs _ _ _ hi (topPair_context _ _ _)
          hp.wf ht.wf hH oldSucc newP newT newZero
          (fun i him hik => newSame i him (by omega)) hold

end Support.GeneralImageRegularLimit

namespace Support.SourceOmegaHighest

open new Support.OTQuotient Support.DimensionCut Support.SourceFundOrder
open Support.SourceSubtermBounds Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageCoefficients

theorem highest_not_diagonal (m : Nat) (a : T (m + 1)) (hr : Recursive a)
    {v : Vec (T (m + 1)) (m + 1)} (hd : T.dom a = .Omega v) : ¬Vec.lt (lastVec m a) v := by
  intro hv
  have hl := last_coordinate_lt (lastVec m a) .Z
  simp only [lastVec_idx, Fin.val_last, ↓reduceIte] at hl
  have hrlt := diagonal_principal_lt_argument (lastVec m a) a hr hd hv
  have hh := T_trans _ _ _ hl hrlt
  rw [T_refl] at hh
  cases hh

theorem highest_Omega_domain (m : Nat) (a : T (m + 1)) (hr : Recursive a)
    {v : Vec (T (m + 1)) (m + 1)} (hd : T.dom a = .Omega v) :
    T.dom (.P (lastVec m a) .Z) = .Omega v := by
  have hn := highest_not_diagonal m a hr hd
  rw [T.dom]
  simp only [↓reduceIte, minIdx_lastVec, hd, reduceCtorEq, hn]

theorem lastVec_replace_last {lam : Nat} (m : Nat) (a b : T lam) :
    (lastVec m a).rplc (Fin.last m) b = lastVec m b := by
  apply vec_ext
  intro i
  simp only [vec_rplc_idx, lastVec_idx, Fin.val_last]
  split <;> rfl

theorem highest_Omega_fund (m : Nat) (a t : T (m + 1)) (hr : Recursive a)
    {v : Vec (T (m + 1)) (m + 1)} (hd : T.dom a = .Omega v) :
    T.fund (.P (lastVec m a) .Z) t = .P (lastVec m (T.fund a t)) .Z := by
  have hn := highest_not_diagonal m a hr hd
  rw [T.fund]
  simp only [↓reduceIte, minIdx_lastVec, hd, reduceCtorEq, hn, GetElem.getElem,
    lastVec_idx, Fin.val_last, lastVec_replace_last]

theorem vectorMass_lastVec {lam : Nat} (m : Nat) (a : T lam) :
    vectorMass (lastVec m a) = mass a := by
  have hz : vectorMass (zeros (lam := lam) m) = 0 :=
    vectorMass_eq_zero _ (by intro i; simp only [zeros, Vec.ofFn_idx])
  simp only [lastVec, vectorMass, hz, Nat.zero_add]

end Support.SourceOmegaHighest

namespace Support.SourceOmegaInvariant

open new Support.OTQuotient Support.DimensionCut Support.SourceFundOrder
open Support.SourceSubtermBounds Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageCoefficients Support.SourceOmegaTail Support.SourceOmegaHighest

def CutSpine {lam : Nat} (i : Fin lam) : T lam → Prop
  | .Z => True
  | .P xs b => (∀ j, i.val < j.val → xs.idx j = .Z) ∧
      CutSpine i (xs.idx i) ∧ CutSpine i b
termination_by s => T.size s
decreasing_by
  all_goals first | exact T.idx_size_lt_P _ _ _ | exact T.add_size_lt_P _ _

theorem CutSpine.zero {lam : Nat} (i : Fin lam) : CutSpine i (.Z : T lam) := by
  rw [CutSpine]; trivial

theorem CutSpine.coordinate_lt {lam : Nat} (i : Fin lam) (xs : Vec (T lam) lam) (b : T lam)
    (hs : CutSpine i (.P xs b)) : T.lt (xs.idx i) (.P xs b) := by
  rw [CutSpine] at hs
  cases he : xs.idx i with
  | Z => rfl
  | P ys c =>
    have hcut := hs.2.1
    rw [he, CutSpine] at hcut
    have harg := CutSpine.coordinate_lt i ys c (he ▸ hs.2.1)
    have hv := compareVec_of_lt_at ys xs i (by rw [he]; exact harg)
      (fun j hj => (hcut.1 j hj).trans (hs.1 j hj).symm)
    simp only [T.lt, compareT, hv]
termination_by T.size (.P xs b)
decreasing_by
  have hh := T.idx_size_lt_P xs b i
  change T.size (xs.idx i) < T.size (.P xs b) at hh
  rw [he] at hh
  exact hh

theorem CutSpine.principal_replace {lam : Nat} (i j : Fin lam) (xs : Vec (T lam) lam)
    (a : T lam) (hs : CutSpine i (.P xs .Z)) (hji : j.val ≤ i.val)
    (ha : j = i → CutSpine i a) : CutSpine i (.P (xs.rplc j a) .Z) := by
  rw [CutSpine] at hs ⊢
  refine ⟨?_, ?_, CutSpine.zero i⟩
  · intro l hl
    rw [vec_rplc_idx, ite_eq_right (by omega)]
    exact hs.1 l hl
  · rw [vec_rplc_idx]
    split
    · rename_i he
      exact ha (Fin.ext he.symm)
    · exact hs.2.1

theorem CutSpine.mul_principal {lam : Nat} (i : Fin lam) (xs : Vec (T lam) lam) (t : T lam)
    (hs : CutSpine i (.P xs .Z)) : CutSpine i (T.mul (.P xs .Z) t) := by
  cases t with
  | Z => rw [T.mul]; exact CutSpine.zero i
  | P ys b =>
    change CutSpine i (.P xs (T.mul (.P xs .Z) b))
    rw [CutSpine] at hs ⊢
    have hp : CutSpine i (.P xs .Z) := by rw [CutSpine]; exact ⟨hs.1, hs.2.1, CutSpine.zero i⟩
    exact ⟨hs.1, hs.2.1, CutSpine.mul_principal i xs b hp⟩
termination_by T.size t
decreasing_by exact T.add_size_lt_P _ _

theorem CutSpine.fund {lam : Nat} (i : Fin lam) (s t : T lam) (hs : CutSpine i s) :
    CutSpine i (T.fund s t) := by
  cases heS : s with
  | Z => rw [T.fund]; exact CutSpine.zero i
  | P xs b =>
    rw [heS, CutSpine] at hs
    rw [T.fund]
    by_cases hb : b = .Z
    · subst b
      simp only [↓reduceIte]
      have hp : CutSpine i (.P xs .Z) := by rw [CutSpine]; exact ⟨hs.1, hs.2.1, CutSpine.zero i⟩
      cases hm : T.domVecMinIdx xs with
      | none => exact CutSpine.zero i
      | some p =>
        obtain ⟨j, d⟩ := p
        have hji : j.val ≤ i.val := by
          by_cases hj : j.val ≤ i.val
          · exact hj
          · have hz := hs.1 j (by omega)
            have hn := (minIdx_spec xs hm).2.1
            rw [(minIdx_spec xs hm).1, hz, T.dom] at hn
            exact False.elim (hn rfl)
        have replace (a : T lam) (ha : j = i → CutSpine i a) :
            CutSpine i (.P (xs.rplc j a) .Z) :=
          CutSpine.principal_replace i j xs a hp hji ha
        have update (a : T lam) : CutSpine i (.P (xs.rplc j (T.fund (xs.idx j) a)) .Z) := by
          apply replace
          intro he
          subst j
          exact CutSpine.fund i _ a hs.2.1
        cases d with
        | zero | omega => exact update t
        | Omega v =>
          change CutSpine i (if Vec.lt xs v then
            .P (xs.rplc j (T.fund (xs.idx j) (T.iter (T.fund (xs.idx j)) t))) .Z
            else .P (xs.rplc j (T.fund (xs.idx j) t)) .Z)
          split <;> exact update _
        | one =>
          obtain ⟨m, hj⟩ := j
          cases m with
          | zero => exact CutSpine.mul_principal i _ t (update .Z)
          | succ m =>
            apply CutSpine.principal_replace i ⟨m, Nat.lt_of_succ_lt hj⟩ _ t (update .Z)
              (by change m ≤ i.val; change m + 1 ≤ i.val at hji; omega)
            intro he
            have hv := congrArg Fin.val he
            change m = i.val at hv
            change m + 1 ≤ i.val at hji
            omega
    · rw [ite_eq_right hb, CutSpine]
      exact ⟨hs.1, hs.2.1, CutSpine.fund i b t hs.2.2⟩
termination_by T.size s
decreasing_by
  all_goals simp only [heS]
  all_goals first | exact T.idx_size_lt_P _ _ _ | exact T.add_size_lt_P _ _

theorem above_zero_of_vec_le {lam m : Nat} (i : Nat) (xs ys : Vec (T lam) m)
    (hy : ∀ j, i < j.val → ys.idx j = .Z) (hxy : Vec.le xs ys) :
    ∀ j, i < j.val → xs.idx j = .Z := by
  induction xs with
  | nil => intro j; exact j.elim0
  | snoc m xs x ih =>
    cases ys with
    | snoc _ ys y =>
      intro j hj
      have him : i < m := by have := j.isLt; omega
      have hy0 := hy (Fin.last m) him
      rw [vec_snoc_idx_last] at hy0
      have hx0 : x = .Z := by
        have hh := vec_le_last xs ys x y hxy
        rw [hy0] at hh
        cases x with
        | Z => rfl
        | P => cases hh <;> contradiction
      have hlow : Vec.le xs ys := by
        rw [hy0, hx0] at hxy
        exact (vec_same_last_le xs ys .Z).mp hxy
      by_cases hjm : j.val < m
      · let l : Fin m := ⟨j.val, hjm⟩
        have he : j = l.castSucc := Fin.ext rfl
        rw [he, vec_snoc_idx_cast]
        exact ih ys (fun a ha => by simpa only [vec_snoc_idx_cast] using hy a.castSucc ha)
          hlow l hj
      · have he : j = Fin.last m := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
        rw [he, vec_snoc_idx_last]
        exact hx0

theorem above_zero_of_lt_principal {lam : Nat} (i : Fin lam)
    (xs ys : Vec (T lam) lam) (b c : T lam)
    (hx : ∀ j, i.val < j.val → xs.idx j = .Z) (h : T.lt (.P ys c) (.P xs b)) :
    ∀ j, i.val < j.val → ys.idx j = .Z := by
  have hv : Vec.le ys xs := by
    change (match compareVec ys xs with | .eq => compareT c b | o => o) = .lt at h
    cases he : compareVec ys xs with
    | lt => exact Or.inl he
    | eq => exact Or.inr he
    | gt => rw [he] at h; cases h
  exact above_zero_of_vec_le i.val ys xs hx hv

theorem TreeBelow.cutSpine {lam : Nat} (i : Fin lam) (xs : Vec (T lam) lam) (b s : T lam)
    (hx : ∀ j, i.val < j.val → xs.idx j = .Z) (hs : TreeBelow (.P xs b) s) : CutSpine i s := by
  cases heS : s with
  | Z => exact CutSpine.zero i
  | P ys c =>
    rw [heS, TreeBelow] at hs
    rw [CutSpine]
    exact ⟨above_zero_of_lt_principal i xs ys b c hx hs.1,
      TreeBelow.cutSpine i xs b _ hx (hs.2.1 i), TreeBelow.cutSpine i xs b c hx hs.2.2⟩
termination_by T.size s
decreasing_by
  all_goals simp only [heS]
  all_goals first | exact T.idx_size_lt_P _ _ _ | exact T.add_size_lt_P _ _

theorem treeBelow_mul_of_root_lt {lam : Nat} (xs : Vec (T lam) lam) (bound t : T lam)
    (hx : ∀ i, TreeBelow bound (xs.idx i)) (hz : TreeBelow bound .Z)
    (hroot : T.lt (T.mul (.P xs .Z) t) bound) : TreeBelow bound (T.mul (.P xs .Z) t) := by
  cases heT : t with
  | Z => rw [T.mul]; exact hz
  | P ys b =>
    rw [heT] at hroot
    change TreeBelow bound (.P xs (T.mul (.P xs .Z) b))
    rw [TreeBelow]
    refine ⟨hroot, hx, ?_⟩
    apply treeBelow_mul_of_root_lt xs bound b hx hz
    exact T_trans _ _ _
      (descending_tail_lt xs _ (Support.SourceDescending.mul_principal_descending xs (.P ys b))) hroot
termination_by T.size t
decreasing_by rw [heT]; exact T.add_size_lt_P _ _

theorem ChildrenBelow.fund_of_root_lt {lam : Nat} {s t bound : T lam}
    (hs : ChildrenBelow bound s) (ht : TreeBelow bound t) (hroot : T.lt (T.fund s t) bound) :
    ChildrenBelow bound (T.fund s t) := by
  cases s with
  | Z => rw [T.fund, ChildrenBelow]; trivial
  | P xs b =>
    rw [ChildrenBelow] at hs
    by_cases hb : b = .Z
    · subst b
      rw [T.fund] at hroot ⊢
      simp only [↓reduceIte] at hroot ⊢
      cases hm : T.domVecMinIdx xs with
      | none => rw [ChildrenBelow]; trivial
      | some p =>
        obtain ⟨i, d⟩ := p
        rw [hm] at hroot
        have hf : ∀ a, TreeBelow bound a → TreeBelow bound (T.fund (xs.idx i) a) :=
          fun a ha => (hs.1 i).fund ha
        cases d with
        | zero | omega => exact ⟨treeBelow_rplc xs i _ bound hs.1 (hf t ht), hs.2⟩
        | Omega ys =>
          change ChildrenBelow bound (if Vec.lt xs ys then
            .P (xs.rplc i (T.fund (xs.idx i) (T.iter (T.fund (xs.idx i)) t))) .Z
            else .P (xs.rplc i (T.fund (xs.idx i) t)) .Z)
          by_cases hv : Vec.lt xs ys
          · rw [ite_eq_left hv]
            exact ⟨treeBelow_rplc xs i _ bound hs.1
              (hf _ (treeBelow_iter (T.fund (xs.idx i)) bound t ht.zero hf)), hs.2⟩
          · rw [ite_eq_right hv]
            exact ⟨treeBelow_rplc xs i _ bound hs.1 (hf t ht), hs.2⟩
        | one =>
          obtain ⟨m, him⟩ := i
          cases m with
          | zero =>
            apply TreeBelow.children
            exact treeBelow_mul_of_root_lt _ bound t
              (treeBelow_rplc xs ⟨0, him⟩ _ bound hs.1 (hf .Z ht.zero)) ht.zero hroot
          | succ m =>
            exact ⟨treeBelow_rplc _ ⟨m, Nat.lt_of_succ_lt him⟩ t bound
              (treeBelow_rplc xs ⟨m + 1, him⟩ _ bound hs.1 (hf .Z ht.zero)) ht, hs.2⟩
    · rw [T.fund, ite_eq_right hb]
      exact ⟨hs.1, hs.2.fund ht⟩

theorem coordinate_fund_subterms {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (t : T lam)
    (ha0 : xs.idx i ≠ .Z)
    (hfund : T.fund (.P xs .Z) t = .P (xs.rplc i (T.fund (xs.idx i) t)) .Z)
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z))
    (ht : ∀ a, Subterm a t → T.lt a t)
    (hinc : T.lt t (T.fund (.P xs .Z) t)) :
    ∀ a, Subterm a (T.fund (.P xs .Z) t) → T.lt a (T.fund (.P xs .Z) t) := by
  by_cases ht0 : t = .Z
  · subst t; exact fund_zero_subterms (.P xs .Z) hs
  · let s : T lam := .P xs .Z
    let a : T lam := xs.idx i
    have ham : 0 < mass a := mass_positive ha0
    have hgap : gap s t = vectorMass xs := by
      simp only [s, gap, ite_eq_right ht0, mass]
      omega
    have hsource := (childrenBelow_iff s s).mpr hs
    have harg : TreeBelow (T.fund s t) t :=
      treeBelow_of_subterms _ t hinc (fun c hc => T_trans _ _ _ (ht c hc) hinc)
    have hchildren : ChildrenBelow (T.fund s t) a := by
      apply (childrenBelow_iff _ _).mpr
      intro c hc
      apply small_lt_fund_all s t c (hs c (Subterm.trans hc (Subterm.coordinate xs .Z i)))
      rw [hgap]
      exact Nat.lt_of_lt_of_le (Support.SourceCoefficientGap.mass_lt_of_subterm hc)
        (vectorMass_idx_le xs i)
    have hcoords : ∀ j : Fin lam, j ≠ i → TreeBelow (T.fund s t) (xs.idx j) := by
      intro j hj
      apply treeBelow_fund_of_small s t _ (hsource.1 j)
      rw [hgap]
      have hp := vectorMass_pair_le xs j i hj
      change 0 < mass (xs.idx i) at ham
      omega
    have hupdated : TreeBelow (T.fund s t) (T.fund a t) := by
      by_cases hsmall : mass a < vectorMass xs
      · exact (treeBelow_fund_of_small s t a (hsource.1 i) (by rw [hgap]; exact hsmall)).fund harg
      · have hsingle : ∀ j : Fin lam, j ≠ i → xs.idx j = .Z := by
          intro j hj
          have hp := vectorMass_pair_le xs j i hj
          have hm0 : mass (xs.idx j) = 0 := by
            change mass (xs.idx j) + mass a ≤ vectorMass xs at hp
            omega
          by_cases hz : xs.idx j = .Z
          · exact hz
          · have hmpos := mass_positive hz
            omega
        have hhigh : ∀ j : Fin lam, i.val < j.val → xs.idx j = .Z :=
          fun j hj => hsingle j (by intro he; rw [he] at hj; omega)
        have hcut : CutSpine i a := TreeBelow.cutSpine i xs .Z a hhigh (hsource.1 i)
        have hcut' := CutSpine.fund i a t hcut
        have hparent : CutSpine i (.P (xs.rplc i (T.fund a t)) .Z) := by
          rw [CutSpine]
          refine ⟨?_, ?_, CutSpine.zero i⟩
          · intro j hj
            rw [vec_rplc_idx, ite_eq_right (by omega)]
            exact hhigh j hj
          · rw [vec_rplc_idx, ite_eq_left rfl]
            exact hcut'
        have hroot : T.lt (T.fund a t) (T.fund s t) := by
          rw [hfund]
          have hh := CutSpine.coordinate_lt i (xs.rplc i (T.fund a t)) .Z hparent
          simpa only [vec_rplc_idx, ↓reduceIte] using hh
        exact (treeBelow_iff _ _).mpr ⟨hroot, ChildrenBelow.fund_of_root_lt hchildren harg hroot⟩
    apply (childrenBelow_iff _ _).mp
    change ChildrenBelow (T.fund s t) (T.fund s t)
    rw [hfund]
    rw [hfund] at harg hupdated hcoords
    refine ⟨?_, harg.zero⟩
    intro j
    rw [vec_rplc_idx]
    split
    · exact hupdated
    · rename_i hj
      exact hcoords j (by intro he; exact hj (congrArg Fin.val he))

theorem inherited_fund_subterms {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam)
    (t : T lam) {v : Vec (T lam) lam}
    (hm : T.domVecMinIdx xs = some (i, .Omega v)) (hn : ¬Vec.lt xs v)
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z))
    (ht : ∀ a, Subterm a t → T.lt a t)
    (hinc : T.lt t (T.fund (.P xs .Z) t)) :
    ∀ a, Subterm a (T.fund (.P xs .Z) t) → T.lt a (T.fund (.P xs .Z) t) := by
  apply coordinate_fund_subterms xs i t _ _ hs ht hinc
  · intro he
    have hd := (minIdx_spec xs hm).1.symm
    rw [he, T.dom] at hd
    cases hd
  · simp only [T.fund, ↓reduceIte, hm, hn, GetElem.getElem]

theorem fund_Omega_subterms {lam : Nat} (s t : T lam) (hr : Recursive s)
    {v : Vec (T lam) lam} (hd : T.dom s = .Omega v)
    (hs : ∀ a, Subterm a s → T.lt a s)
    (ht : ∀ a, Subterm a t → T.lt a t) (hinc : T.lt t (T.fund s t)) :
    ∀ a, Subterm a (T.fund s t) → T.lt a (T.fund s t) := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [T.dom] at hd
      simp only [↓reduceIte] at hd
      cases hm : T.domVecMinIdx xs with
      | none => rw [hm] at hd; cases hd
      | some p =>
        obtain ⟨i, d⟩ := p
        cases d with
        | zero | omega => simp only [hm] at hd; cases hd
        | one =>
          have hi : i.val ≠ 0 := by
            intro he; simp only [hm, he, ↓reduceIte] at hd; cases hd
          obtain ⟨m, him⟩ := i
          cases m with
          | zero => exact False.elim (hi rfl)
          | succ m => exact regular_fund_subterms xs him hm t hs ht hinc
        | Omega ys =>
          have hn : ¬Vec.lt xs ys := by
            intro he; simp only [hm, he, ↓reduceIte] at hd; cases hd
          exact inherited_fund_subterms xs i t hm hn hs ht hinc
    · exact fund_tail_subterms xs b t hb (Omega_head_mass_pos xs b hr hd) hs ht hinc

theorem Omega_iter_subterms {lam : Nat} (s : T lam) (hr : Recursive s)
    {v : Vec (T lam) lam} (hd : T.dom s = .Omega v)
    (hs : ∀ a, Subterm a s → T.lt a s) (n : Nat) :
    ∀ a, Subterm a (T.iter (T.fund s) (T.ofNat n)) → T.lt a (T.iter (T.fund s) (T.ofNat n)) := by
  induction n with
  | zero =>
    intro a ha
    have hh := ha.size_lt
    simp only [T.ofNat, T.iter, T.size] at hh
    omega
  | succ n ih =>
    rw [iter_ofNat_succ]
    exact fund_Omega_subterms s _ hr hd hs ih
      (by simpa only [iter_ofNat_succ] using domOmega_iter_lt_next s hd n)

end Support.SourceOmegaInvariant

namespace Support.GeneralImageHighOmega

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageRegularLimit
open Support.SourceRecursiveDescending Support.SourceSubtermBounds
open Support.SourceFundOrder Support.SourceOmegaTail Support.SourceOmegaHighest
open Support.SourceOmegaInvariant
open Support.GeneralImageOmegaCoefficients Support.CountableSource

universe u

theorem high_recursive_image (k : Nat) (a : new.T (k + 3))
    (hs : RecursiveWF (k + 3) (topNode k a)) : RecursiveWF (k + 3) a := by
  rw [topNode, RecursiveWF] at hs
  have hh := hs.1 (Fin.last (k + 2))
  simpa only [lastVec_idx, Fin.val_last, ↓reduceIte] using hh

end Support.GeneralImageHighOmega

namespace Support.SourceCountableInvariant

open new Support.OTQuotient Support.DimensionCut Support.SourceFundOrder
open Support.SourceSubtermBounds Support.SourceFundGap Support.SourceRecursiveDescending
open Support.GeneralImageCoefficients Support.SourceOmegaTail Support.SourceOmegaInvariant

theorem TreeBelow.mono_le {lam : Nat} {s a b : T lam} (hs : TreeBelow a s) (hab : T.le a b) :
    TreeBelow b s := by
  have lift (c : T lam) (hc : T.lt c a) : T.lt c b := by
    rcases hab with hab | hab
    · exact T_trans _ _ _ hc hab
    · rw [← T_eq_sound _ _ hab]; exact hc
  exact treeBelow_of_subterms b s (lift s hs.root_lt)
    (fun c hc => lift c (Support.SourceSubtermBounds.Subterm.treeBelow hc hs).root_lt)

theorem treeBelow_ofNat {lam : Nat} (n : Nat) (bound : T lam) (h : T.lt (T.ofNat n) bound) :
    TreeBelow bound (T.ofNat n) := by
  cases n with
  | zero => rw [T.ofNat, TreeBelow]; exact h
  | succ n =>
    rw [T.ofNat, TreeBelow]
    have hn : T.lt (T.ofNat (lam := lam) n) (T.ofNat (n + 1)) :=
      by rw [← Support.SourceSuccessor.nat_succ]; exact
        (Support.SourceSuccessor.lt_succ_iff_le _ _).mpr (Or.inr (T_refl _))
    have hb := T_trans _ _ _ hn h
    have hz : TreeBelow bound .Z := (treeBelow_ofNat n bound hb).zero
    exact ⟨h, by intro i; simp only [Vec.ofFn_idx]; exact hz, treeBelow_ofNat n bound hb⟩

theorem ofNat_subterms (lam n : Nat) :
    ∀ a, Subterm a (T.ofNat (lam := lam) n) → T.lt a (T.ofNat n) := by
  cases n with
  | zero => intro a ha; have hh := ha.size_lt; simp only [T.ofNat, T.size] at hh; omega
  | succ n =>
    apply (childrenBelow_iff _ _).mp
    change ChildrenBelow (T.ofNat (n + 1)) (.P (zeros lam) (T.ofNat n))
    have hn : T.lt (T.ofNat (lam := lam) n) (T.ofNat (n + 1)) :=
      by rw [← Support.SourceSuccessor.nat_succ]; exact
        (Support.SourceSuccessor.lt_succ_iff_le _ _).mpr (Or.inr (T_refl _))
    have ht := treeBelow_ofNat n _ hn
    exact ⟨by intro i; rw [zeros, Vec.ofFn_idx]; exact ht.zero, ht⟩

theorem succ_le_of_lt {lam : Nat} {a b : T lam} (h : T.lt a b) :
    T.le (Support.SourceSuccessor.succ a) b := by
  rcases T_total (Support.SourceSuccessor.succ a) b with hh | hh | hh
  · exact Or.inl hh
  · have hb := (Support.SourceSuccessor.lt_succ_iff_le b a).mp hh
    rcases hb with hb | hb
    · have bad := T_trans _ _ _ h hb; rw [T_refl] at bad; cases bad
    · rw [T_eq_sound _ _ hb] at h; unfold T.lt at h; rw [T_refl] at h; cases h
  · exact Or.inr (by rw [hh]; exact T_refl b)

theorem ofNat_le_countable_fund {lam : Nat} (s : T lam) (hd : T.dom s = .omega) (n : Nat) :
    T.le (T.ofNat n) (T.fund s (T.ofNat n)) := by
  induction n with
  | zero => cases he : T.fund s (T.ofNat 0) with
    | Z => exact Or.inr rfl
    | P => exact Or.inl rfl
  | succ n ih =>
    have hn : T.lt (T.ofNat n) (T.fund s (T.ofNat (n + 1))) := by
      have hi := countable_fund_lt_next s hd n
      rcases ih with ih | ih
      · exact T_trans _ _ _ ih hi
      · rw [T_eq_sound _ _ ih]; exact hi
    simpa only [Support.SourceSuccessor.nat_succ] using succ_le_of_lt hn

theorem coordinate_update_root_lt {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (t : T lam)
    (ha0 : xs.idx i ≠ .Z)
    (hfund : T.fund (.P xs .Z) t = .P (xs.rplc i (T.fund (xs.idx i) t)) .Z)
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z)) :
    T.lt (T.fund (xs.idx i) t) (T.fund (.P xs .Z) t) := by
  by_cases ht0 : t = .Z
  · subst t
    have hh : Subterm ((xs.rplc i (T.fund (xs.idx i) .Z)).idx i) (T.fund (.P xs .Z) .Z) := by
      rw [hfund]; exact Subterm.coordinate _ .Z i
    have hb := fund_zero_subterms (.P xs .Z) hs _ hh
    rw [hfund] at hb
    rw [hfund]
    simpa only [vec_rplc_idx, ↓reduceIte] using hb
  · have hgap : gap (.P xs .Z) t = vectorMass xs := by simp only [gap, ht0, ↓reduceIte, mass]; omega
    by_cases hsmall : mass (xs.idx i) < vectorMass xs
    · have hroot := small_lt_fund_all (.P xs .Z) t (xs.idx i)
        (hs _ (Subterm.coordinate xs .Z i)) (by rw [hgap]; exact hsmall)
      exact T_trans _ _ _ (fund_lt _ t ha0) hroot
    · have hsingle : ∀ j : Fin lam, j ≠ i → xs.idx j = .Z := by
        intro j hj
        have hp := vectorMass_pair_le xs j i hj
        by_cases hz : xs.idx j = .Z
        · exact hz
        · have hmpos := mass_positive hz
          omega
      have hhigh : ∀ j : Fin lam, i.val < j.val → xs.idx j = .Z :=
        fun j hj => hsingle j (by intro he; rw [he] at hj; omega)
      have hc := (childrenBelow_iff _ _).mpr hs
      have hcut := (TreeBelow.cutSpine i xs .Z _ hhigh (hc.1 i)).fund i _ t
      have hp : CutSpine i (.P (xs.rplc i (T.fund (xs.idx i) t)) .Z) := by
        rw [CutSpine]
        refine ⟨?_, ?_, CutSpine.zero i⟩
        · intro j hj; rw [vec_rplc_idx, ite_eq_right (by omega)]; exact hhigh j hj
        · rw [vec_rplc_idx, ite_eq_left rfl]; exact hcut
      rw [hfund]
      simpa only [vec_rplc_idx, ↓reduceIte] using CutSpine.coordinate_lt i _ .Z hp

theorem mul_nat_subterms {lam : Nat} (xs : Vec (T lam) lam)
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z)) (n : Nat) :
    ∀ a, Subterm a (T.mul (.P xs .Z) (T.ofNat n)) →
      T.lt a (T.mul (.P xs .Z) (T.ofNat n)) := by
  cases n with
  | zero => intro a ha; have hh := ha.size_lt; simp only [T.ofNat, T.mul, T.size] at hh; omega
  | succ n =>
    rw [mul_principal_ofNat_succ]
    apply (childrenBelow_iff _ _).mp
    have hp : T.le (.P xs .Z) (.P xs (T.mul (.P xs .Z) (T.ofNat n))) :=
      head_le_self (.P xs (T.mul (.P xs .Z) (T.ofNat n)))
    have hc := (childrenBelow_iff _ _).mpr hs
    have hx : ∀ i, TreeBelow (.P xs (T.mul (.P xs .Z) (T.ofNat n))) (xs.idx i) :=
      fun i => TreeBelow.mono_le (hc.1 i) hp
    have hz : TreeBelow (.P xs (T.mul (.P xs .Z) (T.ofNat n))) .Z := by rw [TreeBelow]; rfl
    refine ⟨hx, treeBelow_mul_of_root_lt xs _ _ hx hz ?_⟩
    exact descending_tail_lt xs _ (Support.SourceDescending.mul_principal_descending xs (T.ofNat (n + 1)))

theorem zero_vector_recursive_isNat {lam : Nat} (b : T lam)
    (hr : Recursive (.P (zeros lam) b)) : ∃ n, (.P (zeros lam) b : T lam) = T.ofNat (n + 1) := by
  cases heB : b with
  | Z => exact ⟨0, rfl⟩
  | P ys c =>
    rw [heB, Recursive] at hr
    have hh := hr.2.2.2
    change T.le (.P ys .Z) (T.ofNat 1) at hh
    have hy : ys = zeros lam := by
      rcases hh with hh | hh
      · exact False.elim (nonzero_not_below_one (by intro he; cases he) hh)
      · exact (T.P.inj (T_eq_sound _ _ hh)).1
    subst ys
    obtain ⟨n, hn⟩ := zero_vector_recursive_isNat c hr.2.1
    refine ⟨n + 1, ?_⟩
    change T.P (zeros lam) (.P (zeros lam) c) = T.P (zeros lam) (T.ofNat (n + 1))
    exact congrArg (T.P (zeros lam)) hn
termination_by T.size b
decreasing_by rw [heB]; exact T.add_size_lt_P _ _

theorem omega_head_mass_pos {lam : Nat} (xs : Vec (T lam) lam) (b : T lam)
    (hr : Recursive (.P xs b)) (hd : T.dom (.P xs b) = .omega) : 0 < vectorMass xs := by
  by_cases hm : 0 < vectorMass xs
  · exact hm
  have hx : xs = zeros lam := by
    apply vec_ext
    intro i
    rw [zeros, Vec.ofFn_idx]
    by_cases hz : xs.idx i = .Z
    · exact hz
    · have hh := vectorMass_idx_le xs i
      have hp := mass_positive hz
      omega
  rw [hx] at hr hd
  obtain ⟨n, hn⟩ := zero_vector_recursive_isNat b hr
  rw [hn, ← Support.SourceSuccessor.nat_succ, Support.SourceSuccessor.dom_succ] at hd
  cases hd

theorem numeral_lt_nonzero_head {lam : Nat} (xs : Vec (T lam) lam) (b : T lam)
    (hx : 0 < vectorMass xs) (n : Nat) : T.lt (T.ofNat n) (.P xs b) := by
  have hv : compareVec (zeros lam) xs = .lt := by
    rcases Vec_total (zeros lam) xs with hv | hv | hv
    · exact hv
    · exact False.elim (compareVec_zero_not_lt xs hv)
    · have hzero := vectorMass_eq_zero xs (by intro i; rw [← hv, zeros, Vec.ofFn_idx])
      omega
  cases n with
  | zero => rfl
  | succ n =>
    change compareT (.P (zeros lam) (T.ofNat n)) (.P xs b) = .lt
    simp only [compareT, hv]

theorem zero_successor_fund_subterms {lam : Nat} (xs : Vec (T lam) lam)
    (i : Fin lam) (hi : i.val = 0) (hm : T.domVecMinIdx xs = some (i, .one))
    (hs : ∀ a, Subterm a (.P xs .Z) → T.lt a (.P xs .Z)) (n : Nat) :
    ∀ a, Subterm a (T.fund (.P xs .Z) (T.ofNat n)) →
      T.lt a (T.fund (.P xs .Z) (T.ofNat n)) := by
  obtain ⟨j, hj⟩ := i
  change j = 0 at hi
  subst j
  have hd := (minIdx_spec xs hm).1.symm
  let p := T.fund (xs.idx ⟨0, hj⟩) .Z
  let ys := xs.rplc ⟨0, hj⟩ p
  have hfund (t : T lam) : T.fund (.P xs .Z) t = T.mul (.P ys .Z) t := by
    simp only [T.fund, ↓reduceIte, hm, GetElem.getElem]
    rfl
  have hfone : T.fund (.P xs .Z) (T.ofNat 1) = .P ys .Z := by
    rw [hfund]
    simp only [T.ofNat, T.mul, HAdd.hAdd, Add.add, T.oplus]
  have hchild : T.fund (xs.idx ⟨0, hj⟩) (T.ofNat 1) = p := by
    obtain ⟨a, he⟩ := Support.GeneralImageWFInvariant.dom_one_succ _ hd
    simp only [p, he, Support.SourceSuccessor.fund_succ]
  have hplain : T.fund (.P xs .Z) (T.ofNat 1) =
      .P (xs.rplc ⟨0, hj⟩ (T.fund (xs.idx ⟨0, hj⟩) (T.ofNat 1))) .Z := by
    rw [hfone, hchild]
  have hq : ∀ a, Subterm a (.P ys .Z) → T.lt a (.P ys .Z) := by
    by_cases hone : (.P ys .Z : T lam) = T.ofNat 1
    · rw [hone]; exact ofNat_subterms lam 1
    · have hinc : T.lt (T.ofNat 1) (T.fund (.P xs .Z) (T.ofNat 1)) := by
        rw [hfone]
        rcases T_total (T.ofNat (lam := lam) 1) (.P ys .Z) with he | he | he
        · exact he
        · exact False.elim (nonzero_not_below_one (by intro hz; cases hz) he)
        · exact False.elim (hone he.symm)
      have ha0 : xs.idx ⟨0, hj⟩ ≠ .Z := by intro he; rw [he, T.dom] at hd; cases hd
      have hh := coordinate_fund_subterms xs ⟨0, hj⟩ (T.ofNat 1) ha0 hplain hs
        (ofNat_subterms lam 1) hinc
      rw [hfone] at hh
      exact hh
  rw [hfund]
  exact mul_nat_subterms ys hq n

theorem fund_omega_subterms (m : Nat) (s : T (m + 1)) (hr : Recursive s)
    (hd : T.dom s = .omega) (hs : ∀ a, Subterm a s → T.lt a s) (n : Nat) :
    ∀ a, Subterm a (T.fund s (T.ofNat n)) → T.lt a (T.fund s (T.ofNat n)) := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rcases omega_selector_of_subterms m xs hr hs hd with hm | ⟨i, hm⟩
      · exact zero_successor_fund_subterms xs ⟨0, by omega⟩ rfl hm hs n
      · have hchild := (minIdx_spec xs hm).1.symm
        have ha0 : xs.idx i ≠ .Z := by intro he; rw [he, T.dom] at hchild; cases hchild
        have hfund : T.fund (.P xs .Z) (T.ofNat n) =
            .P (xs.rplc i (T.fund (xs.idx i) (T.ofNat n))) .Z := by
          simp only [T.fund, ↓reduceIte, hm, GetElem.getElem]
        have hroot := coordinate_update_root_lt xs i (T.ofNat n) ha0 hfund hs
        have hinc : T.lt (T.ofNat n) (T.fund (.P xs .Z) (T.ofNat n)) := by
          rcases ofNat_le_countable_fund _ hchild n with hn | hn
          · exact T_trans _ _ _ hn hroot
          · rw [← T_eq_sound _ _ hn] at hroot; exact hroot
        exact coordinate_fund_subterms xs i (T.ofNat n) ha0 hfund hs (ofNat_subterms _ n) hinc
    · have hx := omega_head_mass_pos xs b hr hd
      apply fund_tail_subterms xs b (T.ofNat n) hb hx hs (ofNat_subterms _ n)
      rw [T.fund, ite_eq_right hb]
      exact numeral_lt_nonzero_head xs _ hx n

end Support.SourceCountableInvariant

namespace Support.GeneralImageHeadCuts

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageRegularLimit
open Support.GeneralImageLimitSupport
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients

universe u

theorem inacc_zero_le (n : Nat) (a : Term) : Term.le (.inacc n .zero) (.inacc n a) = true := by
  cases a <;> simp [Term.le, Term.lt]

theorem hOne_positive_cut (cut : Nat) (hc : 0 < cut) : Term.hOne (.inacc cut .zero) = [] := by
  simp [Term.hOne, Term.predR, Term.le, Term.lt, Term.bigOmega,
    Support.CountableTarget.lt_zero, show 0 < cut from hc]

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

end Support.GeneralImageHeadCuts

namespace Support.GeneralImageRelativePredecessor

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
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
  apply Support.GeneralImageHeadCuts.no_coeff_eq_nil
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
            rw [Support.OT2.H_succTerm]
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
          rw [Support.OT2.H_succTerm]
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

theorem zero_coordinate_relative_support [LargeCardinals.{u}] (k : Nat) (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (xs : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
    (hx : xs.idx ⟨0, by omega⟩ = Support.SourceSuccessor.succ b)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) {z : Term}
    (hz : z ∈ Term.H v (convert (k + 3) (code (.P (xs.rplc ⟨0, by omega⟩ b) .Z)))) :
    z ∈ Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
      (z = convert (k + 3) (code b) ∨ z = dropOne (convert (k + 3) (code b))) ∧
        (convert (k + 3) (code (Support.SourceSuccessor.succ b)) ∈
            Term.H v (convert (k + 3) (code (.P xs .Z))) ∨
          dropOne (convert (k + 3) (code (Support.SourceSuccessor.succ b))) ∈
            Term.H v (convert (k + 3) (code (.P xs .Z)))) := by
  let ys := xs.rplc ⟨0, by omega⟩ b
  let us := arguments (k + 3) (trim (codes xs))
  let vs := arguments (k + 3) (trim (codes ys))
  have hb : RecursiveWF (k + 3) b := by
    rw [RecursiveWF] at hs
    exact (recursive_succ_iff _ _).mp (hx ▸ hs.1 ⟨0, by omega⟩)
  have he : ∀ i, 0 < i → i < k + 3 → us[i]?.getD .zero = vs[i]?.getD .zero := by
    intro i hi hik
    rw [converted_coordinate xs ⟨i, hik⟩, converted_coordinate ys ⟨i, hik⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : i ≠ 0)]
  have htop : topPair (k + 1) (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero) =
      topPair (k + 1) (vs[k + 2]?.getD .zero) (vs[k + 1]?.getD .zero) := by
    rw [he (k + 2) (by omega) (by omega), he (k + 1) (by omega) (by omega)]
  have hctx := Support.GeneralImageRegularLimit.topPair_context (k + 1)
    (us[k + 2]?.getD .zero) (us[k + 1]?.getD .zero)
  have h0 : us[0]?.getD .zero = succTerm (convert (k + 3) (code b)) := by
    rw [converted_coordinate xs ⟨0, by omega⟩, hx, convert_succ]
  have h0' : vs[0]?.getD .zero = convert (k + 3) (code b) := by
    rw [converted_coordinate ys ⟨0, by omega⟩]
    simp only [ys, vec_rplc_idx, ↓reduceIte]
  have hw := hs.wf
  rw [convert_principal, principal_as_layers] at hw
  change z ∈ Term.H v (convert (k + 3) (code (.P ys .Z))) at hz
  rw [convert_principal, principal_as_layers, ← htop] at hz
  have h := lower_zero_relative_support v hvR hv (k + 1) (by omega) us vs _ _ hctx hb.wf h0 h0'
    (fun i hi hik => he i hi (by omega)) hw hz
  simpa only [convert_succ, convert_principal, principal_as_layers] using h

theorem zero_coordinate_relative_closed [LargeCardinals.{u}] (k : Nat) (v : Term)
    (hvR : Term.isRT v = true) (hv : Term.wf v = true)
    (xs : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
    (hx : xs.idx ⟨0, by omega⟩ = Support.SourceSuccessor.succ b)
    (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) :
    Term.allLt (Term.H v (convert (k + 3) (code (.P (xs.rplc ⟨0, by omega⟩ b) .Z))))
      (convert (k + 3) (code (.P (xs.rplc ⟨0, by omega⟩ b) .Z))) = true := by
  obtain ⟨hn, _⟩ := zero_coordinate_predecessor k xs b hx hs
  have hb : RecursiveWF (k + 3) b := by
    rw [RecursiveWF] at hs
    exact (recursive_succ_iff _ _).mp (hx ▸ hs.1 ⟨0, by omega⟩)
  have hbs := (recursive_succ_iff _ _).mpr hb
  have hnon : xs.idx ⟨0, by omega⟩ ≠ .Z := by
    rw [hx]; exact Support.SourceSuccessor.succ_ne_zero b
  have hp : Term.isPrin (convert (k + 3) (code (.P xs .Z))) = true := by
    rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_isPrin _ _
  have hone := principal_image_ne_one k xs ⟨0, by omega⟩ hs hnon
  have hmass : Support.SourceFundGap.mass (.P (xs.rplc ⟨0, by omega⟩ b) .Z) + 1 =
      Support.SourceFundGap.mass (.P xs .Z) := by
    have hbalance := Support.SourceFundGap.vectorMass_rplc xs ⟨0, by omega⟩ b
    rw [hx, Support.SourceFundGap.mass_succ] at hbalance
    simp only [Support.SourceFundGap.mass]; omega
  have hfund : new.T.fund (.P xs .Z) (new.T.ofNat 1) = .P (xs.rplc ⟨0, by omega⟩ b) .Z := by
    rw [fund_zero_coordinate_successor k xs b _ hx]
    simp only [new.T.ofNat, new.T.mul]; rfl
  apply (Term.allLt_iff _ _).mpr
  intro z hz
  have hzold : Term.lt z (convert (k + 3) (code (.P xs .Z))) = true := by
    rcases zero_coordinate_relative_support k v hvR hv xs b hx hs hz with h | ⟨he, hmem⟩
    · exact (Term.allLt_iff _ _).mp hH z h
    · have hslt : Term.lt (convert (k + 3) (code (Support.SourceSuccessor.succ b)))
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
  rcases H_convert_source k v (.P (xs.rplc ⟨0, by omega⟩ b) .Z) hz with rfl | ⟨a, ha, he⟩
  · apply (zero_lt_iff _).mpr
    rw [convert_principal]; exact Support.GeneralImageEmbedding.principal_ne_zero _ _
  · have har := ha.recursiveWF hn
    have hal : new.T.lt a (.P xs .Z) := by
      apply (convert_order k _ _ har hs).mpr
      rcases he with rfl | rfl
      · exact hzold
      · exact undrop_lt_principal _ _ har.wf hs.wf hp hone hzold
    have ham := Support.SourceCoefficientGap.mass_lt_of_subterm ha
    have hgap : Support.SourceFundGap.mass a < Support.SourceFundGap.gap (.P xs .Z) (new.T.ofNat 1) := by
      rw [Support.SourceFundGap.gap_nonzero _ _ (by intro h; cases h)]; omega
    have ha' := Support.SourceFundGap.small_lt_fund_all (.P xs .Z) (new.T.ofNat 1) a hal hgap
    rw [hfund] at ha'
    have hlt := (convert_order k _ _ har hn).mp ha'
    rcases he with rfl | rfl
    · exact hlt
    · exact dropOne_lt_of_lt har.wf hn.wf hlt

theorem H_drop_bound (v t : Term) (ht : Term.wf t = true)
    (hH : Term.allLt (Term.H v t) t = true) :
    Term.allLt (Term.H v (dropOne t)) (dropOne t) = true := by
  by_cases hh : Term.head t = Term.one
  · obtain ⟨n, rfl⟩ := head_one_nat ht hh
    rw [dropOne_nat]; exact H_nat_bound v n
  · simpa only [dropOne_of_head_ne hh] using hH

theorem H_mul_principal_bound [LargeCardinals.{u}] (k : Nat) (v : Term)
    (xs : Vec (new.T (k + 3)) (k + 3)) (hs : RecursiveWF (k + 3) (.P xs .Z))
    (hH : Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z))))
      (convert (k + 3) (code (.P xs .Z))) = true) (n : Nat) :
    Term.allLt (Term.H v (convert (k + 3) (code (new.T.mul (.P xs .Z) (new.T.ofNat n)))))
      (convert (k + 3) (code (new.T.mul (.P xs .Z) (new.T.ofNat n)))) = true := by
  cases n with
  | zero => simp [new.T.ofNat, new.T.mul, code, convert, Term.H, Term.allLt]
  | succ n =>
    have hm := mul_principal_recursiveWF xs hs (new.T.ofNat (n + 1))
    have hle : new.T.le (.P xs .Z) (new.T.mul (.P xs .Z) (new.T.ofNat (n + 1))) := by
      change compareT (.P xs .Z) (.P xs (new.T.mul (.P xs .Z) (new.T.ofNat n))) = .lt ∨
        compareT (.P xs .Z) (.P xs (new.T.mul (.P xs .Z) (new.T.ofNat n))) = .eq
      simp only [compareT, Vec_refl]
      cases new.T.mul (.P xs .Z) (new.T.ofNat n) <;> simp [compareT]
    have hle' := image_le_of_le k _ _ hs hm hle
    apply (Term.allLt_iff _ _).mpr
    intro z hz
    have ho := H_mul_principal_support (k + 3) xs (n + 1) v hz
    have hl := (Term.allLt_iff _ _).mp hH z ho
    rcases (Term.le_iff_eq_or_lt _ _).mp hle' with he | he
    · simpa only [← he] using hl
    · exact lemma_6_1.{u}.2.1 _ _ _ (H_coefficient_wf v _ hs.wf ho) hs.wf hm.wf hl he

theorem fund_zero_successor_relative [LargeCardinals.{u}] (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (b : new.T (k + 3))
    (hx : xs.idx ⟨0, by omega⟩ = Support.SourceSuccessor.succ b)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (n : Nat) :
    RecursiveWF (k + 3) (new.T.fund (.P xs .Z) (new.T.ofNat n)) ∧
      ∀ v, Term.isRT v = true → Term.wf v = true →
        Term.allLt (Term.H v (convert (k + 3) (code (.P xs .Z)))) (convert (k + 3) (code (.P xs .Z))) = true →
        Term.allLt (Term.H v (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))))
          (convert (k + 3) (code (new.T.fund (.P xs .Z) (new.T.ofNat n)))) = true := by
  obtain ⟨hn, _⟩ := zero_coordinate_predecessor k xs b hx hs
  rw [fund_zero_coordinate_successor k xs b _ hx]
  refine ⟨mul_principal_recursiveWF _ hn _, ?_⟩
  intro v hvR hv hH
  exact H_mul_principal_bound k v _ hn (zero_coordinate_relative_closed k v hvR hv xs b hx hs hH) n

end Support.GeneralImageRelativePredecessor

namespace Support.GeneralImageCountableLayers

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.GeneralImageRelativePredecessor

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

theorem principal_replace_relative_recursiveWF (k : Nat)
    (xs : Vec (new.T (k + 3)) (k + 3)) (i : Fin (k + 3)) (hib : i.val ≤ k + 1)
    (hlow : ∀ j, j.val < i.val → xs.idx j = .Z)
    (hs : RecursiveWF (k + 3) (.P xs .Z)) (a : new.T (k + 3))
    (ha : RecursiveWF (k + 3) a) (hc0 : xs.idx i ≠ .Z)
    (hdrop : dropOne (convert (k + 3) (code (xs.idx i))) = convert (k + 3) (code (xs.idx i)))
    (hrel : ∀ v, Term.isRT v = true → Term.wf v = true →
      Term.allLt (Term.H v (convert (k + 3) (code (xs.idx i)))) (convert (k + 3) (code (xs.idx i))) = true →
      Term.allLt (Term.H v (convert (k + 3) (code a))) (convert (k + 3) (code a)) = true) :
    RecursiveWF (k + 3) (.P (xs.rplc i a) .Z) := by
  let ys := xs.rplc i a
  let oldArgs := arguments (k + 3) (trim (codes xs))
  let newArgs := arguments (k + 3) (trim (codes ys))
  have hold (j : Fin (k + 3)) : oldArgs[j.val]?.getD .zero = convert (k + 3) (code (xs.idx j)) :=
    converted_coordinate xs j
  have hnew (j : Fin (k + 3)) : newArgs[j.val]?.getD .zero = convert (k + 3) (code (ys.idx j)) :=
    converted_coordinate ys j
  have hnewa : newArgs[i.val]?.getD .zero = convert (k + 3) (code a) := by
    rw [hnew i]; simp only [ys, vec_rplc_idx, ↓reduceIte]
  have hzero : ∀ j, j < i.val → newArgs[j]?.getD .zero = .zero := by
    intro j hj
    rw [hnew ⟨j, by omega⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
    rw [hlow ⟨j, by omega⟩ hj]; simp only [code, convert]
  have hsame : ∀ j, i.val < j → j < k + 3 → newArgs[j]?.getD .zero = oldArgs[j]?.getD .zero := by
    intro j hj hjk
    rw [hnew ⟨j, hjk⟩, hold ⟨j, hjk⟩]
    simp only [ys, vec_rplc_idx, ite_eq_right (by omega : j ≠ i.val)]
  have hcoords : ∀ j, RecursiveWF (k + 3) (xs.idx j) := by rw [RecursiveWF] at hs; exact hs.1
  have hc := (hcoords i).wf
  rw [RecursiveWF]
  refine ⟨?_, recursive_zero _ _, ?_⟩
  · intro j
    simp only [vec_rplc_idx]
    split
    · exact ha
    · exact hcoords j
  · rw [convert_principal, principal_as_layers]
    change Term.wf (lower (k + 1) newArgs
      (topPair (k + 1) (newArgs[k + 2]?.getD .zero) (newArgs[k + 1]?.getD .zero))) = true
    rw [hsame (k + 2) (by omega) (by omega)]
    have hw := hs.wf
    rw [convert_principal, principal_as_layers] at hw
    by_cases he : i.val = k + 1
    · rw [← he, hnewa]
      apply lower_zero_wf i.val newArgs _ hzero
      have htop := lower_context_wf (k + 1) oldArgs _ (topPair_context _ _ _) hw
      rw [← he, hold i] at htop
      apply topPair_replace_relative_wf i.val _ _ _ _ ha.wf _ hdrop hrel htop
      · rw [he, hold ⟨k + 2, by omega⟩]; exact inacc_image_drop_wf k _ (hcoords _)
      · intro hz
        exact hc0 (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp hz))
    · rw [hsame (k + 1) (by omega) (by omega)]
      exact lower_replace_relative_wf (k + 1) i.val (by omega) oldArgs newArgs _ _ _
        (topPair_context _ _ _) hc ha.wf hdrop hrel (hold i) hnewa hzero
        (fun j hj hjk => hsame j hj (by omega)) hw

end Support.GeneralImageCountableLayers

namespace Support.GeneralImageCountableRecursion

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageCountableLayers Support.GeneralImageRelativePredecessor
open Support.GeneralImageOmegaCoefficients
open Support.GeneralImageCoefficients Support.SourceRecursiveDescending Support.SourceFundOrder
open Support.BinaryTranslation Support.TargetArithmetic

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

theorem H_low_empty_above_Omega (v : Term) (hOmega : Term.lt Term.bigOmega v = true)
    (d m : Nat) (a : new.T (m + 1)) :
    Term.H v (convert d (code (.P (lowVec m a) .Z))) = [] := by
  rw [convert_low_principal, Term.H]
  split
  · rfl
  · simp only [Term.bigOmega, Term.H, ↓reduceIte, List.nil_append]

theorem numeral_recursiveWF (d lam n : Nat) : RecursiveWF d (new.T.ofNat (lam := lam) n) := by
  induction n with
  | zero => exact recursive_zero d lam
  | succ n ih =>
    rw [← Support.SourceSuccessor.nat_succ]
    exact (recursive_succ_iff d _).mpr ih

theorem convert_numeral (d lam n : Nat) :
    convert d (code (new.T.ofNat (lam := lam) n)) = Support.FiniteCorrespondence.natTerm n := by
  have hp : principal d [] = Term.one := by
    simpa only [Support.UserImage.oneCode, convert, arguments, Support.OT2.assemble, ↓reduceIte] using convert_one d
  induction n with
  | zero => simp only [new.T.ofNat, code, convert, Support.FiniteCorrespondence.natTerm]
  | succ n ih =>
    rw [Support.FiniteCorrespondence.code_ofNat] at ih ⊢
    rw [Support.FiniteCorrespondence.natCode, convert, arguments, hp, ih]
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Support.OT2.assemble, Support.FiniteCorrespondence.natTerm_ne_zero,
        ↓reduceIte, Support.FiniteCorrespondence.natTerm]

theorem drop_image_of_omega [LargeCardinals.{u}] (k : Nat) (s : new.T (k + 3))
    (hs : RecursiveWF (k + 3) s) (hd : new.T.dom s = .omega) :
    dropOne (convert (k + 3) (code s)) = convert (k + 3) (code s) := by
  apply dropOne_of_head_ne
  intro hh
  obtain ⟨n, he⟩ := head_one_nat hs.wf hh
  have hn := numeral_recursiveWF (k + 3) (k + 3) (n + 1)
  have hsNat : s = new.T.ofNat (n + 1) := convert_injective k s _ hs hn
    (he.trans (convert_numeral _ _ _).symm)
  rw [hsNat, ← Support.SourceSuccessor.nat_succ, Support.SourceSuccessor.dom_succ] at hd
  cases hd

end Support.GeneralImageCountableRecursion

namespace Support.GeneralImageOmegaContext

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.BinaryTranslation Support.TargetArithmetic
open Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant
open Support.GeneralImageHighOmega Support.SourceOmegaHighest
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

theorem convert_positive_layers (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3))
    (i : Fin (k + 3)) (hi : 0 < i.val) (hib : i.val ≤ k + 1)
    (hhigh : ∀ j, i.val < j.val → xs.idx j = .Z) :
    convert (k + 3) (code (.P xs .Z)) =
      lower i.val (arguments (k + 3) (trim (codes xs)))
        (step i.val .zero (convert (k + 3) (code (xs.idx i)))) := by
  let args := arguments (k + 3) (trim (codes xs))
  have hget (j : Fin (k + 3)) : args[j.val]?.getD .zero = convert (k + 3) (code (xs.idx j)) :=
    converted_coordinate xs j
  have hzero (j : Nat) (hj : i.val < j) (hjk : j < k + 3) : args[j]?.getD .zero = .zero := by
    rw [hget ⟨j, hjk⟩, hhigh ⟨j, hjk⟩ hj, code, convert]
  rw [convert_principal, principal_as_layers]
  change lower (k + 1) args (topPair (k + 1) (args[k + 2]?.getD .zero)
    (args[k + 1]?.getD .zero)) = _
  rw [hzero (k + 2) (by omega) (by omega)]
  by_cases he : i.val = k + 1
  · rw [← he, hget i]
    congr 1
    simp only [topPair, step, ↓reduceIte, Nat.ne_of_gt hi]
  · rw [hzero (k + 1) (by omega) (by omega)]
    simp only [topPair, ↓reduceIte]
    rw [lower_clear_above_cut (k + 1) (i.val + 1) (by omega) (by omega) args
      (fun j hj hjk => hzero j (by omega) (by omega)), lower_succ, hget i]

theorem convert_positive_single (k : Nat) (xs : Vec (new.T (k + 3)) (k + 3))
    (i : Fin (k + 3)) (hi : 0 < i.val) (hib : i.val ≤ k + 1)
    (hlow : ∀ j, j.val < i.val → xs.idx j = .Z)
    (hhigh : ∀ j, i.val < j.val → xs.idx j = .Z) (hne : xs.idx i ≠ .Z) :
    convert (k + 3) (code (.P xs .Z)) =
      .psi (.inacc i.val .zero) (dropOne (convert (k + 3) (code (xs.idx i)))) := by
  rw [convert_positive_layers k xs i hi hib hhigh]
  have ha0 : convert (k + 3) (code (xs.idx i)) ≠ .zero := by
    intro h
    exact hne (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp h))
  simp only [step, ↓reduceIte, Nat.ne_of_gt hi, ha0]
  apply lower_zero_nonzero _ _ _ (by intro h; cases h)
  intro j hj
  rw [converted_coordinate xs ⟨j, by omega⟩, hlow ⟨j, by omega⟩ hj, code, convert]

end Support.GeneralImageOmegaContext

namespace Support.GeneralImageSharedContext

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant
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
  rw [Support.OT2.H_succTerm, regular_H_context_empty_of_wf n a hwa hu, H_one_empty_above_Omega _ hOmega]
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

end Support.GeneralImageSharedContext

namespace Support.GeneralImageSharedTopPair

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant
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

end Support.GeneralImageSharedTopPair

namespace Support.GeneralImageMiddleRecursion

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant

universe u

theorem pairCut_image_pred (k : Nat) (h : new.T (k + 3)) (hne : h ≠ .Z)
    (hw : RecursiveWF (k + 3) h) :
    Term.predR (pairCut (k + 1) (convert (k + 3) (code h))) =
      convert (k + 3) (code (topNode k h)) := by
  have hz : convert (k + 3) (code h) ≠ .zero := by
    intro he; exact hne (code_injective ((Support.GeneralImageEmbedding.fixed_convert_zero_iff _ _).mp he))
  have hi := indices_drop (indices_convert (k + 3) (by omega) (code h))
  have hf : Term.fT (dropOne (convert (k + 3) (code h))) ≤ k + 1 := by
    have hf := Support.TargetIndexCuts.IndicesBelow.fT_lt (by omega : 0 < k + 2) hi
    omega
  rw [convert_topNode k h hne]
  simp only [pairCut, hz, ↓reduceIte, Term.predR, succTerm_ne_zero,
    predT_succTerm (dropOne_wf hw.wf), hf, ↓reduceIte]

theorem highest_principal_lt {m : Nat} (xs ys : Vec (new.T (m + 1)) (m + 1))
    (hh : new.T.lt (xs.idx (Fin.last m)) (ys.idx (Fin.last m))) :
    new.T.lt (.P xs .Z) (.P ys .Z) := by
  have hv := compareVec_of_lt_at xs ys (Fin.last m) hh
    (by intro j hj; have := j.isLt; simp only [Fin.val_last] at hj; omega)
  simp only [new.T.lt, compareT, hv]

end Support.GeneralImageMiddleRecursion

namespace Support.GeneralImageChangingMiddle

open new OCF.Jaeger Support.OTQuotient Support.DimensionImage Support.CountableSource
open Support.GeneralImageRawOrder Support.GeneralImageWFInvariant
open Support.GeneralImageLimitBranches Support.GeneralImageLimitSupport Support.GeneralImageRegularLimit
open Support.GeneralImageLayerOrder Support.GeneralImagePrincipalOrder Support.GeneralImageTopPair
open Support.GeneralImageRelativePredecessor Support.GeneralImageCountableRecursion
open Support.GeneralImageHeadCuts Support.GeneralImageOmegaContext Support.GeneralImageSharedContext
open Support.GeneralImageSharedTopPair Support.GeneralImageMiddleRecursion
open Support.BinaryTranslation Support.TargetArithmetic Support.GeneralImageCoefficients
open Support.SourceFundOrder Support.SourceRecursiveDescending Support.GeneralImageOmegaCoefficients
open Support.SourceOmegaInvariant

universe u

theorem pairCut_convert_wf (k : Nat) (h : new.T (k + 3)) (hh : RecursiveWF (k + 3) h) :
    Term.wf (pairCut (k + 1) (convert (k + 3) (code h))) = true := by
  by_cases hz : convert (k + 3) (code h) = .zero
  · simp [pairCut, hz, Term.wf, Term.fT]
  · simp only [pairCut, hz, ↓reduceIte]
    apply (Term.wf_inacc_iff _ _).mpr
    refine ⟨succTerm_wf (dropOne_wf hh.wf), ?_⟩
    cases he : dropOne (convert (k + 3) (code h)) <;> simp [succTerm, Term.fT, Term.one, Term.bigOmega]

end Support.GeneralImageChangingMiddle

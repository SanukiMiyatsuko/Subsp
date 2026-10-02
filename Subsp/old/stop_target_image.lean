import Subsp.old.stop_ot_domain

/-! Target-side downward-closure infrastructure for the legacy translation image. -/

namespace LegacyTranslation

theorem target_image_downward
    (Image : T → Prop)
    (hsound : ∀ a : T, Image a → T.isNF1 a ∧ a < T.P 1 T.Z T.Z)
    (hstep : ∀ a : T, Image a → ∀ n : Nat,
      Image (T.fund1 a (T.ofNat n)))
    (a b : T) (ha : Image a) (hb : T.isNF1 b) (hba : b ≤ a) :
    Image b := by
  have main :
      ∀ a : T.NF1, Image a.val →
        a.val < T.P 1 T.Z T.Z →
        ∀ b : T, T.isNF1 b → b ≤ a.val → Image b := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
        intro ha hab b hb hba
        rcases hba with hba | rfl
        · obtain ⟨n, hfall, hupper⟩ :=
            fund1_countable_cofinal a.val b a.property hb hab hba
          have him := hstep a.val ha n
          have hsim := hsound _ him
          exact ih ⟨_, hsim.1⟩ hfall him hsim.2 b hb hupper
        · exact ha
  exact main ⟨a, (hsound a ha).1⟩ ha (hsound a ha).2 b hb hba

theorem target_image_of_upper
    (Image : T → Prop)
    (hsound : ∀ a : T, Image a → T.isNF1 a ∧ a < T.P 1 T.Z T.Z)
    (hstep : ∀ a : T, Image a → ∀ n : Nat,
      Image (T.fund1 a (T.ofNat n)))
    (b : T) (hb : T.isNF1 b)
    (a : T) (ha : Image a) (hba : b < a) :
    Image b :=
  target_image_downward Image hsound hstep a b ha hb (Or.inl hba)

end LegacyTranslation

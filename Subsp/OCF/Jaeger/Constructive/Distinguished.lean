import Subsp.OCF.Jaeger.Constructive.Syntax

/-! Buchholz's distinguished sets for Jäger's notation system, following Arai's presentation with
the maximal distinguished set.

* `Hull α X` is the set `C^α(X)`: the closure of `{0} ∪ (X ∩ α)` under `+`, `I_n` and `ψ_σ` for
  regular `σ > α`.
* `WPart Y` is the well-founded part of `Y`.
* `Dist X` says that `X` is distinguished: below the next regular term after any `α ≤ X`, the set
  `X` is the well-founded part of `Hull α X`.
* `Wmax` is the union of all distinguished sets (an impredicative definition in `Prop`), and
  `Good α` says `α ∈ C^α(Wmax)` and `C^α(Wmax) ∩ α ⊆ Wmax`.

The main result here, `wmax_of_good_hyp`, builds a new distinguished set from `Good α` and an
extension hypothesis. -/

namespace OCF.Jaeger.Term

inductive Hull (α : Term) (X : Term → Prop) : Term → Prop where
  | zero : Hull α X zero
  | mem {β : Term} (hX : X β) (hw : wf β = true) (hβ : lt β α = true) : Hull α X β
  | add {a b : Term} (hw : wf (add a b) = true) (ha : Hull α X a) (hb : Hull α X b) :
      Hull α X (add a b)
  | inacc {n : Nat} {b : Term} (hw : wf (inacc n b) = true) (hb : Hull α X b) :
      Hull α X (inacc n b)
  | psi {σ b : Term} (hw : wf (psi σ b) = true) (hσα : lt α σ = true) (hσ : Hull α X σ)
      (hb : Hull α X b) : Hull α X (psi σ b)

def Rel (Y : Term → Prop) (x y : Term) : Prop := Y x ∧ lt x y = true

def WPart (Y : Term → Prop) (β : Term) : Prop := Y β ∧ Acc (Rel Y) β

def Dist (X : Term → Prop) : Prop :=
  (∀ β, X β → wf β = true) ∧
    ∀ α, wf α = true → (∃ δ, X δ ∧ le α δ = true) →
      ∀ β, (WPart (Hull α X) β ∧ lt β (nr α) = true) ↔ (X β ∧ lt β (nr α) = true)

def Wmax (β : Term) : Prop := ∃ X, Dist X ∧ X β

def Good (α : Term) : Prop := Hull α Wmax α ∧ ∀ β, Hull α Wmax β → lt β α = true → Wmax β

/-! ### Order helpers -/

theorem le_antisymm {a b : Term} (h1 : le a b = true) (h2 : le b a = true) : a = b :=
  ((le_iff a b).mp h1).resolve_right (fun h => by rw [not_lt_of_le h2] at h; cases h)

theorem le_trans {a b c : Term} (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : le a b = true) (h2 : le b c = true) : le a c = true :=
  ((le_iff a b).mp h1).elim (fun e => by rw [e]; exact h2)
    (fun h => le_of_lt (lt_of_lt_of_le wa wb wc h h2))

/-! ### Hulls -/

theorem Hull.wf_of {α : Term} {X : Term → Prop} {β : Term} (h : Hull α X β) : wf β = true := by
  cases h <;> first | assumption | exact wf_zero

/-- Hulls are mapped constructor by constructor, given the members and the admissible indices. -/
theorem Hull.map {α β : Term} {X Y : Term → Prop}
    (hmem : ∀ γ, X γ → wf γ = true → lt γ α = true → Hull β Y γ)
    (hpsi : ∀ σ, wf σ = true → isRT σ = true → lt α σ = true → lt β σ = true) {γ : Term}
    (h : Hull α X γ) : Hull β Y γ := by
  induction h with
  | zero => exact Hull.zero
  | mem hX hw hlt => exact hmem _ hX hw hlt
  | add hw _ _ iha ihb => exact Hull.add hw iha ihb
  | inacc hw _ ihb => exact Hull.inacc hw ihb
  | psi hw hσα _ _ ihσ ihb => exact Hull.psi hw (hpsi _ (wf_psi hw).2.1 (wf_psi hw).1 hσα) ihσ ihb

theorem Hull.mono {α : Term} {X Y : Term → Prop}
    (h : ∀ γ, X γ → wf γ = true → lt γ α = true → Y γ) {β : Term} (hb : Hull α X β) :
    Hull α Y β :=
  hb.map (fun γ hX hw hlt => Hull.mem (h γ hX hw hlt) hw hlt) (fun _ _ _ h => h)

theorem Hull.congr {α : Term} {X Y : Term → Prop}
    (h : ∀ γ, wf γ = true → lt γ α = true → (X γ ↔ Y γ)) (β : Term) :
    Hull α X β ↔ Hull α Y β :=
  ⟨Hull.mono (fun γ hX hw hlt => (h γ hw hlt).mp hX),
    Hull.mono (fun γ hY hw hlt => (h γ hw hlt).mpr hY)⟩

/-- Regular terms above `α` lie above everything below `α⁺`. -/
theorem lt_of_lt_nr {α β σ : Term} (wα : wf α = true) (wβ : wf β = true) (wσ : wf σ = true)
    (hσR : isRT σ = true) (h1 : lt α σ = true) (h2 : lt β (nr α) = true) : lt β σ = true :=
  lt_of_lt_of_le wβ (nr_spec α wα).1 wσ h2 (nr_least α wα σ wσ hσR h1)

/-- Raising the parameter inside the same interval below the next regular term. -/
theorem Hull.raise {α β : Term} {X : Term → Prop} (wα : wf α = true) (wβ : wf β = true)
    (h1 : lt α β = true) (h2 : lt β (nr α) = true) {γ : Term} (hγ : Hull α X γ) :
    Hull β X γ :=
  hγ.map (fun _ hX hw hlt => Hull.mem hX hw (lt_trans hw wα wβ hlt h1))
    (fun _ wσ hσR hσ => lt_of_lt_nr wα wβ wσ hσR hσ h2)

theorem Hull.lower_aux {X : Term → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α : Term}
    (wα : wf α = true) : ∀ γ β : Term, wf β = true → le α β = true → Hull β X γ →
      Hull α X γ ∨ (X γ ∧ lt γ β = true) := by
  intro γ
  induction γ using size_induction with
  | h γ ih =>
    intro β wβ hαβ h
    have conv : ∀ c : Term, size c < size γ → Hull β X c → Hull α X c := by
      intro c hc hcβ
      have wc := hcβ.wf_of
      refine (ih c hc β wβ hαβ hcβ).elim id (fun ⟨hXc, _⟩ => ?_)
      cases hca : lt c α with
      | true => exact Hull.mem hXc wc hca
      | false =>
        exact (ih c hc c wc (le_of_not_lt wα wc hca) (HX c hXc)).resolve_right
          (fun ⟨_, h⟩ => by rw [lt_irrefl] at h; cases h)
    cases h with
    | zero => exact Or.inl Hull.zero
    | mem hX _ hlt => exact Or.inr ⟨hX, hlt⟩
    | add hw ha hb =>
      exact Or.inl (Hull.add hw (conv _ (by size_omega) ha) (conv _ (by size_omega) hb))
    | inacc hw hb => exact Or.inl (Hull.inacc hw (conv _ (by size_omega) hb))
    | psi hw hσβ hσ hb =>
      exact Or.inl (Hull.psi hw (lt_of_le_of_lt wα wβ (wf_psi hw).2.1 hαβ hσβ)
        (conv _ (by size_omega) hσ) (conv _ (by size_omega) hb))

/-- `α ≤ β ⇒ C^β(X) ⊆ C^α(X)`, provided every element of `X` belongs to its own hull. -/
theorem Hull.lower {X : Term → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {α β : Term}
    (wα : wf α = true) (wβ : wf β = true) (hαβ : le α β = true) {γ : Term} (h : Hull β X γ) :
    Hull α X γ := by
  have wγ := h.wf_of
  refine (Hull.lower_aux HX wα γ β wβ hαβ h).elim id (fun ⟨hX, _⟩ => ?_)
  cases hγα : lt γ α with
  | true => exact Hull.mem hX wγ hγα
  | false =>
    exact (Hull.lower_aux HX wα γ γ wγ (le_of_not_lt wα wγ hγα) (HX γ hX)).resolve_right
      (fun ⟨_, h⟩ => by rw [lt_irrefl] at h; cases h)

theorem Hull.sub_of_lt_nr {X : Term → Prop} (HX : ∀ γ, X γ → Hull γ X γ) {β γ : Term}
    (wβ : wf β = true) (wγ : wf γ = true) (h : lt γ (nr β) = true) {x : Term}
    (hx : Hull β X x) : Hull γ X x := by
  rcases lt_trichotomy wγ wβ with h' | rfl | h'
  · exact Hull.lower HX wγ wβ (le_of_lt h') hx
  · exact hx
  · exact Hull.raise wβ wγ h' h hx

/-! ### Well-founded parts -/

theorem acc_of_below {Y Z : Term → Prop} (hY : ∀ x, Y x → wf x = true) :
    ∀ β : Term, Acc (Rel Z) β → wf β = true → (∀ x, Y x → lt x β = true → Z x) →
      Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    intro wβ hb
    refine Acc.intro β ?_
    intro x hx
    exact ih x ⟨hb x hx.1 hx.2, hx.2⟩ (hY x hx.1)
      (fun x' hx' hx'x => hb x' hx' (lt_trans (hY x' hx') (hY x hx.1) wβ hx'x hx.2))

theorem acc_sub {Y Z : Term → Prop} (h : ∀ x, Y x → Z x) :
    ∀ β : Term, Acc (Rel Z) β → Acc (Rel Y) β := by
  intro β hacc
  induction hacc with
  | intro β _ ih =>
    exact Acc.intro β (fun x hx => ih x ⟨h x hx.1, hx.2⟩)

theorem WPart.congr {Y Z : Term → Prop} (h : ∀ x, Y x ↔ Z x) (β : Term) :
    WPart Y β ↔ WPart Z β :=
  Iff.intro (fun hb => ⟨(h β).mp hb.1, acc_sub (fun x hx => (h x).mpr hx) β hb.2⟩)
    (fun hb => ⟨(h β).mpr hb.1, acc_sub (fun x hx => (h x).mp hx) β hb.2⟩)

theorem WPart.down {Y : Term → Prop} {β γ : Term} (hβ : WPart Y β) (hγ : Y γ)
    (h : lt γ β = true) : WPart Y γ :=
  ⟨hγ, hβ.2.inv ⟨hγ, h⟩⟩

/-! ### Distinguished sets -/

theorem Dist.mem_wf {X : Term → Prop} (hX : Dist X) {β : Term} (h : X β) : wf β = true :=
  hX.1 β h

theorem Dist.self {X : Term → Prop} (hX : Dist X) {γ : Term} (hγ : X γ) :
    WPart (Hull γ X) γ := by
  have wγ := hX.mem_wf hγ
  exact ((hX.2 γ wγ ⟨γ, hγ, le_refl γ⟩ γ).mpr ⟨hγ, (nr_spec γ wγ).2.2⟩).1

theorem Dist.self_hull {X : Term → Prop} (hX : Dist X) {γ : Term} (hγ : X γ) : Hull γ X γ :=
  (hX.self hγ).1

theorem Dist.hull {X : Term → Prop} (hX : Dist X) {γ : Term} (hγ : X γ) {β : Term}
    (wβ : wf β = true) : Hull β X γ := by
  have wγ := hX.mem_wf hγ
  cases h : lt γ β with
  | true => exact Hull.mem hγ wγ h
  | false =>
    exact Hull.lower (fun _ h => hX.self_hull h) wβ wγ (le_of_not_lt wβ wγ h) (hX.self_hull hγ)

theorem Dist.acc {X : Term → Prop} (hX : Dist X) {δ : Term} (hδ : X δ) : Acc (Rel X) δ := by
  have wδ := hX.mem_wf hδ
  exact acc_of_below hX.1 δ (hX.self hδ).2 wδ (fun x hx hxδ => Hull.mem hx (hX.mem_wf hx) hxδ)

/-- Comparability of distinguished sets, proved by a double induction along `X` and `Y`. -/
theorem dist_claim {X Y : Term → Prop} (hX : Dist X) (hY : Dist Y) :
    ∀ δ, X δ → (∃ ε, Y ε ∧ le δ ε = true) → Y δ ∧ (∀ ε, Y ε → lt ε δ = true → X ε) := by
  have key : ∀ δ, Acc (Rel X) δ → X δ → (∃ ε, Y ε ∧ le δ ε = true) →
      Y δ ∧ (∀ ε, Y ε → lt ε δ = true → X ε) := by
    intro δ hacc
    induction hacc with
    | intro δ _ ihX =>
      intro hδ hδY
      obtain ⟨ε₀, hε₀, hδε₀⟩ := hδY
      have wδ := hX.mem_wf hδ
      have wε₀ := hY.mem_wf hε₀
      have s1 : ∀ x, X x → lt x δ = true → Y x := fun x hx hxδ =>
        (ihX x ⟨hx, hxδ⟩ hx
          ⟨ε₀, hε₀, le_of_lt (lt_of_lt_of_le (hX.mem_wf hx) wδ wε₀ hxδ hδε₀)⟩).1
      have key2 : ∀ ε, Acc (Rel Y) ε → Y ε → lt ε δ = true → X ε := by
        intro ε hacc'
        induction hacc' with
        | intro ε _ ihY =>
          intro hε hεδ
          have wε := hY.mem_wf hε
          have agree : ∀ γ, wf γ = true → lt γ ε = true → (X γ ↔ Y γ) := fun γ wγ hγε =>
            Iff.intro (fun hγ => s1 γ hγ (lt_trans wγ wε wδ hγε hεδ))
              (fun hγ => ihY γ ⟨hγ, hγε⟩ hγ (lt_trans wγ wε wδ hγε hεδ))
          have hxε : WPart (Hull ε X) ε := (WPart.congr (Hull.congr agree) ε).mpr (hY.self hε)
          exact ((hX.2 ε wε ⟨δ, hδ, le_of_lt hεδ⟩ ε).mp ⟨hxε, (nr_spec ε wε).2.2⟩).1
      have s2 : ∀ ε, Y ε → lt ε δ = true → X ε := fun ε hε => key2 ε (hY.acc hε) hε
      refine ⟨?_, s2⟩
      have agree : ∀ γ, wf γ = true → lt γ δ = true → (X γ ↔ Y γ) := fun γ _ hγδ =>
        Iff.intro (fun hγ => s1 γ hγ hγδ) (fun hγ => s2 γ hγ hγδ)
      have hyδ : WPart (Hull δ Y) δ := (WPart.congr (Hull.congr agree) δ).mp (hX.self hδ)
      exact ((hY.2 δ wδ ⟨ε₀, hε₀, hδε₀⟩ δ).mp ⟨hyδ, (nr_spec δ wδ).2.2⟩).1
  intro δ hδ
  exact key δ (hX.acc hδ) hδ

theorem dist_agree {X Y : Term → Prop} (hX : Dist X) (hY : Dist Y) {α : Term}
    (wα : wf α = true) (hαX : ∃ δ, X δ ∧ le α δ = true) (hαY : ∃ ε, Y ε ∧ le α ε = true) :
    ∀ β, lt β (nr α) = true → (X β ↔ Y β) := by
  obtain ⟨δ, hδ, hαδ⟩ := hαX
  obtain ⟨ε, hε, hαε⟩ := hαY
  have agree : ∀ γ, wf γ = true → lt γ α = true → (X γ ↔ Y γ) := fun γ wγ hγα =>
    Iff.intro
      (fun hγ => (dist_claim hX hY γ hγ
        ⟨ε, hε, le_of_lt (lt_of_lt_of_le wγ wα (hY.mem_wf hε) hγα hαε)⟩).1)
      (fun hγ => (dist_claim hY hX γ hγ
        ⟨δ, hδ, le_of_lt (lt_of_lt_of_le wγ wα (hX.mem_wf hδ) hγα hαδ)⟩).1)
  have hc := Hull.congr agree
  intro β hβ
  exact Iff.intro
    (fun hb => ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mp
      ⟨(WPart.congr hc β).mp ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)
    (fun hb => ((hX.2 α wα ⟨δ, hδ, hαδ⟩ β).mp
      ⟨(WPart.congr hc β).mpr ((hY.2 α wα ⟨ε, hε, hαε⟩ β).mpr ⟨hb, hβ⟩).1, hβ⟩).1)

/-! ### The maximal distinguished set -/

theorem wmax_dist : Dist Wmax := by
  refine ⟨fun β hβ => hβ.elim (fun X h => h.1.mem_wf h.2), ?_⟩
  intro α wα hα β
  obtain ⟨δ, ⟨X₀, hX₀, hδ⟩, hαδ⟩ := hα
  have hnα := nr_spec α wα
  have agreeW : ∀ γ, lt γ (nr α) = true → (Wmax γ ↔ X₀ γ) := by
    intro γ hγ
    refine Iff.intro ?_ (fun h => ⟨X₀, hX₀, h⟩)
    intro hW
    obtain ⟨Y, hY, hγY⟩ := hW
    have wγ := hY.mem_wf hγY
    cases hγα : lt γ α with
    | false =>
      exact (dist_agree hX₀ hY wα ⟨δ, hδ, hαδ⟩ ⟨γ, hγY, le_of_not_lt wα wγ hγα⟩ γ hγ).mpr hγY
    | true =>
      exact (dist_agree hX₀ hY wγ
        ⟨δ, hδ, le_of_lt (lt_of_lt_of_le wγ wα (hX₀.mem_wf hδ) hγα hαδ)⟩
        ⟨γ, hγY, le_refl γ⟩ γ (nr_spec γ wγ).2.2).mpr hγY
  have hc : ∀ x, Hull α Wmax x ↔ Hull α X₀ x :=
    Hull.congr (fun γ wγ hγα => agreeW γ (lt_trans wγ wα hnα.1 hγα hnα.2.2))
  rw [WPart.congr hc β, hX₀.2 α wα ⟨δ, hδ, hαδ⟩ β]
  exact Iff.intro (fun h => ⟨(agreeW β h.2).mpr h.1, h.2⟩) (fun h => ⟨(agreeW β h.2).mp h.1, h.2⟩)

theorem wmax_wf {β : Term} (h : Wmax β) : wf β = true := wmax_dist.mem_wf h

theorem wmax_self {γ : Term} (h : Wmax γ) : WPart (Hull γ Wmax) γ := wmax_dist.self h

theorem wmax_hull {γ : Term} (h : Wmax γ) {β : Term} (wβ : wf β = true) : Hull β Wmax γ :=
  wmax_dist.hull h wβ

theorem wmax_acc {δ : Term} (h : Wmax δ) : Acc (Rel Wmax) δ := wmax_dist.acc h

theorem HW : ∀ γ, Wmax γ → Hull γ Wmax γ := fun _ h => wmax_dist.self_hull h

/-- Members of `C^β(Wmax)` bounded by an element of `Wmax` below `β⁺` belong to `Wmax`. -/
theorem wmax_bounded {α β δ : Term} (wβ : wf β = true) (hα : Hull β Wmax α) (hδ : Wmax δ)
    (hαδ : le α δ = true) (hδβ : lt δ (nr β) = true) : Wmax α := by
  have wδ := wmax_wf hδ
  have wα := hα.wf_of
  have hα' : Hull δ Wmax α := Hull.sub_of_lt_nr HW wβ wδ hδβ hα
  rcases (le_iff α δ).mp hαδ with e | hlt
  · rw [e]
    exact hδ
  · have hw := WPart.down (wmax_self hδ) hα' hlt
    exact ((wmax_dist.2 δ wδ ⟨δ, hδ, le_refl δ⟩ α).mp
      ⟨hw, lt_trans wα wδ (nr_spec δ wδ).1 hlt (nr_spec δ wδ).2.2⟩).1

theorem wmax_good {γ : Term} (h : Wmax γ) : Good γ :=
  ⟨HW γ h, fun _ hβ hlt => wmax_bounded (wmax_wf h) hβ h (le_of_lt hlt) (nr_spec _ (wmax_wf h)).2.2⟩

theorem acc_hull_of_wmax {μ δ : Term} (hδ : Wmax δ)
    (h : ∀ x, Hull μ Wmax x → lt x δ = true → Wmax x) : Acc (Rel (Hull μ Wmax)) δ :=
  acc_of_below (fun _ hx => hx.wf_of) δ (wmax_acc hδ) (wmax_wf hδ) h

/-! ### Extending `Wmax` -/

/-- The extension hypothesis: below `α`, the well-founded parts of the hulls `C^γ(Wmax)` up to
`γ⁺ ≤ α` contain no new elements. -/
def Hyp (α : Term) : Prop := ∀ γ, wf γ = true → le (nr γ) α = true → ∀ β,
  WPart (Hull γ Wmax) β → lt β (nr γ) = true → Wmax β

def Ext (α β : Term) : Prop := WPart (Hull α Wmax) β ∧ lt β (nr α) = true

theorem wmax_of_good_hyp {α : Term} (hG : Good α) (hH : Hyp α) : Wmax α := by
  have wα := hG.1.wf_of
  have hnα := nr_spec α wα
  have accα : ∀ x, Wmax x → lt x α = true → Acc (Rel (Hull α Wmax)) x := fun x hx hxα =>
    acc_hull_of_wmax hx (fun x' hx' hx'x =>
      hG.2 x' hx' (lt_trans hx'.wf_of (wmax_wf hx) wα hx'x hxα))
  have agree : ∀ β, lt β α = true → (Ext α β ↔ Wmax β) := fun β hβα =>
    ⟨fun hb => hG.2 β hb.1.1 hβα, fun hb => ⟨⟨Hull.mem hb (wmax_wf hb) hβα, accα β hb hβα⟩,
      lt_trans (wmax_wf hb) wα hnα.1 hβα hnα.2.2⟩⟩
  have hYwf : ∀ β, Ext α β → wf β = true := fun β hb => hb.1.1.wf_of
  refine ⟨Ext α, ⟨hYwf, ?_⟩,
    ⟨⟨hG.1, Acc.intro α (fun x hx => accα x (hG.2 x hx.1 hx.2) hx.2)⟩, hnα.2.2⟩⟩
  intro γ wγ ⟨ε, hε, hγε⟩ β
  have hnγ := nr_spec γ wγ
  have hnγnα := nr_least γ wγ (nr α) hnα.1 hnα.2.1 (lt_of_le_of_lt wγ (hYwf ε hε) hnα.1 hγε hε.2)
  have split : le (nr γ) α = true ∨ lt α (nr γ) = true :=
    (lt_trichotomy hnγ.1 wα).elim (fun h => Or.inl (le_of_lt h))
      (fun h => h.elim (fun e => Or.inl (by rw [e]; exact le_refl α)) Or.inr)
  rcases split with hle | hgt
  · have hγα : lt γ α = true := lt_of_lt_of_le wγ hnγ.1 wα hnγ.2.2 hle
    rw [WPart.congr (Hull.congr (fun x wx hxγ => agree x (lt_trans wx wγ wα hxγ hγα))) β]
    constructor
    · intro hb
      exact ⟨(agree β (lt_of_lt_of_le hb.1.1.wf_of hnγ.1 wα hb.2 hle)).mpr
        (hH γ wγ hle β hb.1 hb.2), hb.2⟩
    · intro hb
      have wb := hYwf β hb.1
      have hbW := (agree β (lt_of_lt_of_le wb hnγ.1 wα hb.2 hle)).mp hb.1
      refine ⟨?_, hb.2⟩
      cases hβγ : lt β γ with
      | false => exact ((wmax_dist.2 γ wγ ⟨β, hbW, le_of_not_lt wγ wb hβγ⟩ β).mpr ⟨hbW, hb.2⟩).1
      | true =>
        exact ⟨Hull.mem hbW wb hβγ, acc_hull_of_wmax hbW (fun x hx hxβ => wmax_bounded wb
          (Hull.lower HW wb wγ (le_of_lt hβγ) hx) hbW (le_of_lt hxβ) (nr_spec β wb).2.2)⟩
  · have heqn : nr γ = nr α := le_antisymm hnγnα (nr_least α wα (nr γ) hnγ.1 hnγ.2.1 hgt)
    have hc : ∀ x, Hull γ (Ext α) x ↔ Hull α Wmax x := by
      rcases lt_trichotomy wγ wα with hγα | rfl | hαγ
      · intro x
        rw [Hull.congr (fun x wx hxγ => agree x (lt_trans wx wγ wα hxγ hγα)) x]
        exact ⟨Hull.raise wγ wα hγα hgt, Hull.lower HW wγ wα (le_of_lt hγα)⟩
      · exact Hull.congr (fun x _ hxγ => agree x hxγ)
      · intro x
        exact ⟨Hull.map (fun _ hY _ _ => hY.1.1) (fun _ wσ _ h => lt_trans wα wγ wσ hαγ h),
          Hull.map (fun _ hW hw hlt => Hull.mem ((agree _ hlt).mpr hW) hw
            (lt_trans hw wα wγ hlt hαγ))
            (fun _ wσ hσR h => lt_of_lt_nr wα wγ wσ hσR h (by rw [← heqn]; exact hnγ.2.2))⟩
    rw [WPart.congr hc β, heqn]
    exact ⟨fun hb => ⟨⟨hb.1, hb.2⟩, hb.2⟩, fun hb => ⟨hb.1.1, hb.2⟩⟩

end OCF.Jaeger.Term

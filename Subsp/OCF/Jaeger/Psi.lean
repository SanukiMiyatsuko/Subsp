import Subsp.OCF.Jaeger.Ordinal

/-! Inaccessibles (from `LargeCardinals`), the collapsing functions ψ and the term sets T. -/

namespace OCF.Jaeger

universe u

open Ordinal

noncomputable section

def EnumDef (X : Ordinal.{u} → Prop) (α : Ordinal.{u}) : Prop :=
  ∃ ξ, X ξ ∧ ∀ β, β < α → enum X β < ξ

section Enum

variable {X : Ordinal.{u} → Prop}

theorem EnumDef.of_le {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β ≤ α) : EnumDef X β := by
  cases h with
  | intro ξ hξ =>
    exact Exists.intro ξ (And.intro hξ.1 (fun γ hγ => hξ.2 γ (lt_of_lt_of_le hγ hβ)))

theorem EnumDef.mem {α : Ordinal.{u}} (h : EnumDef X α) : X (enum X α) := (enum_spec X α h).1

theorem EnumDef.lt {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β < α) :
    enum X β < enum X α := (enum_spec X α h).2 β hβ

theorem EnumDef.le_of_le {α β : Ordinal.{u}} (h : EnumDef X α) (hβ : β ≤ α) :
    enum X β ≤ enum X α := by
  cases hβ with
  | inl hβ => exact le_of_lt (h.lt hβ)
  | inr hβ => rw [hβ]; exact le_refl _

theorem enum_le_of {α ξ : Ordinal.{u}} (hX : X ξ) (h : ∀ β, β < α → enum X β < ξ) :
    enum X α ≤ ξ := enum_le X α ξ hX h

theorem enum_eq_zero {α : Ordinal.{u}} (h : ¬ EnumDef X α) : enum X α = 0 := by
  rw [enum_eq]
  unfold least
  exact dite_eq_right h

theorem EnumDef.of_ne_zero {α : Ordinal.{u}} (h : enum X α ≠ 0) : EnumDef X α :=
  Classical.byContradiction (fun hn => h (enum_eq_zero hn))

theorem EnumDef.le_enum {α : Ordinal.{u}} (h : EnumDef X α) : α ≤ enum X α := by
  induction α using lt_wellFounded.induction with
  | h α ih =>
    apply le_of_not_lt
    intro hlt
    exact not_lt_of_le (ih _ hlt (h.of_le (le_of_lt hlt))) (h.lt hlt)

theorem EnumDef.lt_iff {α β : Ordinal.{u}} (hα : EnumDef X α) (hβ : EnumDef X β) :
    enum X β < enum X α ↔ β < α := by
  apply Iff.intro
  · intro h
    apply lt_of_not_le
    intro hle
    exact not_lt_of_le (hβ.le_of_le hle) h
  · exact hα.lt

theorem EnumDef.inj {α β : Ordinal.{u}} (hα : EnumDef X α) (hβ : EnumDef X β)
    (e : enum X α = enum X β) : α = β := by
  cases lt_total α β with
  | inl h => exact absurd e (ne_of_lt (hβ.lt h))
  | inr h =>
    cases h with
    | inl h => exact h
    | inr h => exact absurd e (ne_of_gt (hα.lt h))

theorem enum_surj {α ξ : Ordinal.{u}} (hX : X ξ) (hξ : ξ ≤ enum X α) :
    ∃ β, β ≤ α ∧ enum X β = ξ := by
  cases Ordinal.exists_min (fun β => ξ ≤ enum X β) (Exists.intro α hξ) with
  | intro β hβ =>
    have hβα : β ≤ α := le_of_not_lt (fun hlt => hβ.2 α hlt hξ)
    exact Exists.intro β (And.intro hβα (le_antisymm
      (enum_le_of hX (fun γ hγ => lt_of_not_le (hβ.2 γ hγ))) hβ.1))

def LimClosed (X : Ordinal.{u} → Prop) : Prop := ∀ ξ, IsLimitPoint X ξ → X ξ

theorem IsLimitPoint.isLimit {ξ : Ordinal.{u}} (h : IsLimitPoint X ξ) : IsLimit ξ := by
  apply And.intro h.1
  intro β hβ
  cases h.2 β hβ with
  | intro a ha => exact lt_of_le_of_lt (succ_le_of_lt ha.2.1) ha.2.2

theorem enum_limit (hX : LimClosed X) {l : Ordinal.{u}} (hl : IsLimit l)
    (h : ∀ β, β < l → EnumDef X β) : EnumDef X l ∧ enum X l = supLt l (enum X) := by
  have hlt : ∀ β, β < l → enum X β < supLt l (enum X) := by
    intro β hβ
    exact lt_of_lt_of_le ((h (succ β) (hl.2 β hβ)).lt (lt_succ_self β))
      (le_supLt l (enum X) (hl.2 β hβ))
  have hXs : X (supLt l (enum X)) := by
    apply hX
    apply And.intro (lt_of_le_of_lt (zero_le _) (hlt 0 hl.1))
    intro η hη
    cases (lt_supLt_iff l (enum X) η).mp hη with
    | intro β hβ => exact Exists.intro (enum X β) (And.intro (h β hβ.1).mem
        (And.intro hβ.2 (hlt β hβ.1)))
  have hdef : EnumDef X l := Exists.intro _ (And.intro hXs hlt)
  refine And.intro hdef (le_antisymm (enum_le_of hXs hlt) ?_)
  exact (supLt_le_iff _ _ _).mpr (fun β hβ => le_of_lt (hdef.lt hβ))

theorem enum_below_regular {θ : Ordinal.{u}} (hθ : IsRegular θ)
    (hunb : ∀ η, η < θ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < θ) :
    ∀ α, α < θ → EnumDef X α ∧ enum X α < θ := by
  intro α
  induction α using lt_wellFounded.induction with
  | h α ih =>
    intro hα
    have hs : supLt α (enum X) < θ :=
      hθ.supLt_lt hα (fun β hβ => (ih β hβ (lt_trans β α θ hβ hα)).2)
    cases hunb _ hs with
    | intro ξ hξ =>
      have hbelow : ∀ β, β < α → enum X β < ξ :=
        fun β hβ => lt_of_le_of_lt (le_supLt α (enum X) hβ) hξ.2.1
      exact And.intro (Exists.intro ξ (And.intro hξ.1 hbelow))
        (lt_of_le_of_lt (enum_le_of hξ.1 hbelow) hξ.2.2)

theorem enum_fixed_regular {θ : Ordinal.{u}} (hθ : IsRegular θ)
    (hunb : ∀ η, η < θ → ∃ ξ, X ξ ∧ η < ξ ∧ ξ < θ) (hXθ : X θ) :
    EnumDef X θ ∧ enum X θ = θ := by
  have hb := enum_below_regular hθ hunb
  have hdef : EnumDef X θ := Exists.intro θ (And.intro hXθ (fun β hβ => (hb β hβ).2))
  exact And.intro hdef (le_antisymm (enum_le_of hXθ (fun β hβ => (hb β hβ).2)) hdef.le_enum)

end Enum

theorem subset_closure {A : Ordinal.{u} → Prop} {ξ : Ordinal.{u}} (h : A ξ) : closure A ξ :=
  (closure_iff A ξ).mpr (Or.inl h)

theorem isLimitPoint_of_closure {A : Ordinal.{u} → Prop} {ξ : Ordinal.{u}}
    (h : IsLimitPoint (closure A) ξ) : IsLimitPoint A ξ := by
  apply And.intro h.1
  intro η hη
  cases h.2 η hη with
  | intro b hb =>
    cases (closure_iff A b).mp hb.1 with
    | inl hA => exact Exists.intro b (And.intro hA hb.2)
    | inr hlp =>
      cases hlp.2 η hb.2.1 with
      | intro a ha => exact Exists.intro a (And.intro ha.1 (And.intro ha.2.1
          (lt_trans a b ξ ha.2.2 hb.2.2)))

theorem closure_limClosed (A : Ordinal.{u} → Prop) : LimClosed (closure A) :=
  fun ξ h => (closure_iff A ξ).mpr (Or.inr (isLimitPoint_of_closure h))

theorem enum_closure_zero_mem {A : Ordinal.{u} → Prop} (h : EnumDef (closure A) 0) :
    A (enum (closure A) 0) := by
  cases (closure_iff A _).mp h.mem with
  | inl hA => exact hA
  | inr hlp =>
    cases hlp.2 0 hlp.1 with
    | intro a ha =>
      have := enum_le_of (X := closure A) (α := 0) (subset_closure ha.1)
        (fun β hβ => absurd hβ (not_lt_zero β))
      exact absurd (lt_of_lt_of_le ha.2.2 this) (lt_irrefl a)

theorem enum_closure_succ_mem {A : Ordinal.{u} → Prop} {β : Ordinal.{u}}
    (h : EnumDef (closure A) (succ β)) : A (enum (closure A) (succ β)) := by
  cases (closure_iff A _).mp h.mem with
  | inl hA => exact hA
  | inr hlp =>
    cases hlp.2 _ (h.lt (lt_succ_self β)) with
    | intro a ha =>
      have hβ : EnumDef (closure A) β := h.of_le (le_of_lt (lt_succ_self β))
      have := enum_le_of (X := closure A) (α := succ β) (subset_closure ha.1)
        (fun γ hγ => lt_of_le_of_lt (hβ.le_of_le (le_of_lt_succ hγ)) ha.2.1)
      exact absurd (lt_of_lt_of_le ha.2.2 this) (lt_irrefl a)

theorem R.omega_lt {ξ : Ordinal.{u}} (h : R ξ) : omega < ξ := h.1

theorem R.regular {ξ : Ordinal.{u}} (h : R ξ) : IsRegular ξ := h.2

theorem R.pos {ξ : Ordinal.{u}} (h : R ξ) : 0 < ξ := h.2.pos

theorem R.isLimit {ξ : Ordinal.{u}} (h : R ξ) : IsLimit ξ := h.2.isLimit

theorem R.isPrincipal {ξ : Ordinal.{u}} (h : R ξ) : IsPrincipal ξ := h.2.isPrincipal

def ISet (n : Nat) (ξ : Ordinal.{u}) : Prop := R ξ ∧ ∀ m, m < n → I m ξ = ξ

def IX (n : Nat) : Ordinal.{u} → Prop := closure (ISet n)

theorem I_eq_fun (n : Nat) : I.{u} n = enum (IX n) := by
  rw [I_eq]
  rfl

theorem I_eq_enum (n : Nat) (β : Ordinal.{u}) : I n β = enum (IX n) β := by
  rw [I_eq_fun]

theorem IX.omega_lt {n : Nat} {ξ : Ordinal.{u}} (h : IX n ξ) : omega < ξ := by
  cases (closure_iff _ ξ).mp h with
  | inl h => exact h.1.omega_lt
  | inr h =>
    cases h.2 0 h.1 with
    | intro a ha => exact lt_trans _ _ _ ha.1.1.omega_lt ha.2.2

theorem IX.pos {n : Nat} {ξ : Ordinal.{u}} (h : IX n ξ) : 0 < ξ :=
  lt_of_le_of_lt (zero_le _) h.omega_lt

theorem IX.isPrincipal {n : Nat} {ξ : Ordinal.{u}} (h : IX n ξ) : IsPrincipal ξ := by
  cases (closure_iff _ ξ).mp h with
  | inl h => exact h.1.isPrincipal
  | inr h =>
    apply And.intro (ne_of_gt h.1)
    apply addPrincipal_of_limit
    intro η hη
    cases h.2 η hη with
    | intro a ha =>
      exact Exists.intro a (And.intro ha.1.1.isPrincipal.2 (And.intro ha.2.1 (le_of_lt ha.2.2)))

theorem IX.isLimit {n : Nat} {ξ : Ordinal.{u}} (h : IX n ξ) : IsLimit ξ := by
  cases (closure_iff _ ξ).mp h with
  | inl h => exact h.1.isLimit
  | inr h => exact h.isLimit

theorem I_ne_zero_iff (n : Nat) (β : Ordinal.{u}) : I n β ≠ 0 ↔ EnumDef (IX n) β := by
  rw [I_eq_enum]
  apply Iff.intro
  · exact EnumDef.of_ne_zero
  · intro h
    exact ne_of_gt h.mem.pos

theorem iSet_iff (n : Nat) (ξ : Ordinal.{u}) : ISet n ξ ↔ Inaccessible n ξ := by
  induction n using Nat.strongRecOn generalizing ξ with
  | ind n ih =>
    rw [inaccessible_iff]
    apply Iff.intro
    · intro h
      refine And.intro h.1 (fun m hm β hβ => ?_)
      have hfix : I m ξ = ξ := h.2 m hm
      have hdef : EnumDef (IX m) ξ := by
        apply (I_ne_zero_iff m ξ).mp
        rw [hfix]
        exact ne_of_gt h.1.pos
      have hsβ : succ β < ξ := h.1.isLimit.succ_lt hβ
      have hdef' : EnumDef (IX m) (succ β) := hdef.of_le (le_of_lt hsβ)
      have hmem : ISet m (enum (IX m) (succ β)) := enum_closure_succ_mem hdef'
      have hlt := hdef.lt hsβ
      rw [← I_eq_enum m ξ, hfix] at hlt
      exact Exists.intro _ (And.intro (lt_of_lt_of_le (lt_succ_self β) hdef'.le_enum)
        (And.intro hlt ((ih m hm _).mp hmem)))
    · intro h
      refine And.intro h.1 (fun m hm => ?_)
      have hunb : ∀ η, η < ξ → ∃ ζ, IX m ζ ∧ η < ζ ∧ ζ < ξ := by
        intro η hη
        cases h.2 m hm η hη with
        | intro μ hμ =>
          exact Exists.intro μ (And.intro (subset_closure ((ih m hm μ).mpr hμ.2.2))
            (And.intro hμ.1 hμ.2.1))
      have hXξ : IX m ξ := by
        apply (closure_iff _ ξ).mpr
        apply Or.inr
        apply And.intro h.1.pos
        intro η hη
        cases h.2 m hm η hη with
        | intro μ hμ => exact Exists.intro μ (And.intro ((ih m hm μ).mpr hμ.2.2)
            (And.intro hμ.1 hμ.2.1))
      rw [I_eq_enum]
      exact (enum_fixed_regular h.1.regular hunb hXξ).2

theorem exists_least_nat (P : Nat → Prop) (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, m < n → ¬ P m := by
  cases h with
  | intro n hn =>
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hm : ∃ m, m < n ∧ P m
      · cases hm with
        | intro m hm => exact ih m hm.1 hm.2
      · exact Exists.intro n (And.intro hn (fun m hmn hPm => hm (Exists.intro m
          (And.intro hmn hPm))))

class LargeCardinals : Prop where
  out : NInaccessiblesExist.{u}

section Hypothesis

variable [LargeCardinals.{u}]

theorem exists_iSet (n : Nat) : ∃ ξ : Ordinal.{u}, ISet n ξ := by
  have H : NInaccessiblesExist.{u} := LargeCardinals.out
  cases H n with
  | intro κ hκ => exact Exists.intro κ ((iSet_iff n κ).mpr hκ)

theorem enumDef_IX_zero (n : Nat) : EnumDef (IX.{u} n) 0 := by
  cases exists_iSet.{u} n with
  | intro ξ hξ =>
    exact Exists.intro ξ (And.intro (subset_closure hξ) (fun β hβ => absurd hβ (not_lt_zero β)))

omit [LargeCardinals.{u}] in
theorem δ_eq (n : Nat) : δ.{u} n = enum (IX n) 0 := I_eq_enum n 0

theorem δ_mem (n : Nat) : ISet n (δ.{u} n) := by
  rw [δ_eq]
  exact enum_closure_zero_mem (enumDef_IX_zero n)

omit [LargeCardinals.{u}] in
theorem δ_le {n : Nat} {ξ : Ordinal.{u}} (h : IX n ξ) : δ n ≤ ξ := by
  rw [δ_eq]
  exact enum_le_of h (fun β hβ => absurd hβ (not_lt_zero β))

theorem δ_lt_δ_succ (n : Nat) : δ.{u} n < δ (n + 1) := by
  have h := (iSet_iff _ _).mp (δ_mem.{u} (n + 1))
  rw [inaccessible_iff] at h
  cases h.2 n (Nat.lt_succ_self n) 0 h.1.pos with
  | intro μ hμ => exact lt_of_le_of_lt (δ_le (subset_closure ((iSet_iff n μ).mpr hμ.2.2))) hμ.2.1

theorem δ_lt {m n : Nat} (h : m < n) : δ.{u} m < δ n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero m)
  | succ n ih =>
    cases Nat.lt_succ_iff_lt_or_eq.mp h with
    | inl h' => exact lt_trans _ _ _ (ih h') (δ_lt_δ_succ n)
    | inr h' => rw [h']; exact δ_lt_δ_succ n

theorem δ_lt_Λ₀ (n : Nat) : δ.{u} n < Λ₀ :=
  lt_of_lt_of_le (δ_lt_δ_succ n) (δ_le_Λ₀ (n + 1))

theorem omega_lt_δ (n : Nat) : omega < δ.{u} n := (δ_mem n).1.omega_lt

theorem omega_lt_Λ₀ : omega < (Λ₀ : Ordinal.{u}) := lt_trans _ _ _ (omega_lt_δ 0) (δ_lt_Λ₀ 0)

theorem Λ₀_pos : (0 : Ordinal.{u}) < Λ₀ := lt_of_le_of_lt (zero_le _) omega_lt_Λ₀

theorem isLimit_Λ₀ : IsLimit (Λ₀ : Ordinal.{u}) := by
  apply And.intro Λ₀_pos
  intro β hβ
  cases (lt_Λ₀_iff β).mp hβ with
  | intro n hn => exact lt_trans _ _ _ ((δ_mem n).1.isLimit.succ_lt hn) (δ_lt_Λ₀ n)

theorem isPrincipal_Λ₀ : IsPrincipal (Λ₀ : Ordinal.{u}) := by
  apply And.intro (ne_of_gt Λ₀_pos)
  intro x y hx hy
  cases (lt_Λ₀_iff x).mp hx with
  | intro n hn =>
    cases (lt_Λ₀_iff y).mp hy with
    | intro m hm =>
      have hR := (δ_mem (n + m)).1
      have hxn : x < δ (n + m) := lt_of_lt_of_le hn (δ_le_of_le (Nat.le_add_right n m))
      have hym : y < δ (n + m) := lt_of_lt_of_le hm (δ_le_of_le (Nat.le_add_left m n))
      exact lt_trans _ _ _ (hR.regular.add_lt hxn hym) (δ_lt_Λ₀ _)
where
  δ_le_of_le {a b : Nat} (h : a ≤ b) : δ.{u} a ≤ δ b := by
    cases Nat.lt_or_eq_of_le h with
    | inl h => exact le_of_lt (δ_lt h)
    | inr h => rw [h]; exact le_refl _

theorem I_domain (n : Nat) {α : Ordinal.{u}} (hα : α < Λ₀) :
    EnumDef (IX n) α ∧ I n α < Λ₀ := by
  cases (lt_Λ₀_iff α).mp hα with
  | intro k hk =>
    have hkj : k < k + n + 1 := by omega
    have hnj : n < k + n + 1 := by omega
    have hαj : α < δ (k + n + 1) := lt_trans _ _ _ hk (δ_lt hkj)
    have hinac := (inaccessible_iff _ _).mp ((iSet_iff _ _).mp (δ_mem.{u} (k + n + 1)))
    have hunb : ∀ η, η < δ (k + n + 1) → ∃ ξ, IX n ξ ∧ η < ξ ∧ ξ < δ (k + n + 1) := by
      intro η hη
      cases hinac.2 n hnj η hη with
      | intro μ hμ =>
        exact Exists.intro μ (And.intro (subset_closure ((iSet_iff n μ).mpr hμ.2.2))
          (And.intro hμ.1 hμ.2.1))
    have h := enum_below_regular hinac.1.regular hunb α hαj
    rw [I_eq_enum]
    exact And.intro h.1 (lt_trans _ _ _ h.2 (δ_lt_Λ₀ _))

theorem I_def (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : EnumDef (IX n) β := (I_domain n hβ).1

theorem I_lt_Λ₀ (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : I n β < Λ₀ := (I_domain n hβ).2

theorem I_mem (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : IX n (I n β) := by
  rw [I_eq_enum]
  exact (I_def n hβ).mem

theorem le_I (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : β ≤ I n β := by
  rw [I_eq_enum]
  exact (I_def n hβ).le_enum

theorem I_lt_I_iff (n : Nat) {β γ : Ordinal.{u}} (hβ : β < Λ₀) (hγ : γ < Λ₀) :
    I n β < I n γ ↔ β < γ := by
  rw [I_eq_enum, I_eq_enum]
  exact (I_def n hγ).lt_iff (I_def n hβ)

theorem I_lt_I (n : Nat) {β γ : Ordinal.{u}} (hβγ : β < γ) (hγ : γ < Λ₀) : I n β < I n γ :=
  (I_lt_I_iff n (lt_trans _ _ _ hβγ hγ) hγ).mpr hβγ

theorem I_le_I (n : Nat) {β γ : Ordinal.{u}} (hβγ : β ≤ γ) (hγ : γ < Λ₀) : I n β ≤ I n γ := by
  cases hβγ with
  | inl h => exact le_of_lt (I_lt_I n h hγ)
  | inr h => rw [h]; exact le_refl _

theorem I_inj (n : Nat) {β γ : Ordinal.{u}} (hβ : β < Λ₀) (hγ : γ < Λ₀) (e : I n β = I n γ) :
    β = γ := by
  rw [I_eq_enum, I_eq_enum] at e
  exact (I_def n hβ).inj (I_def n hγ) e

theorem I_pos (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : 0 < I n β := (I_mem n hβ).pos

theorem omega_lt_I (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : omega < I n β :=
  (I_mem n hβ).omega_lt

omit [LargeCardinals.{u}] in
theorem I_zero_eq_δ (n : Nat) : I.{u} n 0 = δ n := rfl

theorem I_limit (n : Nat) {l : Ordinal.{u}} (hl : IsLimit l) (hlΛ : l < Λ₀) :
    I n l = supLt l (I n) := by
  rw [I_eq_fun]
  exact (enum_limit (closure_limClosed _) hl
    (fun β hβ => I_def n (lt_trans _ _ _ hβ hlΛ))).2

theorem I_surj (n : Nat) {ξ : Ordinal.{u}} (hξ : IX n ξ) (hξΛ : ξ < Λ₀) :
    ∃ β, β < Λ₀ ∧ I n β = ξ := by
  have hle : ξ ≤ enum (IX n) ξ := by
    rw [← I_eq_enum]
    exact le_I n hξΛ
  cases enum_surj hξ hle with
  | intro β hβ =>
    rw [← I_eq_enum] at hβ
    exact Exists.intro β (And.intro (lt_of_le_of_lt hβ.1 hξΛ) hβ.2)

omit [LargeCardinals.{u}] in

theorem le_I_of_ne_zero (n : Nat) {β : Ordinal.{u}} (h : I n β ≠ 0) : β ≤ I n β := by
  have hdef := (I_ne_zero_iff n β).mp h
  rw [I_eq_enum]
  exact hdef.le_enum

theorem IX.fixed {m n : Nat} (hmn : m < n) {ξ : Ordinal.{u}} (h : IX n ξ) (hξ : ξ < Λ₀) :
    I m ξ = ξ := by
  cases (closure_iff _ ξ).mp h with
  | inl h => exact h.2 m hmn
  | inr h =>
    apply le_antisymm _ (le_I m hξ)
    rw [I_limit m h.isLimit hξ]
    apply (supLt_le_iff _ _ _).mpr
    intro y hy
    cases h.2 y hy with
    | intro s hs =>
      have hsΛ := lt_trans _ _ _ hs.2.2 hξ
      have := I_lt_I m hs.2.1 hsΛ
      rw [hs.1.2 m hmn] at this
      exact le_of_lt (lt_trans _ _ _ this hs.2.2)

theorem I_normal (n : Nat) :
    (∀ β, β < Λ₀ → I.{u} n β < Λ₀) ∧
    (∀ β γ, β < γ → γ < Λ₀ → I.{u} n β < I n γ) ∧
    (∀ l, IsLimit l → l < Λ₀ → I.{u} n l = supLt l (I n)) :=
  And.intro (fun _ h => I_lt_Λ₀ n h)
    (And.intro (fun _ _ h h' => I_lt_I n h h') (fun _ h h' => I_limit n h h'))

theorem lemma_3_1_a (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) :
    R (I.{u} n 0) ∧ R (I n (succ β)) := by
  rw [I_eq_enum, I_eq_enum]
  exact And.intro (enum_closure_zero_mem (I_def n Λ₀_pos)).1
    (enum_closure_succ_mem (I_def n (isLimit_Λ₀.succ_lt hβ))).1

theorem lemma_3_1_b {m n : Nat} (h : m < n) {β : Ordinal.{u}} (hβ : β < Λ₀) :
    I m (I n β) = I n β :=
  IX.fixed h (I_mem n hβ) (I_lt_Λ₀ n hβ)

theorem lemma_3_1_c (n : Nat) {β γ : Ordinal.{u}} (hβγ : β < γ) (hγ : γ < Λ₀) :
    I n β < I n γ := I_lt_I n hβγ hγ

theorem lemma_3_1_d {m n : Nat} (h : m < n) : I.{u} m 0 < I n 0 := δ_lt h

theorem lemma_3_1_e (n : Nat) : ordNat n ≤ I.{u} n 0 :=
  le_of_lt (lt_trans _ _ _ (ordNat_lt_omega n) (omega_lt_δ n))

theorem theorem_3_2 (n₁ n₂ : Nat) {β₁ β₂ : Ordinal.{u}} (h₁ : β₁ < Λ₀) (h₂ : β₂ < Λ₀) :
    I n₁ β₁ = I n₂ β₂ ↔
      (n₁ < n₂ ∧ β₁ = I n₂ β₂) ∨ (n₁ = n₂ ∧ β₁ = β₂) ∨ (n₂ < n₁ ∧ I n₁ β₁ = β₂) := by
  cases Nat.lt_trichotomy n₁ n₂ with
  | inl h =>
    have key : I n₁ β₁ = I n₂ β₂ ↔ β₁ = I n₂ β₂ := by
      apply Iff.intro
      · intro e
        apply I_inj n₁ h₁ (I_lt_Λ₀ n₂ h₂)
        rw [lemma_3_1_b h h₂]
        exact e
      · intro e
        rw [e, lemma_3_1_b h h₂]
    rw [key]
    apply Iff.intro
    · intro e
      exact Or.inl (And.intro h e)
    · intro hc
      cases hc with
      | inl hc => exact hc.2
      | inr hc =>
        cases hc with
        | inl hc => exact absurd hc.1 (Nat.ne_of_lt h)
        | inr hc => exact absurd hc.1 (Nat.lt_asymm h)
  | inr h =>
    cases h with
    | inl h =>
      rw [h]
      apply Iff.intro
      · intro e
        exact Or.inr (Or.inl (And.intro rfl (I_inj n₂ h₁ h₂ e)))
      · intro hc
        cases hc with
        | inl hc => exact absurd hc.1 (Nat.lt_irrefl n₂)
        | inr hc =>
          cases hc with
          | inl hc => rw [hc.2]
          | inr hc => exact absurd hc.1 (Nat.lt_irrefl n₂)
    | inr h =>
      have key : I n₁ β₁ = I n₂ β₂ ↔ I n₁ β₁ = β₂ := by
        apply Iff.intro
        · intro e
          apply I_inj n₂ (I_lt_Λ₀ n₁ h₁) h₂
          rw [lemma_3_1_b h h₁]
          exact e
        · intro e
          rw [← e, lemma_3_1_b h h₁]
      rw [key]
      apply Iff.intro
      · intro e
        exact Or.inr (Or.inr (And.intro h e))
      · intro hc
        cases hc with
        | inl hc => exact absurd hc.1 (Nat.lt_asymm h)
        | inr hc =>
          cases hc with
          | inl hc => exact absurd hc.1.symm (Nat.ne_of_lt h)
          | inr hc => exact hc.2

theorem theorem_3_3 (n₁ n₂ : Nat) {β₁ β₂ : Ordinal.{u}} (h₁ : β₁ < Λ₀) (h₂ : β₂ < Λ₀) :
    I n₁ β₁ < I n₂ β₂ ↔
      (n₁ < n₂ ∧ β₁ < I n₂ β₂) ∨ (n₁ = n₂ ∧ β₁ < β₂) ∨ (n₂ < n₁ ∧ I n₁ β₁ < β₂) := by
  cases Nat.lt_trichotomy n₁ n₂ with
  | inl h =>
    have key : I n₁ β₁ < I n₂ β₂ ↔ β₁ < I n₂ β₂ := by
      have e := lemma_3_1_b h h₂
      apply Iff.intro
      · intro hc
        rw [← e] at hc
        exact (I_lt_I_iff n₁ h₁ (I_lt_Λ₀ n₂ h₂)).mp hc
      · intro hc
        rw [← e]
        exact (I_lt_I_iff n₁ h₁ (I_lt_Λ₀ n₂ h₂)).mpr hc
    rw [key]
    apply Iff.intro
    · intro hc
      exact Or.inl (And.intro h hc)
    · intro hc
      cases hc with
      | inl hc => exact hc.2
      | inr hc =>
        cases hc with
        | inl hc => exact absurd hc.1 (Nat.ne_of_lt h)
        | inr hc => exact absurd hc.1 (Nat.lt_asymm h)
  | inr h =>
    cases h with
    | inl h =>
      rw [h, I_lt_I_iff n₂ h₁ h₂]
      apply Iff.intro
      · intro hc
        exact Or.inr (Or.inl (And.intro rfl hc))
      · intro hc
        cases hc with
        | inl hc => exact absurd hc.1 (Nat.lt_irrefl n₂)
        | inr hc =>
          cases hc with
          | inl hc => exact hc.2
          | inr hc => exact absurd hc.1 (Nat.lt_irrefl n₂)
    | inr h =>
      have key : I n₁ β₁ < I n₂ β₂ ↔ I n₁ β₁ < β₂ := by
        have e := lemma_3_1_b h h₁
        apply Iff.intro
        · intro hc
          rw [← e] at hc
          exact (I_lt_I_iff n₂ (I_lt_Λ₀ n₁ h₁) h₂).mp hc
        · intro hc
          rw [← e]
          exact (I_lt_I_iff n₂ (I_lt_Λ₀ n₁ h₁) h₂).mpr hc
      rw [key]
      apply Iff.intro
      · intro hc
        exact Or.inr (Or.inr (And.intro h hc))
      · intro hc
        cases hc with
        | inl hc => exact absurd hc.1 (Nat.lt_asymm h)
        | inr hc =>
          cases hc with
          | inl hc => exact absurd hc.1.symm (Nat.ne_of_lt h)
          | inr hc => exact hc.2

theorem not_isLimit_of_lt_regular {n : Nat} {β γ : Ordinal.{u}} (hR : R γ) (hβ : β < γ)
    (hγ : γ < Λ₀) (e : I n β = γ) : ¬ IsLimit β := by
  intro hl
  have hsup : supLt β (I n) = γ := by
    rw [← e]
    exact (I_limit n hl (lt_trans _ _ _ hβ hγ)).symm
  have hcof : CofinalFrom β γ := by
    refine Exists.intro (fun x => I n (type ((representative β).below x))) (And.intro ?_ hsup)
    intro x
    rw [← e]
    exact I_lt_I n (initial_lt β x) (lt_trans _ _ _ hβ hγ)
  have hcf : cf γ ≤ β := least_le _ hcof
  rw [hR.regular.2] at hcf
  exact not_lt_of_le hcf hβ

omit [LargeCardinals.{u}] in

theorem NFI.lt {γ β : Ordinal.{u}} {n : Nat} (h : NFI γ n β) (hR : R γ) : β < γ := by
  have hne : I n β ≠ 0 := by
    rw [← h.1]
    exact ne_of_gt hR.pos
  have hle := le_I_of_ne_zero n hne
  rw [← h.1] at hle
  apply lt_of_le_of_ne hle
  intro e
  rw [e] at h
  exact h.2 hR.isLimit

omit [LargeCardinals.{u}] in
theorem NFI.lt_Λ₀ {γ β : Ordinal.{u}} {n : Nat} (h : NFI γ n β) (hR : R γ) (hγ : γ < Λ₀) :
    β < Λ₀ := lt_trans _ _ _ (h.lt hR) hγ

theorem theorem_3_4 {γ : Ordinal.{u}} (hR : R γ) (hγ : γ < Λ₀) :
    ∃ n β, NFI γ n β ∧ ∀ n' β', NFI γ n' β' → n' = n ∧ β' = β := by
  have hex : ∃ k, γ < I k γ := by
    cases (lt_Λ₀_iff γ).mp hγ with
    | intro k hk => exact Exists.intro k (lt_of_lt_of_le hk (I_le_I k (zero_le γ) hγ))
  cases exists_least_nat _ hex with
  | intro n hn =>
    have hset : ISet n γ := by
      refine And.intro hR (fun m hm => ?_)
      exact le_antisymm (le_of_not_lt (hn.2 m hm)) (le_I m hγ)
    cases I_surj n (subset_closure hset) hγ with
    | intro β hβ =>
      have hβγ : β < γ := by
        apply lt_of_le_of_ne (by rw [← hβ.2]; exact le_I n hβ.1)
        intro e
        rw [e] at hβ
        rw [hβ.2] at hn
        exact lt_irrefl γ hn.1
      have hNF : NFI γ n β :=
        And.intro hβ.2.symm (not_isLimit_of_lt_regular hR hβγ hγ hβ.2)
      refine Exists.intro n (Exists.intro β (And.intro hNF ?_))
      intro n' β' h'
      have hβ' := h'.lt_Λ₀ hR hγ
      have e : I n' β' = I n β := h'.1.symm.trans hNF.1
      cases (theorem_3_2 n' n hβ' hβ.1).mp e with
      | inl hc =>
        rw [hc.2, ← hNF.1] at h'
        exact absurd hR.isLimit h'.2
      | inr hc =>
        cases hc with
        | inl hc => exact hc
        | inr hc =>
          rw [← hc.2, ← h'.1] at hβγ
          exact absurd hβγ (lt_irrefl γ)

theorem NFI.unique {γ β β' : Ordinal.{u}} {n n' : Nat} (h : NFI γ n β) (h' : NFI γ n' β')
    (hR : R γ) (hγ : γ < Λ₀) : n = n' ∧ β = β' := by
  cases theorem_3_4 hR hγ with
  | intro m hm =>
    cases hm with
    | intro b hb =>
      have e1 := hb.2 n β h
      have e2 := hb.2 n' β' h'
      exact And.intro (e1.1.trans e2.1.symm) (e1.2.trans e2.2.symm)

theorem R_of_NFI {γ β : Ordinal.{u}} {n : Nat} (h : NFI γ n β) (hβ : β < Λ₀) : R γ := by
  rw [h.1]
  cases zero_or_succ_of_not_isLimit h.2 with
  | inl h0 =>
    rw [h0]
    exact (lemma_3_1_a n Λ₀_pos).1
  | inr hs =>
    cases hs with
    | intro b hb =>
      rw [hb]
      rw [hb] at hβ
      exact (lemma_3_1_a n (lt_trans _ _ _ (lt_succ_self b) hβ)).2

theorem regPred_I_zero (n : Nat) : regPred (I.{u} n 0) = 0 := by
  apply regPred_eq_zero
  intro h
  cases h with
  | intro m hm =>
    cases hm with
    | intro β hβ =>
      have hR := (lemma_3_1_a n Λ₀_pos.{u}).1
      have hΛ := I_lt_Λ₀ n Λ₀_pos.{u}
      have := (NFI.unique (And.intro rfl not_isLimit_zero) hβ hR hΛ).2
      exact succ_ne_zero β this.symm

theorem regPred_I_succ (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) :
    regPred (I n (succ β)) = I n β := by
  have hsΛ := isLimit_Λ₀.succ_lt hβ
  have hR := (lemma_3_1_a n hβ).2
  have hΛ := I_lt_Λ₀ n hsΛ
  cases regPred_spec _ (Exists.intro n (Exists.intro β (And.intro rfl (not_isLimit_succ β)))) with
  | intro m hm =>
    cases hm with
    | intro b hb =>
      have e := NFI.unique (And.intro rfl (not_isLimit_succ β)) hb.1 hR hΛ
      rw [hb.2, ← e.1, ← succ_inj e.2]

theorem regPred_of_NFI {γ β : Ordinal.{u}} {n : Nat} (h : NFI γ n β) (hβ : β < Λ₀) :
    (β = 0 ∧ regPred γ = 0) ∨ ∃ b, β = succ b ∧ regPred γ = I n b := by
  rw [h.1]
  cases zero_or_succ_of_not_isLimit h.2 with
  | inl h0 =>
    rw [h0]
    exact Or.inl (And.intro rfl (regPred_I_zero n))
  | inr hs =>
    cases hs with
    | intro b hb =>
      rw [hb] at hβ
      refine Or.inr (Exists.intro b (And.intro hb ?_))
      rw [hb]
      exact regPred_I_succ n (lt_trans _ _ _ (lt_succ_self b) hβ)

theorem regPred_lt {κ : Ordinal.{u}} (hR : R κ) (hκ : κ < Λ₀) : regPred κ < κ := by
  cases theorem_3_4 hR hκ with
  | intro n hn =>
    cases hn with
    | intro β hβ =>
      have hβΛ := hβ.1.lt_Λ₀ hR hκ
      cases regPred_of_NFI hβ.1 hβΛ with
      | inl h => rw [h.2]; exact hR.pos
      | inr h =>
        cases h with
        | intro b hb =>
          rw [hb.2, hβ.1.1, hb.1]
          rw [hb.1] at hβΛ
          exact I_lt_I n (lt_succ_self b) hβΛ

theorem lemma_3_5 {α ξ : Nat} {η β : Ordinal.{u}} (hαξ : α ≤ ξ) (hη : η < Λ₀) (hβ : β < Λ₀)
    (hlt : I ξ η < I α β) (hβL : ¬ IsLimit β) : I ξ η ≤ regPred (I α β) := by
  cases zero_or_succ_of_not_isLimit hβL with
  | inl h0 =>
    rw [h0] at hlt
    have h1 : I α 0 ≤ I ξ 0 := by
      cases Nat.lt_or_eq_of_le hαξ with
      | inl h => exact le_of_lt (δ_lt h)
      | inr h => rw [h]; exact le_refl _
    exact absurd hlt (not_lt_of_le (le_trans h1 (I_le_I ξ (zero_le η) hη)))
  | inr hs =>
    cases hs with
    | intro β₀ hβ₀ =>
      have hβ₀Λ : β₀ < Λ₀ := by
        rw [hβ₀] at hβ
        exact lt_trans _ _ _ (lt_succ_self β₀) hβ
      rw [hβ₀, regPred_I_succ α hβ₀Λ]
      rw [hβ₀] at hlt hβ
      cases Nat.lt_or_eq_of_le hαξ with
      | inl h =>
        have h1 : I ξ η < succ β₀ := by
          rw [← lemma_3_1_b h hη] at hlt
          exact (I_lt_I_iff α (I_lt_Λ₀ ξ hη) hβ).mp hlt
        exact le_trans (le_of_lt_succ h1) (le_I α hβ₀Λ)
      | inr h =>
        rw [← h] at hlt
        rw [← h]
        exact I_le_I α (le_of_lt_succ ((I_lt_I_iff α hη hβ).mp hlt)) hβ₀Λ

theorem lemma_3_6_a (n : Nat) : δ.{u} n < δ (n + 1) ∧ δ.{u} (n + 1) < Λ₀ :=
  And.intro (δ_lt_δ_succ n) (δ_lt_Λ₀ (n + 1))

theorem lemma_3_6_b (n : Nat) : ordNat n < I.{u} n 0 ∧ I.{u} n 0 < Λ₀ :=
  And.intro (lt_trans _ _ _ (ordNat_lt_omega n) (omega_lt_δ n)) (δ_lt_Λ₀ n)

theorem lemma_3_6_c : ¬ R (Λ₀ : Ordinal.{u}) := by
  intro hR
  have hcof : CofinalFrom omega (Λ₀ : Ordinal.{u}) := by
    refine Exists.intro (fun x => δ (natOf (type ((representative omega).below x))))
      (And.intro (fun x => δ_lt_Λ₀ _) ?_)
    apply le_antisymm
    · exact (sup_le_iff _ _).mpr (fun x => le_of_lt (δ_lt_Λ₀ _))
    · apply (sup_le_iff _ _).mpr
      intro n
      cases initial_surjective omega (ordNat n.down) (ordNat_lt_omega n.down) with
      | intro x hx =>
        have := le_sup (fun x : (representative (omega : Ordinal.{u})).Carrier =>
          δ (natOf (type ((representative omega).below x)))) x
        rw [← hx, natOf_ordNat] at this
        exact this
  have hcf : cf (Λ₀ : Ordinal.{u}) ≤ omega := least_le _ hcof
  rw [hR.regular.2] at hcf
  exact not_lt_of_le hcf omega_lt_Λ₀

theorem Λ₀_eq_least :
    (Λ₀ : Ordinal.{u}) = least (fun ξ => 0 < ξ ∧ ∀ n : Nat, ordNat n < ξ → I n 0 < ξ) := by
  have hΛ : (0 : Ordinal.{u}) < Λ₀ ∧ ∀ n : Nat, ordNat n < Λ₀ → I n 0 < Λ₀ :=
    And.intro Λ₀_pos (fun n _ => δ_lt_Λ₀ n)
  have hmin : ∀ ξ : Ordinal.{u}, (0 < ξ ∧ ∀ n : Nat, ordNat n < ξ → I n 0 < ξ) → Λ₀ ≤ ξ := by
    intro ξ hξ
    have h0 : I.{u} 0 0 < ξ := hξ.2 0 hξ.1
    have hω : omega < ξ := lt_trans _ _ _ (omega_lt_δ 0) h0
    apply (sup_le_iff _ _).mpr
    intro n
    exact le_of_lt (hξ.2 n.down (lt_trans _ _ _ (ordNat_lt_omega n.down) hω))
  apply le_antisymm
  · exact hmin _ (least_spec (fun ξ : Ordinal.{u} => 0 < ξ ∧ ∀ n : Nat, ordNat n < ξ → I n 0 < ξ)
      (Exists.intro _ hΛ)).1
  · exact least_le _ hΛ

theorem lemma_3_7_a (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : ordNat n < I n β :=
  lt_trans _ _ _ (ordNat_lt_omega n) (omega_lt_I n hβ)

theorem lemma_3_7_b (n : Nat) {β : Ordinal.{u}} (h : I n β ≠ 0) : I n β < Λ₀ ↔ β < Λ₀ := by
  apply Iff.intro
  · intro hI
    exact lt_of_le_of_lt (le_I_of_ne_zero n h) hI
  · exact I_lt_Λ₀ n

end Hypothesis

end
end OCF.Jaeger

namespace OCF.Jaeger

universe u

open Ordinal

noncomputable section

theorem Cn_induction {κ α : Ordinal.{u}} {motive : Nat → Ordinal.{u} → Prop}
    (pred : ∀ n, motive n (regPred κ))
    (lt_pred : ∀ n γ, γ < regPred κ → motive n γ)
    (add : ∀ n β γ, Cn κ α n β → Cn κ α n γ → motive n β → motive n γ →
      motive (n + 1) (β + γ))
    (inacc : ∀ n m γ, Cn κ α n (ordNat m) → Cn κ α n γ → motive n (ordNat m) → motive n γ →
      motive (n + 1) (I m γ))
    (lt_reg : ∀ n π γ, IsRegBelowΛ₀ π → γ < π → π < κ → Cn κ α n π → motive n π →
      motive (n + 1) γ)
    (psi : ∀ n π γ, γ < α → IsRegBelowΛ₀ π → Cn κ α n γ → Cn κ α n π → C π γ γ →
      motive n γ → motive n π → motive (n + 1) (Ψ π γ))
    {n : Nat} {ξ : Ordinal.{u}} (h : Cn κ α n ξ) : motive n ξ := by
  unfold Cn at h
  induction h with
  | pred n => exact pred n
  | lt_pred n γ hγ => exact lt_pred n γ hγ
  | add n β γ hβ hγ ihβ ihγ => exact add n β γ hβ hγ ihβ ihγ
  | inacc n m γ hm hγ ihm ihγ => exact inacc n m γ hm hγ ihm ihγ
  | lt_reg n π γ hπ hγπ hπκ hπC ih => exact lt_reg n π γ hπ hγπ hπκ hπC ih
  | psi n π γ hγα hπ hγC hπC hγ ihγ ihπ =>
    have h := psi n π γ hγα hπ hγC hπC ((stages_C π γ γ).mp hγ) ihγ ihπ
    rw [← stages_Ψ] at h
    exact h

theorem Cn_zero_inv {κ α ξ : Ordinal.{u}} (h : Cn κ α 0 ξ) : ξ ≤ regPred κ := by
  unfold Cn at h
  cases h with
  | pred => exact le_refl _
  | lt_pred _ _ hγ => exact le_of_lt hγ

theorem Cn_succ_inv {κ α ξ : Ordinal.{u}} {n : Nat} (h : Cn κ α (n + 1) ξ) :
    ξ ≤ regPred κ ∨ (∃ β γ, Cn κ α n β ∧ Cn κ α n γ ∧ ξ = β + γ) ∨
      (∃ m γ, Cn κ α n (ordNat m) ∧ Cn κ α n γ ∧ ξ = I m γ) ∨
      (∃ π, IsRegBelowΛ₀ π ∧ ξ < π ∧ π < κ ∧ Cn κ α n π) ∨
      (∃ π γ, γ < α ∧ IsRegBelowΛ₀ π ∧ Cn κ α n γ ∧ Cn κ α n π ∧ C π γ γ ∧ ξ = Ψ π γ) := by
  unfold Cn at h
  cases h with
  | pred => exact Or.inl (le_refl _)
  | lt_pred _ _ hγ => exact Or.inl (le_of_lt hγ)
  | add _ β γ hβ hγ =>
    exact Or.inr (Or.inl (Exists.intro β (Exists.intro γ (And.intro hβ (And.intro hγ rfl)))))
  | inacc _ m γ hm hγ =>
    exact Or.inr (Or.inr (Or.inl (Exists.intro m (Exists.intro γ
      (And.intro hm (And.intro hγ rfl))))))
  | lt_reg _ π γ hπ hγπ hπκ hπC =>
    exact Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro π
      (And.intro hπ (And.intro hγπ (And.intro hπκ hπC)))))))
  | psi _ π γ hγα hπ hγC hπC hγ =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Exists.intro π (Exists.intro γ
      (And.intro hγα (And.intro hπ (And.intro hγC (And.intro hπC
        (And.intro ((stages_C π γ γ).mp hγ) (stages_Ψ π γ)))))))))))

theorem C_of_Cn {κ α ξ : Ordinal.{u}} {n : Nat} (h : Cn κ α n ξ) : C κ α ξ := Exists.intro n h

theorem C_zero (κ α : Ordinal.{u}) : C κ α 0 := C_of_Cn (Cn_zero κ α 0)

theorem C_regPred (κ α : Ordinal.{u}) : C κ α (regPred κ) := C_of_Cn (Cn_pred κ α 0)

theorem C_of_le_regPred {κ α ξ : Ordinal.{u}} (h : ξ ≤ regPred κ) : C κ α ξ := by
  cases h with
  | inl h => exact C_of_Cn (Cn_lt_pred κ α 0 ξ h)
  | inr h => rw [h]; exact C_regPred κ α

theorem C_lt_reg {κ α π γ : Ordinal.{u}} (hπ : IsRegBelowΛ₀ π) (hγπ : γ < π) (hπκ : π < κ)
    (hπC : C κ α π) : C κ α γ := by
  cases hπC with
  | intro n hn => exact C_of_Cn (Cn_lt_reg κ α n π γ hπ hγπ hπκ hn)

theorem C_psi {κ α π γ : Ordinal.{u}} (hγα : γ < α) (hπ : IsRegBelowΛ₀ π) (hγC : C κ α γ)
    (hπC : C κ α π) (hγ : C π γ γ) : C κ α (Ψ π γ) := by
  cases hγC with
  | intro n hn =>
    cases hπC with
    | intro m hm =>
      exact C_of_Cn (Cn_psi κ α (max n m) π γ hγα hπ (Cn_mono κ α (Nat.le_max_left n m) γ hn)
        (Cn_mono κ α (Nat.le_max_right n m) π hm) hγ)

theorem C_mono_arg {κ α β : Ordinal.{u}} (hαβ : α ≤ β) {ξ : Ordinal.{u}} (h : C κ α ξ) :
    C κ β ξ := by
  cases h with
  | intro n hn => exact C_of_Cn (Cn_mono_arg κ hαβ n ξ hn)

theorem lt_Ψ_iff_C {κ α ξ : Ordinal.{u}} (h : ξ < Ψ κ α) : C κ α ξ := C_of_lt_Ψ κ α ξ h

theorem Ψ_le_of_not_C {κ α ξ : Ordinal.{u}} (h : ¬ C κ α ξ) : Ψ κ α ≤ ξ := least_le _ h

theorem lemma_4_5_a (κ α : Ordinal.{u}) : IsPrincipal (Ψ κ α) := by
  apply And.intro (ne_of_gt (lt_of_le_of_lt (zero_le _) (regPred_lt_Ψ κ α)))
  intro x y hx hy
  apply lt_of_not_le
  intro hle
  cases le_add_cases x y (Ψ κ α) hle (not_lt_of_le (le_of_lt hx)) with
  | intro d hd =>
    have hC := C_add κ α x d (C_of_lt_Ψ κ α x hx) (C_of_lt_Ψ κ α d (lt_of_le_of_lt hd.1 hy))
    rw [← hd.2] at hC
    exact Ψ_not_C κ α hC

theorem IsRegBelowΛ₀.R {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : R κ := h.1

theorem IsRegBelowΛ₀.lt_Λ₀ {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : κ < Λ₀ := h.2

theorem IsRegBelowΛ₀.regular {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : IsRegular κ := h.1.2

theorem IsRegBelowΛ₀.omega_lt {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : omega < κ := h.1.1

theorem IsRegBelowΛ₀.pos {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : 0 < κ := h.1.pos

theorem IsRegBelowΛ₀.Ω_le {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : Ω ≤ κ :=
  δ_le (subset_closure (And.intro h.1 (fun m hm => absurd hm (Nat.not_lt_zero m))))

theorem Ω_eq_δ : (Ω : Ordinal.{u}) = δ 0 := rfl

theorem Cn_Ω (κ α : Ordinal.{u}) : Cn κ α 1 Ω := Cn_inacc κ α 0 0 0 (Cn_zero κ α 0) (Cn_zero κ α 0)

theorem lemma_4_4_a (κ : Ordinal.{u}) {α β : Ordinal.{u}} (hαβ : α ≤ β) :
    (∀ ξ, C κ α ξ → C κ β ξ) ∧ Ψ κ α ≤ Ψ κ β :=
  And.intro (fun _ h => C_mono_arg hαβ h) (Ψ_mono κ hαβ)

section Hypothesis

variable [LargeCardinals.{u}]

theorem IsRegBelowΛ₀.regPred_lt {κ : Ordinal.{u}} (h : IsRegBelowΛ₀ κ) : regPred κ < κ :=
  OCF.Jaeger.regPred_lt h.1 h.2

theorem isRegBelowΛ₀_Ω : IsRegBelowΛ₀ (Ω : Ordinal.{u}) :=
  And.intro (lemma_3_1_a 0 Λ₀_pos.{u}).1 (δ_lt_Λ₀ 0)

theorem omega_lt_Ω : omega < (Ω : Ordinal.{u}) := omega_lt_δ 0

theorem one_lt_Ω : succ 0 < (Ω : Ordinal.{u}) := by
  have h := ordNat_lt_omega.{u} 1
  exact lt_trans _ _ _ h omega_lt_Ω

theorem Ω_le_I (n : Nat) {β : Ordinal.{u}} (hβ : β < Λ₀) : Ω ≤ I n β := by
  have h1 : (Ω : Ordinal.{u}) ≤ I n 0 := by
    cases Nat.eq_zero_or_pos n with
    | inl h => rw [h]; exact le_refl _
    | inr h => exact le_of_lt (δ_lt h)
  exact le_trans h1 (I_le_I n (zero_le β) hβ)

theorem C_of_le_Ω {κ α ξ : Ordinal.{u}} (hΩ : Ω < κ) (hξ : ξ ≤ Ω) : C κ α ξ := by
  cases hξ with
  | inl h => exact C_of_Cn (Cn_lt_reg κ α 1 Ω ξ isRegBelowΛ₀_Ω h hΩ (Cn_Ω κ α))
  | inr h => rw [h]; exact C_of_Cn (Cn_Ω κ α)

theorem Ω_lt_Ψ {κ α : Ordinal.{u}} (hΩ : Ω < κ) : Ω < Ψ κ α := by
  apply lt_of_not_le
  intro h
  exact Ψ_not_C κ α (C_of_le_Ω hΩ h)

theorem Ψ_isLimit {κ α : Ordinal.{u}} (hΩ : Ω < κ) : IsLimit (Ψ κ α) :=
  (lemma_4_5_a κ α).isLimit (lt_trans _ _ _ one_lt_Ω (Ω_lt_Ψ hΩ))

theorem small_Cn {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) :
    ∀ n, Small κ (Cn κ α n) := by
  have hreg := hκ.regular
  have hsucc : succ (regPred κ) < κ := hreg.isLimit.succ_lt hκ.regPred_lt
  intro n
  induction n with
  | zero => exact (small_lt hsucc).mono (fun ξ h => lt_succ_of_le (Cn_zero_inv h))
  | succ n ih =>
    have h1 : Small κ (fun ξ => ξ ≤ regPred κ) :=
      (small_lt hsucc).mono (fun ξ h => lt_succ_of_le h)
    have h2 := Small.image2 hreg ih ih (fun x y => x + y)
    have h3 := Small.image2 hreg ih ih (fun x y => I (natOf x) y)
    have h4 := Small.iUnion (A := fun π z => z < π) hreg
      (ih.mono (A := fun π => Cn κ α n π ∧ π < κ) (fun π h => h.1)) (fun π h => small_lt h.2)
    have h5 := Small.image2 hreg ih ih (fun x y => Ψ x y)
    refine ((((h1.union hreg h2).union hreg h3).union hreg h4).union hreg h5).mono ?_
    intro ξ hξ
    cases Cn_succ_inv hξ with
    | inl h => exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    | inr h =>
      cases h with
      | inl h =>
        cases h with
        | intro β h =>
          cases h with
          | intro γ h =>
            exact Or.inl (Or.inl (Or.inl (Or.inr (Exists.intro β (Exists.intro γ h)))))
      | inr h =>
        cases h with
        | inl h =>
          cases h with
          | intro m h =>
            cases h with
            | intro γ h =>
              refine Or.inl (Or.inl (Or.inr (Exists.intro (ordNat m) (Exists.intro γ
                (And.intro h.1 (And.intro h.2.1 ?_))))))
              show ξ = I (natOf (ordNat m)) γ
              rw [natOf_ordNat]
              exact h.2.2
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | intro π h =>
              exact Or.inl (Or.inr (Exists.intro π (And.intro (And.intro h.2.2.2 h.2.2.1) h.2.1)))
          | inr h =>
            cases h with
            | intro π h =>
              cases h with
              | intro γ h =>
                exact Or.inr (Exists.intro π (Exists.intro γ
                  (And.intro h.2.2.2.1 (And.intro h.2.2.1 h.2.2.2.2.2))))

theorem lemma_4_1 {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) :
    Small κ (C κ α) := by
  have h := Small.iUnion (A := fun x => Cn κ α (natOf x)) hκ.regular (small_natOrd hκ.omega_lt)
    (fun x _ => small_Cn hκ α (natOf x))
  refine h.mono ?_
  intro ξ hξ
  cases hξ with
  | intro n hn =>
    refine Exists.intro (ordNat n) (And.intro (Exists.intro n rfl) ?_)
    show Cn κ α (natOf (ordNat n)) ξ
    rw [natOf_ordNat]
    exact hn

theorem theorem_4_2 {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) :
    regPred κ < Ψ κ α ∧ Ψ κ α < κ := by
  apply And.intro (regPred_lt_Ψ κ α)
  cases exists_not_mem_of_small hκ.regular (lemma_4_1 hκ α) with
  | intro ξ hξ => exact lt_of_le_of_lt (Ψ_le_of_not_C hξ.2) hξ.1

theorem Ψ_lt {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) : Ψ κ α < κ :=
  (theorem_4_2 hκ α).2

theorem Ψ_lt_Λ₀ {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) : Ψ κ α < Λ₀ :=
  lt_trans _ _ _ (Ψ_lt hκ α) hκ.lt_Λ₀

theorem C_lt_Λ₀ {κ α ξ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (h : C κ α ξ) : ξ < Λ₀ := by
  cases h with
  | intro n hn =>
    refine Cn_induction (motive := fun _ ξ => ξ < Λ₀) ?_ ?_ ?_ ?_ ?_ ?_ hn
    · intro _
      exact lt_trans _ _ _ hκ.regPred_lt hκ.lt_Λ₀
    · intro _ γ hγ
      exact lt_trans _ _ _ (lt_trans _ _ _ hγ hκ.regPred_lt) hκ.lt_Λ₀
    · intro _ β γ _ _ hβ hγ
      exact isPrincipal_Λ₀.2 β γ hβ hγ
    · intro _ m γ _ _ _ hγ
      exact I_lt_Λ₀ m hγ
    · intro _ π γ hπ hγπ _ _ _
      exact lt_trans _ _ _ hγπ hπ.lt_Λ₀
    · intro _ π γ _ hπ _ _ _ _ _
      exact Ψ_lt_Λ₀ hπ γ

omit [LargeCardinals.{u}] in
theorem lt_of_I_eq {κ σ : Ordinal.{u}} {ρ : Nat} (hκ : IsRegBelowΛ₀ κ) (h : κ = I ρ σ) :
    σ < Λ₀ := by
  have hne : I ρ σ ≠ 0 := by
    rw [← h]
    exact ne_of_gt hκ.pos
  exact lt_of_le_of_lt (le_I_of_ne_zero ρ hne) (h ▸ hκ.lt_Λ₀)

theorem lemma_4_3_a {κ σ ξ : Ordinal.{u}} {ρ : Nat} (hκ : IsRegBelowΛ₀ κ) (h : κ = I ρ σ)
    (hξ : ξ ≤ ordNat ρ) (α : Ordinal.{u}) : C κ α ξ := by
  cases ρ with
  | zero =>
    have : ξ = 0 := (le_zero_iff ξ).mp hξ
    rw [this]
    exact C_zero κ α
  | succ k =>
    have hσ := lt_of_I_eq hκ h
    have hΩ : Ω < κ := by
      rw [h]
      exact lt_of_lt_of_le (δ_lt (Nat.zero_lt_succ k)) (I_le_I (k + 1) (zero_le σ) hσ)
    exact C_of_le_Ω hΩ (le_of_lt (lt_of_le_of_lt hξ
      (lt_trans _ _ _ (ordNat_lt_omega (k + 1)) omega_lt_Ω)))

theorem lemma_4_3_b {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) : C κ α κ := by
  cases theorem_3_4 hκ.R hκ.lt_Λ₀ with
  | intro ρ h =>
    cases h with
    | intro σ hσ =>
      have hNF := hσ.1
      have hσΛ := hNF.lt_Λ₀ hκ.R hκ.lt_Λ₀
      have hρ : C κ α (ordNat ρ) := lemma_4_3_a hκ hNF.1 (le_refl _) α
      have hσC : C κ α σ := by
        cases regPred_of_NFI hNF hσΛ with
        | inl h0 => rw [h0.1]; exact C_zero κ α
        | inr hs =>
          cases hs with
          | intro b hb =>
            have hbΛ : b < Λ₀ := lt_trans _ _ _ (hb.1 ▸ lt_succ_self b) hσΛ
            have hble : b ≤ regPred κ := by
              rw [hb.2]
              exact le_I ρ hbΛ
            cases hble with
            | inl hlt =>
              rw [hb.1]
              exact C_of_le_regPred (succ_le_of_lt hlt)
            | inr he =>
              have hΩ : Ω < κ := by
                apply lt_of_le_of_lt (Ω_le_I ρ hbΛ)
                rw [hNF.1, hb.1]
                exact I_lt_I ρ (lt_succ_self b) (hb.1 ▸ hσΛ)
              have h1 : C κ α (succ 0) := C_of_le_Ω hΩ (le_of_lt one_lt_Ω)
              have := C_add κ α _ _ (C_regPred κ α) h1
              rw [add_one_eq_succ, ← he, ← hb.1] at this
              exact this
      have := C_inacc κ α ρ σ hρ hσC
      rw [← hNF.1] at this
      exact this

theorem lemma_4_4_b {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) {α β : Ordinal.{u}} (hαβ : α < β)
    (hα : C κ α α) : Ψ κ α < Ψ κ β := by
  have hΨ : C κ β (Ψ κ α) :=
    C_psi hαβ hκ (C_mono_arg (le_of_lt hαβ) hα) (lemma_4_3_b hκ β) hα
  cases Ψ_mono κ (le_of_lt hαβ) with
  | inl h => exact h
  | inr e =>
    rw [e] at hΨ
    exact absurd hΨ (Ψ_not_C κ β)

theorem lemma_4_5_b {κ σ : Ordinal.{u}} {ρ ξ : Nat} (hκ : IsRegBelowΛ₀ κ) (h : κ = I ρ σ)
    (hξρ : ξ < ρ) (α : Ordinal.{u}) : I ξ (Ψ κ α) = Ψ κ α := by
  have hσ := lt_of_I_eq hκ h
  have hψκ := Ψ_lt hκ α
  have hψΛ := Ψ_lt_Λ₀ hκ α
  have hfix : I ξ κ = κ := by
    rw [h]
    exact lemma_3_1_b hξρ hσ
  have hΩ : Ω < κ := by
    rw [h]
    exact lt_of_lt_of_le (δ_lt (Nat.lt_of_le_of_lt (Nat.zero_le ξ) hξρ))
      (I_le_I ρ (zero_le σ) hσ)
  have hex : ∃ β, Ψ κ α < I ξ β := Exists.intro κ (by rw [hfix]; exact hψκ)
  cases Ordinal.exists_min (fun β => Ψ κ α < I ξ β) hex with
  | intro β hβ =>
    have hβκ : β ≤ κ := le_of_not_lt (fun hlt => hβ.2 κ hlt (by rw [hfix]; exact hψκ))
    have hβΛ : β < Λ₀ := lt_of_le_of_lt hβκ hκ.lt_Λ₀
    have hβL : ¬ IsLimit β := by
      intro hl
      have := hβ.1
      rw [I_limit ξ hl hβΛ] at this
      cases (lt_supLt_iff _ _ _).mp this with
      | intro b hb => exact hβ.2 b hb.1 hb.2
    have hβlt : β < κ := lt_of_le_of_ne hβκ (fun e => hβL (e ▸ hκ.R.isLimit))
    have hπκ : I ξ β < κ := by
      rw [← hfix]
      exact I_lt_I ξ hβlt hκ.lt_Λ₀
    have hπ : IsRegBelowΛ₀ (I ξ β) :=
      And.intro (R_of_NFI (And.intro rfl hβL) hβΛ) (lt_trans _ _ _ hπκ hκ.lt_Λ₀)
    have hπC : ¬ C κ α (I ξ β) := fun hC => Ψ_not_C κ α (C_lt_reg hπ hβ.1 hπκ hC)
    have hξC : C κ α (ordNat ξ) := lemma_4_3_a hκ h (le_of_lt (ordNat_lt hξρ)) α
    have hβC : ¬ C κ α β := fun hC => hπC (C_inacc κ α ξ β hξC hC)
    cases zero_or_succ_of_not_isLimit hβL with
    | inl h0 => exact absurd (h0 ▸ C_zero κ α) hβC
    | inr hs =>
      cases hs with
      | intro β₀ hβ₀ =>
        have hβ₀Λ : β₀ < Λ₀ := lt_trans _ _ _ (lt_succ_self β₀) (hβ₀ ▸ hβΛ)
        have hle1 : I ξ β₀ ≤ Ψ κ α :=
          le_of_not_lt (hβ.2 β₀ (by rw [hβ₀]; exact lt_succ_self β₀))
        have hle2 : Ψ κ α ≤ β₀ := by
          apply le_of_not_lt
          intro hlt
          apply hβC
          rw [hβ₀]
          exact C_of_lt_Ψ κ α _ ((Ψ_isLimit hΩ).succ_lt hlt)
        have e1 : Ψ κ α = β₀ := le_antisymm hle2 (le_trans (le_I ξ hβ₀Λ) hle1)
        rw [e1]
        exact le_antisymm (by rw [← e1] at hle1 ⊢; exact e1 ▸ hle1) (le_I ξ hβ₀Λ)

theorem lemma_4_6 {κ γ : Ordinal.{u}} {β : Nat} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u})
    (h₁ : I β γ < κ) (h₂ : γ < Ψ κ α) : I β γ < Ψ κ α := by
  have hγΛ : γ < Λ₀ := lt_trans _ _ _ h₂ (Ψ_lt_Λ₀ hκ α)
  cases theorem_3_4 hκ.R hκ.lt_Λ₀ with
  | intro ρ h =>
    cases h with
    | intro σ hσ =>
      have hNF := hσ.1
      have hσΛ := hNF.lt_Λ₀ hκ.R hκ.lt_Λ₀
      cases Nat.lt_or_ge β ρ with
      | inl hβρ =>
        rw [← lemma_4_5_b hκ hNF.1 hβρ α]
        exact I_lt_I β h₂ (Ψ_lt_Λ₀ hκ α)
      | inr hρβ =>
        have h' : I β γ < I ρ σ := hNF.1 ▸ h₁
        have := lemma_3_5 hρβ hγΛ hσΛ h' hNF.2
        rw [← hNF.1] at this
        exact lt_of_le_of_lt this (theorem_4_2 hκ α).1

theorem lemma_4_7_a {κ γ : Ordinal.{u}} {β : Nat} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u})
    (h : γ < I β γ) : Ψ κ α ≠ I β γ := by
  intro e
  have h₁ : I β γ < κ := e ▸ Ψ_lt hκ α
  have h₂ : γ < Ψ κ α := e ▸ h
  have := lemma_4_6 hκ α h₁ h₂
  rw [e] at this
  exact lt_irrefl _ this

theorem lemma_4_7_b {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α : Ordinal.{u}) :
    ¬ R (Ψ κ α) := by
  intro hR
  cases theorem_3_4 hR (Ψ_lt_Λ₀ hκ α) with
  | intro n h =>
    cases h with
    | intro β hβ =>
      have hlt := hβ.1.lt hR
      have := lemma_4_7_a hκ α (β := n) (γ := β) (hβ.1.1 ▸ hlt)
      exact this hβ.1.1

theorem lemma_4_8_a {κ π : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hπ : IsRegBelowΛ₀ π)
    (α : Ordinal.{u}) (h₁ : Ψ κ α < π) (h₂ : π < κ) : Ψ κ α ≤ regPred π := by
  cases theorem_3_4 hπ.R hπ.lt_Λ₀ with
  | intro ξ h =>
    cases h with
    | intro η hη =>
      have hNF := hη.1
      have hηΛ := hNF.lt_Λ₀ hπ.R hπ.lt_Λ₀
      have hψη : Ψ κ α ≤ η := by
        apply le_of_not_lt
        intro hlt
        have := lemma_4_6 hκ α (β := ξ) (γ := η) (hNF.1 ▸ h₂) hlt
        rw [← hNF.1] at this
        exact lt_asymm this h₁
      have hΩ : Ω < κ := lt_of_le_of_lt hπ.Ω_le h₂
      cases regPred_of_NFI hNF hηΛ with
      | inl h0 =>
        rw [h0.1] at hψη
        exact absurd (lt_of_lt_of_le (Ω_lt_Ψ hΩ) hψη) (not_lt_zero _)
      | inr hs =>
        cases hs with
        | intro b hb =>
          rw [hb.2]
          rw [hb.1] at hψη hηΛ
          have hψb : Ψ κ α ≤ b := by
            cases hψη with
            | inl hlt => exact le_of_lt_succ hlt
            | inr he => exact absurd he ((Ψ_isLimit hΩ).ne_succ b)
          exact le_trans hψb (le_I ξ (lt_trans _ _ _ (lt_succ_self b) hηΛ))

theorem lemma_4_8_b {κ π : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hπ : IsRegBelowΛ₀ π)
    (α : Ordinal.{u}) (h : π < κ) : ¬ (regPred π < Ψ κ α ∧ Ψ κ α < π) := by
  intro h'
  exact not_lt_of_le (lemma_4_8_a hκ hπ α h'.2 h) h'.1

theorem theorem_4_9 {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (α ξ : Ordinal.{u}) :
    (C κ α ξ ∧ ξ < κ) ↔ ξ < Ψ κ α := by
  apply Iff.intro
  · intro h
    cases h.1 with
    | intro n hn =>
      refine Cn_induction (motive := fun _ ξ => ξ < κ → ξ < Ψ κ α) ?_ ?_ ?_ ?_ ?_ ?_ hn h.2
      · intro _ _
        exact (theorem_4_2 hκ α).1
      · intro _ γ hγ _
        exact lt_trans _ _ _ hγ (theorem_4_2 hκ α).1
      · intro _ β γ _ _ ihβ ihγ hlt
        exact (lemma_4_5_a κ α).2 β γ (ihβ (lt_of_le_of_lt (le_add β γ) hlt))
          (ihγ (lt_of_le_of_lt (right_le_add β γ) hlt))
      · intro _ m γ _ hγC _ ihγ hlt
        have hγΛ := C_lt_Λ₀ hκ (C_of_Cn hγC)
        exact lemma_4_6 hκ α hlt (ihγ (lt_of_le_of_lt (le_I m hγΛ) hlt))
      · intro _ π γ _ hγπ hπκ _ ihπ _
        exact lt_trans _ _ _ hγπ (ihπ hπκ)
      · intro _ π γ hγα hπ _ _ hγ _ ihπ hlt
        cases lt_total κ π with
        | inl hκπ =>
          exact lt_of_le_of_lt (lemma_4_8_a hπ hκ γ hlt hκπ) (theorem_4_2 hκ α).1
        | inr h' =>
          cases h' with
          | inl e =>
            rw [← e] at hγ ⊢
            exact lemma_4_4_b hκ hγα hγ
          | inr hπκ =>
            exact lt_trans _ _ _ (Ψ_lt hπ γ) (ihπ hπκ)
  · intro h
    exact And.intro (C_of_lt_Ψ κ α ξ h) (lt_trans _ _ _ h (Ψ_lt hκ α))

theorem lemma_4_10 {κ π : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hπ : IsRegBelowΛ₀ π)
    (hπκ : π < κ) (α β : Ordinal.{u}) :
    (π ≤ Ψ κ α → Ψ π β < Ψ κ α) ∧ (Ψ κ α < π → Ψ κ α < Ψ π β) := by
  apply And.intro
  · intro h
    exact lt_of_lt_of_le (Ψ_lt hπ β) h
  · intro h
    exact lt_of_le_of_lt (lemma_4_8_a hκ hπ α h hπκ) (theorem_4_2 hπ β).1

theorem Ψ_ne_regular {κ π : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hπ : R π) (α : Ordinal.{u}) :
    π ≠ Ψ κ α := fun e => lemma_4_7_b hκ α (e ▸ hπ)

theorem theorem_4_11 {κ₁ κ₂ α₁ α₂ : Ordinal.{u}} (hκ₁ : IsRegBelowΛ₀ κ₁)
    (hκ₂ : IsRegBelowΛ₀ κ₂) (e : Ψ κ₁ α₁ = Ψ κ₂ α₂) (h₁ : C κ₁ α₁ α₁) (h₂ : C κ₂ α₂ α₂) :
    κ₁ = κ₂ ∧ α₁ = α₂ := by
  have hκ : κ₁ = κ₂ := by
    cases lt_total κ₁ κ₂ with
    | inl hlt =>
      have h10 := lemma_4_10 hκ₂ hκ₁ hlt α₂ α₁
      cases lt_or_le (Ψ κ₂ α₂) κ₁ with
      | inl h' => exact absurd e (ne_of_gt (h10.2 h'))
      | inr h' => exact absurd e (ne_of_lt (h10.1 h'))
    | inr h' =>
      cases h' with
      | inl h' => exact h'
      | inr hlt =>
        have h10 := lemma_4_10 hκ₁ hκ₂ hlt α₁ α₂
        cases lt_or_le (Ψ κ₁ α₁) κ₂ with
        | inl h' => exact absurd e (ne_of_lt (h10.2 h'))
        | inr h' => exact absurd e (ne_of_gt (h10.1 h'))
  apply And.intro hκ
  rw [← hκ] at e h₂
  cases lt_total α₁ α₂ with
  | inl hlt => exact absurd e (ne_of_lt (lemma_4_4_b hκ₁ hlt h₁))
  | inr h' =>
    cases h' with
    | inl h' => exact h'
    | inr hlt => exact absurd e (ne_of_gt (lemma_4_4_b hκ₁ hlt h₂))

theorem theorem_4_12 {κ σ γ : Ordinal.{u}} {ρ β : Nat} (hκ : IsRegBelowΛ₀ κ) (hNF : NFI κ ρ σ)
    (α : Ordinal.{u}) (hγ : γ < Λ₀) :
    I β γ < Ψ κ α ↔ (β < ρ ∧ γ < Ψ κ α) ∨ (ρ ≤ β ∧ I β γ < κ) := by
  have hσΛ := hNF.lt_Λ₀ hκ.R hκ.lt_Λ₀
  apply Iff.intro
  · intro h
    have hγψ : γ < Ψ κ α := lt_of_le_of_lt (le_I β hγ) h
    cases Nat.lt_or_ge β ρ with
    | inl hβρ => exact Or.inl (And.intro hβρ hγψ)
    | inr hρβ => exact Or.inr (And.intro hρβ (lt_trans _ _ _ h (Ψ_lt hκ α)))
  · intro h
    cases h with
    | inl h =>
      rw [← lemma_4_5_b hκ hNF.1 h.1 α]
      exact I_lt_I β h.2 (Ψ_lt_Λ₀ hκ α)
    | inr h =>
      have h' : I β γ < I ρ σ := hNF.1 ▸ h.2
      have := lemma_3_5 h.1 hγ hσΛ h' hNF.2
      rw [← hNF.1] at this
      exact lt_of_le_of_lt this (theorem_4_2 hκ α).1

theorem theorem_4_13 {κ₁ κ₂ α₁ α₂ : Ordinal.{u}} (hκ₁ : IsRegBelowΛ₀ κ₁)
    (hκ₂ : IsRegBelowΛ₀ κ₂) (h₁ : C κ₁ α₁ α₁) (h₂ : C κ₂ α₂ α₂) :
    Ψ κ₁ α₁ < Ψ κ₂ α₂ ↔
      (κ₁ < κ₂ ∧ κ₁ < Ψ κ₂ α₂) ∨ (κ₁ = κ₂ ∧ α₁ < α₂) ∨ (κ₂ < κ₁ ∧ Ψ κ₁ α₁ < κ₂) := by
  cases lt_total κ₁ κ₂ with
  | inl hlt =>
    have h10 := lemma_4_10 hκ₂ hκ₁ hlt α₂ α₁
    apply Iff.intro
    · intro h
      refine Or.inl (And.intro hlt ?_)
      cases lt_or_le (Ψ κ₂ α₂) κ₁ with
      | inl h' => exact absurd (h10.2 h') (lt_asymm h)
      | inr h' =>
        exact lt_of_le_of_ne h' (Ψ_ne_regular hκ₂ hκ₁.R α₂)
    · intro h
      cases h with
      | inl h => exact h10.1 (le_of_lt h.2)
      | inr h =>
        cases h with
        | inl h => exact absurd h.1 (ne_of_lt hlt)
        | inr h => exact absurd h.1 (lt_asymm hlt)
  | inr h' =>
    cases h' with
    | inl e =>
      rw [← e] at h₂ ⊢
      apply Iff.intro
      · intro h
        refine Or.inr (Or.inl (And.intro rfl ?_))
        cases lt_total α₁ α₂ with
        | inl h' => exact h'
        | inr h' =>
          cases h' with
          | inl h' => rw [h'] at h; exact absurd h (lt_irrefl _)
          | inr h' => exact absurd (lemma_4_4_b hκ₁ h' h₂) (lt_asymm h)
      · intro h
        cases h with
        | inl h => exact absurd h.1 (lt_irrefl κ₁)
        | inr h =>
          cases h with
          | inl h => exact lemma_4_4_b hκ₁ h.2 h₁
          | inr h => exact absurd h.1 (lt_irrefl κ₁)
    | inr hlt =>
      have h10 := lemma_4_10 hκ₁ hκ₂ hlt α₁ α₂
      apply Iff.intro
      · intro h
        refine Or.inr (Or.inr (And.intro hlt ?_))
        cases lt_or_le (Ψ κ₁ α₁) κ₂ with
        | inl h' => exact h'
        | inr h' => exact absurd (h10.1 h') (lt_asymm h)
      · intro h
        cases h with
        | inl h => exact absurd h.1 (lt_asymm hlt)
        | inr h =>
          cases h with
          | inl h => exact absurd h.1.symm (ne_of_lt hlt)
          | inr h => exact h10.2 h.2

theorem lemma_4_14_a {κ α γ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (h : C κ α γ) {p : Ordinal.{u}}
    (hp : IsComponent γ p) : C κ α p := by
  cases h with
  | intro n hn =>
    refine Cn_induction (motive := fun _ ξ => ∀ p, IsComponent ξ p → C κ α p)
      ?_ ?_ ?_ ?_ ?_ ?_ hn p hp
    · intro _ p hp
      exact C_of_le_regPred hp.le
    · intro _ γ hγ p hp
      exact C_of_le_regPred (le_of_lt (lt_of_le_of_lt hp.le hγ))
    · intro _ β γ _ _ ihβ ihγ p hp
      cases isComponent_add hp with
      | inl h => exact ihβ p h
      | inr h => exact ihγ p h
    · intro n m γ hm hγ _ _ p hp
      have hγΛ := C_lt_Λ₀ hκ (C_of_Cn hγ)
      rw [isComponent_of_principal (I_mem m hγΛ).isPrincipal hp]
      exact C_of_Cn (Cn_inacc κ α n m γ hm hγ)
    · intro n π γ hπ hγπ hπκ hπC _ p hp
      exact C_lt_reg hπ (lt_of_le_of_lt hp.le hγπ) hπκ (C_of_Cn hπC)
    · intro n π γ hγα hπ hγC hπC hγ _ _ p hp
      rw [isComponent_of_principal (lemma_4_5_a π γ) hp]
      exact C_psi hγα hπ (C_of_Cn hγC) (C_of_Cn hπC) hγ

theorem lemma_4_14_a' {κ α γ : Ordinal.{u}} {l : List Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ)
    (hNF : NFSum γ l) (h : C κ α γ) : ∀ p, p ∈ l → C κ α p :=
  fun _ hp => lemma_4_14_a hκ h (Exists.intro l (And.intro hNF.1 hp))

theorem lemma_4_14_b {κ α γ : Ordinal.{u}} {β : Nat} (hκ : IsRegBelowΛ₀ κ) (hγ : γ < I β γ)
    (h : C κ α (I β γ)) : C κ α (ordNat β) ∧ C κ α γ := by
  cases lt_or_le (I β γ) κ with
  | inl hlt =>
    have hψ := (theorem_4_9 hκ α _).mp (And.intro h hlt)
    have hIΛ := C_lt_Λ₀ hκ h
    have hγΛ : γ < Λ₀ := lt_trans _ _ _ hγ hIΛ
    exact And.intro (C_of_lt_Ψ κ α _ (lt_trans _ _ _ (lemma_3_7_a β hγΛ) hψ))
      (C_of_lt_Ψ κ α _ (lt_trans _ _ _ hγ hψ))
  | inr hle =>
    cases h with
    | intro n hn =>
      refine Cn_induction (motive := fun _ ξ => ∀ (β : Nat) γ, γ < I β γ → ξ = I β γ →
          κ ≤ ξ → C κ α (ordNat β) ∧ C κ α γ) ?_ ?_ ?_ ?_ ?_ ?_ hn β γ hγ rfl hle
      · intro _ β γ _ _ hκξ
        exact absurd hκ.regPred_lt (not_lt_of_le hκξ)
      · intro _ x hx β γ _ _ hκξ
        exact absurd (lt_trans _ _ _ hx hκ.regPred_lt) (not_lt_of_le hκξ)
      · intro _ x y hx hy ihx ihy β γ hγ e hκξ
        have hP : IsPrincipal (x + y) := by
          rw [e]
          exact (I_mem β (lt_trans _ _ _ hγ (e ▸ C_lt_Λ₀ hκ (C_of_Cn (Cn_add κ α _ x y hx hy)))))
            |>.isPrincipal
        cases hP.add_cases with
        | inl h' =>
          rw [h'.1] at e hκξ
          exact ihx β γ hγ e hκξ
        | inr h' =>
          rw [h'] at e hκξ
          exact ihy β γ hγ e hκξ
      · intro _ m η hm hη _ ihη β γ hγ e hκξ
        have hηΛ := C_lt_Λ₀ hκ (C_of_Cn hη)
        have hIΛ : I m η < Λ₀ := I_lt_Λ₀ m hηΛ
        have hγΛ : γ < Λ₀ := lt_trans _ _ _ hγ (e ▸ hIΛ)
        cases (theorem_3_2 m β hηΛ hγΛ).mp e with
        | inl hc =>
          rw [hc.2, ← e] at ihη
          exact ihη β γ hγ e hκξ
        | inr hc =>
          cases hc with
          | inl hc =>
            rw [← hc.1, ← hc.2]
            exact And.intro (C_of_Cn hm) (C_of_Cn hη)
          | inr hc =>
            rw [← e, hc.2] at hγ
            exact absurd hγ (lt_irrefl _)
      · intro _ π x _ hxπ hπκ _ _ β γ _ _ hκξ
        exact absurd (lt_trans _ _ _ hxπ hπκ) (not_lt_of_le hκξ)
      · intro _ π x _ hπ _ _ _ _ _ β γ hγ e _
        exact absurd e (lemma_4_7_a hπ x hγ)

theorem lemma_4_14_c {κ π α β : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hπ : IsRegBelowΛ₀ π)
    (hπκ : π < κ) (h : C κ α (Ψ π β)) : C κ α π := by
  have hψ : Ψ π β < Ψ κ α :=
    (theorem_4_9 hκ α _).mp (And.intro h (lt_trans _ _ _ (Ψ_lt hπ β) hπκ))
  have hle : π ≤ Ψ κ α := by
    apply le_of_not_lt
    intro hlt
    exact lt_asymm hψ ((lemma_4_10 hκ hπ hπκ α β).2 hlt)
  exact C_of_lt_Ψ κ α π (lt_of_le_of_ne hle (Ψ_ne_regular hκ hπ.R α))

theorem C_psi_inv {κ α x : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (h : C κ α x)
    (hx : ∃ π β, IsRegBelowΛ₀ π ∧ x = Ψ π β) (hκx : κ ≤ x) :
    ∃ ν ξ, ξ < α ∧ IsRegBelowΛ₀ ν ∧ C κ α ξ ∧ C κ α ν ∧ C ν ξ ξ ∧ x = Ψ ν ξ := by
  cases h with
  | intro n hn =>
    refine Cn_induction (motive := fun _ x => (∃ π β, IsRegBelowΛ₀ π ∧ x = Ψ π β) → κ ≤ x →
        ∃ ν ξ, ξ < α ∧ IsRegBelowΛ₀ ν ∧ C κ α ξ ∧ C κ α ν ∧ C ν ξ ξ ∧ x = Ψ ν ξ)
      ?_ ?_ ?_ ?_ ?_ ?_ hn hx hκx
    · intro _ _ hκξ
      exact absurd hκ.regPred_lt (not_lt_of_le hκξ)
    · intro _ y hy _ hκξ
      exact absurd (lt_trans _ _ _ hy hκ.regPred_lt) (not_lt_of_le hκξ)
    · intro _ y z _ _ ihy ihz hx hκξ
      have hP : IsPrincipal (y + z) := by
        cases hx with
        | intro π h =>
          cases h with
          | intro β h => rw [h.2]; exact lemma_4_5_a π β
      cases hP.add_cases with
      | inl h' =>
        rw [h'.1] at hx hκξ ⊢
        exact ihy hx hκξ
      | inr h' =>
        rw [h'] at hx hκξ ⊢
        exact ihz hx hκξ
    · intro _ m η _ hη _ ihη hx hκξ
      have hηΛ := C_lt_Λ₀ hκ (C_of_Cn hη)
      cases hx with
      | intro π h =>
        cases h with
        | intro β h =>
          cases le_I m hηΛ with
          | inl hlt => exact absurd h.2.symm (lemma_4_7_a h.1 β hlt)
          | inr he =>
            rw [← he] at h hκξ ⊢
            exact ihη (Exists.intro π (Exists.intro β h)) hκξ
    · intro _ π y _ hyπ hπκ _ _ _ hκξ
      exact absurd (lt_trans _ _ _ hyπ hπκ) (not_lt_of_le hκξ)
    · intro _ π γ hγα hπ hγC hπC hγ _ _ _ _
      exact Exists.intro π (Exists.intro γ (And.intro hγα (And.intro hπ (And.intro (C_of_Cn hγC)
        (And.intro (C_of_Cn hπC) (And.intro hγ rfl))))))

theorem lemma_4_14_d {κ π α β : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hπ : IsRegBelowΛ₀ π)
    (hκπ : κ ≤ π) (hβ : C π β β) (hpred : regPred κ < Ψ π β) (h : C κ α (Ψ π β)) :
    β < α ∧ C κ α π ∧ C κ α β := by
  cases hκπ with
  | inr e =>
    rw [← e] at hβ hpred h ⊢
    have hψ : Ψ κ β < Ψ κ α := (theorem_4_9 hκ α _).mp (And.intro h (Ψ_lt hκ β))
    have hβα : β < α := lt_of_not_le (fun hle => not_lt_of_le (Ψ_mono κ hle) hψ)
    exact And.intro hβα (And.intro (lemma_4_3_b hκ α) (C_mono_arg (le_of_lt hβα) hβ))
  | inl hlt =>
    have hκψ : κ ≤ Ψ π β := by
      apply le_of_not_lt
      intro h'
      exact not_lt_of_le (lemma_4_8_a hπ hκ β h' hlt) hpred
    cases C_psi_inv hκ h (Exists.intro π (Exists.intro β (And.intro hπ rfl))) hκψ with
    | intro ν h' =>
      cases h' with
      | intro ξ h' =>
        have e := theorem_4_11 hπ h'.2.1 h'.2.2.2.2.2 hβ h'.2.2.2.2.1
        rw [e.1, e.2]
        exact And.intro h'.1 (And.intro h'.2.2.2.1 h'.2.2.1)

end Hypothesis

end
end OCF.Jaeger

namespace OCF.Jaeger

universe u

open Ordinal

noncomputable section

inductive TD : Ordinal.{u} → Nat → Prop where

  | zero (d : Nat) : TD 0 d

  | sum (d : Nat) (γ : Ordinal.{u}) (l : List Ordinal.{u}) (h0 : 0 < γ) (hNF : NFSum γ l)
      (hl : ∀ p, p ∈ l → TD p d) : TD γ (d + 1)

  | inacc (d β : Nat) (γ : Ordinal.{u}) (hβ : TD (ordNat β) d) (hγ : TD γ d)
      (hlt : γ < I β γ) : TD (I β γ) (d + 1)

  | psi (d : Nat) (κ β : Ordinal.{u}) (hκ : IsRegBelowΛ₀ κ) (hκT : TD κ d) (hβT : TD β d)
      (hβ : C κ β β) : TD (Ψ κ β) (d + 1)

def T (α : Ordinal.{u}) : Prop := ∃ d, TD α d

def G (α : Ordinal.{u}) : Nat :=
  open Classical in
  if h : ∃ d, TD α d then Classical.choose (exists_least_nat (fun d => TD α d) h) else 0

theorem TD.mono {α : Ordinal.{u}} {d : Nat} (h : TD α d) {e : Nat} (hde : d ≤ e) : TD α e := by
  induction h generalizing e with
  | zero _ => exact TD.zero e
  | sum d γ l h0 hNF _ ih =>
    cases e with
    | zero => exact absurd hde (Nat.not_succ_le_zero d)
    | succ e => exact TD.sum e γ l h0 hNF (fun p hp => ih p hp (Nat.le_of_succ_le_succ hde))
  | inacc d β γ _ _ hlt ihβ ihγ =>
    cases e with
    | zero => exact absurd hde (Nat.not_succ_le_zero d)
    | succ e =>
      exact TD.inacc e β γ (ihβ (Nat.le_of_succ_le_succ hde)) (ihγ (Nat.le_of_succ_le_succ hde)) hlt
  | psi d κ β hκ _ _ hβ ihκ ihβ =>
    cases e with
    | zero => exact absurd hde (Nat.not_succ_le_zero d)
    | succ e =>
      exact TD.psi e κ β hκ (ihκ (Nat.le_of_succ_le_succ hde)) (ihβ (Nat.le_of_succ_le_succ hde)) hβ

theorem TD.T {α : Ordinal.{u}} {d : Nat} (h : TD α d) : T α := Exists.intro d h

theorem TD_G {α : Ordinal.{u}} (h : T α) : TD α (G α) := by
  have h' : ∃ d, TD α d := h
  unfold G
  rw [dite_eq_left h']
  exact (Classical.choose_spec (exists_least_nat (fun d => TD α d) h')).1

theorem G_le {α : Ordinal.{u}} {d : Nat} (h : TD α d) : G α ≤ d := by
  have hT : ∃ d, TD α d := Exists.intro d h
  unfold G
  rw [dite_eq_left hT]
  apply Nat.le_of_not_lt
  intro hlt
  exact (Classical.choose_spec (exists_least_nat (fun d => TD α d) hT)).2 d hlt h

theorem TD_iff_G_le {α : Ordinal.{u}} (h : T α) (d : Nat) : TD α d ↔ G α ≤ d :=
  Iff.intro G_le (fun hd => (TD_G h).mono hd)

theorem T_zero : T (0 : Ordinal.{u}) := Exists.intro 0 (TD.zero 0)

theorem G_zero : G (0 : Ordinal.{u}) = 0 := Nat.le_zero.mp (G_le (TD.zero 0))

theorem TD_list {l : List Ordinal.{u}} (h : ∀ p, p ∈ l → T p) : ∃ d, ∀ p, p ∈ l → TD p d := by
  induction l with
  | nil => exact Exists.intro 0 (fun p hp => absurd hp List.not_mem_nil)
  | cons a l ih =>
    cases ih (fun p hp => h p (List.mem_cons_of_mem a hp)) with
    | intro d hd =>
      cases h a List.mem_cons_self with
      | intro e he =>
        refine Exists.intro (max d e) (fun p hp => ?_)
        cases List.mem_cons.mp hp with
        | inl hpa => rw [hpa]; exact he.mono (Nat.le_max_right d e)
        | inr hp => exact (hd p hp).mono (Nat.le_max_left d e)

theorem I_isPrincipal_of_lt {β : Nat} {γ : Ordinal.{u}} (h : γ < I β γ) : IsPrincipal (I β γ) := by
  have hne : I β γ ≠ 0 := ne_of_gt (lt_of_le_of_lt (zero_le γ) h)
  have hdef := (I_ne_zero_iff β γ).mp hne
  rw [I_eq_enum]
  exact hdef.mem.isPrincipal

section Hypothesis

variable [LargeCardinals.{u}]

theorem lemma_5_1 {α : Ordinal.{u}} (h : T α) : α < Λ₀ := by
  cases h with
  | intro d h =>
    induction h with
    | zero _ => exact Λ₀_pos
    | sum _ γ l _ hNF _ ih =>
      rw [hNF.1.eq]
      exact listSum_lt isPrincipal_Λ₀ ih
    | inacc _ β γ _ _ _ _ ihγ => exact I_lt_Λ₀ β ihγ
    | psi _ κ β hκ _ _ _ _ _ => exact Ψ_lt_Λ₀ hκ β

theorem I_rep_unique {β β' : Nat} {γ γ' : Ordinal.{u}} (h : γ < I β γ) (h' : γ' < I β' γ')
    (e : I β γ = I β' γ') (hΛ : I β γ < Λ₀) : β = β' ∧ γ = γ' := by
  have hγ : γ < Λ₀ := lt_trans _ _ _ h hΛ
  have hγ' : γ' < Λ₀ := lt_trans _ _ _ h' (e ▸ hΛ)
  cases (theorem_3_2 β β' hγ hγ').mp e with
  | inl hc =>
    have hfix : γ = I β γ := hc.2.trans e.symm
    rw [← hfix] at h
    exact absurd h (lt_irrefl _)
  | inr hc =>
    cases hc with
    | inl hc => exact hc
    | inr hc =>
      have hfix : γ' = I β' γ' := hc.2.symm.trans e
      rw [← hfix] at h'
      exact absurd h' (lt_irrefl _)

omit [LargeCardinals.{u}] in

theorem TD_sum_inv {γ : Ordinal.{u}} {l : List Ordinal.{u}} {d : Nat} (h : TD γ d)
    (h0 : 0 < γ) (hNF : NFSum γ l) : ∃ d', d = d' + 1 ∧ ∀ p, p ∈ l → TD p d' := by
  cases h with
  | zero _ => exact absurd h0 (lt_irrefl 0)
  | sum d' _ l' _ hNF' hl' =>
    rw [cnf_unique hNF.1 hNF'.1]
    exact Exists.intro d' (And.intro rfl hl')
  | inacc d' β γ' _ _ hlt => exact absurd (I_isPrincipal_of_lt hlt) (fun hP => hNF.not_principal hP)
  | psi d' κ β _ _ _ _ => exact absurd (lemma_4_5_a κ β) (fun hP => hNF.not_principal hP)

theorem TD_inacc_inv {β : Nat} {γ : Ordinal.{u}} {d : Nat} (h : TD (I β γ) d)
    (hlt : γ < I β γ) : ∃ d', d = d' + 1 ∧ TD (ordNat.{u} β) d' ∧ TD γ d' := by
  have hΛ : I β γ < Λ₀ := lemma_5_1 (Exists.intro d h)
  generalize hx : I β γ = x at h
  cases h with
  | zero _ => exact absurd hx (ne_of_gt (lt_of_le_of_lt (zero_le γ) hlt))
  | sum d' _ l h0 hNF _ =>
    rw [← hx] at hNF
    exact absurd (I_isPrincipal_of_lt hlt) (fun hP => hNF.not_principal hP)
  | inacc d' β' γ' hβ' hγ' hlt' =>
    have e := I_rep_unique hlt hlt' hx hΛ
    rw [e.1, e.2]
    exact Exists.intro d' (And.intro rfl (And.intro hβ' hγ'))
  | psi d' κ β' hκ _ _ _ => exact absurd hx.symm (lemma_4_7_a hκ β' hlt)

theorem TD_psi_inv {κ β : Ordinal.{u}} {d : Nat} (h : TD (Ψ κ β) d) (hκ : IsRegBelowΛ₀ κ)
    (hβ : C κ β β) : ∃ d', d = d' + 1 ∧ TD κ d' ∧ TD β d' := by
  generalize hx : Ψ κ β = x at h
  cases h with
  | zero _ => exact absurd hx (ne_of_gt (lemma_4_5_a κ β).pos)
  | sum d' _ l h0 hNF _ =>
    rw [← hx] at hNF
    exact absurd (lemma_4_5_a κ β) (fun hP => hNF.not_principal hP)
  | inacc d' β' γ' _ _ hlt' => exact absurd hx (lemma_4_7_a hκ β hlt')
  | psi d' κ' β' hκ' hκT hβT hβ' =>
    have e := theorem_4_11 hκ hκ' hx hβ hβ'
    rw [e.1, e.2]
    exact Exists.intro d' (And.intro rfl (And.intro hκT hβT))

def maxG : List Ordinal.{u} → Nat
  | [] => 0
  | p :: l => max (G p) (maxG l)

omit [LargeCardinals.{u}] in
theorem maxG_le_iff (l : List Ordinal.{u}) (d : Nat) : maxG l ≤ d ↔ ∀ p, p ∈ l → G p ≤ d := by
  induction l with
  | nil => exact Iff.intro (fun _ p hp => absurd hp List.not_mem_nil) (fun _ => Nat.zero_le d)
  | cons a l ih =>
    show max (G a) (maxG l) ≤ d ↔ _
    rw [Nat.max_le, ih]
    apply Iff.intro
    · intro h p hp
      cases List.mem_cons.mp hp with
      | inl e => rw [e]; exact h.1
      | inr hp => exact h.2 p hp
    · intro h
      exact And.intro (h a List.mem_cons_self) (fun p hp => h p (List.mem_cons_of_mem a hp))

omit [LargeCardinals.{u}] in

theorem G_sum {γ : Ordinal.{u}} {l : List Ordinal.{u}} (h0 : 0 < γ) (hNF : NFSum γ l)
    (hl : ∀ p, p ∈ l → T p) : G γ = maxG l + 1 := by
  have hT : TD γ (maxG l + 1) :=
    TD.sum _ γ l h0 hNF (fun p hp => (TD_G (hl p hp)).mono (((maxG_le_iff l _).mp
      (Nat.le_refl _)) p hp))
  apply Nat.le_antisymm (G_le hT)
  cases TD_sum_inv (TD_G (Exists.intro _ hT)) h0 hNF with
  | intro d' hd' =>
    rw [hd'.1]
    exact Nat.succ_le_succ ((maxG_le_iff l d').mpr (fun p hp => G_le (hd'.2 p hp)))

theorem G_inacc {β : Nat} {γ : Ordinal.{u}} (hβ : T (ordNat.{u} β)) (hγ : T γ) (hlt : γ < I β γ) :
    G (I β γ) = max (G (ordNat.{u} β)) (G γ) + 1 := by
  have hT : TD (I β γ) (max (G (ordNat β)) (G γ) + 1) :=
    TD.inacc _ β γ ((TD_G hβ).mono (Nat.le_max_left _ _)) ((TD_G hγ).mono (Nat.le_max_right _ _))
      hlt
  apply Nat.le_antisymm (G_le hT)
  cases TD_inacc_inv (TD_G (Exists.intro _ hT)) hlt with
  | intro d' hd' =>
    rw [hd'.1]
    exact Nat.succ_le_succ (Nat.max_le.mpr (And.intro (G_le hd'.2.1) (G_le hd'.2.2)))

theorem G_psi {κ β : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hκT : T κ) (hβT : T β)
    (hβ : C κ β β) : G (Ψ κ β) = max (G κ) (G β) + 1 := by
  have hT : TD (Ψ κ β) (max (G κ) (G β) + 1) :=
    TD.psi _ κ β hκ ((TD_G hκT).mono (Nat.le_max_left _ _)) ((TD_G hβT).mono
      (Nat.le_max_right _ _)) hβ
  apply Nat.le_antisymm (G_le hT)
  cases TD_psi_inv (TD_G (Exists.intro _ hT)) hκ hβ with
  | intro d' hd' =>
    rw [hd'.1]
    exact Nat.succ_le_succ (Nat.max_le.mpr (And.intro (G_le hd'.2.1) (G_le hd'.2.2)))

omit [LargeCardinals.{u}] in

theorem T_cases {α : Ordinal.{u}} (h : T α) :
    α = 0 ∨
    (0 < α ∧ ∃ l, NFSum α l ∧ ∀ p, p ∈ l → T p) ∨
    (∃ (β : Nat) (γ : Ordinal.{u}), α = I β γ ∧ γ < I β γ ∧ T (ordNat.{u} β) ∧ T γ) ∨
    (∃ κ β, α = Ψ κ β ∧ IsRegBelowΛ₀ κ ∧ T κ ∧ T β ∧ C κ β β) := by
  cases h with
  | intro d h =>
    cases h with
    | zero _ => exact Or.inl rfl
    | sum d' γ l h0 hNF hl =>
      exact Or.inr (Or.inl (And.intro h0 (Exists.intro l (And.intro hNF
        (fun p hp => (hl p hp).T)))))
    | inacc d' β γ hβ hγ hlt =>
      exact Or.inr (Or.inr (Or.inl (Exists.intro β (Exists.intro γ
        (And.intro rfl (And.intro hlt (And.intro hβ.T hγ.T)))))))
    | psi d' κ β hκ hκT hβT hβ =>
      exact Or.inr (Or.inr (Or.inr (Exists.intro κ (Exists.intro β
        (And.intro rfl (And.intro hκ (And.intro hκT.T (And.intro hβT.T hβ))))))))

omit [LargeCardinals.{u}] in
theorem T_rules_exclusive_sum_I {α : Ordinal.{u}} {l : List Ordinal.{u}} {β : Nat}
    {γ : Ordinal.{u}} (hNF : NFSum α l) (e : α = I β γ) (hlt : γ < I β γ) : False :=
  hNF.not_principal (e ▸ I_isPrincipal_of_lt hlt)

omit [LargeCardinals.{u}] in
theorem T_rules_exclusive_sum_psi {α κ β : Ordinal.{u}} {l : List Ordinal.{u}}
    (hNF : NFSum α l) (e : α = Ψ κ β) : False :=
  hNF.not_principal (e ▸ lemma_4_5_a κ β)

theorem T_rules_exclusive_I_psi {κ β' γ : Ordinal.{u}} {β : Nat} (hκ : IsRegBelowΛ₀ κ)
    (hlt : γ < I β γ) (e : I β γ = Ψ κ β') : False :=
  lemma_4_7_a hκ β' hlt e.symm

omit [LargeCardinals.{u}] in
theorem T_components {α p : Ordinal.{u}} (h : T α) (hp : IsComponent α p) : T p := by
  cases h with
  | intro d h =>
    cases h with
    | zero _ => exact absurd hp isComponent_zero
    | sum d' γ l h0 hNF hl =>
      cases hp with
      | intro l' hl' =>
        rw [cnf_unique hl'.1 hNF.1] at hl'
        exact (hl p hl'.2).T
    | inacc d' β γ hβ hγ hlt =>
      rw [isComponent_of_principal (I_isPrincipal_of_lt hlt) hp]
      exact (TD.inacc d' β γ hβ hγ hlt).T
    | psi d' κ β hκ hκT hβT hβ =>
      rw [isComponent_of_principal (lemma_4_5_a κ β) hp]
      exact (TD.psi d' κ β hκ hκT hβT hβ).T

omit [LargeCardinals.{u}] in
theorem T_of_cnf {α : Ordinal.{u}} {l : List Ordinal.{u}} (hcnf : CNF α l)
    (hl : ∀ p, p ∈ l → T p) : T α := by
  cases eq_zero_or_pos α with
  | inl h0 => rw [h0]; exact T_zero
  | inr hpos =>
    cases Classical.em (IsPrincipal α) with
    | inl hP =>
      rw [cnf_of_principal hP hcnf] at hl
      exact hl α List.mem_cons_self
    | inr hP =>
      cases TD_list hl with
      | intro d hd => exact (TD.sum d α l hpos (nfSum_of_cnf hcnf hP) hd).T

omit [LargeCardinals.{u}] in

theorem T_add {β γ : Ordinal.{u}} (hβ : T β) (hγ : T γ) : T (β + γ) := by
  cases cnf_exists (β + γ) with
  | intro l hl =>
    apply T_of_cnf hl
    intro p hp
    cases isComponent_add (Exists.intro l (And.intro hl hp)) with
    | inl h => exact T_components hβ h
    | inr h => exact T_components hγ h

omit [LargeCardinals.{u}] in
theorem C_listSum {κ α : Ordinal.{u}} {l : List Ordinal.{u}} (h : ∀ p, p ∈ l → C κ α p) :
    C κ α (listSum l) := by
  induction l with
  | nil => exact C_zero κ α
  | cons a l ih =>
    exact C_add κ α a _ (h a List.mem_cons_self) (ih (fun p hp => h p (List.mem_cons_of_mem a hp)))

theorem regPred_Ω : regPred (Ω : Ordinal.{u}) = 0 := regPred_I_zero 0

theorem T_of_C_Ω {ξ : Ordinal.{u}} (h : C Ω Λ₀ ξ) : T ξ := by
  cases h with
  | intro n hn =>
    refine Cn_induction (motive := fun _ ξ => T ξ) ?_ ?_ ?_ ?_ ?_ ?_ hn
    · intro _
      rw [regPred_Ω]
      exact T_zero
    · intro _ γ hγ
      rw [regPred_Ω] at hγ
      exact absurd hγ (not_lt_zero γ)
    · intro _ β γ _ _ hβ hγ
      exact T_add hβ hγ
    · intro _ m γ _ _ hm hγ
      cases le_I m (lemma_5_1 hγ) with
      | inl hlt =>
        cases hm with
        | intro d hd =>
          cases hγ with
          | intro e he =>
            exact (TD.inacc (max d e) m γ (hd.mono (Nat.le_max_left d e))
              (he.mono (Nat.le_max_right d e)) hlt).T
      | inr he => rw [← he]; exact hγ
    · intro _ π γ hπ hγπ hπΩ _ _
      exact absurd hπΩ (not_lt_of_le hπ.Ω_le)
    · intro _ π γ _ hπ _ _ hγ hγT hπT
      cases hπT with
      | intro d hd =>
        cases hγT with
        | intro e he =>
          exact (TD.psi (max d e) π γ hπ (hd.mono (Nat.le_max_left d e))
            (he.mono (Nat.le_max_right d e)) hγ).T

theorem C_Ω_of_T {ξ : Ordinal.{u}} (h : T ξ) : C Ω Λ₀ ξ := by
  cases h with
  | intro d h =>
    induction h with
    | zero _ => exact C_zero Ω Λ₀
    | sum _ γ l _ hNF _ ih =>
      rw [hNF.1.eq]
      exact C_listSum ih
    | inacc _ β γ _ _ _ ihβ ihγ => exact C_inacc Ω Λ₀ β γ ihβ ihγ
    | psi _ κ β hκ _ hβT hβ ihκ ihβ =>
      exact C_psi (lemma_5_1 hβT.T) hκ ihβ ihκ hβ

theorem theorem_5_2 (ξ : Ordinal.{u}) : T ξ ↔ C Ω Λ₀ ξ := Iff.intro C_Ω_of_T T_of_C_Ω

theorem corollary_5_3 (ξ : Ordinal.{u}) : ξ < Ψ Ω Λ₀ ↔ T ξ ∧ ξ < Ω := by
  rw [theorem_5_2]
  exact (theorem_4_9 isRegBelowΛ₀_Ω Λ₀ ξ).symm

theorem Ψ_Ω_zero : Ψ (Ω : Ordinal.{u}) 0 = succ 0 := by
  have hC : ∀ ξ, C Ω 0 ξ → ξ = 0 ∨ Ω ≤ ξ := by
    intro ξ h
    cases h with
    | intro n hn =>
      refine Cn_induction (motive := fun _ ξ => ξ = 0 ∨ Ω ≤ ξ) ?_ ?_ ?_ ?_ ?_ ?_ hn
      · intro _
        exact Or.inl regPred_Ω
      · intro _ γ hγ
        rw [regPred_Ω] at hγ
        exact absurd hγ (not_lt_zero γ)
      · intro _ β γ _ _ hβ hγ
        cases hβ with
        | inl h => rw [h, zero_add]; exact hγ
        | inr h => exact Or.inr (le_trans h (le_add β γ))
      · intro _ m γ _ hγ _ _
        exact Or.inr (Ω_le_I m (C_lt_Λ₀ isRegBelowΛ₀_Ω (C_of_Cn hγ)))
      · intro _ π γ hπ _ hπΩ _ _
        exact absurd hπΩ (not_lt_of_le hπ.Ω_le)
      · intro _ π γ hγα _ _ _ _ _ _
        exact absurd hγα (not_lt_zero γ)
  apply le_antisymm
  · apply Ψ_le_of_not_C
    intro h
    cases hC _ h with
    | inl h => exact succ_ne_zero 0 h
    | inr h => exact not_lt_of_le h one_lt_Ω
  · apply succ_le_of_lt
    exact lt_of_le_of_lt (zero_le _) (regPred_lt_Ψ Ω 0)

theorem T_ordNat (n : Nat) : T (ordNat.{u} n) := by
  induction n with
  | zero => exact T_zero
  | succ n ih =>
    have h1 : T (succ (0 : Ordinal.{u})) := by
      rw [← Ψ_Ω_zero]
      exact (TD.psi 1 Ω 0 isRegBelowΛ₀_Ω (TD.inacc 0 0 0 (TD.zero 0) (TD.zero 0)
        (I_pos 0 Λ₀_pos)) (TD.zero 1) (C_zero Ω 0)).T
    rw [ordNat_succ, ← add_one_eq_succ]
    exact T_add ih h1

def iIndex (α : Ordinal.{u}) : Nat :=
  open Classical in
  if h : ∃ (m : Nat) (γ : Ordinal.{u}), α = I m γ ∧ γ < I m γ then Classical.choose h else 0

def fIndex (α : Ordinal.{u}) : Nat :=
  open Classical in
  if ∃ (m : Nat) (γ : Ordinal.{u}), α = I m γ ∧ γ < I m γ then iIndex α
  else if h : ∃ κ β, α = Ψ κ β ∧ IsRegBelowΛ₀ κ ∧ C κ β β then iIndex (Classical.choose h)
  else 0

theorem iIndex_I {m : Nat} {γ : Ordinal.{u}} (hlt : γ < I m γ) (hΛ : I m γ < Λ₀) :
    iIndex (I m γ) = m := by
  have h : ∃ (m' : Nat) (γ' : Ordinal.{u}), I m γ = I m' γ' ∧ γ' < I m' γ' :=
    Exists.intro m (Exists.intro γ (And.intro rfl hlt))
  unfold iIndex
  rw [dite_eq_left h]
  cases Classical.choose_spec h with
  | intro γ' hγ' => exact (I_rep_unique hlt hγ'.2 hγ'.1 hΛ).1.symm

theorem fIndex_I {m : Nat} {γ : Ordinal.{u}} (hlt : γ < I m γ) (hΛ : I m γ < Λ₀) :
    fIndex (I m γ) = m := by
  have h : ∃ (m' : Nat) (γ' : Ordinal.{u}), I m γ = I m' γ' ∧ γ' < I m' γ' :=
    Exists.intro m (Exists.intro γ (And.intro rfl hlt))
  unfold fIndex
  simp only [h, ↓reduceIte]
  exact iIndex_I hlt hΛ

theorem iIndex_of_NFI {κ σ : Ordinal.{u}} {ρ : Nat} (hκ : IsRegBelowΛ₀ κ) (hNF : NFI κ ρ σ) :
    iIndex κ = ρ := by
  have hlt : σ < I ρ σ := hNF.1 ▸ hNF.lt hκ.R
  rw [hNF.1]
  exact iIndex_I hlt (hNF.1 ▸ hκ.lt_Λ₀)

theorem fIndex_psi {κ β σ : Ordinal.{u}} {ρ : Nat} (hκ : IsRegBelowΛ₀ κ) (hβ : C κ β β)
    (hNF : NFI κ ρ σ) : fIndex (Ψ κ β) = ρ := by
  have hnI : ¬ ∃ (m : Nat) (γ : Ordinal.{u}), Ψ κ β = I m γ ∧ γ < I m γ := by
    intro h
    cases h with
    | intro m h =>
      cases h with
      | intro γ h => exact lemma_4_7_a hκ β h.2 h.1
  have h : ∃ κ' β', Ψ κ β = Ψ κ' β' ∧ IsRegBelowΛ₀ κ' ∧ C κ' β' β' :=
    Exists.intro κ (Exists.intro β (And.intro rfl (And.intro hκ hβ)))
  unfold fIndex
  simp only [hnI, ↓reduceIte]
  rw [dite_eq_left h]
  cases Classical.choose_spec h with
  | intro β' hβ' =>
    have e := theorem_4_11 hκ hβ'.2.1 hβ'.1 hβ hβ'.2.2
    rw [← e.1]
    exact iIndex_of_NFI hκ hNF

omit [LargeCardinals.{u}] in
theorem fIndex_of_not_principal {α : Ordinal.{u}} (hP : ¬ IsPrincipal α) : fIndex α = 0 := by
  have hnI : ¬ ∃ (m : Nat) (γ : Ordinal.{u}), α = I m γ ∧ γ < I m γ := by
    intro h
    cases h with
    | intro m h =>
      cases h with
      | intro γ h => exact hP (h.1 ▸ I_isPrincipal_of_lt h.2)
  have hnΨ : ¬ ∃ κ β, α = Ψ κ β ∧ IsRegBelowΛ₀ κ ∧ C κ β β := by
    intro h
    cases h with
    | intro κ h =>
      cases h with
      | intro β h => exact hP (h.1 ▸ lemma_4_5_a κ β)
  unfold fIndex
  simp only [hnI, ↓reduceIte]
  rw [dite_eq_right hnΨ]

omit [LargeCardinals.{u}] in
theorem fIndex_zero : fIndex (0 : Ordinal.{u}) = 0 :=
  fIndex_of_not_principal (fun h => h.1 rfl)

theorem fIndex_spec {α : Ordinal.{u}} (h : T α) :
    T (ordNat.{u} (fIndex α)) ∧ G (ordNat.{u} (fIndex α)) ≤ G α := by
  apply And.intro (T_ordNat _)
  have key : ∀ d, TD α d → G (ordNat.{u} (fIndex α)) ≤ d := by
    intro d hd
    clear h
    induction hd with
    | zero _ =>
      rw [fIndex_zero, ordNat_zero, G_zero]
      exact Nat.zero_le _
    | sum d γ l _ hNF _ _ =>
      rw [fIndex_of_not_principal (fun hP => hNF.not_principal hP), ordNat_zero, G_zero]
      exact Nat.zero_le _
    | inacc d β γ hβ hγ hlt _ _ =>
      rw [fIndex_I hlt (lemma_5_1 (TD.inacc d β γ hβ hγ hlt).T)]
      exact Nat.le_succ_of_le (G_le hβ)
    | psi d κ β hκ hκT hβT hβ ihκ _ =>
      cases theorem_3_4 hκ.R hκ.lt_Λ₀ with
      | intro ρ hρ =>
        cases hρ with
        | intro σ hσ =>
          rw [fIndex_psi hκ hβ hσ.1]
          have := ihκ
          have hfκ : fIndex κ = ρ := by
            rw [hσ.1.1]
            exact fIndex_I (hσ.1.1 ▸ hσ.1.lt hκ.R) (hσ.1.1 ▸ hκ.lt_Λ₀)
          rw [hfκ] at this
          exact Nat.le_succ_of_le this
  exact key _ (TD_G h)

theorem lemma_5_4 {γ : Ordinal.{u}} (h : T γ) (β : Nat) : γ < I β γ ↔ fIndex γ ≤ β := by
  have hγΛ := lemma_5_1 h
  cases T_cases h with
  | inl h0 =>
    rw [h0, fIndex_zero]
    exact Iff.intro (fun _ => Nat.zero_le β) (fun _ => I_pos β Λ₀_pos)
  | inr h' =>
    cases h' with
    | inl hs =>
      cases hs.2 with
      | intro l hl =>
        rw [fIndex_of_not_principal (fun hP => hl.1.not_principal hP)]
        apply Iff.intro (fun _ => Nat.zero_le β)
        intro _
        apply lt_of_le_of_ne (le_I β hγΛ)
        intro e
        have hP : IsPrincipal (I β γ) := (I_mem β hγΛ).isPrincipal
        rw [← e] at hP
        exact hl.1.not_principal hP
    | inr h' =>
      cases h' with
      | inl hI =>
        cases hI with
        | intro m hI =>
          cases hI with
          | intro η hη =>
            have hηΛ := lemma_5_1 hη.2.2.2
            rw [hη.1, fIndex_I hη.2.1 (hη.1 ▸ hγΛ)]
            apply Iff.intro
            · intro hlt
              apply Nat.le_of_not_lt
              intro hβm
              rw [lemma_3_1_b hβm hηΛ] at hlt
              exact lt_irrefl _ hlt
            · intro hmβ
              cases Nat.lt_or_eq_of_le hmβ with
              | inl hmβ =>
                have hIΛ := I_lt_Λ₀ m hηΛ
                exact (theorem_3_3 m β hηΛ hIΛ).mpr (Or.inl (And.intro hmβ
                  (lt_of_lt_of_le hη.2.1 (le_I β hIΛ))))
              | inr hmβ =>
                rw [← hmβ]
                exact I_lt_I m hη.2.1 (I_lt_Λ₀ m hηΛ)
      | inr hΨ =>
        cases hΨ with
        | intro κ hΨ =>
          cases hΨ with
          | intro ξ hξ =>
            cases theorem_3_4 hξ.2.1.R hξ.2.1.lt_Λ₀ with
            | intro ρ hρ =>
              cases hρ with
              | intro σ hσ =>
                rw [hξ.1, fIndex_psi hξ.2.1 hξ.2.2.2.2 hσ.1]
                rw [hξ.1] at hγΛ
                apply Iff.intro
                · intro hlt
                  apply Nat.le_of_not_lt
                  intro hβρ
                  rw [lemma_4_5_b hξ.2.1 hσ.1.1 hβρ ξ] at hlt
                  exact lt_irrefl _ hlt
                · intro hρβ
                  apply lt_of_le_of_ne (le_I β hγΛ)
                  intro e
                  have hlt : I β (Ψ κ ξ) < I ρ σ := by
                    rw [← e, ← hσ.1.1]
                    exact Ψ_lt hξ.2.1 ξ
                  have hσΛ := hσ.1.lt_Λ₀ hξ.2.1.R hξ.2.1.lt_Λ₀
                  have h1 := lemma_3_5 hρβ hγΛ hσΛ hlt hσ.1.2
                  rw [← hσ.1.1, ← e] at h1
                  exact not_lt_of_le h1 (theorem_4_2 hξ.2.1 ξ).1

inductive HMem (κ : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} → Prop where

  | sum (α : Ordinal.{u}) (l : List Ordinal.{u}) (p ξ : Ordinal.{u}) (h0 : 0 < α)
      (hNF : NFSum α l) (hp : p ∈ l) (h : HMem κ p ξ) : HMem κ α ξ

  | inacc_idx (β : Nat) (γ ξ : Ordinal.{u}) (hlt : γ < I β γ) (h : HMem κ (ordNat β) ξ) :
      HMem κ (I β γ) ξ
  | inacc_arg (β : Nat) (γ ξ : Ordinal.{u}) (hlt : γ < I β γ) (h : HMem κ γ ξ) :
      HMem κ (I β γ) ξ

  | psi_lt (π β ξ : Ordinal.{u}) (hπ : IsRegBelowΛ₀ π) (hβ : C π β β)
      (hpred : regPred κ < Ψ π β) (hπκ : π < κ) (h : HMem κ π ξ) : HMem κ (Ψ π β) ξ

  | psi_self (π β : Ordinal.{u}) (hπ : IsRegBelowΛ₀ π) (hβ : C π β β)
      (hpred : regPred κ < Ψ π β) (hκπ : κ ≤ π) : HMem κ (Ψ π β) β
  | psi_arg (π β ξ : Ordinal.{u}) (hπ : IsRegBelowΛ₀ π) (hβ : C π β β)
      (hpred : regPred κ < Ψ π β) (hκπ : κ ≤ π) (h : HMem κ β ξ) : HMem κ (Ψ π β) ξ
  | psi_idx (π β ξ : Ordinal.{u}) (hπ : IsRegBelowΛ₀ π) (hβ : C π β β)
      (hpred : regPred κ < Ψ π β) (hκπ : κ ≤ π) (h : HMem κ π ξ) : HMem κ (Ψ π β) ξ

omit [LargeCardinals.{u}] in
theorem HMem_zero {κ ξ : Ordinal.{u}} (h : HMem κ 0 ξ) : False := by
  generalize hx : (0 : Ordinal.{u}) = x at h
  cases h with
  | sum _ _ _ _ h0 _ _ _ => rw [← hx] at h0; exact lt_irrefl 0 h0
  | inacc_idx β γ _ hlt _ => exact absurd hx.symm (ne_of_gt (lt_of_le_of_lt (zero_le γ) hlt))
  | inacc_arg β γ _ hlt _ => exact absurd hx.symm (ne_of_gt (lt_of_le_of_lt (zero_le γ) hlt))
  | psi_lt π β _ _ _ hpred _ _ =>
    exact absurd hx.symm (ne_of_gt (lt_of_le_of_lt (zero_le _) hpred))
  | psi_self π β _ _ hpred _ =>
    exact absurd hx.symm (ne_of_gt (lt_of_le_of_lt (zero_le _) hpred))
  | psi_arg π β _ _ _ hpred _ _ =>
    exact absurd hx.symm (ne_of_gt (lt_of_le_of_lt (zero_le _) hpred))
  | psi_idx π β _ _ _ hpred _ _ =>
    exact absurd hx.symm (ne_of_gt (lt_of_le_of_lt (zero_le _) hpred))

omit [LargeCardinals.{u}] in
theorem HMem_sum_iff {κ α ξ : Ordinal.{u}} {l : List Ordinal.{u}} (h0 : 0 < α) (hNF : NFSum α l) :
    HMem κ α ξ ↔ ∃ p, p ∈ l ∧ HMem κ p ξ := by
  apply Iff.intro
  · intro h
    generalize hx : α = x at h
    cases h with
    | sum _ l' p _ _ hNF' hp hH =>
      rw [← hx] at hNF'
      rw [cnf_unique hNF.1 hNF'.1]
      exact Exists.intro p (And.intro hp hH)
    | inacc_idx _ _ _ hlt _ =>
      rw [hx] at hNF
      exact (hNF.not_principal (I_isPrincipal_of_lt hlt)).elim
    | inacc_arg _ _ _ hlt _ =>
      rw [hx] at hNF
      exact (hNF.not_principal (I_isPrincipal_of_lt hlt)).elim
    | psi_lt _ _ _ _ _ _ _ _ =>
      rw [hx] at hNF
      exact (hNF.not_principal (lemma_4_5_a _ _)).elim
    | psi_self _ _ _ _ _ _ =>
      rw [hx] at hNF
      exact (hNF.not_principal (lemma_4_5_a _ _)).elim
    | psi_arg _ _ _ _ _ _ _ _ =>
      rw [hx] at hNF
      exact (hNF.not_principal (lemma_4_5_a _ _)).elim
    | psi_idx _ _ _ _ _ _ _ _ =>
      rw [hx] at hNF
      exact (hNF.not_principal (lemma_4_5_a _ _)).elim
  · intro h
    cases h with
    | intro p hp => exact HMem.sum α l p ξ h0 hNF hp.1 hp.2

theorem HMem_inacc_iff {κ ξ γ : Ordinal.{u}} {β : Nat} (hlt : γ < I β γ) (hΛ : I β γ < Λ₀) :
    HMem κ (I β γ) ξ ↔ HMem κ (ordNat β) ξ ∨ HMem κ γ ξ := by
  apply Iff.intro
  · intro h
    generalize hx : I β γ = x at h
    cases h with
    | sum _ l _ _ _ hNF _ _ =>
      rw [← hx] at hNF
      exact absurd (I_isPrincipal_of_lt hlt) (fun hP => hNF.not_principal hP)
    | inacc_idx β' γ' _ hlt' hH =>
      have e := I_rep_unique hlt hlt' hx hΛ
      rw [e.1]
      exact Or.inl hH
    | inacc_arg β' γ' _ hlt' hH =>
      have e := I_rep_unique hlt hlt' hx hΛ
      rw [e.2]
      exact Or.inr hH
    | psi_lt _ _ _ hπ _ _ _ _ => exact absurd hx.symm (lemma_4_7_a hπ _ hlt)
    | psi_self _ _ hπ _ _ _ => exact absurd hx.symm (lemma_4_7_a hπ _ hlt)
    | psi_arg _ _ _ hπ _ _ _ _ => exact absurd hx.symm (lemma_4_7_a hπ _ hlt)
    | psi_idx _ _ _ hπ _ _ _ _ => exact absurd hx.symm (lemma_4_7_a hπ _ hlt)
  · intro h
    cases h with
    | inl h => exact HMem.inacc_idx β γ ξ hlt h
    | inr h => exact HMem.inacc_arg β γ ξ hlt h

theorem HMem_psi_iff {κ π β ξ : Ordinal.{u}} (hπ : IsRegBelowΛ₀ π) (hβ : C π β β) :
    HMem κ (Ψ π β) ξ ↔ regPred κ < Ψ π β ∧
      ((π < κ ∧ HMem κ π ξ) ∨ (κ ≤ π ∧ (ξ = β ∨ HMem κ β ξ ∨ HMem κ π ξ))) := by
  apply Iff.intro
  · intro h
    generalize hx : Ψ π β = x at h
    cases h with
    | sum _ l _ _ _ hNF _ _ =>
      rw [← hx] at hNF
      exact absurd (lemma_4_5_a π β) (fun hP => hNF.not_principal hP)
    | inacc_idx β' γ' _ hlt' _ => exact absurd hx (lemma_4_7_a hπ β hlt')
    | inacc_arg β' γ' _ hlt' _ => exact absurd hx (lemma_4_7_a hπ β hlt')
    | psi_lt π' β' _ hπ' hβ' hpred hπκ hH =>
      have e := theorem_4_11 hπ hπ' hx hβ hβ'
      cases e with
      | intro e1 e2 =>
        subst e1
        subst e2
        exact And.intro hpred (Or.inl (And.intro hπκ hH))
    | psi_self π' β' hπ' hβ' hpred hκπ =>
      have e := theorem_4_11 hπ hπ' hx hβ hβ'
      cases e with
      | intro e1 e2 =>
        subst e1
        subst e2
        exact And.intro hpred (Or.inr (And.intro hκπ (Or.inl rfl)))
    | psi_arg π' β' _ hπ' hβ' hpred hκπ hH =>
      have e := theorem_4_11 hπ hπ' hx hβ hβ'
      cases e with
      | intro e1 e2 =>
        subst e1
        subst e2
        exact And.intro hpred (Or.inr (And.intro hκπ (Or.inr (Or.inl hH))))
    | psi_idx π' β' _ hπ' hβ' hpred hκπ hH =>
      have e := theorem_4_11 hπ hπ' hx hβ hβ'
      cases e with
      | intro e1 e2 =>
        subst e1
        subst e2
        exact And.intro hpred (Or.inr (And.intro hκπ (Or.inr (Or.inr hH))))
  · intro h
    cases h.2 with
    | inl h' => exact HMem.psi_lt π β ξ hπ hβ h.1 h'.1 h'.2
    | inr h' =>
      cases h'.2 with
      | inl e => rw [e]; exact HMem.psi_self π β hπ hβ h.1 h'.1
      | inr h'' =>
        cases h'' with
        | inl hH => exact HMem.psi_arg π β ξ hπ hβ h.1 h'.1 hH
        | inr hH => exact HMem.psi_idx π β ξ hπ hβ h.1 h'.1 hH

theorem lemma_5_5_a (κ : Ordinal.{u}) {α : Ordinal.{u}} (hT : T α) (hα : α ≤ regPred κ)
    (ξ : Ordinal.{u}) : ¬ HMem κ α ξ := by
  cases hT with
  | intro d hd =>
    revert hα ξ
    induction hd with
    | zero _ => intro _ ξ; exact HMem_zero
    | sum _ γ l h0 hNF _ ih =>
      intro hα ξ h
      cases (HMem_sum_iff h0 hNF).mp h with
      | intro p hp => exact ih p hp.1 (le_trans (le_of_lt (hNF.2 p hp.1)) hα) ξ hp.2
    | inacc d β γ hβT hγT hlt ihβ ihγ =>
      intro hα ξ h
      have hΛ : I β γ < Λ₀ := lemma_5_1 (TD.inacc d β γ hβT hγT hlt).T
      have hγΛ : γ < Λ₀ := lt_trans _ _ _ hlt hΛ
      cases (HMem_inacc_iff hlt hΛ).mp h with
      | inl h' => exact ihβ (le_trans (le_of_lt (lemma_3_7_a β hγΛ)) hα) ξ h'
      | inr h' => exact ihγ (le_trans (le_of_lt hlt) hα) ξ h'
    | psi _ π β hπ _ _ hβ _ _ =>
      intro hα ξ h
      exact not_lt_of_le hα ((HMem_psi_iff hπ hβ).mp h).1

theorem lemma_5_5_b (κ : Ordinal.{u}) {α : Ordinal.{u}} (hT : T α) {ξ : Ordinal.{u}}
    (h : HMem κ α ξ) : T ξ := by
  cases hT with
  | intro d hd =>
    revert ξ
    induction hd with
    | zero _ => intro ξ h; exact absurd h HMem_zero
    | sum _ γ l h0 hNF _ ih =>
      intro ξ h
      cases (HMem_sum_iff h0 hNF).mp h with
      | intro p hp => exact ih p hp.1 hp.2
    | inacc d β γ hβT hγT hlt ihβ ihγ =>
      intro ξ h
      have hΛ : I β γ < Λ₀ := lemma_5_1 (TD.inacc d β γ hβT hγT hlt).T
      cases (HMem_inacc_iff hlt hΛ).mp h with
      | inl h' => exact ihβ h'
      | inr h' => exact ihγ h'
    | psi _ π β hπ _ hβT hβ ihπ ihβ =>
      intro ξ h
      have h' := ((HMem_psi_iff hπ hβ).mp h).2
      cases h' with
      | inl h' => exact ihπ h'.2
      | inr h' =>
        cases h'.2 with
        | inl e => rw [e]; exact hβT.T
        | inr h'' =>
          cases h'' with
          | inl hH => exact ihβ hH
          | inr hH => exact ihπ hH

theorem lemma_5_5_c (κ : Ordinal.{u}) {α : Ordinal.{u}} (hT : T α) {ξ : Ordinal.{u}}
    (h : HMem κ α ξ) : G ξ < G α := by
  have key : ∀ d, TD α d → ∀ ξ, HMem κ α ξ → ∃ e, e < d ∧ TD ξ e := by
    intro d hd
    clear h hT
    induction hd with
    | zero _ => intro ξ h; exact absurd h HMem_zero
    | sum d γ l h0 hNF _ ih =>
      intro ξ h
      cases (HMem_sum_iff h0 hNF).mp h with
      | intro p hp =>
        cases ih p hp.1 ξ hp.2 with
        | intro e he => exact Exists.intro e (And.intro (Nat.lt_succ_of_lt he.1) he.2)
    | inacc d β γ hβT hγT hlt ihβ ihγ =>
      intro ξ h
      have hΛ : I β γ < Λ₀ := lemma_5_1 (TD.inacc d β γ hβT hγT hlt).T
      cases (HMem_inacc_iff hlt hΛ).mp h with
      | inl h' =>
        cases ihβ ξ h' with
        | intro e he => exact Exists.intro e (And.intro (Nat.lt_succ_of_lt he.1) he.2)
      | inr h' =>
        cases ihγ ξ h' with
        | intro e he => exact Exists.intro e (And.intro (Nat.lt_succ_of_lt he.1) he.2)
    | psi d π β hπ _ hβT hβ ihπ ihβ =>
      intro ξ h
      have h' := ((HMem_psi_iff hπ hβ).mp h).2
      cases h' with
      | inl h' =>
        cases ihπ ξ h'.2 with
        | intro e he => exact Exists.intro e (And.intro (Nat.lt_succ_of_lt he.1) he.2)
      | inr h' =>
        cases h'.2 with
        | inl e => rw [e]; exact Exists.intro d (And.intro (Nat.lt_succ_self d) hβT)
        | inr h'' =>
          cases h'' with
          | inl hH =>
            cases ihβ ξ hH with
            | intro e he => exact Exists.intro e (And.intro (Nat.lt_succ_of_lt he.1) he.2)
          | inr hH =>
            cases ihπ ξ hH with
            | intro e he => exact Exists.intro e (And.intro (Nat.lt_succ_of_lt he.1) he.2)
  cases key _ (TD_G hT) ξ h with
  | intro e he => exact Nat.lt_of_le_of_lt (G_le he.2) he.1

theorem lemma_5_6 {κ : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) {γ : Ordinal.{u}} (hT : T γ)
    (α : Ordinal.{u}) : C κ α γ ↔ ∀ ξ, HMem κ γ ξ → ξ < α := by
  cases hT with
  | intro d hd =>
    induction hd with
    | zero _ =>
      exact Iff.intro (fun _ ξ h => absurd h HMem_zero) (fun _ => C_zero κ α)
    | sum _ γ l h0 hNF _ ih =>
      apply Iff.intro
      · intro hC ξ h
        cases (HMem_sum_iff h0 hNF).mp h with
        | intro p hp => exact (ih p hp.1).mp (lemma_4_14_a' hκ hNF hC p hp.1) ξ hp.2
      · intro h
        rw [hNF.1.eq]
        apply C_listSum
        intro p hp
        exact (ih p hp).mpr (fun ξ hξ => h ξ ((HMem_sum_iff h0 hNF).mpr
          (Exists.intro p (And.intro hp hξ))))
    | inacc d β γ hβT hγT hlt ihβ ihγ =>
      have hΛ : I β γ < Λ₀ := lemma_5_1 (TD.inacc d β γ hβT hγT hlt).T
      apply Iff.intro
      · intro hC ξ h
        have hC' := lemma_4_14_b hκ hlt hC
        cases (HMem_inacc_iff hlt hΛ).mp h with
        | inl h' => exact ihβ.mp hC'.1 ξ h'
        | inr h' => exact ihγ.mp hC'.2 ξ h'
      · intro h
        exact C_inacc κ α β γ
          (ihβ.mpr (fun ξ hξ => h ξ ((HMem_inacc_iff hlt hΛ).mpr (Or.inl hξ))))
          (ihγ.mpr (fun ξ hξ => h ξ ((HMem_inacc_iff hlt hΛ).mpr (Or.inr hξ))))
    | psi _ π β hπ _ _ hβ ihπ ihβ =>
      cases le_or_lt (Ψ π β) (regPred κ) with
      | inl hle =>
        apply Iff.intro
        · intro _ ξ h
          exact absurd ((HMem_psi_iff hπ hβ).mp h).1 (not_lt_of_le hle)
        · intro _
          exact C_of_le_regPred hle
      | inr hpred =>
        cases lt_or_le π κ with
        | inl hπκ =>
          apply Iff.intro
          · intro hC ξ h
            have h' := ((HMem_psi_iff hπ hβ).mp h).2
            cases h' with
            | inl h' => exact ihπ.mp (lemma_4_14_c hκ hπ hπκ hC) ξ h'.2
            | inr h' => exact absurd h'.1 (not_le_of_lt hπκ)
          · intro h
            have hπC : C κ α π := ihπ.mpr (fun ξ hξ => h ξ ((HMem_psi_iff hπ hβ).mpr
              (And.intro hpred (Or.inl (And.intro hπκ hξ)))))
            exact C_lt_reg hπ (Ψ_lt hπ β) hπκ hπC
        | inr hκπ =>
          have hH : ∀ ξ, HMem κ (Ψ π β) ξ ↔ (ξ = β ∨ HMem κ β ξ ∨ HMem κ π ξ) := by
            intro ξ
            rw [HMem_psi_iff hπ hβ]
            apply Iff.intro
            · intro h
              cases h.2 with
              | inl h' => exact absurd h'.1 (not_lt_of_le hκπ)
              | inr h' => exact h'.2
            · intro h
              exact And.intro hpred (Or.inr (And.intro hκπ h))
          apply Iff.intro
          · intro hC ξ h
            have hd := lemma_4_14_d hκ hπ hκπ hβ hpred hC
            cases (hH ξ).mp h with
            | inl e => rw [e]; exact hd.1
            | inr h' =>
              cases h' with
              | inl h' => exact ihβ.mp hd.2.2 ξ h'
              | inr h' => exact ihπ.mp hd.2.1 ξ h'
          · intro h
            have hβα : β < α := h β ((hH β).mpr (Or.inl rfl))
            have hβC : C κ α β := ihβ.mpr (fun ξ hξ => h ξ ((hH ξ).mpr (Or.inr (Or.inl hξ))))
            have hπC : C κ α π := ihπ.mpr (fun ξ hξ => h ξ ((hH ξ).mpr (Or.inr (Or.inr hξ))))
            exact C_psi hβα hπ hβC hπC hβ

end Hypothesis

end
end OCF.Jaeger

namespace OCF.Jaeger

universe u

open Ordinal

noncomputable section

theorem inaccessible_zero_iff (κ : Ordinal.{u}) : Inaccessible 0 κ ↔ R κ := by
  rw [inaccessible_iff]
  exact Iff.intro (fun h => h.1) (fun h => And.intro h (fun m hm => absurd hm (Nat.not_lt_zero m)))

def IsNormal (f : Ordinal.{u} → Ordinal.{u}) : Prop :=
  (∀ α β, α < β → f α < f β) ∧ ∀ l, IsLimit l → f l = supLt l f

theorem IsNormal.mono {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) {α β : Ordinal.{u}}
    (h : α ≤ β) : f α ≤ f β := by
  cases h with
  | inl h => exact le_of_lt (hf.1 α β h)
  | inr h => rw [h]; exact le_refl _

theorem IsNormal.le_self {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) (α : Ordinal.{u}) :
    α ≤ f α := by
  induction α using lt_wellFounded.induction with
  | h α ih =>
    apply le_of_not_lt
    intro hlt
    exact not_lt_of_le (ih _ hlt) (hf.1 _ _ hlt)

theorem isClosed_of_limClosed {S : Ordinal.{u} → Prop} (h : LimClosed S) : IsClosed S := by
  intro B hB hne ζ hζ
  cases Classical.em (B ζ) with
  | inl hζB => exact hB ζ hζB
  | inr hζB =>
    have hlt : ∀ β, B β → β < ζ := by
      intro β hβ
      cases hζ.1 β hβ with
      | inl h' => exact h'
      | inr h' =>
        rw [h'] at hβ
        exact absurd hβ hζB
    apply h
    apply And.intro
    · cases hne with
      | intro β hβ => exact lt_of_le_of_lt (zero_le β) (hlt β hβ)
    · intro η hη
      cases hζ.2 η hη with
      | intro β hβ => exact Exists.intro β (And.intro (hB β hβ.1) (And.intro hβ.2 (hlt β hβ.1)))

theorem IsNormal.range_closed_unbounded {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) :
    IsClosed (fun ξ => ∃ α, f α = ξ) ∧ ∀ β, ∃ ξ, (∃ α, f α = ξ) ∧ β ≤ ξ := by
  apply And.intro
  · apply isClosed_of_limClosed
    intro ξ hξ
    cases Ordinal.exists_min (fun α => ξ ≤ f α) (Exists.intro ξ (hf.le_self ξ)) with
    | intro α hα =>
      refine Exists.intro α (le_antisymm ?_ hα.1)
      have hbelow : ∀ β, β < α → f β < ξ := fun β hβ => lt_of_not_le (hα.2 β hβ)
      cases zero_or_succ_or_limit α with
      | inl h0 =>
        cases hξ.2 0 hξ.1 with
        | intro γ hγ =>
          cases hγ.1 with
          | intro δ hδ =>
            have := hα.1
            rw [h0] at this
            rw [← hδ] at hγ
            exact absurd (lt_of_lt_of_le hγ.2.2 this) (not_lt_of_le (hf.mono (zero_le δ)))
      | inr h' =>
        cases h' with
        | inl hs =>
          cases hs with
          | intro β hβ =>
            have hfβ : f β < ξ := hbelow β (by rw [hβ]; exact lt_succ_self β)
            cases hξ.2 (f β) hfβ with
            | intro γ hγ =>
              cases hγ.1 with
              | intro δ hδ =>
                rw [← hδ] at hγ
                have hβδ : β < δ := lt_of_not_le (fun hle => not_lt_of_le (hf.mono hle) hγ.2.1)
                have := hf.mono (succ_le_of_lt hβδ)
                rw [← hβ] at this
                exact absurd (lt_of_le_of_lt (le_trans hα.1 this) hγ.2.2) (lt_irrefl ξ)
        | inr hl =>
          rw [hf.2 α hl]
          exact (supLt_le_iff _ _ _).mpr (fun β hβ => le_of_lt (hbelow β hβ))
  · intro β
    exact Exists.intro (f β) (And.intro (Exists.intro β rfl) (hf.le_self β))

theorem ordClosure_normal {A : Ordinal.{u} → Prop} (hA : ∀ β, ∃ ξ, A ξ ∧ β < ξ) :
    IsNormal (ordClosure A) := by
  have hdef : ∀ α, EnumDef (closure A) α := by
    intro α
    cases hA (supLt α (enum (closure A))) with
    | intro ξ hξ =>
      exact Exists.intro ξ (And.intro (subset_closure hξ.1)
        (fun β hβ => lt_of_le_of_lt (le_supLt α (enum (closure A)) hβ) hξ.2))
  apply And.intro
  · intro α β h
    exact (hdef β).lt h
  · intro l hl
    exact (enum_limit (closure_limClosed A) hl (fun β _ => hdef β)).2

def Countable (α : Ordinal.{u}) : Prop :=
  ∃ f : Ordinal.{u} → Nat, ∀ x y, x < α → y < α → f x = f y → x = y

def CountableSet (S : Ordinal.{u} → Prop) : Prop :=
  ∃ f : Ordinal.{u} → Nat, ∀ x y, S x → S y → f x = f y → x = y

def pairNat (a b : Nat) : Nat := (a + b) * (a + b) + b

theorem sq_add_lt_of_lt {s t : Nat} (h : s < t) : s * s + s < t * t := by
  have h1 : (s + 1) * (s + 1) ≤ t * t := Nat.mul_le_mul h h
  have h2 : (s + 1) * (s + 1) = s * s + 2 * s + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  omega

theorem pairNat_inj {a b c d : Nat} (h : pairNat a b = pairNat c d) : a = c ∧ b = d := by
  unfold pairNat at h
  have hst : a + b = c + d := by
    cases Nat.lt_trichotomy (a + b) (c + d) with
    | inl hlt =>
      have := sq_add_lt_of_lt hlt
      omega
    | inr h' =>
      cases h' with
      | inl e => exact e
      | inr hlt =>
        have := sq_add_lt_of_lt hlt
        omega
  rw [hst] at h
  omega

theorem CountableSet.mono {S S' : Ordinal.{u} → Prop} (h : CountableSet S')
    (hS : ∀ x, S x → S' x) : CountableSet S := by
  cases h with
  | intro f hf => exact Exists.intro f (fun x y hx hy e => hf x y (hS x hx) (hS y hy) e)

theorem CountableSet.iUnion {I : Ordinal.{u} → Prop} {A : Ordinal.{u} → Ordinal.{u} → Prop}
    (hI : CountableSet I) (hA : ∀ i, I i → CountableSet (A i)) :
    CountableSet (fun z => ∃ i, I i ∧ A i z) := by
  classical
  cases hI with
  | intro fI hfI =>
    let enc : Ordinal.{u} → Ordinal.{u} → Nat := fun i =>
      if h : I i then Classical.choose (hA i h) else fun _ => 0
    have henc : ∀ i, I i → ∀ x y, A i x → A i y → enc i x = enc i y → x = y := by
      intro i hi
      have e : enc i = Classical.choose (hA i hi) := dite_eq_left hi
      rw [e]
      exact Classical.choose_spec (hA i hi)
    let idx : Ordinal.{u} → Ordinal.{u} := fun z =>
      if h : ∃ i, I i ∧ A i z then Classical.choose h else 0
    have hidx : ∀ z, (∃ i, I i ∧ A i z) → I (idx z) ∧ A (idx z) z := by
      intro z h
      have e : idx z = Classical.choose h := dite_eq_left h
      rw [e]
      exact Classical.choose_spec h
    refine Exists.intro (fun z => pairNat (fI (idx z)) (enc (idx z) z)) ?_
    intro z w hz hw e
    have hp := pairNat_inj e
    have hiz := hidx z hz
    have hiw := hidx w hw
    have ei : idx z = idx w := hfI _ _ hiz.1 hiw.1 hp.1
    have he := hp.2
    rw [ei] at he hiz
    exact henc _ hiw.1 z w hiz.2 hiw.2 he

theorem Countable.mono {α β : Ordinal.{u}} (h : Countable β) (hαβ : α ≤ β) : Countable α := by
  cases h with
  | intro f hf =>
    exact Exists.intro f (fun x y hx hy e =>
      hf x y (lt_of_lt_of_le hx hαβ) (lt_of_lt_of_le hy hαβ) e)

theorem countable_omega : Countable (omega : Ordinal.{u}) := by
  refine Exists.intro natOf (fun x y hx hy e => ?_)
  cases (lt_omega_iff x).mp hx with
  | intro m hm =>
    cases (lt_omega_iff y).mp hy with
    | intro k hk =>
      rw [hm, hk, natOf_ordNat, natOf_ordNat] at e
      rw [hm, hk, e]

theorem Countable.succ {α : Ordinal.{u}} (h : Countable α) : Countable (succ α) := by
  classical
  cases h with
  | intro f hf =>
    refine Exists.intro (fun x => if x = α then 0 else f x + 1) ?_
    intro x y hx hy e
    by_cases hxa : x = α
    · by_cases hya : y = α
      · rw [hxa, hya]
      · simp only [hxa, hya, ↓reduceIte] at e
        omega
    · by_cases hya : y = α
      · simp only [hxa, hya, ↓reduceIte] at e
        omega
      · simp only [hxa, hya, ↓reduceIte] at e
        have hx' : x < α := lt_of_le_of_ne (le_of_lt_succ hx) hxa
        have hy' : y < α := lt_of_le_of_ne (le_of_lt_succ hy) hya
        exact hf x y hx' hy' (by omega)

theorem cofinalFrom_self {w : Ordinal.{u}} (hw : IsLimit w) : CofinalFrom w w := by
  refine Exists.intro (fun x => type ((representative w).below x))
    (And.intro (fun x => initial_lt w x) ?_)
  apply le_antisymm
  · exact (sup_le_iff _ _).mpr (fun x => le_of_lt (initial_lt w x))
  · apply le_of_not_lt
    intro hlt
    cases initial_surjective w _ (hw.succ_lt hlt) with
    | intro x hx =>
      have := le_sup (fun x : (representative w).Carrier => type ((representative w).below x)) x
      rw [← hx] at this
      exact not_lt_of_le this (lt_succ_self _)

theorem R_of_least_uncountable {w : Ordinal.{u}} (hw : ¬ Countable w)
    (hmin : ∀ α, α < w → Countable α) : R w := by
  have hω : omega < w := by
    apply lt_of_not_le
    intro hle
    exact hw (countable_omega.mono hle)
  have hl : IsLimit w := by
    apply And.intro (lt_of_le_of_lt (zero_le _) hω)
    intro β hβ
    apply lt_of_le_of_ne (succ_le_of_lt hβ)
    intro e
    exact hw (e ▸ (hmin β hβ).succ)
  refine And.intro hω (And.intro hl ?_)
  have hcof := cofinalFrom_self hl
  apply le_antisymm (least_le (fun β => CofinalFrom β w) hcof)
  apply le_of_not_lt
  intro hcf
  have hspec := (least_spec (fun β => CofinalFrom β w) (Exists.intro w hcof)).1
  cases hspec with
  | intro F hF =>
    apply hw
    let β := cf w
    let G : Ordinal.{u} → Ordinal.{u} := fun i =>
      open Classical in
      if h : i < β then F (Classical.choose (initial_surjective β i h)) else 0
    have hG : ∀ x, G (type ((representative β).below x)) = F x := by
      intro x
      have h : type ((representative β).below x) < β := initial_lt β x
      have e : G (type ((representative β).below x)) =
          F (Classical.choose (initial_surjective β _ h)) := dite_eq_left h
      rw [e]
      congr 1
      exact (initial_injective β _ _ (Classical.choose_spec (initial_surjective β _ h))).symm
    have hcover : ∀ ξ, ξ < w → ∃ i, i < β ∧ ξ < G i := by
      intro ξ hξ
      have := hF.2 ▸ hξ
      cases (lt_sup_iff _ ξ).mp this with
      | intro x hx =>
        refine Exists.intro _ (And.intro (initial_lt β x) ?_)
        rw [hG x]
        exact hx
    have hGw : ∀ i, i < β → G i < w := by
      intro i hi
      have e : G i = F (Classical.choose (initial_surjective β i hi)) := dite_eq_left hi
      rw [e]
      exact hF.1 _
    have hc : CountableSet (fun z => ∃ i, (fun i => i < β) i ∧ (fun i z => z < G i) i z) :=
      CountableSet.iUnion (hmin β hcf) (fun i hi => hmin (G i) (hGw i hi))
    cases hc.mono (S := fun z => z < w) (fun z hz => hcover z hz) with
    | intro f hf => exact Exists.intro f hf

section Hypothesis

variable [LargeCardinals.{u}]

theorem Ω_least_uncountable :
    ¬ Countable (Ω : Ordinal.{u}) ∧ ∀ α : Ordinal.{u}, α < Ω → Countable α := by
  have hR : R (Ω : Ordinal.{u}) := isRegBelowΛ₀_Ω.R
  apply And.intro
  · intro h
    cases h with
    | intro f hf =>
      apply not_small_self hR.regular
      refine Exists.intro omega (And.intro omega_lt_Ω (Exists.intro (fun x => ordNat (f x))
        (And.intro (fun x _ => ordNat_lt_omega _) ?_)))
      intro x y hx hy e
      exact hf x y hx hy (ordNat_injective e)
  · intro α hα
    apply Classical.byContradiction
    intro hα'
    cases Ordinal.exists_min (fun β => ¬ Countable β) (Exists.intro α hα') with
    | intro w hw =>
      have hmin : ∀ β, β < w → Countable β :=
        fun β hβ => Classical.byContradiction (hw.2 β hβ)
      have hRw := R_of_least_uncountable hw.1 hmin
      have hΩw : (Ω : Ordinal.{u}) ≤ w :=
        δ_le (subset_closure (And.intro hRw (fun m hm => absurd hm (Nat.not_lt_zero m))))
      have hwα : w ≤ α := le_of_not_lt (fun hlt => hw.2 α hlt hα')
      exact absurd (lt_of_le_of_lt (le_trans hΩw hwα) hα) (lt_irrefl _)

end Hypothesis

end
end OCF.Jaeger

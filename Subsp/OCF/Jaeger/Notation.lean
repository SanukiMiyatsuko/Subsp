import Subsp.OCF.Jaeger.Psi

/-! Jäger's notation system: terms, `Term.lt`, `Term.H`, `Term.wf` and their semantics. -/

namespace OCF.Jaeger

inductive Term : Type where
  | zero : Term
  | add (a b : Term) : Term
  | inacc (n : Nat) (b : Term) : Term
  | psi (u b : Term) : Term
  deriving DecidableEq, Repr

namespace Term

def size : Term → Nat
  | zero => 1
  | add a b => size a + size b + 1
  | inacc _ b => size b + 1
  | psi u b => size u + size b + 1

theorem size_pos (a : Term) : 0 < size a := by
  cases a <;> simp only [size] <;> omega

def bigOmega : Term := inacc 0 zero

def one : Term := psi bigOmega zero

def isPrin : Term → Bool
  | zero => false
  | add _ _ => false
  | inacc _ _ => true
  | psi _ _ => true

def head : Term → Term
  | zero => zero
  | add a _ => a
  | inacc n b => inacc n b
  | psi u b => psi u b

def comps : Term → List Term
  | zero => []
  | add a b => a :: comps b
  | inacc n b => [inacc n b]
  | psi u b => [psi u b]

def fT : Term → Nat
  | zero => 0
  | add _ _ => 0
  | inacc n _ => n
  | psi u _ => fT u

def isSucc : Term → Bool
  | zero => false
  | add _ b => isSucc b
  | inacc _ _ => false
  | psi u b => decide (psi u b = one)

def predT : Term → Term
  | zero => zero
  | add a b => if b = one then a else add a (predT b)
  | inacc _ _ => zero
  | psi _ _ => zero

def isLimT (a : Term) : Bool := !(decide (a = zero)) && !(isSucc a)

def lt : Term → Term → Bool
  | zero, zero => false
  | zero, add _ _ => true
  | zero, inacc _ _ => true
  | zero, psi _ _ => true
  | add _ _, zero => false
  | add a₁ a₂, add b₁ b₂ => if a₁ = b₁ then lt a₂ b₂ else lt a₁ b₁
  | add a₁ _, inacc n c => lt a₁ (inacc n c)
  | add a₁ _, psi v c => lt a₁ (psi v c)
  | inacc _ _, zero => false
  | inacc n c, add b₁ _ => if inacc n c = b₁ then true else lt (inacc n c) b₁
  | inacc n₁ c₁, inacc n₂ c₂ =>
    if n₁ < n₂ then lt c₁ (inacc n₂ c₂) else if n₁ = n₂ then lt c₁ c₂ else lt (inacc n₁ c₁) c₂
  | inacc n c, psi v b =>
    (decide (n < fT v) && lt c (psi v b)) || (decide (fT v ≤ n) && lt (inacc n c) v)
  | psi _ _, zero => false
  | psi v c, add b₁ _ => if psi v c = b₁ then true else lt (psi v c) b₁
  | psi v b, inacc n c =>
    (decide (n < fT v) && (decide (psi v b = c) || lt (psi v b) c)) ||
      (decide (fT v ≤ n) && (decide (v = inacc n c) || lt v (inacc n c)))
  | psi u₁ b₁, psi u₂ b₂ =>
    (lt u₁ u₂ && lt u₁ (psi u₂ b₂)) || (decide (u₁ = u₂) && lt b₁ b₂) ||
      (lt u₂ u₁ && lt (psi u₁ b₁) u₂)
termination_by a b => size a + size b
decreasing_by all_goals (simp only [size]; omega)

def le (a b : Term) : Bool := decide (a = b) || lt a b

def predR : Term → Term
  | zero => zero
  | add _ _ => zero
  | inacc n b =>
    if b = zero then zero else if fT (predT b) ≤ n then inacc n (predT b) else predT b
  | psi _ _ => zero

def hOne (u : Term) : List Term :=
  if le one (predR u) then [] else if lt bigOmega u then [] else [zero]

def H (u : Term) : Term → List Term
  | zero => []
  | add a b => H u a ++ H u b
  | inacc n b => (if n = 0 then [] else hOne u) ++ H u b
  | psi v b =>
    if le (psi v b) (predR u) then [] else if lt v u then H u v else b :: (H u b ++ H u v)

def allLt (l : List Term) (b : Term) : Bool := l.all (fun c => lt c b)

def isRT : Term → Bool
  | zero => false
  | add _ _ => false
  | inacc _ b => !(isLimT b)
  | psi _ _ => false

def wf : Term → Bool
  | zero => true
  | add a b => isPrin a && wf a && wf b && !(decide (b = zero)) && le (head b) a
  | inacc n b => wf b && decide (fT b ≤ n)
  | psi u b => isRT u && wf u && wf b && allLt (H u b) b

end Term

end OCF.Jaeger

namespace OCF.Jaeger

universe u

open Ordinal

noncomputable section

theorem add_isLimit {a b : Ordinal.{u}} (hb : IsLimit b) : IsLimit (a + b) := by
  apply And.intro (lt_of_lt_of_le hb.1 (right_le_add a b))
  intro x hx
  cases (lt_add_iff a b x).mp hx with
  | inl h => exact lt_of_le_of_lt (succ_le_of_lt h) (lt_add_of_pos a hb.1)
  | inr h =>
    cases h with
    | intro d hd =>
      have h1 : succ x ≤ a + succ d := by
        rw [add_succ]
        exact succ_mono hd.2
      exact lt_of_le_of_lt h1 (add_lt_add_right a (hb.2 d hd.1))

theorem succ_of_add_eq_succ {a b x : Ordinal.{u}} (hb : b ≠ 0) (h : a + b = succ x) :
    ∃ y, b = succ y := by
  cases zero_or_succ_or_limit b with
  | inl h0 => exact absurd h0 hb
  | inr h' =>
    cases h' with
    | inl hs => exact hs
    | inr hl => exact absurd h ((add_isLimit hl).ne_succ x)

theorem IsPrincipal.eq_one_of_succ {p x : Ordinal.{u}} (hp : IsPrincipal p) (h : p = succ x) :
    p = succ 0 := by
  cases eq_zero_or_pos x with
  | inl h0 => rw [h, h0]
  | inr hpos =>
    have h1 : succ 0 < p := by
      rw [h]
      exact succ_lt_succ hpos
    have := hp.succ_lt h1 (by rw [h]; exact lt_succ_self x)
    rw [← h] at this
    exact absurd this (lt_irrefl p)

theorem one_add_ordNat (n : Nat) : succ 0 + ordNat.{u} n = ordNat (n + 1) := by
  induction n with
  | zero => rw [ordNat_zero, add_zero]; rfl
  | succ n ih => rw [ordNat_succ, add_succ, ih]; rfl

theorem listSum_replicate_one (n : Nat) :
    listSum (List.replicate n (succ (0 : Ordinal.{u}))) = ordNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, listSum_cons, ih, one_add_ordNat]

theorem cnf_ordNat (n : Nat) : CNF (ordNat.{u} n) (List.replicate n (succ 0)) := by
  refine And.intro ?_ (And.intro ?_ (listSum_replicate_one n).symm)
  · intro p hp
    rw [List.eq_of_mem_replicate hp]
    exact isPrincipal_one
  · apply List.pairwise_replicate.mpr
    exact Or.inr (le_refl _)

theorem cnf_lt_iff_head {x y p q : Ordinal.{u}} {l m : List Ordinal.{u}} (hx : CNF x (p :: l))
    (hy : CNF y (q :: m)) (hpq : p ≠ q) : x < y ↔ p < q := by
  apply Iff.intro
  · intro h
    cases lt_or_le p q with
    | inl h' => exact h'
    | inr h' =>
      cases h' with
      | inl hqp => exact absurd h (lt_asymm (lt_of_lt_of_le (hy.lt_of_head_lt hx.head_principal hqp)
          hx.head_le))
      | inr e => exact absurd e.symm hpq
  · intro h
    exact lt_of_lt_of_le (hx.lt_of_head_lt hy.head_principal h) hy.head_le

section Hypothesis

variable [LargeCardinals.{u}]

theorem HMem_one_iff {κ ξ : Ordinal.{u}} :
    HMem κ (succ 0) ξ ↔ regPred κ < succ 0 ∧ κ ≤ Ω ∧ ξ = 0 := by
  have hΩ : ∀ ζ, ¬ HMem κ Ω ζ := by
    intro ζ h
    have hlt : (0 : Ordinal.{u}) < I 0 0 := I_pos 0 Λ₀_pos
    cases (HMem_inacc_iff hlt (I_lt_Λ₀ 0 Λ₀_pos)).mp h with
    | inl h => exact HMem_zero h
    | inr h => exact HMem_zero h
  rw [← Ψ_Ω_zero, HMem_psi_iff isRegBelowΛ₀_Ω (C_zero Ω 0)]
  apply Iff.intro
  · intro h
    cases h.2 with
    | inl h' => exact absurd h'.2 (hΩ ξ)
    | inr h' =>
      cases h'.2 with
      | inl e => exact And.intro h.1 (And.intro h'.1 e)
      | inr h'' =>
        cases h'' with
        | inl h'' => exact absurd h'' HMem_zero
        | inr h'' => exact absurd h'' (hΩ ξ)
  · intro h
    exact And.intro h.1 (Or.inr (And.intro h.2.1 (Or.inl h.2.2)))

omit [LargeCardinals.{u}] in
theorem HMem_ordNat_iff {κ ξ : Ordinal.{u}} (n : Nat) :
    HMem κ (ordNat n) ξ ↔ n ≠ 0 ∧ HMem κ (succ 0) ξ := by
  cases n with
  | zero =>
    exact Iff.intro (fun h => absurd h HMem_zero) (fun h => absurd rfl h.1)
  | succ n =>
    cases n with
    | zero =>
      exact Iff.intro (fun h => And.intro (Nat.succ_ne_zero 0) h) (fun h => h.2)
    | succ n =>
      have hpos : (0 : Ordinal.{u}) < ordNat (n + 2) := lt_of_le_of_lt (zero_le _)
        (ordNat_lt (Nat.zero_lt_succ (n + 1)))
      have hP : ¬ IsPrincipal (ordNat.{u} (n + 2)) := by
        intro hP
        have := hP.2 (ordNat (n + 1)) (succ 0) (ordNat_lt (Nat.lt_succ_self (n + 1)))
          (ordNat_lt (Nat.one_lt_succ_succ n))
        rw [add_one_eq_succ, ← ordNat_succ] at this
        exact lt_irrefl _ this
      rw [HMem_sum_iff hpos (nfSum_of_cnf (cnf_ordNat (n + 2)) hP)]
      apply Iff.intro
      · intro h
        cases h with
        | intro p hp =>
          rw [List.eq_of_mem_replicate hp.1] at hp
          exact And.intro (Nat.succ_ne_zero _) hp.2
      · intro h
        exact Exists.intro (succ 0) (And.intro (List.mem_replicate.mpr
          (And.intro (Nat.succ_ne_zero _) rfl)) h.2)

end Hypothesis

namespace Term

def V : Term → Ordinal.{u}
  | zero => 0
  | add a b => V a + V b
  | inacc n b => I n (V b)
  | psi v b => Ψ (V v) (V b)

theorem V_zero : V.{u} zero = 0 := rfl

theorem V_add (a b : Term) : V.{u} (add a b) = V a + V b := rfl

theorem V_inacc (n : Nat) (b : Term) : V.{u} (inacc n b) = I n (V b) := rfl

theorem V_psi (v b : Term) : V.{u} (psi v b) = Ψ (V v) (V b) := rfl

theorem V_bigOmega : V.{u} bigOmega = Ω := rfl

theorem listSum_comps (a : Term) : listSum ((comps a).map V.{u}) = V a := by
  induction a with
  | zero => rfl
  | add a b _ ihb =>
    show V a + listSum ((comps b).map V) = V a + V b
    rw [ihb]
  | inacc n b _ => exact add_zero _
  | psi v b _ _ => exact add_zero _

theorem comps_of_isPrin {a : Term} (h : isPrin a = true) : comps a = [a] := by
  cases a with
  | zero => exact (nomatch h)
  | add _ _ => exact (nomatch h)
  | inacc n b => rfl
  | psi v b => rfl

theorem comps_eq_head_cons {a : Term} (h : a ≠ zero) : ∃ r, comps a = head a :: r := by
  cases a with
  | zero => exact absurd rfl h
  | add a b => exact Exists.intro (comps b) rfl
  | inacc n b => exact Exists.intro [] rfl
  | psi v b => exact Exists.intro [] rfl

theorem isPrin_ne_zero {a : Term} (h : isPrin a = true) : a ≠ zero := by
  intro e
  rw [e] at h
  exact (nomatch h)

theorem wf_add_iff (a b : Term) :
    wf (add a b) = true ↔
      isPrin a = true ∧ wf a = true ∧ wf b = true ∧ b ≠ zero ∧ le (head b) a = true := by
  simp only [wf, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  apply Iff.intro
  · intro h
    exact And.intro h.1.1.1.1 (And.intro h.1.1.1.2 (And.intro h.1.1.2 (And.intro h.1.2 h.2)))
  · intro h
    exact And.intro (And.intro (And.intro (And.intro h.1 h.2.1) h.2.2.1) h.2.2.2.1) h.2.2.2.2

theorem wf_inacc_iff (n : Nat) (b : Term) : wf (inacc n b) = true ↔ wf b = true ∧ fT b ≤ n := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq]

theorem wf_psi_iff (v b : Term) :
    wf (psi v b) = true ↔
      isRT v = true ∧ wf v = true ∧ wf b = true ∧ allLt (H v b) b = true := by
  simp only [wf, Bool.and_eq_true]
  apply Iff.intro
  · intro h
    exact And.intro h.1.1.1 (And.intro h.1.1.2 (And.intro h.1.2 h.2))
  · intro h
    exact And.intro (And.intro (And.intro h.1 h.2.1) h.2.2.1) h.2.2.2

theorem allLt_iff (l : List Term) (b : Term) : allLt l b = true ↔ ∀ c, c ∈ l → lt c b = true := by
  unfold allLt
  simp only [List.all_eq_true]

theorem wf_zero : wf zero = true := rfl

theorem wf_bigOmega : wf bigOmega = true := rfl

theorem wf_one : wf one = true := by
  simp only [one, bigOmega, wf, isRT, isLimT, isSucc, H, allLt]
  rfl

theorem isSucc_eq_one {a : Term} (hp : isPrin a = true) (h : isSucc a = true) : a = one := by
  cases a with
  | zero => exact (nomatch hp)
  | add _ _ => exact (nomatch hp)
  | inacc _ _ => exact (nomatch h)
  | psi v b =>
    simp only [isSucc, decide_eq_true_eq] at h
    exact h

theorem predT_add (a b : Term) : predT (add a b) = if b = one then a else add a (predT b) := rfl

theorem head_predT_add {c d : Term} (hc : isPrin c = true) :
    head (predT (add c d)) = c ∧ predT (add c d) ≠ zero := by
  rw [predT_add]
  by_cases h : d = one
  · simp only [h, ↓reduceIte]
    cases c with
    | zero => exact nomatch hc
    | add _ _ => exact nomatch hc
    | inacc _ _ => exact And.intro rfl (by intro e; cases e)
    | psi _ _ => exact And.intro rfl (by intro e; cases e)
  · simp only [h, ↓reduceIte]
    exact And.intro rfl (by intro e; cases e)

theorem size_predT_lt {a : Term} (h : isSucc a = true) : size (predT a) < size a := by
  induction a with
  | zero => exact (nomatch h)
  | add a b _ ihb =>
    rw [predT_add]
    by_cases hb : b = one
    · simp only [hb, ↓reduceIte, size]
      omega
    · simp only [hb, ↓reduceIte, size]
      have := ihb h
      omega
  | inacc _ _ _ => exact (nomatch h)
  | psi v b _ _ =>
    have := size_pos v
    simp only [predT, size]
    omega

theorem le_iff_eq_or_lt (a b : Term) : le a b = true ↔ a = b ∨ lt a b = true := by
  simp only [le, Bool.or_eq_true, decide_eq_true_eq]

end Term

open Term

structure Sem (a : Term) : Prop where
  T : Jaeger.T (V.{u} a)
  cnf : CNF (V.{u} a) ((comps a).map V)
  fT_eq : fT a = fIndex (V.{u} a)
  succ_iff : isSucc a = true ↔ ∃ x, V.{u} a = succ x
  succ_pred : isSucc a = true →
    wf (predT a) = true ∧ V.{u} a = succ (V.{u} (predT a)) ∧ size (predT a) < size a
  isR_iff : isRT a = true ↔ R (V.{u} a)
  isR_pred : isRT a = true →
    wf (predR a) = true ∧ V.{u} (predR a) = regPred (V.{u} a) ∧ size (predR a) < size a
  inacc_ok : ∀ n b, a = inacc n b → V.{u} b < I n (V.{u} b)
  psi_ok : ∀ v b, a = psi v b → IsRegBelowΛ₀ (V.{u} v) ∧ C (V.{u} v) (V.{u} b) (V.{u} b)

section Hypothesis

variable [LargeCardinals.{u}]

theorem V_one : V.{u} one = succ 0 := Ψ_Ω_zero

namespace Sem

theorem lt_Λ₀ {a : Term} (h : Sem.{u} a) : V.{u} a < Λ₀ := lemma_5_1 h.T

omit [LargeCardinals.{u}] in
theorem zero_iff {a : Term} (h : Sem.{u} a) : a = Term.zero ↔ V.{u} a = 0 := by
  apply Iff.intro
  · intro e
    rw [e]
    rfl
  · intro e
    apply Classical.byContradiction
    intro hne
    cases comps_eq_head_cons hne with
    | intro r hr =>
      have hc := h.cnf
      rw [hr] at hc
      exact absurd e (ne_of_gt hc.pos)

omit [LargeCardinals.{u}] in
theorem pos {a : Term} (h : Sem.{u} a) (ha : a ≠ Term.zero) : 0 < V.{u} a :=
  pos_of_ne_zero (fun e => ha (h.zero_iff.mpr e))

omit [LargeCardinals.{u}] in
theorem principal_of_isPrin {a : Term} (h : Sem.{u} a) (hp : isPrin a = true) :
    IsPrincipal (V.{u} a) := by
  have hc := h.cnf
  rw [comps_of_isPrin hp] at hc
  exact hc.head_principal

omit [LargeCardinals.{u}] in
theorem isPrin_of_principal {a : Term} (h : Sem.{u} a) (hw : wf a = true)
    (hP : IsPrincipal (V.{u} a)) : isPrin a = true := by
  have hc := cnf_of_principal hP h.cnf
  cases a with
  | zero => exact absurd (rfl : V.{u} Term.zero = 0) (ne_of_gt hP.pos)
  | add a b =>
    have hb := ((wf_add_iff a b).mp hw).2.2.2.1
    cases comps_eq_head_cons hb with
    | intro r hr =>
      simp only [comps, hr, List.map_cons, List.cons.injEq, List.cons_ne_nil, and_false] at hc
  | inacc n b => rfl
  | psi v b => rfl

omit [LargeCardinals.{u}] in
theorem lim_iff {a : Term} (h : Sem.{u} a) : isLimT a = true ↔ IsLimit (V.{u} a) := by
  simp only [isLimT, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  apply Iff.intro
  · intro h'
    apply isLimit_iff_not _ (fun e => h'.1 (h.zero_iff.mpr e))
    intro hs
    have := h.succ_iff.mpr hs
    rw [h'.2] at this
    exact absurd this (by decide)
  · intro hl
    apply And.intro
    · intro e
      rw [h.zero_iff.mp e] at hl
      exact not_isLimit_zero hl
    · cases hs : isSucc a with
      | false => rfl
      | true =>
        cases h.succ_iff.mp hs with
        | intro x hx => exact absurd hx (hl.ne_succ x)

end Sem

omit [LargeCardinals.{u}] in
theorem sem_zero : Sem.{u} Term.zero where
  T := T_zero
  cnf := cnf_zero
  fT_eq := fIndex_zero.symm
  succ_iff := Iff.intro (fun h => nomatch h) (fun h => by
    cases h with
    | intro x hx => exact absurd hx.symm (succ_ne_zero x))
  succ_pred := fun h => nomatch h
  isR_iff := Iff.intro (fun h => nomatch h) (fun h => absurd h.pos (lt_irrefl 0))
  isR_pred := fun h => nomatch h
  inacc_ok := fun _ _ h => by cases h
  psi_ok := fun _ _ h => by cases h

theorem sem_add {a b : Term} (hw : wf (add a b) = true) (ha : Sem.{u} a) (hb : Sem.{u} b)
    (hle : V.{u} (head b) ≤ V a) : Sem.{u} (add a b) := by
  have hw' := (wf_add_iff a b).mp hw
  have haP := ha.principal_of_isPrin hw'.1
  have hbpos := hb.pos hw'.2.2.2.1
  have hcnf : CNF (V.{u} (add a b)) ((comps (add a b)).map V) := by
    refine And.intro ?_ (And.intro ?_ ?_)
    · intro p hp
      cases List.mem_cons.mp hp with
      | inl e => rw [e]; exact haP
      | inr hp => exact hb.cnf.principal hp
    · apply List.pairwise_cons.mpr
      apply And.intro _ hb.cnf.2.1
      intro q hq
      cases comps_eq_head_cons hw'.2.2.2.1 with
      | intro r hr =>
        have hc := hb.cnf
        rw [hr] at hc hq
        exact le_trans (hc.mem_le_head hq) hle
    · rw [← listSum_comps]
  have hP : ¬ IsPrincipal (V.{u} (add a b)) := by
    intro hP
    have hl := cnf_of_principal hP hcnf
    cases comps_eq_head_cons hw'.2.2.2.1 with
    | intro r hr =>
      rw [show comps (add a b) = a :: comps b from rfl, hr] at hl
      simp only [List.map_cons, List.cons.injEq, List.cons_ne_nil, and_false] at hl
  have hNF : NFSum (V.{u} (add a b)) ((comps (add a b)).map V) := nfSum_of_cnf hcnf hP
  have hpos : 0 < V.{u} (add a b) := lt_of_lt_of_le haP.pos (le_add _ _)
  exact {
    T := T_add ha.T hb.T
    cnf := hcnf
    fT_eq := (fIndex_of_not_principal hP).symm
    succ_iff := by
      show isSucc b = true ↔ _
      rw [hb.succ_iff]
      apply Iff.intro
      · intro h
        cases h with
        | intro y hy => exact Exists.intro (V a + y) (by rw [V_add, hy, add_succ])
      · intro h
        cases h with
        | intro x hx => exact succ_of_add_eq_succ (ne_of_gt hbpos) hx
    succ_pred := by
      intro hs
      have hs' : isSucc b = true := hs
      rw [predT_add]
      by_cases hone : b = one
      · simp only [hone, ↓reduceIte]
        refine And.intro hw'.2.1 (And.intro ?_ ?_)
        · rw [V_add, V_one, add_one_eq_succ]
        · simp only [size]
          omega
      · simp only [hone, ↓reduceIte]
        have hsp := hb.succ_pred hs'
        have hbadd : ∃ c d, b = Term.add c d := by
          cases b with
          | zero => exact (nomatch hs')
          | add c d => exact Exists.intro c (Exists.intro d rfl)
          | inacc _ _ => exact (nomatch hs')
          | psi v c =>
            exact absurd (isSucc_eq_one (by rfl) hs') hone
        cases hbadd with
        | intro c hcd =>
          cases hcd with
          | intro d hcd =>
            have hwb := hw'.2.2.1
            rw [hcd] at hwb
            have hhd := head_predT_add (d := d) ((wf_add_iff c d).mp hwb).1
            refine And.intro ?_ (And.intro ?_ ?_)
            · apply (wf_add_iff _ _).mpr
              refine And.intro hw'.1 (And.intro hw'.2.1 (And.intro hsp.1 (And.intro ?_ ?_)))
              · rw [hcd]; exact hhd.2
              · rw [hcd, hhd.1]
                have := hw'.2.2.2.2
                rw [hcd] at this
                exact this
            · rw [V_add, V_add, hsp.2.1, add_succ]
            · have := hsp.2.2
              simp only [size]
              omega
    isR_iff := Iff.intro (fun h => nomatch h) (fun h => absurd h.isPrincipal hP)
    isR_pred := fun h => nomatch h
    inacc_ok := fun _ _ h => by cases h
    psi_ok := fun _ _ h => by cases h
  }

theorem T_inacc_of {n : Nat} {γ : Ordinal.{u}} (hγ : Jaeger.T γ) (hlt : γ < I n γ) :
    Jaeger.T (I n γ) := by
  cases T_ordNat.{u} n with
  | intro d hd =>
    cases hγ with
    | intro e he =>
      exact (TD.inacc (max d e) n γ (hd.mono (Nat.le_max_left d e))
        (he.mono (Nat.le_max_right d e)) hlt).T

omit [LargeCardinals.{u}] in
theorem T_psi_of {κ β : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hκT : Jaeger.T κ) (hβT : Jaeger.T β)
    (hβ : C κ β β) : Jaeger.T (Ψ κ β) := by
  cases hκT with
  | intro d hd =>
    cases hβT with
    | intro e he =>
      exact (TD.psi (max d e) κ β hκ (hd.mono (Nat.le_max_left d e))
        (he.mono (Nat.le_max_right d e)) hβ).T

theorem sem_inacc {n : Nat} {b : Term} (hw : wf (inacc n b) = true) (hb : Sem.{u} b)
    (hpb : isSucc b = true → Sem.{u} (predT b)) : Sem.{u} (inacc n b) := by
  have hw' := (wf_inacc_iff n b).mp hw
  have hlt : V.{u} b < I n (V b) := (lemma_5_4 hb.T n).mpr (hb.fT_eq ▸ hw'.2)
  have hbΛ := hb.lt_Λ₀
  have hIΛ : I n (V.{u} b) < Λ₀ := I_lt_Λ₀ n hbΛ
  have hP : IsPrincipal (V.{u} (inacc n b)) := I_isPrincipal_of_lt hlt
  have hRiff : R (I n (V.{u} b)) ↔ ¬ IsLimit (V.{u} b) :=
    Iff.intro (fun hR => not_isLimit_of_lt_regular hR hlt hIΛ rfl)
      (fun hnl => R_of_NFI (And.intro rfl hnl) hbΛ)
  exact {
    T := T_inacc_of hb.T hlt
    cnf := cnf_single hP
    fT_eq := (fIndex_I hlt hIΛ).symm
    succ_iff := Iff.intro (fun h => nomatch h) (fun h => by
      cases h with
      | intro x hx => exact absurd hx ((I_mem n hbΛ).isLimit.ne_succ x))
    succ_pred := fun h => nomatch h
    isR_iff := by
      show (!(isLimT b)) = true ↔ R (I n (V.{u} b))
      rw [hRiff, ← hb.lim_iff]
      cases isLimT b <;> simp
    isR_pred := by
      intro hR
      have hR' : isLimT b = false := by
        have : (!(isLimT b)) = true := hR
        cases h : isLimT b with
        | false => rfl
        | true => rw [h] at this; exact nomatch this
      have hpr : predR (inacc n b) = (if b = Term.zero then Term.zero else
          if fT (predT b) ≤ n then inacc n (predT b) else predT b) := rfl
      rw [hpr]
      by_cases hb0 : b = Term.zero
      · rw [hb0]
        simp only [↓reduceIte]
        refine And.intro rfl (And.intro ?_ ?_)
        · show (0 : Ordinal.{u}) = regPred (I n 0)
          rw [regPred_I_zero]
        · simp only [size]
          omega
      · simp only [hb0, ↓reduceIte]
        have hs : isSucc b = true := by
          simp only [isLimT, Bool.and_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at hR'
          cases hR' with
          | inl h => exact absurd h hb0
          | inr h => exact h
        have hsp := hb.succ_pred hs
        have spb := hpb hs
        have hxΛ := spb.lt_Λ₀
        have hreg : regPred (V.{u} (inacc n b)) = I n (V (predT b)) := by
          rw [V_inacc, hsp.2.1]
          exact regPred_I_succ n hxΛ
        by_cases hf : fT (predT b) ≤ n
        · simp only [hf, ↓reduceIte]
          refine And.intro ((wf_inacc_iff n _).mpr (And.intro hsp.1 hf)) (And.intro hreg.symm ?_)
          have := hsp.2.2
          simp only [size]
          omega
        · simp only [hf, ↓reduceIte]
          refine And.intro hsp.1 (And.intro ?_ ?_)
          · rw [hreg]
            apply le_antisymm (le_I n hxΛ)
            apply le_of_not_lt
            intro hlt'
            exact hf (spb.fT_eq ▸ (lemma_5_4 spb.T n).mp hlt')
          · have := hsp.2.2
            simp only [size]
            omega
    inacc_ok := fun _ _ h => by cases h; exact hlt
    psi_ok := fun _ _ h => by cases h
  }

theorem sem_psi {v b : Term} (hw : wf (psi v b) = true) (hv : Sem.{u} v) (hb : Sem.{u} b)
    (hC : C (V.{u} v) (V b) (V b))
    (hone : V.{u} v = Ω → V.{u} b = 0 → v = bigOmega ∧ b = Term.zero) : Sem.{u} (psi v b) := by
  have hw' := (wf_psi_iff v b).mp hw
  have hκ : IsRegBelowΛ₀ (V.{u} v) := And.intro (hv.isR_iff.mp hw'.1) hv.lt_Λ₀
  have hP : IsPrincipal (V.{u} (psi v b)) := lemma_4_5_a _ _
  exact {
    T := T_psi_of hκ hv.T hb.T hC
    cnf := cnf_single hP
    fT_eq := by
      show fT v = fIndex (Ψ (V v) (V b))
      cases theorem_3_4 hκ.R hκ.lt_Λ₀ with
      | intro ρ h =>
        cases h with
        | intro σ hσ =>
          rw [hv.fT_eq, fIndex_psi hκ hC hσ.1, hσ.1.1]
          exact fIndex_I (hσ.1.1 ▸ hσ.1.lt hκ.R) (hσ.1.1 ▸ hκ.lt_Λ₀)
    succ_iff := by
      show decide (psi v b = one) = true ↔ _
      rw [decide_eq_true_iff]
      apply Iff.intro
      · intro e
        rw [e, V_one]
        exact Exists.intro 0 rfl
      · intro h
        cases h with
        | intro x hx =>
          have e1 := hP.eq_one_of_succ hx
          rw [V_psi, ← Ψ_Ω_zero] at e1
          have e2 := theorem_4_11 hκ isRegBelowΛ₀_Ω e1 hC (C_zero Ω 0)
          have e3 := hone e2.1 e2.2
          rw [e3.1, e3.2]
          rfl
    succ_pred := by
      intro hs
      have e : psi v b = one := of_decide_eq_true hs
      cases e
      refine And.intro rfl (And.intro ?_ ?_)
      · show V.{u} one = succ (V Term.zero)
        exact V_one
      · decide
    isR_iff := Iff.intro (fun h => nomatch h) (fun h => absurd h (lemma_4_7_b hκ _))
    isR_pred := fun h => nomatch h
    inacc_ok := fun _ _ h => by cases h
    psi_ok := fun _ _ h => by cases h; exact And.intro hκ hC
  }

end Hypothesis

end
end OCF.Jaeger

namespace OCF.Jaeger

universe u

open Ordinal Term

noncomputable section

section Hypothesis

variable [LargeCardinals.{u}]

omit [LargeCardinals.{u}] in
theorem HMem_comps {κ ξ : Ordinal.{u}} {a : Term} (s : Sem.{u} a) (hw : wf a = true)
    (ha : a ≠ Term.zero) : HMem κ (V a) ξ ↔ ∃ p, p ∈ comps a ∧ HMem κ (V p) ξ := by
  cases a with
  | zero => exact absurd rfl ha
  | add c d =>
    have hNP : ¬ IsPrincipal (V.{u} (add c d)) := fun hP => nomatch s.isPrin_of_principal hw hP
    rw [HMem_sum_iff (s.pos ha) (nfSum_of_cnf s.cnf hNP)]
    apply Iff.intro
    · intro h
      cases h with
      | intro x hx =>
        cases List.mem_map.mp hx.1 with
        | intro p hp =>
          refine Exists.intro p (And.intro hp.1 ?_)
          rw [hp.2]
          exact hx.2
    · intro h
      cases h with
      | intro p hp => exact Exists.intro (V p) (And.intro (List.mem_map.mpr
          (Exists.intro p (And.intro hp.1 rfl))) hp.2)
  | inacc n b =>
    apply Iff.intro
    · intro h
      exact Exists.intro _ (And.intro List.mem_cons_self h)
    · intro h
      cases h with
      | intro p hp =>
        rw [List.mem_singleton.mp hp.1] at hp
        exact hp.2
  | psi v b =>
    apply Iff.intro
    · intro h
      exact Exists.intro _ (And.intro List.mem_cons_self h)
    · intro h
      cases h with
      | intro p hp =>
        rw [List.mem_singleton.mp hp.1] at hp
        exact hp.2

omit [LargeCardinals.{u}] in
theorem le_corr {a b : Term} (hL : lt a b = true ↔ V.{u} a < V b)
    (hI : V.{u} a = V b → a = b) : le a b = true ↔ V.{u} a ≤ V b := by
  rw [le_iff_eq_or_lt, hL]
  apply Iff.intro
  · intro h
    cases h with
    | inl e => rw [e]; exact le_refl _
    | inr h => exact Or.inl h
  · intro h
    cases h with
    | inl h => exact Or.inr h
    | inr e => exact Or.inl (hI e)

omit [LargeCardinals.{u}] in
theorem size_isRT {v : Term} (h : isRT v = true) : 2 ≤ size v := by
  cases v with
  | zero => exact nomatch h
  | add _ _ => exact nomatch h
  | inacc n c =>
    have := size_pos c
    simp only [size]
    omega
  | psi _ _ => exact nomatch h

omit [LargeCardinals.{u}] in
theorem mem_hOne {v x : Term} (h : x ∈ hOne v) : x = Term.zero := by
  unfold hOne at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · exact List.mem_singleton.mp h

theorem H_corr {v : Term} {N : Nat} (hvR : isRT v = true) (hv : Sem.{u} v) (hvw : wf v = true)
    (hS : ∀ c, size c < N → wf c = true → Sem.{u} c)
    (hL : ∀ c d, size c < N → size d < N → wf c = true → wf d = true →
      (lt c d = true ↔ V.{u} c < V d))
    (hI : ∀ c d, size c < N → size d < N → wf c = true → wf d = true → V.{u} c = V d → c = d) :
    ∀ b, size v + size b < N → wf b = true →
      (∀ c, c ∈ H v b → wf c = true ∧ size c ≤ size b) ∧
      (∀ ξ, HMem (V.{u} v) (V b) ξ ↔ ∃ c, c ∈ H v b ∧ V.{u} c = ξ) := by
  have hvsize := size_isRT hvR
  have hpr := hv.isR_pred hvR
  have hle : ∀ c d, size c < N → size d < N → wf c = true → wf d = true →
      (le c d = true ↔ V.{u} c ≤ V d) :=
    fun c d hc hd hwc hwd => le_corr (hL c d hc hd hwc hwd) (hI c d hc hd hwc hwd)
  intro b
  induction b with
  | zero =>
    intro _ _
    apply And.intro
    · intro c hc
      exact nomatch hc
    · intro ξ
      apply Iff.intro
      · intro h
        exact absurd h HMem_zero
      · intro h
        cases h with
        | intro c hc => exact nomatch hc.1
  | add c d ihc ihd =>
    intro hsz hw
    have hsz' : size v + size c < N ∧ size v + size d < N := by
      simp only [size] at hsz
      omega
    have hw' := (wf_add_iff c d).mp hw
    have hc' := ihc hsz'.1 hw'.2.1
    have hd' := ihd hsz'.2 hw'.2.2.1
    have sadd := hS (add c d) (by omega) hw
    have sd := hS d (by omega) hw'.2.2.1
    have hcomps : ∀ ξ, HMem (V.{u} v) (V d) ξ ↔ ∃ p, p ∈ comps d ∧ HMem (V.{u} v) (V p) ξ :=
      fun ξ => HMem_comps sd hw'.2.2.1 hw'.2.2.2.1
    apply And.intro
    · intro x hx
      cases List.mem_append.mp hx with
      | inl hx =>
        have := hc'.1 x hx
        exact And.intro this.1 (by simp only [size]; omega)
      | inr hx =>
        have := hd'.1 x hx
        exact And.intro this.1 (by simp only [size]; omega)
    · intro ξ
      rw [HMem_comps sadd hw (by intro e; cases e)]
      show (∃ p, p ∈ c :: comps d ∧ HMem _ (V p) ξ) ↔ ∃ x, x ∈ H v c ++ H v d ∧ V x = ξ
      apply Iff.intro
      · intro h
        cases h with
        | intro p hp =>
          cases List.mem_cons.mp hp.1 with
          | inl e =>
            rw [e] at hp
            cases (hc'.2 ξ).mp hp.2 with
            | intro x hx => exact Exists.intro x (And.intro (List.mem_append_left _ hx.1) hx.2)
          | inr hpd =>
            cases (hd'.2 ξ).mp ((hcomps ξ).mpr (Exists.intro p (And.intro hpd hp.2))) with
            | intro x hx => exact Exists.intro x (And.intro (List.mem_append_right _ hx.1) hx.2)
      · intro h
        cases h with
        | intro x hx =>
          cases List.mem_append.mp hx.1 with
          | inl hxc =>
            exact Exists.intro c (And.intro List.mem_cons_self
              ((hc'.2 ξ).mpr (Exists.intro x (And.intro hxc hx.2))))
          | inr hxd =>
            cases (hcomps ξ).mp ((hd'.2 ξ).mpr (Exists.intro x (And.intro hxd hx.2))) with
            | intro p hp => exact Exists.intro p (And.intro (List.mem_cons_of_mem _ hp.1) hp.2)
  | inacc n c ihc =>
    intro hsz hw
    have hsz' : size v + size c < N := by
      simp only [size] at hsz
      omega
    have hw' := (wf_inacc_iff n c).mp hw
    have hc' := ihc hsz' hw'.1
    have si := hS (inacc n c) (by omega) hw
    have hlt := si.inacc_ok n c rfl
    have hIΛ := si.lt_Λ₀
    have hcsize := size_pos c
    have hN4 : 4 < N := by
      simp only [size] at hsz
      omega
    have hone_le : le one (predR v) = true ↔ succ 0 ≤ regPred (V.{u} v) := by
      rw [hle one (predR v) (by simp only [one, bigOmega, size]; omega) (by omega) wf_one hpr.1,
        V_one, hpr.2.1]
    have hom_lt : lt bigOmega v = true ↔ Ω < V.{u} v :=
      hL bigOmega v (by simp only [bigOmega, size]; omega) (by omega) wf_bigOmega hvw
    have hOne_corr : ∀ ξ, (∃ x, x ∈ hOne v ∧ V.{u} x = ξ) ↔
        (regPred (V.{u} v) < succ 0 ∧ V.{u} v ≤ Ω ∧ ξ = 0) := by
      intro ξ
      unfold hOne
      by_cases h1 : le one (predR v) = true
      · simp only [h1, ↓reduceIte]
        apply Iff.intro
        · intro h
          cases h with
          | intro x hx => exact nomatch hx.1
        · intro h
          exact absurd (hone_le.mp h1) (not_le_of_lt h.1)
      · simp only [h1, ↓reduceIte, Bool.false_eq_true]
        by_cases h2 : lt bigOmega v = true
        · simp only [h2, ↓reduceIte]
          apply Iff.intro
          · intro h
            cases h with
            | intro x hx => exact nomatch hx.1
          · intro h
            exact absurd (hom_lt.mp h2) (not_lt_of_le h.2.1)
        · simp only [h2, ↓reduceIte, Bool.false_eq_true]
          apply Iff.intro
          · intro h
            cases h with
            | intro x hx =>
              rw [List.mem_singleton.mp hx.1] at hx
              refine And.intro (lt_of_not_le (fun h' => h1 (hone_le.mpr h')))
                (And.intro (le_of_not_lt (fun h' => h2 (hom_lt.mpr h'))) hx.2.symm)
          · intro h
            exact Exists.intro Term.zero (And.intro List.mem_cons_self h.2.2.symm)
    apply And.intro
    · intro x hx
      cases List.mem_append.mp hx with
      | inl hx =>
        have hn : n ≠ 0 := by
          intro hn
          rw [hn] at hx
          exact nomatch hx
        simp only [hn, ↓reduceIte] at hx
        rw [mem_hOne hx]
        exact And.intro wf_zero (by simp only [size]; omega)
      | inr hx =>
        have := hc'.1 x hx
        exact And.intro this.1 (by simp only [size]; omega)
    · intro ξ
      rw [V_inacc, HMem_inacc_iff hlt hIΛ, HMem_ordNat_iff, HMem_one_iff, hc'.2 ξ]
      show _ ↔ ∃ x, x ∈ (if n = 0 then [] else hOne v) ++ H v c ∧ V x = ξ
      apply Iff.intro
      · intro h
        cases h with
        | inl h =>
          have hn := h.1
          simp only [hn, ↓reduceIte]
          cases (hOne_corr ξ).mpr h.2 with
          | intro x hx => exact Exists.intro x (And.intro (List.mem_append_left _ hx.1) hx.2)
        | inr h =>
          cases h with
          | intro x hx => exact Exists.intro x (And.intro (List.mem_append_right _ hx.1) hx.2)
      · intro h
        cases h with
        | intro x hx =>
          cases List.mem_append.mp hx.1 with
          | inl hx1 =>
            have hn : n ≠ 0 := by
              intro hn
              rw [hn] at hx1
              exact nomatch hx1
            simp only [hn, ↓reduceIte] at hx1
            exact Or.inl (And.intro hn ((hOne_corr ξ).mp (Exists.intro x (And.intro hx1 hx.2))))
          | inr hx1 => exact Or.inr (Exists.intro x (And.intro hx1 hx.2))
  | psi w c ihw ihc =>
    intro hsz hw
    have hsz' : size v + size w < N ∧ size v + size c < N := by
      simp only [size] at hsz
      omega
    have hw' := (wf_psi_iff w c).mp hw
    have sp := hS (psi w c) (by omega) hw
    have hok := sp.psi_ok w c rfl
    have hw_ := ihw hsz'.1 hw'.2.1
    have hc_ := ihc hsz'.2 hw'.2.2.1
    have hle_ : le (psi w c) (predR v) = true ↔ Ψ (V.{u} w) (V c) ≤ regPred (V.{u} v) := by
      rw [hle _ _ (by omega) (by omega) hw hpr.1, hpr.2.1]
      rfl
    have hlt_ : lt w v = true ↔ V.{u} w < V v := hL w v (by omega) (by omega) hw'.2.1 hvw
    have hHeq : H v (psi w c) =
        if le (psi w c) (predR v) then [] else if lt w v then H v w else c :: (H v c ++ H v w) :=
      rfl
    apply And.intro
    · intro x hx
      rw [hHeq] at hx
      by_cases h1 : le (psi w c) (predR v) = true
      · simp only [h1, ↓reduceIte] at hx
        exact nomatch hx
      · simp only [h1, ↓reduceIte, Bool.false_eq_true] at hx
        by_cases h2 : lt w v = true
        · simp only [h2, ↓reduceIte] at hx
          have := hw_.1 x hx
          exact And.intro this.1 (by simp only [size]; omega)
        · simp only [h2, ↓reduceIte, Bool.false_eq_true] at hx
          cases List.mem_cons.mp hx with
          | inl e =>
            rw [e]
            exact And.intro hw'.2.2.1 (by simp only [size]; omega)
          | inr hx =>
            cases List.mem_append.mp hx with
            | inl hx =>
              have := hc_.1 x hx
              exact And.intro this.1 (by simp only [size]; omega)
            | inr hx =>
              have := hw_.1 x hx
              exact And.intro this.1 (by simp only [size]; omega)
    · intro ξ
      rw [V_psi, HMem_psi_iff hok.1 hok.2, hHeq]
      by_cases h1 : le (psi w c) (predR v) = true
      · simp only [h1, ↓reduceIte]
        apply Iff.intro
        · intro h
          exact absurd (hle_.mp h1) (not_le_of_lt h.1)
        · intro h
          cases h with
          | intro x hx => exact nomatch hx.1
      · have hpred : regPred (V.{u} v) < Ψ (V w) (V c) := lt_of_not_le (fun h => h1 (hle_.mpr h))
        simp only [h1, ↓reduceIte, Bool.false_eq_true]
        by_cases h2 : lt w v = true
        · have hπκ := hlt_.mp h2
          simp only [h2, ↓reduceIte]
          rw [← hw_.2 ξ]
          apply Iff.intro
          · intro h
            cases h.2 with
            | inl h' => exact h'.2
            | inr h' => exact absurd h'.1 (not_le_of_lt hπκ)
          · intro h
            exact And.intro hpred (Or.inl (And.intro hπκ h))
        · have hκπ : V.{u} v ≤ V w := le_of_not_lt (fun h => h2 (hlt_.mpr h))
          simp only [h2, ↓reduceIte, Bool.false_eq_true]
          apply Iff.intro
          · intro h
            cases h.2 with
            | inl h' => exact absurd h'.1 (not_lt_of_le hκπ)
            | inr h' =>
              cases h'.2 with
              | inl e => exact Exists.intro c (And.intro List.mem_cons_self e.symm)
              | inr h'' =>
                cases h'' with
                | inl hH =>
                  cases (hc_.2 ξ).mp hH with
                  | intro x hx => exact Exists.intro x (And.intro (List.mem_cons_of_mem _
                      (List.mem_append_left _ hx.1)) hx.2)
                | inr hH =>
                  cases (hw_.2 ξ).mp hH with
                  | intro x hx => exact Exists.intro x (And.intro (List.mem_cons_of_mem _
                      (List.mem_append_right _ hx.1)) hx.2)
          · intro h
            refine And.intro hpred (Or.inr (And.intro hκπ ?_))
            cases h with
            | intro x hx =>
              cases List.mem_cons.mp hx.1 with
              | inl e =>
                rw [e] at hx
                exact Or.inl hx.2.symm
              | inr hx' =>
                cases List.mem_append.mp hx' with
                | inl hxc => exact Or.inr (Or.inl ((hc_.2 ξ).mpr (Exists.intro x
                    (And.intro hxc hx.2))))
                | inr hxw => exact Or.inr (Or.inr ((hw_.2 ξ).mpr (Exists.intro x
                    (And.intro hxw hx.2))))

omit [LargeCardinals.{u}] in
theorem size_head_le (a : Term) : size (head a) ≤ size a := by
  cases a with
  | zero => exact Nat.le_refl _
  | add a b => simp only [head, size]; omega
  | inacc n b => exact Nat.le_refl _
  | psi v b => exact Nat.le_refl _

omit [LargeCardinals.{u}] in
theorem wf_head {a : Term} (h : wf a = true) : wf (head a) = true := by
  cases a with
  | zero => exact h
  | add a b => exact ((wf_add_iff a b).mp h).2.1
  | inacc n b => exact h
  | psi v b => exact h

theorem inj_step {n : Nat} {a b : Term} (ha : size a ≤ n) (hb : size b ≤ n) (hwa : wf a = true)
    (hwb : wf b = true) (sa : Sem.{u} a) (sb : Sem.{u} b)
    (hsub : ∀ c d, size c ≤ n → size d ≤ n → size c + size d < size a + size b →
      wf c = true → wf d = true → V.{u} c = V d → c = d)
    (e : V.{u} a = V b) : a = b := by
  have hP : ∀ x y : Term, wf x = true → Sem.{u} x → Sem.{u} y → isPrin x = false →
      isPrin y = true → V.{u} x = V y → False := by
    intro x y hwx sx sy hx hy e
    have := sx.isPrin_of_principal hwx (e ▸ sy.principal_of_isPrin hy)
    rw [hx] at this
    exact nomatch this
  cases a with
  | zero => exact (sb.zero_iff.mpr e.symm).symm
  | add a₁ a₂ =>
    have hwa' := (wf_add_iff a₁ a₂).mp hwa
    cases b with
    | zero => exact sa.zero_iff.mpr e
    | add b₁ b₂ =>
      have hwb' := (wf_add_iff b₁ b₂).mp hwb
      have hcb : CNF (V.{u} (add a₁ a₂)) ((comps (add b₁ b₂)).map V) := by
        rw [e]
        exact sb.cnf
      have hl := cnf_unique sa.cnf hcb
      simp only [comps, List.map_cons, List.cons.injEq] at hl
      have e₂ : V.{u} a₂ = V b₂ := by
        rw [← listSum_comps a₂, ← listSum_comps b₂, hl.2]
      rw [hsub a₁ b₁ (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.1 hwb'.2.1 hl.1,
        hsub a₂ b₂ (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.2.1 hwb'.2.2.1 e₂]
    | inacc m d => exact (hP _ _ hwa sa sb rfl rfl e).elim
    | psi w d => exact (hP _ _ hwa sa sb rfl rfl e).elim
  | inacc m c =>
    have hwa' := (wf_inacc_iff m c).mp hwa
    cases b with
    | zero => exact sa.zero_iff.mpr e
    | add b₁ b₂ => exact (hP _ _ hwb sb sa rfl rfl e.symm).elim
    | inacc k d =>
      have hwb' := (wf_inacc_iff k d).mp hwb
      have r := I_rep_unique (sa.inacc_ok m c rfl) (sb.inacc_ok k d rfl) e sa.lt_Λ₀
      rw [r.1, hsub c d (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
        (by simp only [size]; omega) hwa'.1 hwb'.1 r.2]
    | psi w d => exact absurd e.symm (lemma_4_7_a (sb.psi_ok w d rfl).1 _ (sa.inacc_ok m c rfl))
  | psi v c =>
    have hwa' := (wf_psi_iff v c).mp hwa
    cases b with
    | zero => exact sa.zero_iff.mpr e
    | add b₁ b₂ => exact (hP _ _ hwb sb sa rfl rfl e.symm).elim
    | inacc k d => exact absurd e (lemma_4_7_a (sa.psi_ok v c rfl).1 _ (sb.inacc_ok k d rfl))
    | psi w d =>
      have hwb' := (wf_psi_iff w d).mp hwb
      have oa := sa.psi_ok v c rfl
      have ob := sb.psi_ok w d rfl
      have r := theorem_4_11 oa.1 ob.1 e oa.2 ob.2
      rw [hsub v w (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.1 hwb'.2.1 r.1,
        hsub c d (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.2.1 hwb'.2.2.1 r.2]

theorem fT_of_isRT {v : Term} (sv : Sem.{u} v) (hκ : IsRegBelowΛ₀ (V.{u} v)) {ρ : Nat}
    {σ : Ordinal.{u}} (hNF : NFI (V.{u} v) ρ σ) : fT v = ρ := by
  rw [sv.fT_eq, hNF.1]
  exact fIndex_I (hNF.1 ▸ hNF.lt hκ.R) (hNF.1 ▸ hκ.lt_Λ₀)

theorem lc_step {n : Nat} {a b : Term} (ha : size a ≤ n) (hb : size b ≤ n) (hwa : wf a = true)
    (hwb : wf b = true) (hS : ∀ c, size c ≤ n → wf c = true → Sem.{u} c)
    (hInj : ∀ c d, size c ≤ n → size d ≤ n → wf c = true → wf d = true → V.{u} c = V d → c = d)
    (hIH : ∀ c d, size c ≤ n → size d ≤ n → size c + size d < size a + size b →
      wf c = true → wf d = true → (lt c d = true ↔ V.{u} c < V d)) :
    lt a b = true ↔ V.{u} a < V b := by
  have sa := hS a ha hwa
  have sb := hS b hb hwb
  cases a with
  | zero =>
    cases b with
    | zero =>
      rw [Term.lt]
      exact Iff.intro (fun h => nomatch h) (fun h => absurd h (lt_irrefl _))
    | add _ _ =>
      rw [Term.lt]
      exact iff_of_true rfl (sb.pos (by intro e; cases e))
    | inacc _ _ =>
      rw [Term.lt]
      exact iff_of_true rfl (sb.pos (by intro e; cases e))
    | psi _ _ =>
      rw [Term.lt]
      exact iff_of_true rfl (sb.pos (by intro e; cases e))
  | add a₁ a₂ =>
    have hwa' := (wf_add_iff a₁ a₂).mp hwa
    have hca : CNF (V.{u} (add a₁ a₂)) (V a₁ :: (comps a₂).map V) := sa.cnf
    cases b with
    | zero =>
      rw [Term.lt]
      exact Iff.intro (fun h => nomatch h) (fun h => absurd h (not_lt_zero _))
    | add b₁ b₂ =>
      have hwb' := (wf_add_iff b₁ b₂).mp hwb
      have hcb : CNF (V.{u} (add b₁ b₂)) (V b₁ :: (comps b₂).map V) := sb.cnf
      rw [Term.lt]
      by_cases h : a₁ = b₁
      · subst h
        simp only [↓reduceIte]
        rw [hIH a₂ b₂ (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.2.1 hwb'.2.2.1, V_add, V_add,
          add_lt_add_iff_right]
      · simp only [h, ↓reduceIte]
        rw [hIH a₁ b₁ (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.1 hwb'.2.1]
        have hne : V.{u} a₁ ≠ V b₁ := fun e => h (hInj a₁ b₁ (by simp only [size] at ha; omega)
          (by simp only [size] at hb; omega) hwa'.2.1 hwb'.2.1 e)
        exact (cnf_lt_iff_head hca hcb hne).symm
    | inacc m d =>
      rw [Term.lt, hIH a₁ _ (by simp only [size] at ha; omega) hb (by simp only [size]; omega)
        hwa'.2.1 hwb]
      have hbP := sb.principal_of_isPrin (rfl : isPrin (inacc m d) = true)
      exact Iff.intro (fun h => hca.lt_of_head_lt hbP h) (fun h => lt_of_le_of_lt hca.head_le h)
    | psi w d =>
      rw [Term.lt, hIH a₁ _ (by simp only [size] at ha; omega) hb (by simp only [size]; omega)
        hwa'.2.1 hwb]
      have hbP := sb.principal_of_isPrin (rfl : isPrin (psi w d) = true)
      exact Iff.intro (fun h => hca.lt_of_head_lt hbP h) (fun h => lt_of_le_of_lt hca.head_le h)
  | inacc m c =>
    have hwa' := (wf_inacc_iff m c).mp hwa
    have sc := hS c (by simp only [size] at ha; omega) hwa'.1
    have haP := sa.principal_of_isPrin (rfl : isPrin (inacc m c) = true)
    cases b with
    | zero =>
      rw [Term.lt]
      exact Iff.intro (fun h => nomatch h) (fun h => absurd h (not_lt_zero _))
    | add b₁ b₂ =>
      have hwb' := (wf_add_iff b₁ b₂).mp hwb
      have hcb : CNF (V.{u} (add b₁ b₂)) (V b₁ :: (comps b₂).map V) := sb.cnf
      have sb₂ := hS b₂ (by simp only [size] at hb; omega) hwb'.2.2.1
      rw [Term.lt]
      by_cases h : inacc m c = b₁
      · subst h
        simp only [↓reduceIte]
        exact iff_of_true trivial (lt_add_of_pos _ (sb₂.pos hwb'.2.2.2.1))
      · simp only [h, ↓reduceIte]
        rw [hIH _ b₁ ha (by simp only [size] at hb; omega) (by simp only [size]; omega) hwa
          hwb'.2.1]
        have hne : V.{u} (inacc m c) ≠ V b₁ := fun e => h (hInj _ b₁ ha
          (by simp only [size] at hb; omega) hwa hwb'.2.1 e)
        apply Iff.intro
        · intro hlt
          exact lt_of_lt_of_le hlt hcb.head_le
        · intro hlt
          apply lt_of_not_le
          intro hle
          exact lt_asymm hlt (hcb.lt_of_head_lt haP (lt_of_le_of_ne hle (fun e => hne e.symm)))
    | inacc k d =>
      have hwb' := (wf_inacc_iff k d).mp hwb
      have sd := hS d (by simp only [size] at hb; omega) hwb'.1
      have h33 := theorem_3_3 m k sc.lt_Λ₀ sd.lt_Λ₀
      rw [Term.lt]
      by_cases h1 : m < k
      · simp only [h1, ↓reduceIte]
        rw [hIH c (inacc k d) (by simp only [size] at ha; omega) hb (by simp only [size]; omega)
          hwa'.1 hwb, V_inacc, V_inacc, h33]
        apply Iff.intro
        · intro h
          exact Or.inl (And.intro h1 h)
        · intro h
          cases h with
          | inl h => exact h.2
          | inr h =>
            cases h with
            | inl h => exact absurd h.1 (Nat.ne_of_lt h1)
            | inr h => exact absurd h.1 (Nat.lt_asymm h1)
      · by_cases h2 : m = k
        · subst h2
          simp only [Nat.lt_irrefl, ↓reduceIte]
          rw [hIH c d (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
            (by simp only [size]; omega) hwa'.1 hwb'.1, V_inacc, V_inacc, h33]
          apply Iff.intro
          · intro h
            exact Or.inr (Or.inl (And.intro rfl h))
          · intro h
            cases h with
            | inl h => exact absurd h.1 (Nat.lt_irrefl m)
            | inr h =>
              cases h with
              | inl h => exact h.2
              | inr h => exact absurd h.1 (Nat.lt_irrefl m)
        · have h3 : k < m := by omega
          simp only [h1, h2, ↓reduceIte]
          rw [hIH (inacc m c) d ha (by simp only [size] at hb; omega) (by simp only [size]; omega)
            hwa hwb'.1, V_inacc m c, V_inacc k d, h33]
          apply Iff.intro
          · intro h
            exact Or.inr (Or.inr (And.intro h3 h))
          · intro h
            cases h with
            | inl h => exact absurd h.1 h1
            | inr h =>
              cases h with
              | inl h => exact absurd h.1 h2
              | inr h => exact h.2
    | psi w d =>
      have hwb' := (wf_psi_iff w d).mp hwb
      have sw := hS w (by simp only [size] at hb; omega) hwb'.2.1
      have hok := sb.psi_ok w d rfl
      cases theorem_3_4 hok.1.R hok.1.lt_Λ₀ with
      | intro ρ h =>
        cases h with
        | intro σ hσ =>
          have hρ := fT_of_isRT sw hok.1 hσ.1
          rw [Term.lt]
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rw [hIH c (psi w d) (by simp only [size] at ha; omega) hb (by simp only [size]; omega)
              hwa'.1 hwb,
            hIH (inacc m c) w ha (by simp only [size] at hb; omega) (by simp only [size]; omega)
              hwa hwb'.2.1, hρ, V_inacc, V_psi]
          exact (theorem_4_12 hok.1 hσ.1 (V d) sc.lt_Λ₀).symm
  | psi v c =>
    have hwa' := (wf_psi_iff v c).mp hwa
    have sv := hS v (by simp only [size] at ha; omega) hwa'.2.1
    have hoka := sa.psi_ok v c rfl
    have haP : IsPrincipal (V.{u} (psi v c)) := lemma_4_5_a _ _
    cases b with
    | zero =>
      rw [Term.lt]
      exact Iff.intro (fun h => nomatch h) (fun h => absurd h (not_lt_zero _))
    | add b₁ b₂ =>
      have hwb' := (wf_add_iff b₁ b₂).mp hwb
      have hcb : CNF (V.{u} (add b₁ b₂)) (V b₁ :: (comps b₂).map V) := sb.cnf
      have sb₂ := hS b₂ (by simp only [size] at hb; omega) hwb'.2.2.1
      rw [Term.lt]
      by_cases h : psi v c = b₁
      · subst h
        simp only [↓reduceIte]
        exact iff_of_true trivial (lt_add_of_pos _ (sb₂.pos hwb'.2.2.2.1))
      · simp only [h, ↓reduceIte]
        rw [hIH _ b₁ ha (by simp only [size] at hb; omega) (by simp only [size]; omega) hwa
          hwb'.2.1]
        have hne : V.{u} (psi v c) ≠ V b₁ := fun e => h (hInj _ b₁ ha
          (by simp only [size] at hb; omega) hwa hwb'.2.1 e)
        apply Iff.intro
        · intro hlt
          exact lt_of_lt_of_le hlt hcb.head_le
        · intro hlt
          apply lt_of_not_le
          intro hle
          exact lt_asymm hlt (hcb.lt_of_head_lt haP (lt_of_le_of_ne hle (fun e => hne e.symm)))
    | inacc k d =>
      have hwb' := (wf_inacc_iff k d).mp hwb
      have sd := hS d (by simp only [size] at hb; omega) hwb'.1
      have hltd := sb.inacc_ok k d rfl
      cases theorem_3_4 hoka.1.R hoka.1.lt_Λ₀ with
      | intro ρ h =>
        cases h with
        | intro σ hσ =>
          have hρ := fT_of_isRT sv hoka.1 hσ.1
          have h412 := theorem_4_12 (β := k) hoka.1 hσ.1 (V c) sd.lt_Λ₀
          have hle1 : (psi v c = d ∨ lt (psi v c) d = true) ↔ V.{u} (psi v c) ≤ V d := by
            rw [← le_iff_eq_or_lt]
            exact le_corr (hIH _ d ha (by simp only [size] at hb; omega)
              (by simp only [size]; omega) hwa hwb'.1)
              (hInj _ d ha (by simp only [size] at hb; omega) hwa hwb'.1)
          have hle2 : (v = inacc k d ∨ lt v (inacc k d) = true) ↔ V.{u} v ≤ V (inacc k d) := by
            rw [← le_iff_eq_or_lt]
            exact le_corr (hIH v _ (by simp only [size] at ha; omega) hb
              (by simp only [size]; omega) hwa'.2.1 hwb)
              (hInj v _ (by simp only [size] at ha; omega) hb hwa'.2.1 hwb)
          have hne : V.{u} (psi v c) ≠ V (inacc k d) := lemma_4_7_a hoka.1 _ hltd
          rw [Term.lt]
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          rw [hle1, hle2, hρ]
          apply Iff.intro
          · intro h
            apply lt_of_le_of_ne _ hne
            apply le_of_not_lt
            intro hlt
            cases h412.mp hlt with
            | inl h' =>
              cases h with
              | inl h => exact not_lt_of_le h.2 h'.2
              | inr h => exact absurd h'.1 (Nat.not_lt.mpr h.1)
            | inr h' =>
              cases h with
              | inl h => exact absurd h.1 (Nat.not_lt.mpr h'.1)
              | inr h => exact not_lt_of_le h.2 h'.2
          · intro h
            cases Nat.lt_or_ge k ρ with
            | inl hk =>
              refine Or.inl (And.intro hk ?_)
              apply le_of_not_lt
              intro hc
              exact lt_asymm h (h412.mpr (Or.inl (And.intro hk hc)))
            | inr hk =>
              refine Or.inr (And.intro hk ?_)
              apply le_of_not_lt
              intro hc
              exact lt_asymm h (h412.mpr (Or.inr (And.intro hk hc)))
    | psi w d =>
      have hwb' := (wf_psi_iff w d).mp hwb
      have hokb := sb.psi_ok w d rfl
      have hu : v = w ↔ V.{u} v = V w := Iff.intro (fun e => by rw [e])
        (hInj v w (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          hwa'.2.1 hwb'.2.1)
      rw [Term.lt]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc]
      rw [hIH v w (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.1 hwb'.2.1,
        hIH v (psi w d) (by simp only [size] at ha; omega) hb (by simp only [size]; omega)
          hwa'.2.1 hwb,
        hIH c d (by simp only [size] at ha; omega) (by simp only [size] at hb; omega)
          (by simp only [size]; omega) hwa'.2.2.1 hwb'.2.2.1,
        hIH w v (by simp only [size] at hb; omega) (by simp only [size] at ha; omega)
          (by simp only [size]; omega) hwb'.2.1 hwa'.2.1,
        hIH (psi v c) w ha (by simp only [size] at hb; omega) (by simp only [size]; omega)
          hwa hwb'.2.1, hu]
      exact (theorem_4_13 hoka.1 hokb.1 hoka.2 hokb.2).symm

theorem good (n : Nat) :
    (∀ a, size a ≤ n → wf a = true → Sem.{u} a) ∧
    (∀ a b, size a ≤ n → size b ≤ n → wf a = true → wf b = true → V.{u} a = V b → a = b) ∧
    (∀ a b, size a ≤ n → size b ≤ n → wf a = true → wf b = true →
      (lt a b = true ↔ V.{u} a < V b)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hS' : ∀ a, size a < n → wf a = true → Sem.{u} a :=
      fun a ha hw => (ih (size a) ha).1 a (Nat.le_refl _) hw
    have hI' : ∀ a b, size a < n → size b < n → wf a = true → wf b = true →
        V.{u} a = V b → a = b :=
      fun a b ha hb => (ih (max (size a) (size b)) (Nat.max_lt.mpr (And.intro ha hb))).2.1 a b
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hL' : ∀ a b, size a < n → size b < n → wf a = true → wf b = true →
        (lt a b = true ↔ V.{u} a < V b) :=
      fun a b ha hb => (ih (max (size a) (size b)) (Nat.max_lt.mpr (And.intro ha hb))).2.2 a b
        (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    have hS : ∀ a, size a ≤ n → wf a = true → Sem.{u} a := by
      intro a ha hw
      cases a with
      | zero => exact sem_zero
      | add c d =>
        have hw' := (wf_add_iff c d).mp hw
        have sc := hS' c (by simp only [size] at ha; omega) hw'.2.1
        have sd := hS' d (by simp only [size] at ha; omega) hw'.2.2.1
        have hhd := size_head_le d
        apply sem_add hw sc sd
        exact (le_corr (hL' _ c (by simp only [size] at ha; omega) (by simp only [size] at ha; omega)
          (wf_head hw'.2.2.1) hw'.2.1) (hI' _ c (by simp only [size] at ha; omega)
          (by simp only [size] at ha; omega) (wf_head hw'.2.2.1) hw'.2.1)).mp hw'.2.2.2.2
      | inacc m c =>
        have hw' := (wf_inacc_iff m c).mp hw
        have sc := hS' c (by simp only [size] at ha; omega) hw'.1
        apply sem_inacc hw sc
        intro hs
        have hsp := sc.succ_pred hs
        exact hS' _ (by simp only [size] at ha; omega) hsp.1
      | psi v c =>
        have hw' := (wf_psi_iff v c).mp hw
        have sv := hS' v (by simp only [size] at ha; omega) hw'.2.1
        have sc := hS' c (by simp only [size] at ha; omega) hw'.2.2.1
        have hκ : IsRegBelowΛ₀ (V.{u} v) := And.intro (sv.isR_iff.mp hw'.1) sv.lt_Λ₀
        have hvsize := size_isRT hw'.1
        have hHc := H_corr (N := size (psi v c)) hw'.1 sv hw'.2.1
          (fun d hd hwd => hS' d (Nat.lt_of_lt_of_le hd ha) hwd)
          (fun d e hd he hwd hwe => hL' d e (Nat.lt_of_lt_of_le hd ha) (Nat.lt_of_lt_of_le he ha)
            hwd hwe)
          (fun d e hd he hwd hwe => hI' d e (Nat.lt_of_lt_of_le hd ha) (Nat.lt_of_lt_of_le he ha)
            hwd hwe) c (by simp only [size]; omega) hw'.2.2.1
        have hC : C (V.{u} v) (V c) (V c) := by
          apply (lemma_5_6 hκ sc.T (V c)).mpr
          intro ξ hξ
          cases (hHc.2 ξ).mp hξ with
          | intro x hx =>
            have hlt := (allLt_iff _ _).mp hw'.2.2.2 x hx.1
            have hxs := hHc.1 x hx.1
            rw [← hx.2]
            exact (hL' x c (by simp only [size] at ha; omega) (by simp only [size] at ha; omega)
              hxs.1 hw'.2.2.1).mp hlt
        apply sem_psi hw sv sc hC
        intro hvΩ hc0
        refine And.intro ?_ (sc.zero_iff.mpr hc0)
        apply hI' v bigOmega (by simp only [size] at ha; omega)
          (by have : size bigOmega = 2 := rfl; simp only [size] at ha; omega) hw'.2.1
          wf_bigOmega
        rw [hvΩ]
        rfl
    have hI : ∀ a b, size a ≤ n → size b ≤ n → wf a = true → wf b = true →
        V.{u} a = V b → a = b := by
      have key : ∀ k a b, size a + size b ≤ k → size a ≤ n → size b ≤ n → wf a = true →
          wf b = true → V.{u} a = V b → a = b := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ihk =>
          intro a b hk ha hb hwa hwb e
          exact inj_step ha hb hwa hwb (hS a ha hwa) (hS b hb hwb)
            (fun c d hc hd hcd hwc hwd e' => ihk (size c + size d) (Nat.lt_of_lt_of_le hcd hk) c d
              (Nat.le_refl _) hc hd hwc hwd e') e
      exact fun a b => key _ a b (Nat.le_refl _)
    have hL : ∀ a b, size a ≤ n → size b ≤ n → wf a = true → wf b = true →
        (lt a b = true ↔ V.{u} a < V b) := by
      have key : ∀ k a b, size a + size b ≤ k → size a ≤ n → size b ≤ n → wf a = true →
          wf b = true → (lt a b = true ↔ V.{u} a < V b) := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k ihk =>
          intro a b hk ha hb hwa hwb
          exact lc_step ha hb hwa hwb hS hI
            (fun c d hc hd hcd hwc hwd => ihk (size c + size d) (Nat.lt_of_lt_of_le hcd hk) c d
              (Nat.le_refl _) hc hd hwc hwd)
      exact fun a b => key _ a b (Nat.le_refl _)
    exact And.intro hS (And.intro hI hL)

theorem sem_of_wf {a : Term} (h : wf a = true) : Sem.{u} a := (good (size a)).1 a (Nat.le_refl _) h

theorem V_inj {a b : Term} (ha : wf a = true) (hb : wf b = true) (e : V.{u} a = V b) : a = b :=
  (good (max (size a) (size b))).2.1 a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) ha hb e

theorem lt_iff_V {a b : Term} (ha : wf a = true) (hb : wf b = true) :
    lt a b = true ↔ V.{u} a < V b :=
  (good (max (size a) (size b))).2.2 a b (Nat.le_max_left _ _) (Nat.le_max_right _ _) ha hb

theorem le_iff_V {a b : Term} (ha : wf a = true) (hb : wf b = true) :
    le a b = true ↔ V.{u} a ≤ V b := le_corr (lt_iff_V ha hb) (V_inj ha hb)

theorem H_iff {v b : Term} (hvR : isRT v = true) (hv : wf v = true) (hb : wf b = true)
    (ξ : Ordinal.{u}) : HMem (V.{u} v) (V b) ξ ↔ ∃ c, c ∈ H v b ∧ V.{u} c = ξ :=
  (H_corr (N := size v + size b + 1) hvR (sem_of_wf hv) hv (fun _ _ hc => sem_of_wf hc)
    (fun _ _ _ _ hc hd => lt_iff_V hc hd) (fun _ _ _ _ hc hd => V_inj hc hd) b
    (Nat.lt_succ_self _) hb).2 ξ

theorem H_wf {v b : Term} (hvR : isRT v = true) (hv : wf v = true) (hb : wf b = true)
    {c : Term} (hc : c ∈ H v b) : wf c = true :=
  ((H_corr (N := size v + size b + 1) hvR (sem_of_wf hv) hv (fun _ _ hc => sem_of_wf hc)
    (fun _ _ _ _ hc hd => lt_iff_V hc hd) (fun _ _ _ _ hc hd => V_inj hc hd) b
    (Nat.lt_succ_self _) hb).1 c hc).1

theorem exists_sum_term (p : Ordinal.{u}) (r : List Ordinal.{u})
    (h : ∀ q, q ∈ p :: r → IsPrincipal q ∧ ∃ a, wf a = true ∧ V.{u} a = q)
    (hnf : Nonincr (p :: r)) :
    ∃ t, wf t = true ∧ V.{u} t = listSum (p :: r) ∧ V.{u} (head t) = p ∧ t ≠ Term.zero := by
  induction r generalizing p with
  | nil =>
    cases (h p List.mem_cons_self).2 with
    | intro a ha =>
      have hP := (h p List.mem_cons_self).1
      have hprin : isPrin a = true := (sem_of_wf ha.1).isPrin_of_principal ha.1 (ha.2 ▸ hP)
      refine Exists.intro a (And.intro ha.1 (And.intro ?_ (And.intro ?_ (isPrin_ne_zero hprin))))
      · rw [listSum_cons, listSum_nil, add_zero, ha.2]
      · cases a with
        | zero => exact nomatch hprin
        | add _ _ => exact nomatch hprin
        | inacc n b => exact ha.2
        | psi v b => exact ha.2
  | cons q r ih =>
    have ht := ih q (fun x hx => h x (List.mem_cons_of_mem p hx))
      (List.pairwise_cons.mp hnf).2
    cases ht with
    | intro t ht =>
      cases (h p List.mem_cons_self).2 with
      | intro a ha =>
        have hP := (h p List.mem_cons_self).1
        have hprin : isPrin a = true := (sem_of_wf ha.1).isPrin_of_principal ha.1 (ha.2 ▸ hP)
        have hqp : q ≤ p := (List.pairwise_cons.mp hnf).1 q List.mem_cons_self
        refine Exists.intro (add a t) (And.intro ?_ (And.intro ?_ (And.intro ha.2 (by
          intro e; cases e))))
        · apply (wf_add_iff a t).mpr
          refine And.intro hprin (And.intro ha.1 (And.intro ht.1 (And.intro ht.2.2.2 ?_)))
          apply (le_iff_V (wf_head ht.1) ha.1).mpr
          rw [ht.2.2.1, ha.2]
          exact hqp
        · rw [V_add, ha.2, ht.2.1]
          rfl

theorem exists_term {α : Ordinal.{u}} (h : Jaeger.T α) : ∃ a, wf a = true ∧ V.{u} a = α := by
  cases h with
  | intro d h =>
    induction h with
    | zero _ => exact Exists.intro Term.zero (And.intro rfl rfl)
    | sum _ γ l h0 hNF _ ih =>
      cases l with
      | nil =>
        rw [hNF.1.eq] at h0
        exact absurd h0 (lt_irrefl 0)
      | cons p r =>
        cases exists_sum_term p r (fun q hq => And.intro (hNF.1.principal hq) (ih q hq))
          hNF.1.2.1 with
        | intro t ht => exact Exists.intro t (And.intro ht.1 (ht.2.1.trans hNF.1.eq.symm))
    | inacc _ β γ _ hγT hlt _ ihγ =>
      cases ihγ with
      | intro c hc =>
        refine Exists.intro (inacc β c) (And.intro ?_ ?_)
        · apply (wf_inacc_iff β c).mpr
          refine And.intro hc.1 ?_
          rw [(sem_of_wf hc.1).fT_eq, hc.2]
          exact (lemma_5_4 hγT.T β).mp hlt
        · rw [V_inacc, hc.2]
    | psi _ κ β hκ _ hβT hβ ihκ ihβ =>
      cases ihκ with
      | intro v hv =>
        cases ihβ with
        | intro c hc =>
          have sv := sem_of_wf hv.1
          have hvR : isRT v = true := sv.isR_iff.mpr (hv.2 ▸ hκ.R)
          refine Exists.intro (psi v c) (And.intro ?_ ?_)
          · apply (wf_psi_iff v c).mpr
            refine And.intro hvR (And.intro hv.1 (And.intro hc.1 ?_))
            apply (allLt_iff _ _).mpr
            intro x hx
            apply (lt_iff_V (H_wf hvR hv.1 hc.1 hx) hc.1).mpr
            have hH : HMem (V.{u} v) (V c) (V x) := (H_iff hvR hv.1 hc.1 _).mpr
              (Exists.intro x (And.intro hx rfl))
            rw [hv.2, hc.2] at hH
            rw [hc.2]
            exact (lemma_5_6 hκ hβT.T β).mp hβ _ hH
          · rw [V_psi, hv.2, hc.2]

def N (α : Ordinal.{u}) : Term :=
  open Classical in
  if h : ∃ a, wf a = true ∧ V.{u} a = α then Classical.choose h else Term.zero

theorem N_spec {α : Ordinal.{u}} (h : Jaeger.T α) : wf (N α) = true ∧ V.{u} (N α) = α := by
  have h' := exists_term h
  unfold N
  rw [dite_eq_left h']
  exact Classical.choose_spec h'

theorem lemma_6_1 :
    (∀ a, wf a = true → lt a a = false) ∧
    (∀ a b c, wf a = true → wf b = true → wf c = true →
      lt a b = true → lt b c = true → lt a c = true) ∧
    (∀ a b, wf a = true → wf b = true → lt a b = true ∨ a = b ∨ lt b a = true) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro a ha
    cases h : lt a a with
    | false => rfl
    | true => exact absurd ((lt_iff_V.{u} ha ha).mp h) (lt_irrefl _)
  · intro a b c ha hb hc hab hbc
    exact (lt_iff_V.{u} ha hc).mpr (lt_trans _ _ _ ((lt_iff_V.{u} ha hb).mp hab)
      ((lt_iff_V.{u} hb hc).mp hbc))
  · intro a b ha hb
    cases lt_total (V.{u} a) (V b) with
    | inl h => exact Or.inl ((lt_iff_V ha hb).mpr h)
    | inr h =>
      cases h with
      | inl h => exact Or.inr (Or.inl (V_inj ha hb h))
      | inr h => exact Or.inr (Or.inr ((lt_iff_V hb ha).mpr h))

theorem lemma_6_2 :
    (∀ α : Ordinal.{u}, Jaeger.T α → wf (N α) = true) ∧
    (∀ β γ : Ordinal.{u}, Jaeger.T β → Jaeger.T γ → β < γ → lt (N β) (N γ) = true) := by
  apply And.intro
  · exact fun α h => (N_spec h).1
  · intro β γ hβ hγ hlt
    apply (lt_iff_V (N_spec hβ).1 (N_spec hγ).1).mpr
    rw [(N_spec hβ).2, (N_spec hγ).2]
    exact hlt

theorem lemma_6_3 :
    (∀ a, wf a = true → Jaeger.T (V.{u} a)) ∧
    (∀ a b, wf a = true → wf b = true → lt a b = true → V.{u} a < V b) :=
  And.intro (fun _ h => (sem_of_wf h).T) (fun _ _ ha hb h => (lt_iff_V ha hb).mp h)

theorem lemma_6_4 :
    (∀ α : Ordinal.{u}, Jaeger.T α → V (N α) = α) ∧
    (∀ a, wf a = true → N (V.{u} a) = a) := by
  apply And.intro
  · exact fun α h => (N_spec h).2
  · intro a ha
    have h := N_spec (sem_of_wf.{u} ha).T
    exact V_inj h.1 ha h.2

theorem theorem_6_5_a :
    (∀ α : Ordinal.{u}, Jaeger.T α → wf (N α) = true) ∧
    (∀ a, wf a = true → ∃ α : Ordinal.{u}, Jaeger.T α ∧ N α = a) ∧
    (∀ β γ : Ordinal.{u}, Jaeger.T β → Jaeger.T γ → N β = N γ → β = γ) ∧
    (∀ β γ : Ordinal.{u}, Jaeger.T β → Jaeger.T γ → (lt (N β) (N γ) = true ↔ β < γ)) := by
  refine And.intro lemma_6_2.1 (And.intro ?_ (And.intro ?_ ?_))
  · intro a ha
    exact Exists.intro (V a) (And.intro (lemma_6_3.1 a ha) (lemma_6_4.2 a ha))
  · intro β γ hβ hγ e
    rw [← lemma_6_4.1 β hβ, ← lemma_6_4.1 γ hγ, e]
  · intro β γ hβ hγ
    rw [lt_iff_V (N_spec hβ).1 (N_spec hγ).1, (N_spec hβ).2, (N_spec hγ).2]

theorem N_add {β γ : Ordinal.{u}} (hβ : Jaeger.T β) (hγ : Jaeger.T γ) (hP : IsPrincipal β)
    (hγ0 : γ ≠ 0) (hle : ∀ p, IsComponent γ p → p ≤ β) : N (β + γ) = add (N β) (N γ) := by
  have sβ := N_spec hβ
  have sγ := N_spec hγ
  have hprin : isPrin (N β) = true :=
    (sem_of_wf sβ.1).isPrin_of_principal sβ.1 (by rw [sβ.2]; exact hP)
  have hγne : N γ ≠ Term.zero := by
    intro e
    have := sγ.2
    rw [e] at this
    exact hγ0 this.symm
  have hw : wf (add (N β) (N γ)) = true := by
    apply (wf_add_iff _ _).mpr
    refine And.intro hprin (And.intro sβ.1 (And.intro sγ.1 (And.intro hγne ?_)))
    apply (le_iff_V (wf_head sγ.1) sβ.1).mpr
    rw [sβ.2]
    have sN := sem_of_wf.{u} sγ.1
    cases comps_eq_head_cons hγne with
    | intro r hr =>
      have hc := sN.cnf
      rw [hr] at hc
      have hcomp : IsComponent (V.{u} (N γ)) (V (head (N γ))) :=
        Exists.intro _ (And.intro hc (List.mem_map.mpr
          (Exists.intro _ (And.intro List.mem_cons_self rfl))))
      rw [sγ.2] at hcomp
      exact hle _ hcomp
  have := lemma_6_4.2 _ hw
  rw [V_add, sβ.2, sγ.2] at this
  exact this

theorem N_inacc {β : Nat} {γ : Ordinal.{u}} (hγ : Jaeger.T γ) (hlt : γ < I β γ) :
    N (I β γ) = inacc β (N γ) := by
  have sγ := N_spec hγ
  have hw : wf (inacc β (N γ)) = true := by
    apply (wf_inacc_iff β _).mpr
    refine And.intro sγ.1 ?_
    rw [(sem_of_wf sγ.1).fT_eq, sγ.2]
    exact (lemma_5_4 hγ β).mp hlt
  have := lemma_6_4.2 _ hw
  rw [V_inacc, sγ.2] at this
  exact this

theorem N_psi {κ β : Ordinal.{u}} (hκ : IsRegBelowΛ₀ κ) (hκT : Jaeger.T κ) (hβT : Jaeger.T β)
    (hβ : C κ β β) : N (Ψ κ β) = psi (N κ) (N β) := by
  have sκ := N_spec hκT
  have sβ := N_spec hβT
  have hvR : isRT (N κ) = true := (sem_of_wf sκ.1).isR_iff.mpr (by rw [sκ.2]; exact hκ.R)
  have hw : wf (psi (N κ) (N β)) = true := by
    apply (wf_psi_iff _ _).mpr
    refine And.intro hvR (And.intro sκ.1 (And.intro sβ.1 ?_))
    apply (allLt_iff _ _).mpr
    intro x hx
    apply (lt_iff_V (H_wf hvR sκ.1 sβ.1 hx) sβ.1).mpr
    have hH : HMem (V.{u} (N κ)) (V (N β)) (V x) := (H_iff hvR sκ.1 sβ.1 _).mpr
      (Exists.intro x (And.intro hx rfl))
    rw [sκ.2, sβ.2] at hH
    rw [sβ.2]
    exact (lemma_5_6 hκ hβT β).mp hβ _ hH
  have := lemma_6_4.2 _ hw
  rw [V_psi, sκ.2, sβ.2] at this
  exact this

theorem N_zero : N (0 : Ordinal.{u}) = Term.zero :=
  lemma_6_4.2 Term.zero rfl

def termOrder : WellOrder.{u} where
  Carrier := ULift.{u} {a : Term // wf a = true ∧ lt a bigOmega = true}
  lt x y := lt x.down.1 y.down.1 = true
  irrefl x h := by
    rw [lemma_6_1.{u}.1 x.down.1 x.down.2.1] at h
    exact nomatch h
  trans x y z := lemma_6_1.{u}.2.1 _ _ _ x.down.2.1 y.down.2.1 z.down.2.1
  total x y := by
    cases lemma_6_1.{u}.2.2 x.down.1 y.down.1 x.down.2.1 y.down.2.1 with
    | inl h => exact Or.inl h
    | inr h =>
      cases h with
      | inl h =>
        apply Or.inr
        apply Or.inl
        cases x with
        | up x =>
          cases y with
          | up y =>
            congr 1
            exact Subtype.ext h
      | inr h => exact Or.inr (Or.inr h)
  wellFounded := Subrelation.wf (fun {x y} h => (lt_iff_V.{u} x.down.2.1 y.down.2.1).mp h)
    (InvImage.wf (fun x : ULift.{u} {a : Term // wf a = true ∧ lt a bigOmega = true} =>
      V.{u} x.down.1) lt_wellFounded)

theorem theorem_6_5_b : type termOrder.{u} = Ψ Ω Λ₀ := by
  let f : ULift.{u} {a : Term // wf a = true ∧ lt a bigOmega = true} → Ordinal.{u} :=
    fun x => V x.down.1
  have hf : ∀ x y, f x = f y → x = y := by
    intro x y e
    cases x with
    | up x =>
      cases y with
      | up y =>
        congr 1
        exact Subtype.ext (V_inj x.2.1 y.2.1 e)
  have hmem : ∀ x, f x < Ψ Ω Λ₀ := by
    intro x
    apply (corollary_5_3 _).mpr
    refine And.intro (lemma_6_3.1 _ x.down.2.1) ?_
    have := (lt_iff_V.{u} x.down.2.1 wf_bigOmega).mp x.down.2.2
    exact this
  have hd : ∀ x a, a < f x → ∃ y, f y = a := by
    intro x a ha
    have hT := (corollary_5_3 a).mp (lt_trans _ _ _ ha (hmem x))
    have sN := N_spec hT.1
    have hlt : lt (N a) bigOmega = true := by
      apply (lt_iff_V.{u} sN.1 wf_bigOmega).mpr
      rw [sN.2]
      exact hT.2
    exact Exists.intro (ULift.up ⟨N a, And.intro sN.1 hlt⟩) sN.2
  have hiso : WellOrder.Iso termOrder.{u} (orderOn f hf) := {
    toFun := fun x => show ULift.{u} {a : Term // wf a = true ∧ Term.lt a bigOmega = true} from x
    invFun := fun x => show ULift.{u} {a : Term // wf a = true ∧ Term.lt a bigOmega = true} from x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    lt_iff := fun x y => by
      show V.{u} (x : ULift.{u} {a : Term // wf a = true ∧ Term.lt a bigOmega = true}).down.1 <
          V (y : ULift.{u} {a : Term // wf a = true ∧ Term.lt a bigOmega = true}).down.1 ↔ _
      exact (lt_iff_V.{u} x.down.2.1 y.down.2.1).symm
  }
  rw [type_eq_of_iso hiso]
  apply eq_of_lt_iff
  intro c
  rw [lt_type_orderOn_iff f hf hd]
  apply Iff.intro
  · intro h
    cases h with
    | intro x hx =>
      rw [hx]
      exact hmem x
  · intro h
    have hT := (corollary_5_3 c).mp h
    have sN := N_spec hT.1
    have hlt : lt (N c) bigOmega = true := by
      apply (lt_iff_V.{u} sN.1 wf_bigOmega).mpr
      rw [sN.2]
      exact hT.2
    exact Exists.intro (ULift.up ⟨N c, And.intro sN.1 hlt⟩) sN.2.symm

end Hypothesis

end
end OCF.Jaeger

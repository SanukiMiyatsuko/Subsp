import Subsp.OCF.Jaeger.Notation

/-! Constructive order theory of Jäger's notation system: `Term.lt` is irreflexive, and on
`Term.wf` terms it is asymmetric, trichotomous and transitive.  Only `propext` and `Quot.sound`
are used. -/

namespace OCF.Jaeger.Term

macro "size_omega" : tactic => `(tactic| ((try simp only [size] at *); omega))

/-! ### Unfolding `lt` -/

theorem lt_zero_right (a : Term) : lt a zero = false := by cases a <;> rw [lt]

theorem lt_zero_left {b : Term} (hb : b ≠ zero) : lt zero b = true := by
  cases b <;> first | exact absurd rfl hb | rw [lt]

theorem lt_add_add (a₁ a₂ b₁ b₂ : Term) :
    lt (add a₁ a₂) (add b₁ b₂) = if a₁ = b₁ then lt a₂ b₂ else lt a₁ b₁ := by rw [lt]

theorem lt_add_prin {y : Term} (hy : isPrin y = true) (a₁ a₂ : Term) :
    lt (add a₁ a₂) y = lt a₁ y := by
  cases y <;> first | (cases hy; done) | rw [lt]

theorem lt_prin_add_iff {x : Term} (hx : isPrin x = true) (b₁ b₂ : Term) :
    lt x (add b₁ b₂) = true ↔ x = b₁ ∨ lt x b₁ = true := by
  cases x <;> first | (cases hx; done) | (rw [lt]; split <;> simp_all)

theorem lt_ii (n m : Nat) (c d : Term) :
    lt (inacc n c) (inacc m d) =
      if n < m then lt c (inacc m d) else if n = m then lt c d else lt (inacc n c) d := by rw [lt]

theorem lt_ii_lt {n m : Nat} (h : n < m) (c d : Term) :
    lt (inacc n c) (inacc m d) = lt c (inacc m d) := by rw [lt_ii, ite_eq_left h]

theorem lt_ii_eq (n : Nat) (c d : Term) : lt (inacc n c) (inacc n d) = lt c d := by
  rw [lt_ii, ite_eq_right (Nat.lt_irrefl n), ite_eq_left rfl]

theorem lt_ii_gt {n m : Nat} (h : m < n) (c d : Term) :
    lt (inacc n c) (inacc m d) = lt (inacc n c) d := by
  rw [lt_ii, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem lt_ip_iff (n : Nat) (c v b : Term) :
    lt (inacc n c) (psi v b) = true ↔
      (n < fT v ∧ lt c (psi v b) = true) ∨ (fT v ≤ n ∧ lt (inacc n c) v = true) := by
  rw [lt]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem lt_pi_iff (n : Nat) (c v b : Term) :
    lt (psi v b) (inacc n c) = true ↔
      (n < fT v ∧ (psi v b = c ∨ lt (psi v b) c = true)) ∨
        (fT v ≤ n ∧ (v = inacc n c ∨ lt v (inacc n c) = true)) := by
  rw [lt]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem lt_pp_iff (u₁ b₁ u₂ b₂ : Term) :
    lt (psi u₁ b₁) (psi u₂ b₂) = true ↔
      ((lt u₁ u₂ = true ∧ lt u₁ (psi u₂ b₂) = true) ∨ (u₁ = u₂ ∧ lt b₁ b₂ = true)) ∨
        (lt u₂ u₁ = true ∧ lt (psi u₁ b₁) u₂ = true) := by
  rw [lt]; simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem lt_ip_iff' (n : Nat) (c : Term) (l : Nat) (v' b : Term) :
    lt (inacc n c) (psi (inacc l v') b) = true ↔
      (n < l ∧ lt c (psi (inacc l v') b) = true) ∨
        (l ≤ n ∧ lt (inacc n c) (inacc l v') = true) :=
  lt_ip_iff n c (inacc l v') b

theorem lt_pi_iff' (n : Nat) (c : Term) (l : Nat) (v' b : Term) :
    lt (psi (inacc l v') b) (inacc n c) = true ↔
      (n < l ∧ (psi (inacc l v') b = c ∨ lt (psi (inacc l v') b) c = true)) ∨
        (l ≤ n ∧ (inacc l v' = inacc n c ∨ lt (inacc l v') (inacc n c) = true)) :=
  lt_pi_iff n c (inacc l v') b

/-! ### Irreflexivity and inversion of `wf` -/

theorem lt_irrefl : ∀ a : Term, lt a a = false
  | zero => by rw [lt]
  | add _ b => by rw [lt_add_add, ite_eq_left rfl]; exact lt_irrefl b
  | inacc _ c => by rw [lt_ii_eq]; exact lt_irrefl c
  | psi u b => by rw [lt, lt_irrefl u, lt_irrefl b]; simp

theorem ne_of_lt {a b : Term} (h : lt a b = true) : a ≠ b := by
  rintro rfl; rw [lt_irrefl] at h; cases h

theorem wf_add {a b : Term} (h : wf (add a b) = true) :
    isPrin a = true ∧ wf a = true ∧ wf b = true ∧ b ≠ zero ∧ le (head b) a = true := by
  rw [wf] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem wf_inacc {n : Nat} {b : Term} (h : wf (inacc n b) = true) : wf b = true ∧ fT b ≤ n := by
  rw [wf] at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h

theorem wf_psi {u b : Term} (h : wf (psi u b) = true) :
    isRT u = true ∧ wf u = true ∧ wf b = true ∧ allLt (H u b) b = true := by
  rw [wf] at h; simp only [Bool.and_eq_true] at h; exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem isRT_inacc {u : Term} (h : isRT u = true) : ∃ k u', u = inacc k u' := by
  cases u <;> first | exact ⟨_, _, rfl⟩ | cases h

theorem psi_ne_of_isRT {u v b : Term} (h : isRT u = true) : u ≠ psi v b := by
  rintro rfl; cases h

theorem shape (x : Term) : x = zero ∨ (∃ x₁ x₂, x = add x₁ x₂) ∨ isPrin x = true := by
  cases x <;> first | exact Or.inl rfl | exact Or.inr (Or.inl ⟨_, _, rfl⟩) | exact Or.inr (Or.inr rfl)

theorem ne_zero_of_isPrin {x : Term} (h : isPrin x = true) : x ≠ zero := by rintro rfl; cases h

/-! ### Asymmetry -/

theorem lt_asymm_aux (N : Nat) : ∀ x y : Term, size x + size y ≤ N →
    lt x y = true → lt y x = true → False := by
  induction N with
  | zero => intro x _ hs; have := size_pos x; exact absurd hs (by omega)
  | succ N ih =>
    intro x y hs h1 h2
    -- a principal term against a sum, and an inaccessible against a collapse
    have hps : ∀ {p a₁ a₂}, lt p (add a₁ a₂) = true → lt (add a₁ a₂) p = true →
        isPrin p = true → size p + size (add a₁ a₂) ≤ N + 1 → False := by
      intro p a₁ a₂ h1 h2 hp hs
      rw [lt_add_prin hp] at h2
      rcases (lt_prin_add_iff hp a₁ a₂).mp h1 with rfl | h1
      · exact ne_of_lt h2 rfl
      · exact ih p a₁ (by size_omega) h1 h2
    have hip : ∀ {n c v b}, lt (inacc n c) (psi v b) = true → lt (psi v b) (inacc n c) = true →
        size (inacc n c) + size (psi v b) ≤ N + 1 → False := by
      intro n c v b h1 h2 hs
      rcases (lt_ip_iff n c v b).mp h1 with ⟨hk, h1⟩ | ⟨hk, h1⟩ <;>
        rcases (lt_pi_iff n c v b).mp h2 with ⟨hk', e | h2⟩ | ⟨hk', e | h2⟩
      all_goals first
        | omega
        | (rw [e] at h1; exact ne_of_lt h1 rfl)
        | exact ih _ _ (by size_omega) h1 h2
    cases x <;> cases y
    all_goals first
      | (rw [lt_zero_right] at h1; cases h1)
      | (rw [lt_zero_right] at h2; cases h2)
      | exact hps h1 h2 rfl (by size_omega)
      | exact hps h2 h1 rfl (by size_omega)
      | exact hip h1 h2 (by size_omega)
      | exact hip h2 h1 (by size_omega)
      | skip
    case add.add x₁ x₂ y₁ y₂ =>
      rw [lt_add_add] at h1 h2
      by_cases e : x₁ = y₁
      · subst e
        rw [ite_eq_left rfl] at h1 h2
        exact ih x₂ y₂ (by size_omega) h1 h2
      · rw [ite_eq_right e] at h1
        rw [ite_eq_right (Ne.symm e)] at h2
        exact ih x₁ y₁ (by size_omega) h1 h2
    case inacc.inacc n c m d =>
      rcases Nat.lt_trichotomy n m with hnm | rfl | hnm
      · rw [lt_ii_lt hnm] at h1; rw [lt_ii_gt hnm] at h2; exact ih _ _ (by size_omega) h1 h2
      · rw [lt_ii_eq] at h1 h2; exact ih _ _ (by size_omega) h1 h2
      · rw [lt_ii_gt hnm] at h1; rw [lt_ii_lt hnm] at h2; exact ih _ _ (by size_omega) h1 h2
    case psi.psi u b v c =>
      rw [lt_pp_iff] at h1 h2
      rcases h1 with (⟨a1, a2⟩ | ⟨rfl, a2⟩) | ⟨a1, a2⟩ <;>
        rcases h2 with (⟨b1, b2⟩ | ⟨e', b2⟩) | ⟨b1, b2⟩
      all_goals first
        | exact ih _ _ (by size_omega) a1 b1
        | exact ih _ _ (by size_omega) a2 b2
        | exact ne_of_lt b1 rfl
        | exact ne_of_lt a1 e'.symm
        | exact ne_of_lt a1 e'

theorem lt_asymm {x y : Term} (h1 : lt x y = true) (h2 : lt y x = true) : False :=
  lt_asymm_aux (size x + size y) x y (Nat.le_refl _) h1 h2

theorem not_lt_of_lt {x y : Term} (h : lt x y = true) : lt y x = false := by
  cases e : lt y x with
  | false => rfl
  | true => exact (lt_asymm h e).elim

/-! ### Trichotomy -/

def Tri (x y : Term) : Prop := lt x y = true ∨ x = y ∨ lt y x = true

theorem Tri.symm {x y : Term} (h : Tri x y) : Tri y x :=
  h.elim (fun h => Or.inr (Or.inr h)) (fun h => h.elim (fun e => Or.inr (Or.inl e.symm)) Or.inl)

theorem tri_add_prin {x₁ x₂ y : Term} (hy : isPrin y = true) (h : Tri x₁ y) :
    Tri (add x₁ x₂) y := by
  rcases h with h | rfl | h
  · exact Or.inl (by rw [lt_add_prin hy]; exact h)
  · exact Or.inr (Or.inr ((lt_prin_add_iff hy _ x₂).mpr (Or.inl rfl)))
  · exact Or.inr (Or.inr ((lt_prin_add_iff hy x₁ x₂).mpr (Or.inr h)))

theorem tri_ip {n : Nat} {c v b : Term} (h1 : n < fT v → Tri c (psi v b))
    (h2 : fT v ≤ n → Tri (inacc n c) v) : Tri (inacc n c) (psi v b) := by
  rw [Tri, lt_ip_iff, lt_pi_iff]
  rcases Nat.lt_or_ge n (fT v) with hk | hk
  · rcases h1 hk with h | e | h
    · exact Or.inl (Or.inl ⟨hk, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hk, Or.inl e.symm⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hk, Or.inr h⟩))
  · rcases h2 hk with h | e | h
    · exact Or.inl (Or.inr ⟨hk, h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hk, Or.inl e.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hk, Or.inr h⟩))

theorem lt_trichotomy_aux (N : Nat) : ∀ x y : Term, size x + size y ≤ N →
    wf x = true → wf y = true → Tri x y := by
  induction N with
  | zero => intro x _ hs; have := size_pos x; exact absurd hs (by omega)
  | succ N ih =>
    intro x y hs wx wy
    cases x <;> cases y
    all_goals first
      | exact Or.inr (Or.inl rfl)
      | exact Or.inl (lt_zero_left (by intro h; cases h))
      | exact Or.inr (Or.inr (lt_zero_left (by intro h; cases h)))
      | exact tri_add_prin rfl (ih _ _ (by size_omega) (wf_add wx).2.1 wy)
      | exact (tri_add_prin rfl (ih _ _ (by size_omega) (wf_add wy).2.1 wx)).symm
      | exact tri_ip (fun _ => ih _ _ (by size_omega) (wf_inacc wx).1 wy)
          (fun _ => ih _ _ (by size_omega) wx (wf_psi wy).2.1)
      | exact (tri_ip (fun _ => ih _ _ (by size_omega) (wf_inacc wy).1 wx)
          (fun _ => ih _ _ (by size_omega) wy (wf_psi wx).2.1)).symm
      | skip
    case add.add x₁ x₂ y₁ y₂ =>
      have wx' := wf_add wx
      have wy' := wf_add wy
      rw [Tri, lt_add_add, lt_add_add]
      by_cases e : x₁ = y₁
      · subst e
        rw [ite_eq_left rfl, ite_eq_left rfl]
        rcases ih x₂ y₂ (by size_omega) wx'.2.2.1 wy'.2.2.1 with h | rfl | h
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr h)
      · rw [ite_eq_right e, ite_eq_right (Ne.symm e)]
        rcases ih x₁ y₁ (by size_omega) wx'.2.1 wy'.2.1 with h | e' | h
        · exact Or.inl h
        · exact absurd e' e
        · exact Or.inr (Or.inr h)
    case inacc.inacc n c m d =>
      have wx' := wf_inacc wx
      have wy' := wf_inacc wy
      rcases Nat.lt_trichotomy n m with hnm | rfl | hnm
      · rw [Tri, lt_ii_lt hnm, lt_ii_gt hnm]
        rcases ih c (inacc m d) (by size_omega) wx'.1 wy with h | rfl | h
        · exact Or.inl h
        · exact absurd wx'.2 (by simp only [fT]; omega)
        · exact Or.inr (Or.inr h)
      · rw [Tri, lt_ii_eq, lt_ii_eq]
        rcases ih c d (by size_omega) wx'.1 wy'.1 with h | rfl | h
        · exact Or.inl h
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr h)
      · rw [Tri, lt_ii_gt hnm, lt_ii_lt hnm]
        rcases ih (inacc n c) d (by size_omega) wx wy'.1 with h | rfl | h
        · exact Or.inl h
        · exact absurd wy'.2 (by simp only [fT]; omega)
        · exact Or.inr (Or.inr h)
    case psi.psi u b v c =>
      have wx' := wf_psi wx
      have wy' := wf_psi wy
      rw [Tri, lt_pp_iff, lt_pp_iff]
      rcases ih u v (by size_omega) wx'.2.1 wy'.2.1 with h | rfl | h
      · rcases ih u (psi v c) (by size_omega) wx'.2.1 wy with h' | e | h'
        · exact Or.inl (Or.inl (Or.inl ⟨h, h'⟩))
        · exact absurd e (psi_ne_of_isRT wx'.1)
        · exact Or.inr (Or.inr (Or.inr ⟨h, h'⟩))
      · rcases ih b c (by size_omega) wx'.2.2.1 wy'.2.2.1 with h | rfl | h
        · exact Or.inl (Or.inl (Or.inr ⟨rfl, h⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, h⟩)))
      · rcases ih v (psi u b) (by size_omega) wy'.2.1 wx with h' | e | h'
        · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h, h'⟩)))
        · exact absurd e (psi_ne_of_isRT wy'.1)
        · exact Or.inl (Or.inr ⟨h, h'⟩)

theorem lt_trichotomy {x y : Term} (wx : wf x = true) (wy : wf y = true) : Tri x y :=
  lt_trichotomy_aux (size x + size y) x y (Nat.le_refl _) wx wy

/-! ### Transitivity

The proof is a nested induction: on a bound `N` for the sizes of all three terms (`TransLE`), and
inside on the total size (`SumIH`).  The two lemmas `psi_lt_of_index_lt` and
`lt_index_of_lt_psi` relate a collapsing term to its index; they only need transitivity for
proper subterms.  Size side conditions are discharged automatically by `size_omega`. -/

theorem lt_psi_index' (j : Nat) (w' f : Term) : lt (psi (inacc j w') f) (inacc j w') = true :=
  (lt_pi_iff' j w' j w' f).mpr (Or.inr ⟨Nat.le_refl j, Or.inl rfl⟩)

theorem lt_psi_index {w : Term} (hw : isRT w = true) (f : Term) : lt (psi w f) w = true := by
  obtain ⟨j, w', rfl⟩ := isRT_inacc hw
  exact lt_psi_index' j w' f

theorem not_index_lt_psi (l : Nat) (v' e : Term) :
    lt (inacc l v') (psi (inacc l v') e) = true → False := by
  intro h
  rcases (lt_ip_iff' l v' l v' e).mp h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact Nat.lt_irrefl l h1
  · rw [lt_irrefl] at h2; cases h2

def TransLE (N : Nat) : Prop := ∀ a b c : Term, wf a = true → wf b = true → wf c = true →
  lt a b = true → lt b c = true → (ha : size a ≤ N := by size_omega) →
    (hb : size b ≤ N := by size_omega) → (hc : size c ≤ N := by size_omega) → lt a c = true

/-- A collapsing term lies below everything above its index. -/
theorem psi_lt_of_index_lt {N : Nat} (TB : TransLE N) : ∀ y : Term, size y ≤ N → wf y = true →
    ∀ (j : Nat) (w' f : Term), size (psi (inacc j w') f) ≤ N + 1 →
      wf (psi (inacc j w') f) = true → lt (inacc j w') y = true →
        lt (psi (inacc j w') f) y = true := by
  intro y
  induction y with
  | zero => intro _ _ j w' f _ _ h; rw [lt_zero_right] at h; cases h
  | add y₁ y₂ ih₁ _ =>
    intro hs wy j w' f hs' ww h
    refine (lt_prin_add_iff rfl y₁ y₂).mpr (Or.inr ?_)
    rcases (lt_prin_add_iff rfl y₁ y₂).mp h with rfl | h
    · exact lt_psi_index' j w' f
    · exact ih₁ (by size_omega) (wf_add wy).2.1 j w' f hs' ww h
  | inacc m g ihg =>
    intro hs wy j w' f hs' ww h
    rw [lt_pi_iff']
    rcases Nat.lt_or_ge m j with hmj | hmj
    · rw [lt_ii_gt hmj] at h
      exact Or.inl ⟨hmj, Or.inr (ihg (by size_omega) (wf_inacc wy).1 j w' f hs' ww h)⟩
    · exact Or.inr ⟨hmj, Or.inr h⟩
  | psi v e _ _ =>
    intro hs wy j w' f hs' ww h
    have wy' := wf_psi wy
    have ww' := wf_psi ww
    obtain ⟨l, v', rfl⟩ := isRT_inacc wy'.1
    rw [lt_pp_iff]
    rcases lt_trichotomy ww'.2.1 wy'.2.1 with hwv | e' | hvw
    · exact Or.inl (Or.inl ⟨hwv, h⟩)
    · rw [← e'] at h; exact (not_index_lt_psi j w' e h).elim
    · rcases (lt_ip_iff' j w' l v' e).mp h with ⟨hjl, h'⟩ | ⟨_, h'⟩
      · rw [lt_ii_gt hjl] at hvw
        exact (not_index_lt_psi l v' e
          (TB (inacc l v') w' _ wy'.2.1 (wf_inacc ww'.2.1).1 wy hvw h')).elim
      · exact (lt_asymm hvw h').elim

/-- Everything below a collapsing term lies below its index. -/
theorem lt_index_of_lt_psi {N : Nat} (TB : TransLE N) : ∀ x : Term, size x ≤ N + 1 →
    wf x = true → ∀ (k : Nat) (u' d : Term), size (psi (inacc k u') d) ≤ N + 1 →
      wf (psi (inacc k u') d) = true → lt x (psi (inacc k u') d) = true →
        lt x (inacc k u') = true := by
  intro x
  induction x with
  | zero => intros; exact lt_zero_left (by intro h; cases h)
  | add x₁ x₂ ih₁ _ =>
    intro hs wx k u' d hs' wb h
    rw [lt_add_prin rfl] at h ⊢
    exact ih₁ (by size_omega) (wf_add wx).2.1 k u' d hs' wb h
  | inacc n g ihg =>
    intro hs wx k u' d hs' wb h
    rcases (lt_ip_iff' n g k u' d).mp h with ⟨hnk, h⟩ | ⟨_, h⟩
    · rw [lt_ii_lt hnk]; exact ihg (by size_omega) (wf_inacc wx).1 k u' d hs' wb h
    · exact h
  | psi w f _ _ =>
    intro hs wx k u' d hs' wb h
    obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wx).1
    rcases (lt_pp_iff _ _ _ _).mp h with (⟨hwu, _⟩ | ⟨e, _⟩) | ⟨_, h⟩
    · rw [lt_pi_iff']
      rcases Nat.lt_or_ge k j with hkj | hkj
      · rw [lt_ii_gt hkj] at hwu
        exact Or.inl ⟨hkj, Or.inr (psi_lt_of_index_lt @TB u' (by size_omega)
          (wf_inacc (wf_psi wb).2.1).1 j w' f hs wx hwu)⟩
      · exact Or.inr ⟨hkj, Or.inr hwu⟩
    · rw [e]; exact lt_psi_index' k u' f
    · exact h

def SumIH (N S : Nat) : Prop := ∀ x y z : Term, wf x = true → wf y = true → wf z = true →
  lt x y = true → lt y z = true → (hx : size x ≤ N + 1 := by size_omega) →
    (hy : size y ≤ N + 1 := by size_omega) → (hz : size z ≤ N + 1 := by size_omega) →
      (hs : size x + size y + size z < S := by size_omega) → lt x z = true

theorem trans_prin {N : Nat} (TB : TransLE N) {a b c : Term} (pa : isPrin a = true)
    (pb : isPrin b = true) (pc : isPrin c = true) (ha : size a ≤ N + 1) (hb : size b ≤ N + 1)
    (hc : size c ≤ N + 1) (IH : SumIH N (size a + size b + size c)) (wa : wf a = true)
    (wb : wf b = true) (wc : wf c = true) (h1 : lt a b = true) (h2 : lt b c = true) :
    lt a c = true := by
  cases a <;> cases b <;> cases c
  all_goals first | (cases pa; done) | (cases pb; done) | (cases pc; done) | skip
  case inacc.inacc.inacc n₁ c₁ n₂ c₂ n₃ c₃ =>
    have wa' := (wf_inacc wa).1
    have wb' := (wf_inacc wb).1
    have wc' := (wf_inacc wc).1
    have h1' := h1
    have h2' := h2
    rcases Nat.lt_trichotomy n₁ n₂ with h12 | rfl | h12
    · rw [lt_ii_lt h12] at h1'
      rcases Nat.lt_trichotomy n₁ n₃ with h13 | rfl | h13
      · rw [lt_ii_lt h13]; exact IH _ _ _ wa' wb wc h1' h2
      · rw [lt_ii_gt h12] at h2'; rw [lt_ii_eq]; exact IH _ _ _ wa' wb wc' h1' h2'
      · rw [lt_ii_gt (Nat.lt_trans h13 h12)] at h2'; rw [lt_ii_gt h13]
        exact IH _ _ _ wa wb wc' h1 h2'
    · rw [lt_ii_eq] at h1'
      rcases Nat.lt_trichotomy n₁ n₃ with h13 | rfl | h13
      · rw [lt_ii_lt h13] at h2'; rw [lt_ii_lt h13]; exact IH _ _ _ wa' wb' wc h1' h2'
      · rw [lt_ii_eq] at h2'; rw [lt_ii_eq]; exact IH _ _ _ wa' wb' wc' h1' h2'
      · rw [lt_ii_gt h13] at h2'; rw [lt_ii_gt h13]; exact IH _ _ _ wa wb wc' h1 h2'
    · rw [lt_ii_gt h12] at h1'
      rcases Nat.lt_trichotomy n₂ n₃ with h23 | rfl | h23
      · rw [lt_ii_lt h23] at h2'; exact IH _ _ _ wa wb' wc h1' h2'
      · rw [lt_ii_eq] at h2'; rw [lt_ii_gt h12]; exact IH _ _ _ wa wb' wc' h1' h2'
      · rw [lt_ii_gt h23] at h2'; rw [lt_ii_gt (Nat.lt_trans h23 h12)]
        exact IH _ _ _ wa wb wc' h1 h2'
  case inacc.inacc.psi n₁ c₁ n₂ c₂ v e =>
    obtain ⟨l, v', rfl⟩ := isRT_inacc (wf_psi wc).1
    have wa' := (wf_inacc wa).1
    have wb' := (wf_inacc wb).1
    rw [lt_ip_iff']
    rcases (lt_ip_iff' _ _ _ _ _).mp h2 with ⟨h2l, h2c⟩ | ⟨h2l, h2v⟩
    · rcases Nat.lt_trichotomy n₁ n₂ with h12 | rfl | h12
      · rw [lt_ii_lt h12] at h1; exact Or.inl ⟨by omega, IH _ _ _ wa' wb wc h1 h2⟩
      · rw [lt_ii_eq] at h1; exact Or.inl ⟨h2l, IH _ _ _ wa' wb' wc h1 h2c⟩
      · rw [lt_ii_gt h12] at h1; exact (lt_ip_iff' _ _ _ _ _).mp (IH _ _ _ wa wb' wc h1 h2c)
    · rcases Nat.lt_or_ge n₁ l with h1l | h1l
      · rw [lt_ii_lt (show n₁ < n₂ by omega)] at h1
        exact Or.inl ⟨h1l, IH _ _ _ wa' wb wc h1 h2⟩
      · exact Or.inr ⟨h1l, IH _ _ _ wa wb (wf_psi wc).2.1 h1 h2v⟩
  case inacc.psi.inacc n₁ c₁ u d n₃ c₃ =>
    obtain ⟨k, u', rfl⟩ := isRT_inacc (wf_psi wb).1
    have wa' := (wf_inacc wa).1
    have wc' := wf_inacc wc
    have nbc : psi (inacc k u') d = c₃ → n₃ < k → False := fun e h => by
      rw [← e] at wc'; exact absurd wc'.2 (by simp only [fT]; omega)
    rcases (lt_ip_iff' _ _ _ _ _).mp h1 with ⟨h1k, h1c⟩ | ⟨h1k, h1u⟩ <;>
      rcases (lt_pi_iff' _ _ _ _ _).mp h2 with ⟨h2k, e | h2c⟩ | ⟨h2k, e | h2u⟩
    · exact (nbc e h2k).elim
    · rcases Nat.lt_trichotomy n₁ n₃ with h13 | rfl | h13
      · rw [lt_ii_lt h13]; exact IH _ _ _ wa' wb wc h1c h2
      · rw [lt_ii_eq]; exact IH _ _ _ wa' wb wc'.1 h1c h2c
      · rw [lt_ii_gt h13]; exact IH _ _ _ wa wb wc'.1 h1 h2c
    · rw [lt_ii_lt (show n₁ < n₃ by omega)]; exact IH _ _ _ wa' wb wc h1c h2
    · rw [lt_ii_lt (show n₁ < n₃ by omega)]; exact IH _ _ _ wa' wb wc h1c h2
    · exact (nbc e h2k).elim
    · rw [lt_ii_gt (show n₃ < n₁ by omega)]; exact IH _ _ _ wa wb wc'.1 h1 h2c
    · rw [← e]; exact h1u
    · exact IH _ _ _ wa (wf_psi wb).2.1 wc h1u h2u
  case inacc.psi.psi n₁ c₁ u d v e =>
    obtain ⟨k, u', rfl⟩ := isRT_inacc (wf_psi wb).1
    obtain ⟨l, v', rfl⟩ := isRT_inacc (wf_psi wc).1
    have wa' := (wf_inacc wa).1
    rw [lt_ip_iff']
    rcases (lt_ip_iff' _ _ _ _ _).mp h1 with ⟨h1k, h1c⟩ | ⟨h1k, h1u⟩ <;>
      rcases (lt_pp_iff _ _ _ _).mp h2 with (⟨huv, huc⟩ | ⟨euv, _⟩) | ⟨hvu, hbv⟩
    · rcases Nat.lt_or_ge n₁ l with h1l | h1l
      · exact Or.inl ⟨h1l, IH _ _ _ wa' wb wc h1c h2⟩
      · have hau : lt (inacc n₁ c₁) (inacc k u') = true := by
          rw [lt_ii_lt h1k]; exact lt_index_of_lt_psi @TB c₁ (by size_omega) wa' k u' d hb wb h1c
        exact (lt_ip_iff' _ _ _ _ _).mp (IH _ _ _ wa (wf_psi wb).2.1 wc hau huc)
    · injection euv with ekl; subst ekl; exact Or.inl ⟨h1k, IH _ _ _ wa' wb wc h1c h2⟩
    · rcases Nat.lt_or_ge n₁ l with h1l | h1l
      · exact Or.inl ⟨h1l, IH _ _ _ wa' wb wc h1c h2⟩
      · exact Or.inr ⟨h1l, IH _ _ _ wa wb (wf_psi wc).2.1 h1 hbv⟩
    · exact (lt_ip_iff' _ _ _ _ _).mp (IH _ _ _ wa (wf_psi wb).2.1 wc h1u huc)
    · injection euv with ekl ev; subst ekl ev; exact Or.inr ⟨h1k, h1u⟩
    · rcases Nat.lt_or_ge n₁ l with h1l | h1l
      · exfalso
        rcases (lt_pi_iff' _ _ _ _ _).mp hbv with ⟨_, _⟩ | ⟨_, e' | h⟩
        · omega
        · rw [e', lt_irrefl] at hvu; cases hvu
        · exact lt_asymm hvu h
      · exact Or.inr ⟨h1l, IH _ _ _ wa wb (wf_psi wc).2.1 h1 hbv⟩
  case psi.inacc.inacc w f n₂ c₂ n₃ c₃ =>
    obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wa).1
    have wb' := wf_inacc wb
    have wc' := (wf_inacc wc).1
    rw [lt_pi_iff']
    rcases (lt_pi_iff' _ _ _ _ _).mp h1 with ⟨h1j, e | hac⟩ | ⟨h1j, h1w⟩
    · rw [← e] at wb'; exact absurd wb'.2 (by simp only [fT]; omega)
    · rcases Nat.lt_trichotomy n₂ n₃ with h23 | rfl | h23
      · rw [lt_ii_lt h23] at h2; exact (lt_pi_iff' _ _ _ _ _).mp (IH _ _ _ wa wb'.1 wc hac h2)
      · rw [lt_ii_eq] at h2; exact Or.inl ⟨h1j, Or.inr (IH _ _ _ wa wb'.1 wc' hac h2)⟩
      · rw [lt_ii_gt h23] at h2; exact Or.inl ⟨by omega, Or.inr (IH _ _ _ wa wb wc' h1 h2)⟩
    · rcases Nat.lt_or_ge n₃ j with h3j | h3j
      · rw [lt_ii_gt (show n₃ < n₂ by omega)] at h2
        exact Or.inl ⟨h3j, Or.inr (IH _ _ _ wa wb wc' h1 h2)⟩
      · refine Or.inr ⟨h3j, Or.inr ?_⟩
        rcases h1w with e | h
        · rw [e]; exact h2
        · exact IH _ _ _ (wf_psi wa).2.1 wb wc h h2
  case psi.inacc.psi w f n₂ c₂ v e =>
    obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wa).1
    obtain ⟨l, v', rfl⟩ := isRT_inacc (wf_psi wc).1
    have wa' := (wf_psi wa).2.1
    have wb' := wf_inacc wb
    have wc' := (wf_psi wc).2.1
    rcases (lt_pi_iff' _ _ _ _ _).mp h1 with ⟨h1j, e' | h⟩ | ⟨h1j, h1w⟩ <;>
      rcases (lt_ip_iff' _ _ _ _ _).mp h2 with ⟨h2l, h2c⟩ | ⟨h2l, h2v⟩
    · rw [← e'] at wb'; exact absurd wb'.2 (by simp only [fT]; omega)
    · rw [← e'] at wb'; exact absurd wb'.2 (by simp only [fT]; omega)
    · exact IH _ _ _ wa wb'.1 wc h h2c
    · rw [lt_pp_iff]
      rcases lt_trichotomy wa' wc' with hwv | ewv | hvw
      · exact Or.inl (Or.inl ⟨hwv, (lt_ip_iff' _ _ _ _ _).mpr (Or.inr ⟨by omega, hwv⟩)⟩)
      · injection ewv with ejl; exact absurd ejl (by omega)
      · exact Or.inr ⟨hvw, IH _ _ _ wa wb wc' h1 h2v⟩
    · have hwc : lt (inacc j w') (psi (inacc l v') e) = true :=
        h1w.elim (fun e' => by rw [e']; exact h2) (fun h => IH _ _ _ wa' wb wc h h2)
      rw [lt_pp_iff]
      rcases lt_trichotomy wa' wc' with hwv | ewv | hvw
      · exact Or.inl (Or.inl ⟨hwv, hwc⟩)
      · injection ewv with ejl; exact absurd ejl (by omega)
      · have hbv := lt_index_of_lt_psi @TB (inacc n₂ c₂) hb wb l v' e hc wc h2
        rcases h1w with e' | h
        · rw [e'] at hvw; exact (lt_asymm hvw hbv).elim
        · exact (lt_asymm (IH _ _ _ wc' wa' wb hvw h) hbv).elim
    · exact (lt_pp_iff _ _ _ _).mpr (Or.inl (Or.inl
        ⟨h1w.elim (fun e' => by rw [e']; exact h2v) (fun h => IH _ _ _ wa' wb wc' h h2v),
          h1w.elim (fun e' => by rw [e']; exact h2) (fun h => IH _ _ _ wa' wb wc h h2)⟩))
  case psi.psi.inacc w f u d n₃ c₃ =>
    obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wa).1
    obtain ⟨k, u', rfl⟩ := isRT_inacc (wf_psi wb).1
    have wc' := wf_inacc wc
    have wu := (wf_psi wb).2.1
    rw [lt_pi_iff']
    rcases (lt_pi_iff' _ _ _ _ _).mp h2 with ⟨h2k, e' | hbc⟩ | ⟨h2k, h2u⟩
    · rw [← e'] at wc'; exact absurd wc'.2 (by simp only [fT]; omega)
    · rcases Nat.lt_or_ge n₃ j with h3j | h3j
      · exact Or.inl ⟨h3j, Or.inr (IH _ _ _ wa wb wc'.1 h1 hbc)⟩
      · rcases (lt_pp_iff _ _ _ _).mp h1 with (⟨_, hwb⟩ | ⟨ewu, _⟩) | ⟨huw, hau⟩
        · exact Or.inr ⟨h3j, Or.inr (IH _ _ _ (wf_psi wa).2.1 wb wc hwb h2)⟩
        · injection ewu with ejk; exact absurd ejk (by omega)
        · exfalso
          rcases (lt_pi_iff' _ _ _ _ _).mp hau with ⟨_, _⟩ | ⟨_, e' | h⟩
          · omega
          · rw [e', lt_irrefl] at huw; cases huw
          · exact lt_asymm huw h
    · rcases (lt_pp_iff _ _ _ _).mp h1 with (⟨hwu, _⟩ | ⟨ewu, _⟩) | ⟨_, hau⟩
      · rcases Nat.lt_or_ge n₃ j with h3j | h3j
        · have hau := psi_lt_of_index_lt @TB (inacc k u') (by size_omega) wu j w' f ha wa hwu
          exact (lt_pi_iff' _ _ _ _ _).mp
            (h2u.elim (fun e' => by rw [← e']; exact hau) (fun h => IH _ _ _ wa wu wc hau h))
        · exact Or.inr ⟨h3j, Or.inr (h2u.elim (fun e' => by rw [← e']; exact hwu)
            (fun h => IH _ _ _ (wf_psi wa).2.1 wu wc hwu h))⟩
      · injection ewu with ejk ew; subst ejk ew; exact Or.inr ⟨h2k, h2u⟩
      · exact (lt_pi_iff' _ _ _ _ _).mp
          (h2u.elim (fun e' => by rw [← e']; exact hau) (fun h => IH _ _ _ wa wu wc hau h))
  case psi.psi.psi w f u d v e =>
    obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wa).1
    obtain ⟨k, u', rfl⟩ := isRT_inacc (wf_psi wb).1
    obtain ⟨l, v', rfl⟩ := isRT_inacc (wf_psi wc).1
    have wa' := wf_psi wa
    have wb' := wf_psi wb
    have wc' := wf_psi wc
    rw [lt_pp_iff]
    rcases (lt_pp_iff _ _ _ _).mp h1 with (⟨hwu, hwb⟩ | ⟨ewu, hfd⟩) | ⟨huw, hau⟩ <;>
      rcases (lt_pp_iff _ _ _ _).mp h2 with (⟨huv, huc⟩ | ⟨euv, hde⟩) | ⟨hvu, hbv⟩
    · exact Or.inl (Or.inl ⟨IH _ _ _ wa'.2.1 wb'.2.1 wc'.2.1 hwu huv,
        IH _ _ _ wa'.2.1 wb wc hwb h2⟩)
    · exact Or.inl (Or.inl ⟨by rw [← euv]; exact hwu, IH _ _ _ wa'.2.1 wb wc hwb h2⟩)
    · exact Or.inl (Or.inl ⟨IH _ _ _ wa'.2.1 wb wc'.2.1 hwb hbv, IH _ _ _ wa'.2.1 wb wc hwb h2⟩)
    · exact Or.inl (Or.inl ⟨by rw [ewu]; exact huv, by rw [ewu]; exact huc⟩)
    · injection ewu with ejk ew; injection euv with ekl ev; subst ejk ekl ew ev
      exact Or.inl (Or.inr ⟨rfl, IH _ _ _ wa'.2.2.1 wb'.2.2.1 wc'.2.2.1 hfd hde⟩)
    · exact Or.inr ⟨by rw [ewu]; exact hvu, IH _ _ _ wa wb wc'.2.1 h1 hbv⟩
    · exact (lt_pp_iff _ _ _ _).mp (IH _ _ _ wa wb'.2.1 wc hau huc)
    · exact Or.inr ⟨by rw [← euv]; exact huw, by rw [← euv]; exact hau⟩
    · rcases lt_trichotomy wa'.2.1 wc'.2.1 with hwv | ewv | hvw
      · exact (lt_asymm hwv (IH _ _ _ wc'.2.1 wb'.2.1 wa'.2.1 hvu huw)).elim
      · rw [ewv] at huw; exact (lt_asymm hvu huw).elim
      · exact Or.inr ⟨hvw, IH _ _ _ wa wb wc'.2.1 h1 hbv⟩

theorem trans_step {N : Nat} (TB : TransLE N) (a b c : Term)
    (ha : size a ≤ N + 1) (hb : size b ≤ N + 1) (hc : size c ≤ N + 1)
    (IH : SumIH N (size a + size b + size c))
    (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true := by
  rcases shape c with rfl | ⟨c₁, c₂, rfl⟩ | pc
  · rw [lt_zero_right] at h2; cases h2
  · have wc' := wf_add wc
    rcases shape b with rfl | ⟨b₁, b₂, rfl⟩ | pb
    · rw [lt_zero_right] at h1; cases h1
    · have wb' := wf_add wb
      rcases shape a with rfl | ⟨a₁, a₂, rfl⟩ | pa
      · exact lt_zero_left (by intro h; cases h)
      · have wa' := wf_add wa
        rw [lt_add_add] at h1 h2 ⊢
        by_cases e1 : a₁ = b₁
        · subst e1
          rw [ite_eq_left rfl] at h1
          by_cases e2 : a₁ = c₁
          · subst e2
            rw [ite_eq_left rfl] at h2 ⊢
            exact IH _ _ _ wa'.2.2.1 wb'.2.2.1 wc'.2.2.1 h1 h2
          · rw [ite_eq_right e2] at h2 ⊢; exact h2
        · rw [ite_eq_right e1] at h1
          by_cases e2 : b₁ = c₁
          · subst e2; rw [ite_eq_right e1]; exact h1
          · rw [ite_eq_right e2] at h2
            have h := IH _ _ _ wa'.2.1 wb'.2.1 wc'.2.1 h1 h2
            rw [ite_eq_right (ne_of_lt h)]; exact h
      · rw [lt_prin_add_iff pa] at h1 ⊢
        rw [lt_add_add] at h2
        by_cases e2 : b₁ = c₁
        · subst e2; exact h1
        · rw [ite_eq_right e2] at h2
          rcases h1 with rfl | h
          · exact Or.inr h2
          · exact Or.inr (IH _ _ _ wa wb'.2.1 wc'.2.1 h h2)
    · rw [lt_prin_add_iff pb] at h2
      rcases shape a with rfl | ⟨a₁, a₂, rfl⟩ | pa
      · exact lt_zero_left (by intro h; cases h)
      · have wa' := wf_add wa
        rw [lt_add_prin pb] at h1
        rw [lt_add_add]
        have h : lt a₁ c₁ = true :=
          h2.elim (fun e => by rw [← e]; exact h1) (fun h => IH _ _ _ wa'.2.1 wb wc'.2.1 h1 h)
        rw [ite_eq_right (ne_of_lt h)]; exact h
      · rw [lt_prin_add_iff pa]
        exact Or.inr (h2.elim (fun e => by rw [← e]; exact h1)
          (fun h => IH _ _ _ wa wb wc'.2.1 h1 h))
  · rcases shape b with rfl | ⟨b₁, b₂, rfl⟩ | pb
    · rw [lt_zero_right] at h1; cases h1
    · have wb' := wf_add wb
      rw [lt_add_prin pc] at h2
      rcases shape a with rfl | ⟨a₁, a₂, rfl⟩ | pa
      · exact lt_zero_left (ne_zero_of_isPrin pc)
      · have wa' := wf_add wa
        rw [lt_add_prin pc]
        rw [lt_add_add] at h1
        by_cases e1 : a₁ = b₁
        · subst e1; exact h2
        · rw [ite_eq_right e1] at h1; exact IH _ _ _ wa'.2.1 wb'.2.1 wc h1 h2
      · rw [lt_prin_add_iff pa] at h1
        rcases h1 with rfl | h
        · exact h2
        · exact IH _ _ _ wa wb'.2.1 wc h h2
    · rcases shape a with rfl | ⟨a₁, a₂, rfl⟩ | pa
      · exact lt_zero_left (ne_zero_of_isPrin pc)
      · rw [lt_add_prin pb] at h1
        rw [lt_add_prin pc]
        exact IH _ _ _ (wf_add wa).2.1 wb wc h1 h2
      · exact trans_prin @TB pa pb pc ha hb hc @IH wa wb wc h1 h2

theorem transLE_all (N : Nat) : TransLE N := by
  induction N with
  | zero => intro a _ _ _ _ _ _ _ ha _ _; have := size_pos a; exact absurd ha (by omega)
  | succ N TB =>
    have key : ∀ S : Nat, ∀ a b c : Term, size a ≤ N + 1 → size b ≤ N + 1 →
        size c ≤ N + 1 → size a + size b + size c ≤ S → wf a = true → wf b = true →
          wf c = true → lt a b = true → lt b c = true → lt a c = true := by
      intro S
      induction S with
      | zero => intro a _ _ _ _ _ hs; have := size_pos a; exact absurd hs (by omega)
      | succ S ihS =>
        intro a b c ha hb hc hs wa wb wc h1 h2
        exact trans_step @TB a b c ha hb hc
          (fun x y z wx wy wz hxy hyz hx hy hz _ =>
            ihS x y z hx hy hz (by omega) wx wy wz hxy hyz) wa wb wc h1 h2
    intro a b c wa wb wc h1 h2 ha hb hc
    exact key _ a b c ha hb hc (Nat.le_refl _) wa wb wc h1 h2

theorem lt_trans {a b c : Term} (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : lt a b = true) (h2 : lt b c = true) : lt a c = true :=
  transLE_all (size a + size b + size c) a b c wa wb wc h1 h2

end OCF.Jaeger.Term

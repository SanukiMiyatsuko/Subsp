import Subsp.OCF.Jaeger.Constructive.Order

/-! Syntactic facts about Jäger's notation used by the well-foundedness proof: components lie
below the terms built from them, the predecessor `predR` of a regular term lies below its
collapses, the coefficients `H` control the comparison with collapsing terms, and the next regular
term `nr`. -/

namespace OCF.Jaeger.Term

theorem size_induction {P : Term → Prop} (h : ∀ t, (∀ s, size s < size t → P s) → P t)
    (t : Term) : P t := by
  have key : ∀ N t, size t ≤ N → P t := by
    intro N
    induction N with
    | zero => intro t ht; have := size_pos t; exact absurd ht (by omega)
    | succ N ih => exact fun t ht => h t (fun s hs => ih s (by omega))
  exact key _ t (Nat.le_refl _)

theorem le_iff (a b : Term) : le a b = true ↔ a = b ∨ lt a b = true := by
  simp only [le, Bool.or_eq_true, decide_eq_true_eq]

theorem le_of_lt {a b : Term} (h : lt a b = true) : le a b = true := (le_iff a b).mpr (Or.inr h)

theorem le_refl (a : Term) : le a a = true := (le_iff a a).mpr (Or.inl rfl)

theorem lt_of_le_of_lt {a b c : Term} (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : le a b = true) (h2 : lt b c = true) : lt a c = true :=
  ((le_iff a b).mp h1).elim (fun e => by rw [e]; exact h2) (fun h => lt_trans wa wb wc h h2)

theorem lt_of_lt_of_le {a b c : Term} (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : lt a b = true) (h2 : le b c = true) : lt a c = true :=
  ((le_iff b c).mp h2).elim (fun e => by rw [← e]; exact h1) (fun h => lt_trans wa wb wc h1 h)

theorem not_lt_of_le {a b : Term} (h : le a b = true) : lt b a = false :=
  ((le_iff a b).mp h).elim (fun e => by rw [e]; exact lt_irrefl b) not_lt_of_lt

theorem le_of_not_lt {a b : Term} (wa : wf a = true) (wb : wf b = true) (h : lt b a = false) :
    le a b = true := by
  rcases lt_trichotomy wa wb with h' | rfl | h'
  · exact le_of_lt h'
  · exact le_refl a
  · rw [h'] at h; cases h

theorem isPrin_of_isRT {u : Term} (h : isRT u = true) : isPrin u = true := by
  obtain ⟨k, u', rfl⟩ := isRT_inacc h; rfl

/-! ### Components lie below -/

theorem lt_add_left {a b : Term} (h : wf (add a b) = true) : lt a (add a b) = true :=
  (lt_prin_add_iff (wf_add h).1 a b).mpr (Or.inl rfl)

theorem lt_add_right_aux : ∀ b : Term, wf b = true → b ≠ zero → ∀ a : Term,
    isPrin a = true → le (head b) a = true → lt b (add a b) = true := by
  intro b
  induction b with
  | zero => intro _ h; exact absurd rfl h
  | add b₁ b₂ _ ih₂ =>
    intro wb _ a _ hle
    have wb' := wf_add wb
    rw [lt_add_add]
    by_cases e : b₁ = a
    · subst e; rw [ite_eq_left rfl]; exact ih₂ wb'.2.2.1 wb'.2.2.2.1 b₁ wb'.1 wb'.2.2.2.2
    · rw [ite_eq_right e]; exact ((le_iff _ _).mp hle).resolve_left e
  | inacc | psi => intro _ _ a _ hle; exact (lt_prin_add_iff rfl a _).mpr ((le_iff _ _).mp hle)

theorem lt_add_right {a b : Term} (h : wf (add a b) = true) : lt b (add a b) = true :=
  let w := wf_add h
  lt_add_right_aux b w.2.2.1 w.2.2.2.1 a w.1 w.2.2.2.2

def PA (s : Term) : Prop := ∀ n : Nat, wf (inacc n s) = true → lt s (inacc n s) = true

def PB (s : Term) : Prop := ∀ (l : Nat) (e : Term), wf (psi (inacc l s) e) = true →
  lt s (psi (inacc l s) e) = true

theorem sub_lt_step (t : Term) (IH : ∀ s : Term, size s < size t → PA s ∧ PB s) :
    PA t ∧ PB t := by
  -- everything below `t` stays below `I_n(t)`
  have L : ∀ y : Term, size y < size t → wf y = true → lt y t = true → ∀ n : Nat,
      wf (inacc n t) = true → lt y (inacc n t) = true := by
    intro y
    induction y using size_induction with
    | h y ihy =>
      intro hs wy h n wt
      have wtt := (wf_inacc wt).1
      cases y with
      | zero => exact lt_zero_left (by intro h; cases h)
      | add y₁ y₂ =>
        rw [lt_add_prin rfl]
        exact ihy y₁ (by size_omega) (by size_omega) (wf_add wy).2.1
          (lt_trans (wf_add wy).2.1 wy wtt (lt_add_left wy) h) n wt
      | inacc m d =>
        have wd := (wf_inacc wy).1
        have hdt := lt_trans wd wy wtt ((IH d (by size_omega)).1 m wy) h
        rcases Nat.lt_trichotomy m n with hmn | rfl | hmn
        · rw [lt_ii_lt hmn]; exact ihy d (by size_omega) (by size_omega) wd hdt n wt
        · rw [lt_ii_eq]; exact hdt
        · rw [lt_ii_gt hmn]; exact h
      | psi v e =>
        obtain ⟨l, v', rfl⟩ := isRT_inacc (wf_psi wy).1
        rw [lt_pi_iff']
        rcases Nat.lt_or_ge n l with hnl | hln
        · exact Or.inl ⟨hnl, Or.inr h⟩
        refine Or.inr ⟨hln, Or.inr ?_⟩
        have wv' := (wf_inacc (wf_psi wy).2.1).1
        have hv't := lt_trans wv' wy wtt ((IH v' (by size_omega)).2 l e wy) h
        rcases Nat.lt_or_ge l n with hln' | hnl'
        · rw [lt_ii_lt hln']; exact ihy v' (by size_omega) (by size_omega) wv' hv't n wt
        · obtain rfl : l = n := by omega
          rw [lt_ii_eq]; exact hv't
  have hA : PA t := by
    intro n wt
    have wtt := (wf_inacc wt).1
    cases t with
    | zero => exact lt_zero_left (by intro h; cases h)
    | add t₁ t₂ =>
      rw [lt_add_prin rfl]
      exact L t₁ (by size_omega) (wf_add wtt).2.1 (lt_add_left wtt) n wt
    | inacc m d =>
      have hd := (IH d (by size_omega)).1 m wtt
      rcases Nat.lt_or_ge m n with hmn | hnm
      · rw [lt_ii_lt hmn]; exact L d (by size_omega) (wf_inacc wtt).1 hd n wt
      · obtain rfl : m = n := by have := (wf_inacc wt).2; simp only [fT] at this; omega
        rw [lt_ii_eq]; exact hd
    | psi v e =>
      obtain ⟨l, v', rfl⟩ := isRT_inacc (wf_psi wtt).1
      have hv' := (IH v' (by size_omega)).2 l e wtt
      rw [lt_pi_iff']
      have hln : l ≤ n := (wf_inacc wt).2
      refine Or.inr ⟨hln, Or.inr ?_⟩
      rcases Nat.lt_or_ge l n with hln' | hnl'
      · rw [lt_ii_lt hln']
        exact L v' (by size_omega) (wf_inacc (wf_psi wtt).2.1).1 hv' n wt
      · obtain rfl : l = n := by omega
        rw [lt_ii_eq]; exact hv'
  refine ⟨hA, ?_⟩
  intro l e wψ
  have wψ' := wf_psi wψ
  have wt := (wf_inacc wψ'.2.1).1
  have htv : lt t (inacc l t) = true := hA l wψ'.2.1
  -- everything up to `t` stays below `ψ_{I_l(t)}(e)`
  have S : ∀ y : Term, size y ≤ size t → wf y = true → (y = t ∨ lt y t = true) →
      lt y (psi (inacc l t) e) = true := by
    intro y
    induction y using size_induction with
    | h y ihy =>
      intro hs wy hy
      have hyt : ∀ z : Term, wf z = true → lt z y = true → lt z t = true := fun z wz hz =>
        hy.elim (fun e' => by rw [← e']; exact hz) (fun h => lt_trans wz wy wt hz h)
      cases y with
      | zero => exact lt_zero_left (by intro h; cases h)
      | add y₁ y₂ =>
        rw [lt_add_prin rfl]
        exact ihy y₁ (by size_omega) (by size_omega) (wf_add wy).2.1
          (Or.inr (hyt y₁ (wf_add wy).2.1 (lt_add_left wy)))
      | inacc m g =>
        have wg := (wf_inacc wy).1
        have hgt := hyt g wg ((IH g (by size_omega)).1 m wy)
        rw [lt_ip_iff']
        rcases Nat.lt_trichotomy m l with hml | rfl | hml
        · exact Or.inl ⟨hml, ihy g (by size_omega) (by size_omega) wg (Or.inr hgt)⟩
        · exact Or.inr ⟨Nat.le_refl m, by rw [lt_ii_eq]; exact hgt⟩
        · refine Or.inr ⟨Nat.le_of_lt hml, ?_⟩
          rw [lt_ii_gt hml]
          rcases hy with rfl | h
          · exact absurd (wf_inacc wψ'.2.1).2 (by simp only [fT]; omega)
          · exact h
      | psi w f =>
        have wy' := wf_psi wy
        obtain ⟨j, w'', rfl⟩ := isRT_inacc wy'.1
        have ww'' := (wf_inacc wy'.2.1).1
        rw [lt_pp_iff]
        rcases lt_trichotomy wy'.2.1 wψ'.2.1 with hwv | ewv | hvw
        · refine Or.inl (Or.inl ⟨hwv, ?_⟩)
          rw [lt_ip_iff']
          rcases Nat.lt_or_ge j l with hjl | hlj
          · exact Or.inl ⟨hjl, ihy w'' (by size_omega) (by size_omega) ww''
              (Or.inr (hyt w'' ww'' ((IH w'' (by size_omega)).2 j f wy)))⟩
          · exact Or.inr ⟨hlj, hwv⟩
        · injection ewv with _ ewt
          subst ewt
          exact absurd hs (by simp only [size]; omega)
        · refine Or.inr ⟨hvw, ?_⟩
          rw [lt_pi_iff']
          rcases Nat.lt_or_ge l j with hlj | hjl
          · exact Or.inl ⟨hlj, hy⟩
          · exact (lt_asymm htv (hyt _ wψ'.2.1
              ((lt_ip_iff' _ _ _ _ _).mpr (Or.inr ⟨hjl, hvw⟩)))).elim
  exact S t (Nat.le_refl _) wt (Or.inl rfl)

theorem sub_lt (t : Term) : PA t ∧ PB t := by
  induction t using size_induction with
  | h t ih => exact sub_lt_step t ih

theorem lt_inacc_self {n : Nat} {c : Term} (h : wf (inacc n c) = true) :
    lt c (inacc n c) = true :=
  (sub_lt c).1 n h

theorem lt_psi_of_arg {l : Nat} {v' e : Term} (h : wf (psi (inacc l v') e) = true) :
    lt v' (psi (inacc l v') e) = true :=
  (sub_lt v').2 l e h

/-! ### Predecessors and coefficients -/

theorem head_of_isPrin {x : Term} (h : isPrin x = true) : head x = x := by
  cases x <;> first | rfl | cases h

theorem wf_inacc_intro {n : Nat} {b : Term} (h1 : wf b = true) (h2 : fT b ≤ n) :
    wf (inacc n b) = true := by
  rw [wf, h1]; simp [h2]

theorem wf_add_intro {a b : Term} (h1 : isPrin a = true) (h2 : wf a = true) (h3 : wf b = true)
    (h4 : b ≠ zero) (h5 : le (head b) a = true) : wf (add a b) = true := by
  rw [wf, h1, h2, h3, h5]; simp [h4]

theorem succ_shape {b : Term} (h : isSucc b = true) :
    b = one ∨ ∃ c₁ c₂, b = add c₁ c₂ ∧ isSucc c₂ = true := by
  cases b <;> first | exact Or.inr ⟨_, _, rfl, h⟩ | exact Or.inl (of_decide_eq_true h) | cases h

theorem predT_spec : ∀ b : Term, wf b = true → isSucc b = true →
    lt (predT b) b = true ∧ wf (predT b) = true := by
  intro b
  induction b with
  | add b₁ b₂ _ ih₂ =>
    intro wb hs
    have wb' := wf_add wb
    by_cases e : b₂ = one
    · rw [predT, ite_eq_left e]; exact ⟨lt_add_left wb, wb'.2.1⟩
    rw [predT, ite_eq_right e]
    obtain ⟨hlt, hw⟩ := ih₂ wb'.2.2.1 hs
    refine ⟨by rw [lt_add_add, ite_eq_left rfl]; exact hlt, ?_⟩
    rcases succ_shape (show isSucc b₂ = true from hs) with e' | ⟨c₁, c₂, rfl, _⟩
    · exact absurd e' e
    have wc := wf_add wb'.2.2.1
    have hh : head (predT (add c₁ c₂)) = c₁ ∧ predT (add c₁ c₂) ≠ zero := by
      by_cases e₂ : c₂ = one
      · rw [predT, ite_eq_left e₂]; exact ⟨head_of_isPrin wc.1, ne_zero_of_isPrin wc.1⟩
      · rw [predT, ite_eq_right e₂]; exact ⟨rfl, by intro h; cases h⟩
    exact wf_add_intro wb'.1 wb'.2.1 hw hh.2 (by rw [hh.1]; exact wb'.2.2.2.2)
  | psi u c _ _ =>
    intro _ h
    rw [predT, show psi u c = one from of_decide_eq_true h]
    exact ⟨lt_zero_left (by intro h; cases h), wf_zero⟩
  | zero | inacc => intro _ h; cases h

theorem isSucc_of_isRT {n : Nat} {b : Term} (h : isRT (inacc n b) = true) (hb : b ≠ zero) :
    isSucc b = true := by
  simp only [isRT, isLimT, Bool.not_and, Bool.not_not, Bool.or_eq_true,
    decide_eq_true_eq] at h
  exact h.resolve_left hb

theorem predR_spec {u a : Term} (h : wf (psi u a) = true) :
    lt (predR u) (psi u a) = true ∧ wf (predR u) = true := by
  have h' := wf_psi h
  obtain ⟨n, b, rfl⟩ := isRT_inacc h'.1
  have wb := (wf_inacc h'.2.1).1
  by_cases hb : b = zero
  · rw [predR, ite_eq_left hb]; exact ⟨lt_zero_left (by intro h; cases h), wf_zero⟩
  rw [predR, ite_eq_right hb]
  obtain ⟨hp, wp⟩ := predT_spec b wb (isSucc_of_isRT h'.1 hb)
  by_cases hf : fT (predT b) ≤ n
  · rw [ite_eq_left hf]
    exact ⟨(lt_ip_iff' _ _ _ _ _).mpr (Or.inr ⟨Nat.le_refl n, by rw [lt_ii_eq]; exact hp⟩),
      wf_inacc_intro wp hf⟩
  · rw [ite_eq_right hf]; exact ⟨lt_trans wp wb h hp (lt_psi_of_arg h), wp⟩

theorem H_zero (u : Term) : H u zero = [] := by rw [H]

theorem H_add (u a b : Term) : H u (add a b) = H u a ++ H u b := by rw [H]

theorem H_inacc (u : Term) (n : Nat) (b : Term) :
    H u (inacc n b) = (if n = 0 then [] else hOne u) ++ H u b := by rw [H]

theorem H_psi (u v b : Term) :
    H u (psi v b) =
      if le (psi v b) (predR u) = true then [] else if lt v u = true then H u v
        else b :: (H u b ++ H u v) := by
  rw [H]

theorem allLt_append {l₁ l₂ : List Term} {b : Term} (h : allLt (l₁ ++ l₂) b = true) :
    allLt l₁ b = true ∧ allLt l₂ b = true := by
  unfold allLt at *; rw [List.all_append] at h; simp only [Bool.and_eq_true] at h; exact h

theorem allLt_cons {c : Term} {l : List Term} {b : Term} (h : allLt (c :: l) b = true) :
    lt c b = true ∧ allLt l b = true := by
  unfold allLt at *; rw [List.all_cons] at h; simp only [Bool.and_eq_true] at h; exact h

/-- The coefficient condition: a term below the index whose coefficients lie below `b` lies
below the collapse `ψ_κ(b)`. -/
theorem lt_psi_of_H {κ b : Term} (hw : wf (psi κ b) = true) : ∀ x : Term, wf x = true →
    allLt (H κ x) b = true → lt x κ = true → lt x (psi κ b) = true := by
  have wκ := (wf_psi hw).2.1
  intro x
  induction x with
  | zero => intros; exact lt_zero_left (by intro h; cases h)
  | add x₁ x₂ ih₁ _ =>
    intro wx hH hx
    rw [H_add] at hH
    rw [lt_add_prin rfl]
    exact ih₁ (wf_add wx).2.1 (allLt_append hH).1
      (lt_trans (wf_add wx).2.1 wx wκ (lt_add_left wx) hx)
  | inacc m d ihd =>
    intro wx hH hx
    rw [H_inacc] at hH
    rw [lt_ip_iff]
    rcases Nat.lt_or_ge m (fT κ) with hm | hm
    · exact Or.inl ⟨hm, ihd (wf_inacc wx).1 (allLt_append hH).2
        (lt_trans (wf_inacc wx).1 wx wκ (lt_inacc_self wx) hx)⟩
    · exact Or.inr ⟨hm, hx⟩
  | psi v c ihv _ =>
    intro wx hH hx
    rw [H_psi] at hH
    by_cases hle : le (psi v c) (predR κ) = true
    · exact lt_of_le_of_lt wx (predR_spec hw).2 hw hle (predR_spec hw).1
    rw [ite_eq_right hle] at hH
    rw [lt_pp_iff]
    by_cases hv : lt v κ = true
    · rw [ite_eq_left hv] at hH
      exact Or.inl (Or.inl ⟨hv, ihv (wf_psi wx).2.1 hH hv⟩)
    rw [ite_eq_right hv] at hH
    rcases lt_trichotomy (wf_psi wx).2.1 wκ with h | e | h
    · exact absurd h hv
    · exact Or.inl (Or.inr ⟨e, (allLt_cons hH).1⟩)
    · exact Or.inr ⟨h, hx⟩

/-! ### `Ω` and `1` -/

theorem not_lt_bigOmega (j : Nat) (d : Term) : lt (inacc j d) bigOmega = false := by
  unfold bigOmega
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [lt_ii_eq, lt_zero_right]
  · rw [lt_ii_gt hj, lt_zero_right]

theorem isRT_bigOmega : isRT bigOmega = true := by simp [bigOmega, isRT, isLimT]

theorem bigOmega_le_inacc (m : Nat) (d : Term) : le bigOmega (inacc m d) = true := by
  unfold bigOmega
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_cases hd : d = zero
    · rw [hd]; exact le_refl _
    · exact le_of_lt (by rw [lt_ii_eq]; exact lt_zero_left hd)
  · exact le_of_lt (by rw [lt_ii_lt hm]; exact lt_zero_left (by intro h; cases h))

theorem one_le_prin {x : Term} (wx : wf x = true) (px : isPrin x = true) : le one x = true := by
  cases x with
  | zero | add => cases px
  | inacc m d =>
    exact le_of_lt ((lt_pi_iff m d bigOmega zero).mpr
      (Or.inr ⟨Nat.zero_le m, (le_iff _ _).mp (bigOmega_le_inacc m d)⟩))
  | psi w f =>
    obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wx).1
    rcases (le_iff _ _).mp (bigOmega_le_inacc j w') with e | h
    · rw [← e]
      by_cases hf : f = zero
      · rw [hf]; exact le_refl _
      · exact le_of_lt ((lt_pp_iff _ _ _ _).mpr (Or.inl (Or.inr ⟨rfl, lt_zero_left hf⟩)))
    · refine le_of_lt ((lt_pp_iff _ _ _ _).mpr (Or.inl (Or.inl ⟨h, ?_⟩)))
      unfold bigOmega
      rw [lt_ip_iff']
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exact Or.inr ⟨Nat.le_of_eq hj, by unfold bigOmega at h; exact h⟩
      · exact Or.inl ⟨hj, lt_zero_left (by intro h; cases h)⟩

theorem not_prin_lt_one {x : Term} (wx : wf x = true) (px : isPrin x = true) :
    lt x one = false := by
  cases h : lt x one with
  | false => rfl
  | true =>
    exfalso
    cases x with
    | zero | add => cases px
    | inacc m d =>
      rcases (lt_ip_iff m d bigOmega zero).mp h with ⟨hm, _⟩ | ⟨_, h'⟩
      · exact Nat.not_lt_zero m hm
      · rw [not_lt_bigOmega] at h'; cases h'
    | psi w f =>
      obtain ⟨j, w', rfl⟩ := isRT_inacc (wf_psi wx).1
      rcases (lt_pp_iff _ _ _ _).mp h with (⟨h', _⟩ | ⟨_, h'⟩) | ⟨hΩ, h'⟩
      · rw [not_lt_bigOmega] at h'; cases h'
      · rw [lt_zero_right] at h'; cases h'
      · rcases (lt_pi_iff 0 zero _ f).mp h' with ⟨_, e | h''⟩ | ⟨_, e | h''⟩
        · cases e
        · rw [lt_zero_right] at h''; cases h''
        · rw [e] at hΩ
          change lt (inacc 0 zero) (inacc 0 zero) = true at hΩ
          rw [lt_irrefl] at hΩ; cases hΩ
        · change lt (inacc j w') bigOmega = true at h''
          rw [not_lt_bigOmega] at h''; cases h''

theorem eq_zero_of_lt_one {x : Term} (wx : wf x = true) (h : lt x one = true) : x = zero := by
  rcases shape x with e | ⟨x₁, x₂, rfl⟩ | px
  · exact e
  · rw [lt_add_prin rfl, not_prin_lt_one (wf_add wx).2.1 (wf_add wx).1] at h; cases h
  · rw [not_prin_lt_one wx px] at h; cases h

/-! ### Successors -/

def succT : Term → Term
  | zero => one
  | add a b => add a (succT b)
  | inacc n b => add (inacc n b) one
  | psi u b => add (psi u b) one

theorem succT_spec : ∀ c : Term, wf c = true →
    wf (succT c) = true ∧ isSucc (succT c) = true ∧ fT (succT c) = 0 ∧ succT c ≠ zero ∧
      lt c (succT c) = true ∧ (c ≠ zero → head (succT c) = head c) := by
  intro c
  induction c with
  | zero =>
    intro _
    exact ⟨wf_one, rfl, rfl, (by intro h; cases h), lt_zero_left (by intro h; cases h),
      fun h => absurd rfl h⟩
  | add c₁ c₂ _ ih₂ =>
    intro wc
    have wc' := wf_add wc
    obtain ⟨w₂, s₂, _, n₂, l₂, h₂⟩ := ih₂ wc'.2.2.1
    refine ⟨wf_add_intro wc'.1 wc'.2.1 w₂ n₂ (by rw [h₂ wc'.2.2.2.1]; exact wc'.2.2.2.2), s₂, rfl,
      (by intro h; cases h), ?_, fun _ => rfl⟩
    show lt (add c₁ c₂) (add c₁ (succT c₂)) = true
    rw [lt_add_add, ite_eq_left rfl]; exact l₂
  | inacc | psi =>
    intro wc
    exact ⟨wf_add_intro rfl wc wf_one (by intro h; cases h) (one_le_prin wc rfl), rfl, rfl,
      (by intro h; cases h), (lt_prin_add_iff rfl _ _).mpr (Or.inl rfl), fun _ => rfl⟩

theorem le_of_lt_add_one {c x : Term} (pc : isPrin c = true) (wx : wf x = true)
    (h : lt x (add c one) = true) : le x c = true := by
  rcases shape x with rfl | ⟨x₁, x₂, rfl⟩ | px
  · exact le_of_lt (lt_zero_left (ne_zero_of_isPrin pc))
  · have wx' := wf_add wx
    rw [lt_add_add] at h
    by_cases e : x₁ = c
    · rw [ite_eq_left e] at h; exact absurd (eq_zero_of_lt_one wx'.2.2.1 h) wx'.2.2.2.1
    · rw [ite_eq_right e] at h; exact le_of_lt (by rw [lt_add_prin pc]; exact h)
  · exact (le_iff _ _).mpr ((lt_prin_add_iff px _ _).mp h)

/-- Nothing lies strictly between `c` and `succT c`. -/
theorem le_of_lt_succT : ∀ c : Term, wf c = true → ∀ x : Term, wf x = true →
    lt x (succT c) = true → le x c = true := by
  intro c
  induction c with
  | zero => intro _ x wx h; rw [eq_zero_of_lt_one wx h]; exact le_refl _
  | add c₁ c₂ _ ih₂ =>
    intro wc x wx h
    have wc' := wf_add wc
    change lt x (add c₁ (succT c₂)) = true at h
    rcases shape x with rfl | ⟨x₁, x₂, rfl⟩ | px
    · exact le_of_lt (lt_zero_left (by intro h; cases h))
    · have wx' := wf_add wx
      rw [lt_add_add] at h
      by_cases e : x₁ = c₁
      · subst e
        rw [ite_eq_left rfl] at h
        rcases (le_iff _ _).mp (ih₂ wc'.2.2.1 x₂ wx'.2.2.1 h) with rfl | h'
        · exact le_refl _
        · exact le_of_lt (by rw [lt_add_add, ite_eq_left rfl]; exact h')
      · rw [ite_eq_right e] at h
        exact le_of_lt (by rw [lt_add_add, ite_eq_right e]; exact h)
    · rcases (lt_prin_add_iff px _ _).mp h with rfl | h
      · exact le_of_lt (lt_add_left wc)
      · exact le_of_lt (lt_trans wx wc'.2.1 wc h (lt_add_left wc))
  | inacc | psi => intro _ x wx h; exact le_of_lt_add_one rfl wx h

/-! ### The next regular term -/

/-- `nr α` is the least regular term above `α`. -/
def nr : Term → Term
  | zero => bigOmega
  | add a _ => nr a
  | inacc n c => if n = 0 then inacc 0 (succT c) else inacc 0 (succT (inacc n c))
  | psi u b => if fT u = 0 then u else inacc 0 (succT (psi u b))

theorem regular_succT {c : Term} (wc : wf c = true) :
    wf (inacc 0 (succT c)) = true ∧ isRT (inacc 0 (succT c)) = true := by
  obtain ⟨w, s, f, _⟩ := succT_spec c wc
  exact ⟨wf_inacc_intro w (Nat.le_of_eq f), by simp [isRT, isLimT, s]⟩

theorem nr_add (a b : Term) : nr (add a b) = nr a := rfl

theorem nr_inacc_zero (c : Term) : nr (inacc 0 c) = inacc 0 (succT c) := by
  rw [nr, ite_eq_left rfl]

theorem nr_inacc_pos {n : Nat} (hn : n ≠ 0) (c : Term) :
    nr (inacc n c) = inacc 0 (succT (inacc n c)) := by
  rw [nr, ite_eq_right hn]

theorem nr_psi_zero {u : Term} (hu : fT u = 0) (b : Term) : nr (psi u b) = u := by
  rw [nr, ite_eq_left hu]

theorem nr_psi_pos {u : Term} (hu : fT u ≠ 0) (b : Term) :
    nr (psi u b) = inacc 0 (succT (psi u b)) := by
  rw [nr, ite_eq_right hu]

theorem nr_spec : ∀ α : Term, wf α = true →
    wf (nr α) = true ∧ isRT (nr α) = true ∧ lt α (nr α) = true := by
  intro α
  induction α with
  | zero => intro _; exact ⟨wf_bigOmega, isRT_bigOmega, lt_zero_left (by intro h; cases h)⟩
  | add a b iha _ =>
    intro wα
    obtain ⟨h1, h2, h3⟩ := iha (wf_add wα).2.1
    rw [nr_add, lt_add_prin (isPrin_of_isRT h2)]
    exact ⟨h1, h2, h3⟩
  | inacc n c _ =>
    intro wα
    by_cases hn : n = 0
    · subst hn
      have hc := (wf_inacc wα).1
      rw [nr_inacc_zero, lt_ii_eq]
      exact ⟨(regular_succT hc).1, (regular_succT hc).2, (succT_spec c hc).2.2.2.2.1⟩
    · rw [nr_inacc_pos hn, lt_ii_gt (Nat.pos_of_ne_zero hn)]
      exact ⟨(regular_succT wα).1, (regular_succT wα).2, (succT_spec _ wα).2.2.2.2.1⟩
  | psi u b _ _ =>
    intro wα
    by_cases hu : fT u = 0
    · rw [nr_psi_zero hu]
      exact ⟨(wf_psi wα).2.1, (wf_psi wα).1, lt_psi_index (wf_psi wα).1 b⟩
    · rw [nr_psi_pos hu]
      exact ⟨(regular_succT wα).1, (regular_succT wα).2, (lt_pi_iff 0 _ u b).mpr
        (Or.inl ⟨Nat.pos_of_ne_zero hu, Or.inr (succT_spec _ wα).2.2.2.2.1⟩)⟩

theorem nr_least : ∀ α : Term, wf α = true → ∀ σ : Term, wf σ = true → isRT σ = true →
    lt α σ = true → le (nr α) σ = true := by
  intro α
  induction α with
  | zero =>
    intro _ σ _ hσ _
    obtain ⟨j, d, rfl⟩ := isRT_inacc hσ
    exact bigOmega_le_inacc j d
  | add a b iha _ =>
    intro wα σ wσ hσ h
    exact iha (wf_add wα).2.1 σ wσ hσ (lt_trans (wf_add wα).2.1 wα wσ (lt_add_left wα) h)
  | inacc n c _ =>
    intro wα σ wσ hσ h
    obtain ⟨j, d, rfl⟩ := isRT_inacc hσ
    have wd := (wf_inacc wσ).1
    refine le_of_not_lt (nr_spec _ wα).1 wσ ?_
    cases hlt : lt (inacc j d) (nr (inacc n c)) with
    | false => rfl
    | true =>
      exfalso
      -- in each case `σ` would lie between a term and its successor
      have key : ∀ x y, wf x = true → wf y = true → lt x (succT y) = true → lt y x = true →
          False := fun x y wx wy h1 h2 => by
        rw [not_lt_of_le (le_of_lt_succT y wy x wx h1)] at h2; cases h2
      by_cases hn0 : n = 0
      · subst hn0
        have hc := (wf_inacc wα).1
        rw [nr_inacc_zero] at hlt
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [lt_ii_eq] at h hlt; exact key d c wd hc hlt h
        · rw [lt_ii_gt hj] at hlt; rw [lt_ii_lt hj] at h; exact key _ c wσ hc hlt h
      · rw [nr_inacc_pos hn0] at hlt
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · rw [lt_ii_eq] at hlt; rw [lt_ii_gt (Nat.pos_of_ne_zero hn0)] at h
          exact key d _ wd wα hlt h
        · rw [lt_ii_gt hj] at hlt; exact key _ _ wσ wα hlt h
  | psi u b _ _ =>
    intro wα σ wσ hσ h
    obtain ⟨j, d, rfl⟩ := isRT_inacc hσ
    have wd := (wf_inacc wσ).1
    by_cases hu : fT u = 0
    · rw [nr_psi_zero hu]
      rcases (lt_pi_iff j d u b).mp h with ⟨hj, _⟩ | ⟨_, h'⟩
      · exact absurd hj (by omega)
      · exact (le_iff _ _).mpr h'
    rw [nr_psi_pos hu]
    refine le_of_not_lt (regular_succT wα).1 wσ ?_
    cases hlt : lt (inacc j d) (inacc 0 (succT (psi u b))) with
    | false => rfl
    | true =>
      exfalso
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [lt_ii_eq] at hlt
        have hd := le_of_lt_succT _ wα d wd hlt
        rcases (lt_pi_iff 0 d u b).mp h with ⟨_, e' | h'⟩ | ⟨hu', _⟩
        · rw [← e'] at wσ; exact hu (Nat.le_zero.mp (wf_inacc wσ).2)
        · rw [not_lt_of_le hd] at h'; cases h'
        · exact hu (Nat.le_zero.mp hu')
      · rw [lt_ii_gt hj] at hlt
        rw [not_lt_of_le (le_of_lt_succT _ wα _ wσ hlt)] at h; cases h

end OCF.Jaeger.Term

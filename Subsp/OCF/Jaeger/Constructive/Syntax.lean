import Subsp.OCF.Jaeger.Constructive.Order

/-! Syntactic facts about Jäger's notation used by the well-foundedness proof: components lie
below the terms built from them, the predecessor `predR` of a regular term lies below its
collapses, the coefficients `H` control the comparison with collapsing terms, and the next regular
term `nr`. -/

namespace OCF.Jaeger.Term

theorem size_induction {P : Term → Prop} (h : ∀ t, (∀ s, size s < size t → P s) → P t)
    (t : Term) : P t := by
  have key : ∀ N : Nat, ∀ t : Term, size t ≤ N → P t := by
    intro N
    induction N with
    | zero =>
      intro t ht
      have := size_pos t
      exact absurd ht (by omega)
    | succ N ih =>
      intro t ht
      exact h t (fun s hs => ih s (by omega))
  exact key _ t (Nat.le_refl _)

theorem le_iff (a b : Term) : le a b = true ↔ a = b ∨ lt a b = true := by
  simp only [le, Bool.or_eq_true, decide_eq_true_eq]

theorem le_of_lt {a b : Term} (h : lt a b = true) : le a b = true :=
  (le_iff a b).mpr (Or.inr h)

theorem le_refl (a : Term) : le a a = true := (le_iff a a).mpr (Or.inl rfl)

theorem lt_of_le_of_lt {a b c : Term} (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : le a b = true) (h2 : lt b c = true) : lt a c = true := by
  rcases (le_iff a b).mp h1 with e | h
  · rw [e]
    exact h2
  · exact lt_trans wa wb wc h h2

theorem lt_of_lt_of_le {a b c : Term} (wa : wf a = true) (wb : wf b = true) (wc : wf c = true)
    (h1 : lt a b = true) (h2 : le b c = true) : lt a c = true := by
  rcases (le_iff b c).mp h2 with e | h
  · rw [← e]
    exact h1
  · exact lt_trans wa wb wc h1 h

theorem not_lt_of_le {a b : Term} (h : le a b = true) : lt b a = false := by
  rcases (le_iff a b).mp h with e | h
  · rw [e]
    exact lt_irrefl b
  · exact not_lt_of_lt h

theorem le_of_not_lt {a b : Term} (wa : wf a = true) (wb : wf b = true) (h : lt b a = false) :
    le a b = true := by
  rcases lt_trichotomy wa wb with h' | e | h'
  · exact le_of_lt h'
  · rw [e]
    exact le_refl b
  · rw [h'] at h
    cases h

theorem isPrin_of_isRT {u : Term} (h : isRT u = true) : isPrin u = true := by
  obtain ⟨k, u', rfl⟩ := isRT_inacc h
  rfl

/-! ### Components lie below -/

theorem lt_add_left {a b : Term} (h : wf (add a b) = true) : lt a (add a b) = true :=
  (lt_prin_add_iff (wf_add h).1 a b).mpr (Or.inl rfl)

theorem lt_add_right_aux : ∀ b : Term, wf b = true → b ≠ zero → ∀ a : Term,
    isPrin a = true → le (head b) a = true → lt b (add a b) = true := by
  intro b
  induction b with
  | zero =>
    intro _ h
    exact absurd rfl h
  | add b₁ b₂ _ ih₂ =>
    intro wb _ a _ hle
    have wb' := wf_add wb
    rw [lt_add_add]
    have hle' : b₁ = a ∨ lt b₁ a = true := (le_iff _ _).mp hle
    by_cases e : b₁ = a
    · rw [ite_eq_left e]
      subst e
      exact ih₂ wb'.2.2.1 wb'.2.2.2.1 b₁ wb'.1 wb'.2.2.2.2
    · rw [ite_eq_right e]
      exact hle'.resolve_left e
  | inacc n c _ =>
    intro _ _ a pa hle
    rcases (le_iff _ _).mp hle with e | h
    · exact (lt_prin_add_iff rfl a _).mpr (Or.inl e)
    · exact (lt_prin_add_iff rfl a _).mpr (Or.inr h)
  | psi v c _ _ =>
    intro _ _ a pa hle
    rcases (le_iff _ _).mp hle with e | h
    · exact (lt_prin_add_iff rfl a _).mpr (Or.inl e)
    · exact (lt_prin_add_iff rfl a _).mpr (Or.inr h)

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
        have wy' := wf_add wy
        rw [lt_add_prin rfl]
        exact ihy y₁ (by size_omega) (by size_omega) wy'.2.1
          (lt_trans wy'.2.1 wy wtt (lt_add_left wy) h) n wt
      | inacc m d =>
        have wy' := wf_inacc wy
        have hd : lt d (inacc m d) = true := (IH d (by size_omega)).1 m wy
        have hdt : lt d t = true := lt_trans wy'.1 wy wtt hd h
        rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
        · rw [lt_ii_lt hmn]
          exact ihy d (by size_omega) (by size_omega) wy'.1 hdt n wt
        · subst hmn
          rw [lt_ii_eq]
          exact hdt
        · rw [lt_ii_gt hmn]
          exact h
      | psi v e =>
        have wy' := wf_psi wy
        obtain ⟨l, v', rfl⟩ := isRT_inacc wy'.1
        rw [lt_pi_iff']
        rcases Nat.lt_or_ge n l with hnl | hln
        · exact Or.inl ⟨hnl, Or.inr h⟩
        · refine Or.inr ⟨hln, Or.inr ?_⟩
          have wv' := (wf_inacc wy'.2.1).1
          have hv' : lt v' (psi (inacc l v') e) = true := (IH v' (by size_omega)).2 l e wy
          have hv't : lt v' t = true := lt_trans wv' wy wtt hv' h
          rcases Nat.lt_or_ge l n with hln' | hnl'
          · rw [lt_ii_lt hln']
            exact ihy v' (by size_omega) (by size_omega) wv' hv't n wt
          · have e' : l = n := by omega
            subst e'
            rw [lt_ii_eq]
            exact hv't
  have hA : PA t := by
    intro n wt
    have wtt := (wf_inacc wt).1
    cases t with
    | zero => exact lt_zero_left (by intro h; cases h)
    | add t₁ t₂ =>
      have wt' := wf_add wtt
      rw [lt_add_prin rfl]
      exact L t₁ (by size_omega) wt'.2.1 (lt_add_left wtt) n wt
    | inacc m d =>
      have hmn : m ≤ n := (wf_inacc wt).2
      have wd := (wf_inacc wtt).1
      have hd : lt d (inacc m d) = true := (IH d (by size_omega)).1 m wtt
      rcases Nat.lt_or_ge m n with hmn' | hnm
      · rw [lt_ii_lt hmn']
        exact L d (by size_omega) wd hd n wt
      · have e' : m = n := by omega
        subst e'
        rw [lt_ii_eq]
        exact hd
    | psi v e =>
      have wt' := wf_psi wtt
      obtain ⟨l, v', rfl⟩ := isRT_inacc wt'.1
      have hln : l ≤ n := (wf_inacc wt).2
      have wv' := (wf_inacc wt'.2.1).1
      have hv' : lt v' (psi (inacc l v') e) = true := (IH v' (by size_omega)).2 l e wtt
      rw [lt_pi_iff']
      refine Or.inr ⟨hln, Or.inr ?_⟩
      rcases Nat.lt_or_ge l n with hln' | hnl'
      · rw [lt_ii_lt hln']
        exact L v' (by size_omega) wv' hv' n wt
      · have e' : l = n := by omega
        subst e'
        rw [lt_ii_eq]
        exact hv'
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
      have hyt : ∀ z : Term, wf z = true → lt z y = true → lt z t = true := by
        intro z wz hz
        rcases hy with e' | h
        · rw [← e']
          exact hz
        · exact lt_trans wz wy wt hz h
      cases y with
      | zero => exact lt_zero_left (by intro h; cases h)
      | add y₁ y₂ =>
        have wy' := wf_add wy
        rw [lt_add_prin rfl]
        exact ihy y₁ (by size_omega) (by size_omega) wy'.2.1
          (Or.inr (hyt y₁ wy'.2.1 (lt_add_left wy)))
      | inacc m g =>
        have wy' := wf_inacc wy
        have hg : lt g (inacc m g) = true := (IH g (by size_omega)).1 m wy
        have hgt := hyt g wy'.1 hg
        rw [lt_ip_iff']
        rcases Nat.lt_trichotomy m l with hml | hml | hml
        · exact Or.inl ⟨hml, ihy g (by size_omega) (by size_omega) wy'.1 (Or.inr hgt)⟩
        · subst hml
          refine Or.inr ⟨Nat.le_refl m, ?_⟩
          rw [lt_ii_eq]
          exact hgt
        · refine Or.inr ⟨Nat.le_of_lt hml, ?_⟩
          rw [lt_ii_gt hml]
          rcases hy with e' | h
          · rw [← e'] at wψ'
            exact absurd (wf_inacc wψ'.2.1).2 (by simp only [fT]; omega)
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
          · refine Or.inl ⟨hjl, ?_⟩
            have hw'' : lt w'' (psi (inacc j w'') f) = true := (IH w'' (by size_omega)).2 j f wy
            exact ihy w'' (by size_omega) (by size_omega) ww'' (Or.inr (hyt w'' ww'' hw''))
          · exact Or.inr ⟨hlj, hwv⟩
        · injection ewv with _ ewt
          subst ewt
          exact absurd hs (by simp only [size]; omega)
        · refine Or.inr ⟨hvw, ?_⟩
          rw [lt_pi_iff']
          rcases Nat.lt_or_ge l j with hlj | hjl
          · exact Or.inl ⟨hlj, hy⟩
          · exfalso
            have hvy : lt (inacc l t) (psi (inacc j w'') f) = true :=
              (lt_ip_iff' _ _ _ _ _).mpr (Or.inr ⟨hjl, hvw⟩)
            have hvt := hyt _ wψ'.2.1 hvy
            exact lt_asymm htv hvt
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

theorem lt_psi_index_of_wf {u b : Term} (h : wf (psi u b) = true) : lt (psi u b) u = true :=
  lt_psi_index (wf_psi h).1 b

/-! ### Predecessors and coefficients -/

theorem head_of_isPrin {x : Term} (h : isPrin x = true) : head x = x := by
  cases x with
  | zero => simp [isPrin] at h
  | add _ _ => simp [isPrin] at h
  | inacc _ _ => rfl
  | psi _ _ => rfl

theorem wf_inacc_intro {n : Nat} {b : Term} (h1 : wf b = true) (h2 : fT b ≤ n) :
    wf (inacc n b) = true := by
  rw [wf, h1]
  simp [h2]

theorem wf_add_intro {a b : Term} (h1 : isPrin a = true) (h2 : wf a = true) (h3 : wf b = true)
    (h4 : b ≠ zero) (h5 : le (head b) a = true) : wf (add a b) = true := by
  rw [wf, h1, h2, h3, h5]
  simp [h4]

theorem succ_shape {b : Term} (h : isSucc b = true) :
    b = one ∨ ∃ c₁ c₂, b = add c₁ c₂ ∧ isSucc c₂ = true := by
  cases b with
  | zero => simp [isSucc] at h
  | add c₁ c₂ => exact Or.inr ⟨c₁, c₂, rfl, h⟩
  | inacc _ _ => simp [isSucc] at h
  | psi u c => exact Or.inl (of_decide_eq_true h)

theorem predT_spec : ∀ b : Term, wf b = true → isSucc b = true →
    lt (predT b) b = true ∧ wf (predT b) = true := by
  intro b
  induction b with
  | zero =>
    intro _ h
    simp [isSucc] at h
  | add b₁ b₂ _ ih₂ =>
    intro wb hs
    have wb' := wf_add wb
    have hs₂ : isSucc b₂ = true := hs
    by_cases e : b₂ = one
    · rw [predT, ite_eq_left e]
      exact ⟨lt_add_left wb, wb'.2.1⟩
    · rw [predT, ite_eq_right e]
      obtain ⟨hlt, hw⟩ := ih₂ wb'.2.2.1 hs₂
      refine ⟨by rw [lt_add_add, ite_eq_left rfl]; exact hlt, ?_⟩
      rcases succ_shape hs₂ with e' | ⟨c₁, c₂, rfl, _⟩
      · exact absurd e' e
      · have wc := wf_add wb'.2.2.1
        have hhead : head (predT (add c₁ c₂)) = c₁ := by
          by_cases e₂ : c₂ = one
          · rw [predT, ite_eq_left e₂]
            exact head_of_isPrin wc.1
          · rw [predT, ite_eq_right e₂]
            rfl
        have hne : predT (add c₁ c₂) ≠ zero := by
          by_cases e₂ : c₂ = one
          · rw [predT, ite_eq_left e₂]
            exact ne_zero_of_isPrin wc.1
          · rw [predT, ite_eq_right e₂]
            intro h
            cases h
        refine wf_add_intro wb'.1 wb'.2.1 hw hne ?_
        rw [hhead]
        exact wb'.2.2.2.2
  | inacc _ _ _ =>
    intro _ h
    simp [isSucc] at h
  | psi u c _ _ =>
    intro _ h
    have e : psi u c = one := of_decide_eq_true h
    rw [predT, e]
    exact ⟨lt_zero_left (by intro h; cases h), wf_zero⟩

theorem isSucc_of_isRT {n : Nat} {b : Term} (h : isRT (inacc n b) = true) (hb : b ≠ zero) :
    isSucc b = true := by
  simp only [isRT, isLimT, Bool.not_and, Bool.not_not, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | h
  · exact absurd h hb
  · exact h

theorem predR_spec {u a : Term} (h : wf (psi u a) = true) :
    lt (predR u) (psi u a) = true ∧ wf (predR u) = true := by
  have h' := wf_psi h
  obtain ⟨n, b, rfl⟩ := isRT_inacc h'.1
  have wb := (wf_inacc h'.2.1).1
  by_cases hb : b = zero
  · rw [predR, ite_eq_left hb]
    exact ⟨lt_zero_left (by intro h; cases h), wf_zero⟩
  · rw [predR, ite_eq_right hb]
    obtain ⟨hp, wp⟩ := predT_spec b wb (isSucc_of_isRT h'.1 hb)
    by_cases hf : fT (predT b) ≤ n
    · rw [ite_eq_left hf]
      refine ⟨(lt_ip_iff' _ _ _ _ _).mpr (Or.inr ⟨Nat.le_refl n, ?_⟩), wf_inacc_intro wp hf⟩
      rw [lt_ii_eq]
      exact hp
    · rw [ite_eq_right hf]
      exact ⟨lt_trans wp wb h hp (lt_psi_of_arg h), wp⟩

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
  unfold allLt at *
  rw [List.all_append] at h
  simp only [Bool.and_eq_true] at h
  exact h

theorem allLt_cons {c : Term} {l : List Term} {b : Term} (h : allLt (c :: l) b = true) :
    lt c b = true ∧ allLt l b = true := by
  unfold allLt at *
  rw [List.all_cons] at h
  simp only [Bool.and_eq_true] at h
  exact h

/-- The coefficient condition: a term below the index whose coefficients lie below `b` lies
below the collapse `ψ_κ(b)`. -/
theorem lt_psi_of_H {κ b : Term} (hw : wf (psi κ b) = true) : ∀ x : Term, wf x = true →
    allLt (H κ x) b = true → lt x κ = true → lt x (psi κ b) = true := by
  have hw' := wf_psi hw
  have wκ := hw'.2.1
  intro x
  induction x with
  | zero =>
    intros
    exact lt_zero_left (by intro h; cases h)
  | add x₁ x₂ ih₁ _ =>
    intro wx hH hx
    have wx' := wf_add wx
    rw [H_add] at hH
    rw [lt_add_prin rfl]
    exact ih₁ wx'.2.1 (allLt_append hH).1 (lt_trans wx'.2.1 wx wκ (lt_add_left wx) hx)
  | inacc m d ihd =>
    intro wx hH hx
    rw [H_inacc] at hH
    have wx' := wf_inacc wx
    rw [lt_ip_iff]
    rcases Nat.lt_or_ge m (fT κ) with hm | hm
    · exact Or.inl ⟨hm, ihd wx'.1 (allLt_append hH).2
        (lt_trans wx'.1 wx wκ (lt_inacc_self wx) hx)⟩
    · exact Or.inr ⟨hm, hx⟩
  | psi v c ihv _ =>
    intro wx hH hx
    have wx' := wf_psi wx
    rw [H_psi] at hH
    by_cases hle : le (psi v c) (predR κ) = true
    · exact lt_of_le_of_lt wx (predR_spec hw).2 hw hle (predR_spec hw).1
    · rw [ite_eq_right hle] at hH
      rw [lt_pp_iff]
      by_cases hv : lt v κ = true
      · rw [ite_eq_left hv] at hH
        exact Or.inl (Or.inl ⟨hv, ihv wx'.2.1 hH hv⟩)
      · rw [ite_eq_right hv] at hH
        have hc := (allLt_cons hH).1
        rcases lt_trichotomy wx'.2.1 wκ with h | e | h
        · exact absurd h hv
        · exact Or.inl (Or.inr ⟨e, hc⟩)
        · exact Or.inr ⟨h, hx⟩

/-! ### `Ω` and `1` -/

theorem not_lt_bigOmega (j : Nat) (d : Term) : lt (inacc j d) bigOmega = false := by
  unfold bigOmega
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rw [lt_ii_eq, lt_zero_right]
  · rw [lt_ii_gt hj, lt_zero_right]

theorem isRT_bigOmega : isRT bigOmega = true := by
  simp [bigOmega, isRT, isLimT]

theorem bigOmega_le_inacc (m : Nat) (d : Term) : le bigOmega (inacc m d) = true := by
  unfold bigOmega
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    by_cases hd : d = zero
    · rw [hd]
      exact le_refl _
    · refine le_of_lt ?_
      rw [lt_ii_eq]
      exact lt_zero_left hd
  · refine le_of_lt ?_
    rw [lt_ii_lt hm]
    exact lt_zero_left (by intro h; cases h)

theorem one_le_prin {x : Term} (wx : wf x = true) (px : isPrin x = true) : le one x = true := by
  cases x with
  | zero => simp [isPrin] at px
  | add _ _ => simp [isPrin] at px
  | inacc m d =>
    refine le_of_lt ((lt_pi_iff m d bigOmega zero).mpr (Or.inr ⟨Nat.zero_le m, ?_⟩))
    exact (le_iff _ _).mp (bigOmega_le_inacc m d)
  | psi w f =>
    have wx' := wf_psi wx
    obtain ⟨j, w', rfl⟩ := isRT_inacc wx'.1
    rcases (le_iff _ _).mp (bigOmega_le_inacc j w') with e | h
    · rw [← e]
      by_cases hf : f = zero
      · rw [hf]
        exact le_refl _
      · refine le_of_lt ((lt_pp_iff _ _ _ _).mpr (Or.inl (Or.inr ⟨rfl, lt_zero_left hf⟩)))
    · refine le_of_lt ((lt_pp_iff _ _ _ _).mpr (Or.inl (Or.inl ⟨h, ?_⟩)))
      unfold bigOmega
      rw [lt_ip_iff']
      rcases Nat.eq_zero_or_pos j with hj | hj
      · exact Or.inr ⟨Nat.le_of_eq hj, by unfold bigOmega at h; exact h⟩
      · exact Or.inl ⟨hj, lt_zero_left (by intro h; cases h)⟩

theorem not_prin_lt_one {x : Term} (wx : wf x = true) (px : isPrin x = true) :
    lt x one = false := by
  cases x with
  | zero => simp [isPrin] at px
  | add _ _ => simp [isPrin] at px
  | inacc m d =>
    cases h : lt (inacc m d) one with
    | false => rfl
    | true =>
      exfalso
      rcases (lt_ip_iff m d bigOmega zero).mp h with ⟨hm, _⟩ | ⟨_, h'⟩
      · exact Nat.not_lt_zero m hm
      · rw [not_lt_bigOmega] at h'
        cases h'
  | psi w f =>
    have wx' := wf_psi wx
    obtain ⟨j, w', rfl⟩ := isRT_inacc wx'.1
    cases h : lt (psi (inacc j w') f) one with
    | false => rfl
    | true =>
      exfalso
      rcases (lt_pp_iff _ _ _ _).mp h with (⟨h', _⟩ | ⟨_, h'⟩) | ⟨hΩ, h'⟩
      · rw [not_lt_bigOmega] at h'
        cases h'
      · rw [lt_zero_right] at h'
        cases h'
      · rcases (lt_pi_iff 0 zero _ f).mp h' with ⟨_, e | h''⟩ | ⟨_, e | h''⟩
        · cases e
        · rw [lt_zero_right] at h''
          cases h''
        · rw [e] at hΩ
          change lt (inacc 0 zero) (inacc 0 zero) = true at hΩ
          rw [lt_irrefl] at hΩ
          cases hΩ
        · change lt (inacc j w') bigOmega = true at h''
          rw [not_lt_bigOmega] at h''
          cases h''

theorem eq_zero_of_lt_one {x : Term} (wx : wf x = true) (h : lt x one = true) : x = zero := by
  rcases shape x with e | ⟨x₁, x₂, rfl⟩ | px
  · exact e
  · have wx' := wf_add wx
    rw [lt_add_prin rfl, not_prin_lt_one wx'.2.1 wx'.1] at h
    cases h
  · rw [not_prin_lt_one wx px] at h
    cases h

/-! ### Successors -/

def succT : Term → Term
  | zero => one
  | add a b => add a (succT b)
  | inacc n b => add (inacc n b) one
  | psi u b => add (psi u b) one

theorem succT_prin {x : Term} (px : isPrin x = true) : succT x = add x one := by
  cases x with
  | zero => simp [isPrin] at px
  | add _ _ => simp [isPrin] at px
  | inacc _ _ => rfl
  | psi _ _ => rfl

theorem succT_spec : ∀ c : Term, wf c = true →
    wf (succT c) = true ∧ isSucc (succT c) = true ∧ fT (succT c) = 0 ∧ succT c ≠ zero ∧
      lt c (succT c) = true ∧ (c ≠ zero → head (succT c) = head c) := by
  intro c
  induction c with
  | zero =>
    intro _
    refine ⟨wf_one, rfl, rfl, (by intro h; cases h), lt_zero_left (by intro h; cases h), ?_⟩
    intro h
    exact absurd rfl h
  | add c₁ c₂ _ ih₂ =>
    intro wc
    have wc' := wf_add wc
    obtain ⟨w₂, s₂, _, n₂, l₂, h₂⟩ := ih₂ wc'.2.2.1
    refine ⟨?_, s₂, rfl, (by intro h; cases h), ?_, fun _ => rfl⟩
    · refine wf_add_intro wc'.1 wc'.2.1 w₂ n₂ ?_
      rw [h₂ wc'.2.2.2.1]
      exact wc'.2.2.2.2
    · show lt (add c₁ c₂) (add c₁ (succT c₂)) = true
      rw [lt_add_add, ite_eq_left rfl]
      exact l₂
  | inacc n b _ =>
    intro wc
    rw [succT_prin rfl]
    refine ⟨wf_add_intro rfl wc wf_one (by intro h; cases h) ?_, rfl, rfl,
      (by intro h; cases h), (lt_prin_add_iff rfl _ _).mpr (Or.inl rfl), fun _ => rfl⟩
    exact one_le_prin wc rfl
  | psi u b _ _ =>
    intro wc
    rw [succT_prin rfl]
    refine ⟨wf_add_intro rfl wc wf_one (by intro h; cases h) ?_, rfl, rfl,
      (by intro h; cases h), (lt_prin_add_iff rfl _ _).mpr (Or.inl rfl), fun _ => rfl⟩
    exact one_le_prin wc rfl

/-- Nothing lies strictly between `c` and `succT c`. -/
theorem le_of_lt_succT : ∀ c : Term, wf c = true → ∀ x : Term, wf x = true →
    lt x (succT c) = true → le x c = true := by
  intro c
  induction c with
  | zero =>
    intro _ x wx h
    rw [eq_zero_of_lt_one wx h]
    exact le_refl _
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
        rcases (le_iff _ _).mp (ih₂ wc'.2.2.1 x₂ wx'.2.2.1 h) with e' | h'
        · rw [e']
          exact le_refl _
        · refine le_of_lt ?_
          rw [lt_add_add, ite_eq_left rfl]
          exact h'
      · rw [ite_eq_right e] at h
        refine le_of_lt ?_
        rw [lt_add_add, ite_eq_right e]
        exact h
    · rcases (lt_prin_add_iff px _ _).mp h with e | h
      · rw [e]
        exact le_of_lt (lt_add_left wc)
      · exact le_of_lt (lt_trans wx wc'.2.1 wc h (lt_add_left wc))
  | inacc n b _ =>
    intro wc x wx h
    rw [succT_prin rfl] at h
    rcases shape x with rfl | ⟨x₁, x₂, rfl⟩ | px
    · exact le_of_lt (lt_zero_left (by intro h; cases h))
    · have wx' := wf_add wx
      rw [lt_add_add] at h
      by_cases e : x₁ = inacc n b
      · rw [ite_eq_left e] at h
        exact absurd (eq_zero_of_lt_one wx'.2.2.1 h) wx'.2.2.2.1
      · rw [ite_eq_right e] at h
        refine le_of_lt ?_
        rw [lt_add_prin rfl]
        exact h
    · rcases (lt_prin_add_iff px _ _).mp h with e | h
      · rw [e]
        exact le_refl _
      · exact le_of_lt h
  | psi u b _ _ =>
    intro wc x wx h
    rw [succT_prin rfl] at h
    rcases shape x with rfl | ⟨x₁, x₂, rfl⟩ | px
    · exact le_of_lt (lt_zero_left (by intro h; cases h))
    · have wx' := wf_add wx
      rw [lt_add_add] at h
      by_cases e : x₁ = psi u b
      · rw [ite_eq_left e] at h
        exact absurd (eq_zero_of_lt_one wx'.2.2.1 h) wx'.2.2.2.1
      · rw [ite_eq_right e] at h
        refine le_of_lt ?_
        rw [lt_add_prin rfl]
        exact h
    · rcases (lt_prin_add_iff px _ _).mp h with e | h
      · rw [e]
        exact le_refl _
      · exact le_of_lt h

/-! ### The next regular term -/

/-- `nr α` is the least regular term above `α`. -/
def nr : Term → Term
  | zero => bigOmega
  | add a _ => nr a
  | inacc n c => if n = 0 then inacc 0 (succT c) else inacc 0 (succT (inacc n c))
  | psi u b => if fT u = 0 then u else inacc 0 (succT (psi u b))

theorem isRT_inacc_succT {n : Nat} {s : Term} (h : isSucc s = true) : isRT (inacc n s) = true := by
  simp [isRT, isLimT, h]

theorem regular_succT {c : Term} (wc : wf c = true) :
    wf (inacc 0 (succT c)) = true ∧ isRT (inacc 0 (succT c)) = true := by
  obtain ⟨w, s, f, _⟩ := succT_spec c wc
  exact ⟨wf_inacc_intro w (Nat.le_of_eq f), isRT_inacc_succT s⟩

theorem nr_zero : nr zero = bigOmega := rfl

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
  | zero =>
    intro _
    exact ⟨wf_bigOmega, isRT_bigOmega, lt_zero_left (by intro h; cases h)⟩
  | add a b iha _ =>
    intro wα
    have wα' := wf_add wα
    obtain ⟨h1, h2, h3⟩ := iha wα'.2.1
    rw [nr_add, lt_add_prin (isPrin_of_isRT h2)]
    exact ⟨h1, h2, h3⟩
  | inacc n c _ =>
    intro wα
    by_cases hn : n = 0
    · subst hn
      have hc := (wf_inacc wα).1
      rw [nr_inacc_zero]
      refine ⟨(regular_succT hc).1, (regular_succT hc).2, ?_⟩
      rw [lt_ii_eq]
      exact (succT_spec c hc).2.2.2.2.1
    · rw [nr_inacc_pos hn]
      refine ⟨(regular_succT wα).1, (regular_succT wα).2, ?_⟩
      rw [lt_ii_gt (Nat.pos_of_ne_zero hn)]
      exact (succT_spec _ wα).2.2.2.2.1
  | psi u b _ _ =>
    intro wα
    have wα' := wf_psi wα
    by_cases hu : fT u = 0
    · rw [nr_psi_zero hu]
      exact ⟨wα'.2.1, wα'.1, lt_psi_index wα'.1 b⟩
    · rw [nr_psi_pos hu]
      refine ⟨(regular_succT wα).1, (regular_succT wα).2, ?_⟩
      exact (lt_pi_iff 0 _ u b).mpr (Or.inl ⟨Nat.pos_of_ne_zero hu,
        Or.inr (succT_spec _ wα).2.2.2.2.1⟩)

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
    have wα' := wf_add wα
    exact iha wα'.2.1 σ wσ hσ (lt_trans wα'.2.1 wα wσ (lt_add_left wα) h)
  | inacc n c _ =>
    intro wα σ wσ hσ h
    obtain ⟨j, d, rfl⟩ := isRT_inacc hσ
    have wd := (wf_inacc wσ).1
    refine le_of_not_lt (nr_spec _ wα).1 wσ ?_
    cases hlt : lt (inacc j d) (nr (inacc n c)) with
    | false => rfl
    | true =>
      exfalso
      by_cases hn0 : n = 0
      · subst hn0
        have hc := (wf_inacc wα).1
        rw [nr_inacc_zero] at hlt
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          rw [lt_ii_eq] at h hlt
          exact absurd (not_lt_of_le (le_of_lt_succT c hc d wd hlt)) (by rw [h]; decide)
        · rw [lt_ii_gt hj] at hlt
          rw [lt_ii_lt hj] at h
          exact absurd (not_lt_of_le (le_of_lt_succT c hc _ wσ hlt)) (by rw [h]; decide)
      · rw [nr_inacc_pos hn0] at hlt
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          rw [lt_ii_eq] at hlt
          rw [lt_ii_gt (Nat.pos_of_ne_zero hn0)] at h
          exact absurd (not_lt_of_le (le_of_lt_succT _ wα d wd hlt)) (by rw [h]; decide)
        · rw [lt_ii_gt hj] at hlt
          exact absurd (not_lt_of_le (le_of_lt_succT _ wα _ wσ hlt)) (by rw [h]; decide)
  | psi u b _ _ =>
    intro wα σ wσ hσ h
    obtain ⟨j, d, rfl⟩ := isRT_inacc hσ
    have wd := (wf_inacc wσ).1
    by_cases hu : fT u = 0
    · rw [nr_psi_zero hu]
      rcases (lt_pi_iff j d u b).mp h with ⟨hj, _⟩ | ⟨_, h'⟩
      · exact absurd hj (by omega)
      · exact (le_iff _ _).mpr h'
    · rw [nr_psi_pos hu]
      refine le_of_not_lt (regular_succT wα).1 wσ ?_
      cases hlt : lt (inacc j d) (inacc 0 (succT (psi u b))) with
      | false => rfl
      | true =>
        exfalso
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          rw [lt_ii_eq] at hlt
          have hd := le_of_lt_succT _ wα d wd hlt
          rcases (lt_pi_iff 0 d u b).mp h with ⟨_, e' | h'⟩ | ⟨hu', _⟩
          · rw [← e'] at wσ
            exact hu (Nat.le_zero.mp (wf_inacc wσ).2)
          · exact absurd (not_lt_of_le hd) (by rw [h']; decide)
          · exact hu (Nat.le_zero.mp hu')
        · rw [lt_ii_gt hj] at hlt
          exact absurd (not_lt_of_le (le_of_lt_succT _ wα _ wσ hlt)) (by rw [h]; decide)

end OCF.Jaeger.Term

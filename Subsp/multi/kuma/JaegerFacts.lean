import Subsp.OCF.Jaeger.Constructive.WellOrder

/-! Constructive facts about Jäger's notation used by the `multi` kumakuma proofs.

They replace the semantic arguments (through `Term.V`, `LargeCardinals` and the hulls `C`) by the
syntactic, choice-free theory of `Subsp/OCF/Jaeger/Constructive`. -/

namespace kumakuma.JaegerFacts

open OCF.Jaeger OCF.Jaeger.Term

/-- The order facts of `lemma_6_1`, proved constructively. -/
theorem jaeger_order :
    (∀ a, wf a = true → lt a a = false) ∧
    (∀ a b c, wf a = true → wf b = true → wf c = true →
      lt a b = true → lt b c = true → lt a c = true) ∧
    (∀ a b, wf a = true → wf b = true → lt a b = true ∨ a = b ∨ lt b a = true) :=
  ⟨fun a _ => lt_irrefl a, fun _ _ _ ha hb hc => lt_trans ha hb hc,
    fun _ _ ha hb => lt_trichotomy ha hb⟩

theorem size_predT_lt' : ∀ b : Term, isSucc b = true → size (predT b) < size b := by
  intro b
  induction b with
  | zero => intro h; simp [isSucc] at h
  | add a c _ ihc =>
    intro h
    by_cases e : c = one
    · rw [predT, ite_eq_left e]
      simp only [size]
      omega
    · rw [predT, ite_eq_right e]
      have := ihc h
      simp only [size]
      omega
  | inacc _ _ _ => intro h; simp [isSucc] at h
  | psi u c _ _ =>
    intro _
    have := size_pos u
    simp only [predT, size]
    omega

/-- Syntactic replacement of `Sem.isR_pred`: the predecessor of a regular term is well formed,
smaller and of smaller size. -/
theorem predR_facts {v : Term} (hv : wf v = true) (hvR : isRT v = true) :
    wf (predR v) = true ∧ lt (predR v) v = true ∧ size (predR v) < size v := by
  obtain ⟨n, b, rfl⟩ := isRT_inacc hvR
  have wb := (wf_inacc hv).1
  by_cases hb : b = zero
  · rw [predR, ite_eq_left hb]
    refine ⟨wf_zero, lt_zero_left (by intro h; cases h), ?_⟩
    rw [hb]
    simp only [size]
    omega
  · rw [predR, ite_eq_right hb]
    have hs := isSucc_of_isRT hvR hb
    obtain ⟨hp, wp⟩ := predT_spec b wb hs
    have hsz := size_predT_lt' b hs
    by_cases hf : fT (predT b) ≤ n
    · rw [ite_eq_left hf]
      refine ⟨wf_inacc_intro wp hf, by rw [lt_ii_eq]; exact hp, ?_⟩
      simp only [size]
      omega
    · rw [ite_eq_right hf]
      refine ⟨wp, lt_trans wp wb hv hp (lt_inacc_self hv), ?_⟩
      simp only [size]
      omega

theorem predR_lt_psi {v a : Term} (hw : wf (psi v a) = true) :
    lt (predR v) (psi v a) = true :=
  (predR_spec hw).1

/-- `a < ψ_v(a)` exactly when `a < v`. -/
theorem lt_psi_self_iff {v a : Term} (hw : wf (psi v a) = true) :
    lt a (psi v a) = true ↔ lt a v = true := by
  have hw' := wf_psi hw
  constructor
  · intro h
    exact lt_trans hw'.2.2.1 hw hw'.2.1 h (lt_psi_index hw'.1 a)
  · intro h
    exact lt_psi_of_H hw a hw'.2.2.1 hw'.2.2.2 h

theorem allLt_append_intro {l₁ l₂ : List Term} {b : Term} (h₁ : allLt l₁ b = true)
    (h₂ : allLt l₂ b = true) : allLt (l₁ ++ l₂) b = true := by
  unfold allLt at *
  rw [List.all_append, h₁, h₂]
  rfl

theorem allLt_cons_intro {c : Term} {l : List Term} {b : Term} (h₁ : lt c b = true)
    (h₂ : allLt l b = true) : allLt (c :: l) b = true := by
  unfold allLt at *
  rw [List.all_cons, h₁, h₂]
  rfl

theorem mem_allLt {l : List Term} {b z : Term} (h : allLt l b = true) (hz : z ∈ l) :
    lt z b = true := by
  unfold allLt at h
  exact List.all_eq_true.mp h z hz

theorem allLt_of_forall {l : List Term} {b : Term} (h : ∀ z, z ∈ l → lt z b = true) :
    allLt l b = true := by
  unfold allLt
  exact List.all_eq_true.mpr h

theorem mem_hOne {v z : Term} (h : z ∈ hOne v) : z = zero := by
  unfold hOne at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp at h
      exact h

/-- Coefficients of well-formed terms are well formed. -/
theorem H_mem_wf (v : Term) : ∀ t : Term, wf t = true → ∀ z, z ∈ H v t → wf z = true := by
  intro t
  induction t with
  | zero =>
    intro _ z hz
    rw [H_zero] at hz
    cases hz
  | add a b iha ihb =>
    intro ht z hz
    have ht' := wf_add ht
    rw [H_add] at hz
    rcases List.mem_append.mp hz with hz | hz
    · exact iha ht'.2.1 z hz
    · exact ihb ht'.2.2.1 z hz
  | inacc n b ihb =>
    intro ht z hz
    rw [H_inacc] at hz
    rcases List.mem_append.mp hz with hz | hz
    · by_cases hn : n = 0
      · rw [ite_eq_left hn] at hz
        cases hz
      · rw [ite_eq_right hn] at hz
        rw [mem_hOne hz]
        exact wf_zero
    · exact ihb (wf_inacc ht).1 z hz
  | psi w b ihw ihb =>
    intro ht z hz
    have ht' := wf_psi ht
    rw [H_psi] at hz
    by_cases h1 : le (psi w b) (predR v) = true
    · rw [ite_eq_left h1] at hz
      cases hz
    · rw [ite_eq_right h1] at hz
      by_cases h2 : lt w v = true
      · rw [ite_eq_left h2] at hz
        exact ihw ht'.2.1 z hz
      · rw [ite_eq_right h2] at hz
        rcases List.mem_cons.mp hz with e | hz
        · rw [e]
          exact ht'.2.2.1
        · rcases List.mem_append.mp hz with hz | hz
          · exact ihb ht'.2.2.1 z hz
          · exact ihw ht'.2.1 z hz

theorem allLt_trans {l : List Term} {c b : Term} (hl : ∀ z, z ∈ l → wf z = true)
    (wc : wf c = true) (wb : wf b = true) (h : allLt l c = true) (hcb : lt c b = true) :
    allLt l b = true :=
  allLt_of_forall (fun z hz => lt_trans (hl z hz) wc wb (mem_allLt h hz) hcb)

theorem hOne_eq_nil_of_lt {v : Term} (h : lt bigOmega v = true) : hOne v = [] := by
  unfold hOne
  by_cases h1 : le one (predR v) = true
  · rw [ite_eq_left h1]
  · rw [ite_eq_right h1, ite_eq_left h]

theorem hOne_eq_nil_of_le {v : Term} (h : le one (predR v) = true) : hOne v = [] := by
  unfold hOne
  rw [ite_eq_left h]

/-- Terms up to the predecessor of `v` have no coefficients with respect to `v`. -/
theorem H_nil_of_le_predR {v : Term} (hv : wf v = true) (hvR : isRT v = true) :
    ∀ t : Term, wf t = true → le t (predR v) = true → H v t = [] := by
  have hp := predR_facts hv hvR
  intro t
  induction t with
  | zero => intros; exact H_zero v
  | add a b iha ihb =>
    intro ht hle
    have ht' := wf_add ht
    rw [H_add, iha ht'.2.1 (le_of_lt (lt_of_lt_of_le ht'.2.1 ht hp.1 (lt_add_left ht) hle)),
      ihb ht'.2.2.1 (le_of_lt (lt_of_lt_of_le ht'.2.2.1 ht hp.1 (lt_add_right ht) hle))]
    rfl
  | inacc n b ihb =>
    intro ht hle
    have wb := (wf_inacc ht).1
    rw [H_inacc, ihb wb (le_of_lt (lt_of_lt_of_le wb ht hp.1 (lt_inacc_self ht) hle))]
    by_cases hn : n = 0
    · rw [ite_eq_left hn]
      rfl
    · rw [ite_eq_right hn, hOne_eq_nil_of_le (le_trans wf_one ht hp.1 (one_le_prin ht rfl) hle)]
      rfl
  | psi w b _ _ =>
    intro _ hle
    rw [H_psi, ite_eq_left hle]

/-- A collapse below a regular `v` but with index above `v` lies below the predecessor of `v`. -/
theorem psi_le_predR {v τ f : Term} (hv : wf v = true) (hvR : isRT v = true)
    (hw : wf (psi τ f) = true) (hvτ : lt v τ = true) (h : lt (psi τ f) v = true) :
    le (psi τ f) (predR v) = true := by
  obtain ⟨n, e, rfl⟩ := isRT_inacc hvR
  have we := (wf_inacc hv).1
  rcases (lt_pi_iff n e τ f).mp h with ⟨_, h'⟩ | ⟨_, h'⟩
  · by_cases he : e = zero
    · exfalso
      rw [he] at h'
      rcases h' with e' | h'
      · cases e'
      · rw [lt_zero_right] at h'
        cases h'
    · have hs := isSucc_of_isRT hvR he
      obtain ⟨_, wp⟩ := predT_spec e we hs
      have hle : le (psi τ f) (predT e) = true := by
        rcases h' with e' | h'
        · exfalso
          rw [← e'] at hs
          have e1 : psi τ f = one := of_decide_eq_true hs
          unfold one at e1
          injection e1 with eτ _
          rw [eτ, not_lt_bigOmega] at hvτ
          cases hvτ
        · exact le_of_lt_predT e we hs _ hw h'
      rw [predR, ite_eq_right he]
      by_cases hf : fT (predT e) ≤ n
      · rw [ite_eq_left hf]
        exact le_trans hw wp (wf_inacc_intro wp hf) hle
          (le_of_lt (lt_inacc_self (wf_inacc_intro wp hf)))
      · rw [ite_eq_right hf]
        exact hle
  · exfalso
    rcases h' with e' | h'
    · rw [e', lt_irrefl] at hvτ
      cases hvτ
    · exact lt_asymm hvτ h'
where
  le_of_lt_predT : ∀ e : Term, wf e = true → isSucc e = true → ∀ x : Term, wf x = true →
      lt x e = true → le x (predT e) = true := by
    intro e
    induction e with
    | zero => intro _ h; simp [isSucc] at h
    | add a b _ ihb =>
      intro we hs x wx h
      have we' := wf_add we
      have hsb : isSucc b = true := hs
      obtain ⟨_, wp⟩ := predT_spec (add a b) we hs
      rcases shape x with rfl | ⟨x₁, x₂, rfl⟩ | px
      · by_cases hz : predT (add a b) = zero
        · rw [hz]
          exact le_refl zero
        · exact le_of_lt (lt_zero_left hz)
      · have wx' := wf_add wx
        rw [lt_add_add] at h
        by_cases e1 : x₁ = a
        · subst e1
          rw [ite_eq_left rfl] at h
          by_cases eb : b = one
          · rw [eb] at h
            exact absurd (eq_zero_of_lt_one wx'.2.2.1 h) wx'.2.2.2.1
          · rw [predT, ite_eq_right eb]
            have hp' : wf (add x₁ (predT b)) = true := by
              have := predT_spec (add x₁ b) we hs
              rw [predT, ite_eq_right eb] at this
              exact this.2
            rcases (le_iff _ _).mp (ihb we'.2.2.1 hsb x₂ wx'.2.2.1 h) with e2 | h2
            · rw [e2]
              exact le_refl _
            · refine le_of_lt ?_
              rw [lt_add_add, ite_eq_left rfl]
              exact h2
        · rw [ite_eq_right e1] at h
          by_cases eb : b = one
          · rw [predT, ite_eq_left eb]
            refine le_of_lt ?_
            rw [lt_add_prin we'.1]
            exact h
          · rw [predT, ite_eq_right eb]
            refine le_of_lt ?_
            rw [lt_add_add, ite_eq_right e1]
            exact h
      · rcases (lt_prin_add_iff px a b).mp h with e1 | h1
        · rw [e1]
          by_cases eb : b = one
          · rw [predT, ite_eq_left eb]
            exact le_refl a
          · rw [predT, ite_eq_right eb]
            have hp' : wf (add a (predT b)) = true := by
              have := predT_spec (add a b) we hs
              rw [predT, ite_eq_right eb] at this
              exact this.2
            exact le_of_lt (lt_add_left hp')
        · by_cases eb : b = one
          · rw [predT, ite_eq_left eb]
            exact le_of_lt h1
          · rw [predT, ite_eq_right eb]
            have hp' : wf (add a (predT b)) = true := by
              have := predT_spec (add a b) we hs
              rw [predT, ite_eq_right eb] at this
              exact this.2
            exact le_of_lt (lt_trans wx we'.2.1 hp' h1 (lt_add_left hp'))
    | inacc _ _ _ => intro _ h; simp [isSucc] at h
    | psi u c _ _ =>
      intro _ hs x wx h
      have e : psi u c = one := of_decide_eq_true hs
      rw [e] at h
      rw [predT, eq_zero_of_lt_one wx h]
      exact le_refl zero

/-- `C^v(B) ∩ v` is an initial segment: coefficient bounds pass to smaller terms below `v`. -/
theorem H_downward {v B : Term} (hv : wf v = true) (hvR : isRT v = true) (wB : wf B = true) :
    ∀ x y : Term, wf x = true → wf y = true → lt x y = true → lt y v = true →
      allLt (H v y) B = true → allLt (H v x) B = true := by
  have hp := predR_facts hv hvR
  have key : ∀ N : Nat, ∀ x y : Term, size x + size y ≤ N → wf x = true → wf y = true →
      lt x y = true → lt y v = true → allLt (H v y) B = true → allLt (H v x) B = true := by
    intro N
    induction N with
    | zero =>
      intro x _ hs
      have := size_pos x
      exact absurd hs (by omega)
    | succ N ih =>
      intro x y hs wx wy hxy hyv hH
      cases x with
      | zero => rw [H_zero]; rfl
      | add x₁ x₂ =>
        have wx' := wf_add wx
        rw [H_add]
        exact allLt_append_intro
          (ih x₁ y (by size_omega) wx'.2.1 wy (lt_trans wx'.2.1 wx wy (lt_add_left wx) hxy) hyv hH)
          (ih x₂ y (by size_omega) wx'.2.2.1 wy
            (lt_trans wx'.2.2.1 wx wy (lt_add_right wx) hxy) hyv hH)
      | inacc n d =>
        have wd := (wf_inacc wx).1
        rw [H_inacc]
        refine allLt_append_intro ?_ (ih d y (by size_omega) wd wy
          (lt_trans wd wx wy (lt_inacc_self wx) hxy) hyv hH)
        by_cases hn : n = 0
        · rw [ite_eq_left hn]
          rfl
        · rw [ite_eq_right hn]
          have hΩx : lt bigOmega (inacc n d) = true := by
            unfold bigOmega
            rw [lt_ii_lt (Nat.pos_of_ne_zero hn)]
            exact lt_zero_left (by intro h; cases h)
          have hΩv := lt_trans wf_bigOmega wx hv hΩx (lt_trans wx wy hv hxy hyv)
          rw [hOne_eq_nil_of_lt hΩv]
          rfl
      | psi σ c =>
        have wx' := wf_psi wx
        by_cases hle : le (psi σ c) (predR v) = true
        · rw [H_nil_of_le_predR hv hvR _ wx hle]
          rfl
        -- the general shape of `H v (psi σ c)` once the first test fails
        have hHx : H v (psi σ c) =
            if lt σ v = true then H v σ else c :: (H v c ++ H v σ) := by
          rw [H_psi, ite_eq_right hle]
        cases y with
        | zero =>
          rw [lt_zero_right] at hxy
          cases hxy
        | add y₁ y₂ =>
          have wy' := wf_add wy
          rw [H_add] at hH
          have hy₁v := lt_trans wy'.2.1 wy hv (lt_add_left wy) hyv
          rcases (lt_prin_add_iff rfl y₁ y₂).mp hxy with e | h
          · rw [e]
            exact (allLt_append hH).1
          · exact ih _ y₁ (by size_omega) wx wy'.2.1 h hy₁v (allLt_append hH).1
        | inacc m e =>
          have we := (wf_inacc wy).1
          have hH' := hH
          rw [H_inacc] at hH'
          have hev := lt_trans we wy hv (lt_inacc_self wy) hyv
          rcases (lt_pi_iff m e σ c).mp hxy with ⟨_, h⟩ | ⟨_, h⟩
          · rcases h with e' | h
            · rw [e']
              exact (allLt_append hH').2
            · exact ih _ e (by size_omega) wx we h hev (allLt_append hH').2
          · have hσv : lt σ v = true := lt_of_le_of_lt wx'.2.1 wy hv ((le_iff _ _).mpr h) hyv
            rw [hHx, ite_eq_left hσv]
            rcases h with e' | h
            · rw [e']
              exact hH
            · exact ih σ (inacc m e) (by size_omega) wx'.2.1 wy h hyv hH
        | psi τ f =>
          have wy' := wf_psi wy
          by_cases hley : le (psi τ f) (predR v) = true
          · exact absurd (le_of_lt (lt_of_lt_of_le wx wy hp.1 hxy hley)) hle
          have hHy : H v (psi τ f) =
              if lt τ v = true then H v τ else f :: (H v f ++ H v τ) := by
            rw [H_psi, ite_eq_right hley]
          rcases (lt_pp_iff σ c τ f).mp hxy with (⟨hστ, hσy⟩ | ⟨eστ, hcf⟩) | ⟨hτσ, hxτ⟩
          · by_cases hσv : lt σ v = true
            · rw [hHx, ite_eq_left hσv]
              exact ih σ (psi τ f) (by size_omega) wx'.2.1 wy hσy hyv hH
            · exfalso
              exact hσv (lt_trans wx'.2.1 wy hv hσy hyv)
          · subst eστ
            by_cases hσv : lt σ v = true
            · rw [hHx, ite_eq_left hσv]
              rw [hHy, ite_eq_left hσv] at hH
              exact hH
            · rw [hHy, ite_eq_right hσv] at hH
              have hfB := (allLt_cons hH).1
              have hrest := allLt_append (allLt_cons hH).2
              rw [hHx, ite_eq_right hσv]
              have hcB := lt_trans wx'.2.2.1 wy'.2.2.1 wB hcf hfB
              have hcc : allLt (H v c) c = true := by
                rcases lt_trichotomy wx'.2.1 hv with h | e | h
                · exact absurd h hσv
                · rw [← e]
                  exact wx'.2.2.2
                · exact absurd (psi_le_predR hv hvR wx h (lt_trans wx wy hv hxy hyv)) hle
              exact allLt_cons_intro hcB (allLt_append_intro
                (allLt_trans (H_mem_wf v c wx'.2.2.1) wx'.2.2.1 wB hcc hcB) hrest.2)
          · have hτv : lt τ v = true := by
              rcases lt_trichotomy wy'.2.1 hv with h | e | h
              · exact h
              · exfalso
                rw [e] at hτσ
                exact hle (psi_le_predR hv hvR wx hτσ (lt_trans wx wy hv hxy hyv))
              · exfalso
                exact hley (psi_le_predR hv hvR wy h hyv)
            rw [hHy, ite_eq_left hτv] at hH
            exact ih (psi σ c) τ (by size_omega) wx wy'.2.1 hxτ hτv hH
  intro x y wx wy hxy hyv hH
  exact key _ x y (Nat.le_refl _) wx wy hxy hyv hH

end kumakuma.JaegerFacts

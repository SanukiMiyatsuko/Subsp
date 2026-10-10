import Subsp.OCF.Jaeger.Constructive.WellOrder

/-! Constructive facts about Jäger's notation used by the `multi` kumakuma proofs.

They replace the semantic arguments (through `Term.V`, `LargeCardinals` and the hulls `C`) by the
syntactic, choice-free theory of `Subsp/OCF/Jaeger/Constructive`. -/

namespace kumakuma.JaegerFacts

open OCF.Jaeger OCF.Jaeger.Term

/-- Syntactic replacement of `Sem.isR_pred`: the predecessor of a regular term is well formed,
smaller and of smaller size. -/
theorem predR_facts {v : Term} (hv : wf v = true) (hvR : isRT v = true) :
    wf (predR v) = true ∧ lt (predR v) v = true ∧ size (predR v) < size v := by
  obtain ⟨n, b, rfl⟩ := isRT_inacc hvR
  have wb := (wf_inacc hv).1
  have := size_pos b
  by_cases hb : b = zero
  · rw [predR, ite_eq_left hb]
    exact ⟨wf_zero, lt_zero_left (by intro h; cases h), by simp only [size]; omega⟩
  rw [predR, ite_eq_right hb]
  have hs := isSucc_of_isRT hvR hb
  obtain ⟨hp, wp⟩ := predT_spec b wb hs
  have := size_predT_lt hs
  by_cases hf : fT (predT b) ≤ n
  · rw [ite_eq_left hf]
    exact ⟨wf_inacc_intro wp hf, by rw [lt_ii_eq]; exact hp, by simp only [size]; omega⟩
  · rw [ite_eq_right hf]
    exact ⟨wp, lt_trans wp wb hv hp (lt_inacc_self hv), by simp only [size]; omega⟩

/-- `a < ψ_v(a)` exactly when `a < v`. -/
theorem lt_psi_self_iff {v a : Term} (hw : wf (psi v a) = true) :
    lt a (psi v a) = true ↔ lt a v = true :=
  have hw' := wf_psi hw
  ⟨fun h => lt_trans hw'.2.2.1 hw hw'.2.1 h (lt_psi_index hw'.1 a),
    lt_psi_of_H hw a hw'.2.2.1 hw'.2.2.2⟩

theorem allLt_append_intro {l₁ l₂ : List Term} {b : Term} (h₁ : allLt l₁ b = true)
    (h₂ : allLt l₂ b = true) : allLt (l₁ ++ l₂) b = true := by
  rw [allLt, List.all_append, Bool.and_eq_true]; exact ⟨h₁, h₂⟩

/-- Coefficients of well-formed terms are well formed. -/
theorem H_mem_wf (v : Term) : ∀ t : Term, wf t = true → ∀ z, z ∈ H v t → wf z = true := by
  intro t
  induction t with
  | zero => intro _ z hz; cases hz
  | add a b iha ihb =>
    intro ht z hz
    rw [H_add] at hz
    exact (List.mem_append.mp hz).elim (iha (wf_add ht).2.1 z) (ihb (wf_add ht).2.2.1 z)
  | inacc n b ihb =>
    intro ht z hz
    rw [H_inacc] at hz
    refine (List.mem_append.mp hz).elim (fun hz => ?_) (ihb (wf_inacc ht).1 z)
    split at hz
    · cases hz
    · rw [mem_hOne hz]; exact wf_zero
  | psi w b ihw ihb =>
    intro ht z hz
    have ht' := wf_psi ht
    rw [H_psi] at hz
    split at hz
    · cases hz
    split at hz
    · exact ihw ht'.2.1 z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ht'.2.2.1
    exact (List.mem_append.mp hz).elim (ihb ht'.2.2.1 z) (ihw ht'.2.1 z)

/-- Terms up to the predecessor of `v` have no coefficients with respect to `v`. -/
theorem H_nil_of_le_predR {v : Term} (hv : wf v = true) (hvR : isRT v = true) :
    ∀ t : Term, wf t = true → le t (predR v) = true → H v t = [] := by
  have hp := predR_facts hv hvR
  have below : ∀ {s t}, wf s = true → wf t = true → lt s t = true → le t (predR v) = true →
      le s (predR v) = true := fun ws wt hst hle => le_of_lt (lt_of_lt_of_le ws wt hp.1 hst hle)
  intro t
  induction t with
  | zero => intros; exact H_zero v
  | add a b iha ihb =>
    intro ht hle
    have ht' := wf_add ht
    rw [H_add, iha ht'.2.1 (below ht'.2.1 ht (lt_add_left ht) hle),
      ihb ht'.2.2.1 (below ht'.2.2.1 ht (lt_add_right ht) hle)]
    rfl
  | inacc n b ihb =>
    intro ht hle
    have wb := (wf_inacc ht).1
    rw [H_inacc, ihb wb (below wb ht (lt_inacc_self ht) hle), hOne,
      ite_eq_left (le_trans wf_one ht hp.1 (one_le_prin ht rfl) hle), ite_self]
    rfl
  | psi w b _ _ => intro _ hle; rw [H_psi, ite_eq_left hle]

theorem succT_predT : ∀ e : Term, wf e = true → isSucc e = true → succT (predT e) = e := by
  intro e
  induction e with
  | add a b _ ihb =>
    intro we hs
    by_cases eb : b = one
    · rw [predT, ite_eq_left eb, eb]
      have := (wf_add we).1
      cases a <;> first | rfl | cases this
    · rw [predT, ite_eq_right eb]; exact congrArg (add a) (ihb (wf_add we).2.2.1 hs)
  | psi u c _ _ => intro _ hs; exact (of_decide_eq_true hs).symm
  | zero | inacc => intro _ h; cases h

/-- A collapse below a regular `v` but with index above `v` lies below the predecessor of `v`. -/
theorem psi_le_predR {v τ f : Term} (hv : wf v = true) (hvR : isRT v = true)
    (hw : wf (psi τ f) = true) (hvτ : lt v τ = true) (h : lt (psi τ f) v = true) :
    le (psi τ f) (predR v) = true := by
  obtain ⟨n, e, rfl⟩ := isRT_inacc hvR
  rcases (lt_pi_iff n e τ f).mp h with ⟨_, rfl | h'⟩ | ⟨_, h' | h'⟩
  · -- a successor collapse is `one`, whose index `Ω` is not above `v`
    have e1 : psi τ f = one := of_decide_eq_true (isSucc_of_isRT hvR (by intro h; cases h))
    rw [(Term.psi.inj e1).1, not_lt_bigOmega] at hvτ; cases hvτ
  · have we := (wf_inacc hv).1
    have he : e ≠ zero := by rintro rfl; rw [lt_zero_right] at h'; cases h'
    have hs := isSucc_of_isRT hvR he
    have wp := (predT_spec e we hs).2
    have hle := le_of_lt_succT _ wp _ hw (by rw [succT_predT e we hs]; exact h')
    rw [predR, ite_eq_right he]
    split
    · next hf =>
      have wi := wf_inacc_intro wp hf
      exact le_trans hw wp wi hle (le_of_lt (lt_inacc_self wi))
    · exact hle
  · rw [h', lt_irrefl] at hvτ; cases hvτ
  · exact (lt_asymm hvτ h').elim

/-- `C^v(B) ∩ v` is an initial segment: coefficient bounds pass to smaller terms below `v`. -/
theorem H_downward {v B : Term} (hv : wf v = true) (hvR : isRT v = true) (wB : wf B = true) :
    ∀ x y : Term, wf x = true → wf y = true → lt x y = true → lt y v = true →
      allLt (H v y) B = true → allLt (H v x) B = true := by
  have hp := predR_facts hv hvR
  suffices key : ∀ N x y, size x + size y ≤ N → wf x = true → wf y = true →
      lt x y = true → lt y v = true → allLt (H v y) B = true → allLt (H v x) B = true from
    fun x y => key _ x y (Nat.le_refl _)
  intro N
  induction N with
  | zero => intro x _ hs; have := size_pos x; exact absurd hs (by omega)
  | succ N ih =>
  have step : ∀ s t, size s + size t ≤ N → wf s = true → wf t = true →
      (s = t ∨ lt s t = true) → lt t v = true → allLt (H v t) B = true →
      allLt (H v s) B = true := by
    rintro s t hst ws wt (rfl | h) htv hHt
    · exact hHt
    · exact ih s t hst ws wt h htv hHt
  intro x y hs wx wy hxy hyv hH
  have hxv := lt_trans wx wy hv hxy hyv
  cases x with
  | zero => rw [H_zero]; rfl
  | add x₁ x₂ =>
    have wx' := wf_add wx
    rw [H_add]
    exact allLt_append_intro
      (ih x₁ y (by size_omega) wx'.2.1 wy (lt_trans wx'.2.1 wx wy (lt_add_left wx) hxy) hyv hH)
      (ih x₂ y (by size_omega) wx'.2.2.1 wy (lt_trans wx'.2.2.1 wx wy (lt_add_right wx) hxy) hyv hH)
  | inacc n d =>
    have wd := (wf_inacc wx).1
    rw [H_inacc]
    refine allLt_append_intro ?_ (ih d y (by size_omega) wd wy
      (lt_trans wd wx wy (lt_inacc_self wx) hxy) hyv hH)
    split
    · rfl
    · next hn =>
      have hΩx : lt bigOmega (inacc n d) = true := by
        unfold bigOmega
        rw [lt_ii_lt (Nat.pos_of_ne_zero hn)]
        exact lt_zero_left (by intro h; cases h)
      rw [hOne, ite_eq_left (lt_trans wf_bigOmega wx hv hΩx hxv), ite_self]
      rfl
  | psi σ c =>
    have wx' := wf_psi wx
    by_cases hle : le (psi σ c) (predR v) = true
    · rw [H_nil_of_le_predR hv hvR _ wx hle]; rfl
    have hσ : lt σ v = true ∨ σ = v := (lt_trichotomy wx'.2.1 hv).imp_right
      (·.resolve_right fun h => hle (psi_le_predR hv hvR wx h hxv))
    cases y with
    | zero => rw [lt_zero_right] at hxy; cases hxy
    | add y₁ y₂ =>
      have wy' := wf_add wy
      rw [H_add] at hH
      exact step _ y₁ (by size_omega) wx wy'.2.1 ((lt_prin_add_iff rfl y₁ y₂).mp hxy)
        (lt_trans wy'.2.1 wy hv (lt_add_left wy) hyv) (allLt_append hH).1
    | inacc m e =>
      have we := (wf_inacc wy).1
      rcases (lt_pi_iff m e σ c).mp hxy with ⟨_, h⟩ | ⟨_, h⟩
      · rw [H_inacc] at hH
        exact step _ e (by size_omega) wx we h (lt_trans we wy hv (lt_inacc_self wy) hyv)
          (allLt_append hH).2
      · rw [H_psi, ite_eq_right hle,
          ite_eq_left (lt_of_le_of_lt wx'.2.1 wy hv ((le_iff _ _).mpr h) hyv)]
        exact step σ _ (by size_omega) wx'.2.1 wy h hyv hH
    | psi τ f =>
      have wy' := wf_psi wy
      have hley : ¬ le (psi τ f) (predR v) = true :=
        fun h => hle (le_of_lt (lt_of_lt_of_le wx wy hp.1 hxy h))
      rcases (lt_pp_iff σ c τ f).mp hxy with (⟨_, hσy⟩ | ⟨rfl, hcf⟩) | ⟨hτσ, hxτ⟩
      · rw [H_psi, ite_eq_right hle, ite_eq_left (lt_trans wx'.2.1 wy hv hσy hyv)]
        exact ih σ _ (by size_omega) wx'.2.1 wy hσy hyv hH
      · rw [H_psi, ite_eq_right hley] at hH
        rw [H_psi, ite_eq_right hle]
        rcases hσ with hσv | rfl
        · rwa [ite_eq_left hσv] at hH ⊢
        · rw [ite_eq_right (by rw [lt_irrefl]; exact Bool.false_ne_true)] at hH ⊢
          have hcB := lt_trans wx'.2.2.1 wy'.2.2.1 wB hcf (allLt_cons hH).1
          rw [allLt, List.all_cons, Bool.and_eq_true]
          exact ⟨hcB, allLt_append_intro ((allLt_iff _ _).mpr fun z hz =>
            lt_trans (H_mem_wf _ _ wx'.2.2.1 z hz) wx'.2.2.1 wB
              ((allLt_iff _ _).mp wx'.2.2.2 z hz) hcB) (allLt_append (allLt_cons hH).2).2⟩
      · have hτv : lt τ v = true := hσ.elim (lt_trans wy'.2.1 wx'.2.1 hv hτσ) (· ▸ hτσ)
        rw [H_psi, ite_eq_right hley, ite_eq_left hτv] at hH
        exact ih _ τ (by size_omega) wx wy'.2.1 hxτ hτv hH

end kumakuma.JaegerFacts

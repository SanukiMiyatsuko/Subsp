import Subsp.OCF.Jaeger.Constructive.Distinguished

/-! The constructive well-ordering proof for Jäger's notation system.

`wmax_of_good` shows `Good α → α ∈ Wmax` (Arai's Lemma 3.26 specialised to Jäger's system, where
collapsing terms are never regular).  Closure of `Wmax` under `0`, `+`, `I_n` and `ψ` follows, so
every `wf` term lies in `Wmax`, and `Term.lt` is well-founded on `wf` terms.  The proof depends
only on `propext` and `Quot.sound`. -/

namespace OCF.Jaeger.Term

/-- Induction over the members of `C^θ(Wmax)` whose coefficients with respect to `ρ` lie below
`c₀`, when `ψ_ρ(c₀) ≤ θ`: terms below `θ` are handled by `good`, the others are decomposed, and
their collapses have index at least `ρ` and argument below `c₀`. -/
theorem coeff_induction {θ ρ c₀ : Term} (P : Term → Prop) (wψ : wf (psi ρ c₀) = true)
    (wθ : wf θ = true) (hψθ : le (psi ρ c₀) θ = true) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → lt x θ = true → size x < S → P x) (hzero : P zero)
    (hadd : ∀ {a b}, wf (add a b) = true → P a → P b → P (add a b))
    (hinacc : ∀ {n b}, wf (inacc n b) = true → P b → P (inacc n b))
    (hpsi : ∀ {σ d}, wf (psi σ d) = true → le ρ σ = true → lt d c₀ = true → lt θ σ = true →
      Hull θ Wmax σ → Hull θ Wmax d → P σ → P d → P (psi σ d)) :
    ∀ x, Hull θ Wmax x → size x < S → allLt (H ρ x) c₀ = true → P x := by
  have wρ := (wf_psi wψ).2.1
  have hpred := predR_spec wψ
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hH
    cases hxθ : lt x θ with
    | true => exact good x hx hxθ hs
    | false =>
      cases hx with
      | zero => exact hzero
      | mem _ _ hlt => rw [hlt] at hxθ; cases hxθ
      | @add a b hw ha hb =>
        rw [H_add] at hH
        exact hadd hw (ih a (by size_omega) ha (by size_omega) (allLt_append hH).1)
          (ih b (by size_omega) hb (by size_omega) (allLt_append hH).2)
      | @inacc n b hw hb =>
        rw [H_inacc] at hH
        exact hinacc hw (ih b (by size_omega) hb (by size_omega) (allLt_append hH).2)
      | @psi σ d hw hθσ hσ hd =>
        have wx' := wf_psi hw
        have hH0 := hH
        rw [H_psi] at hH
        have hnle : ¬ (le (psi σ d) (predR ρ) = true) := fun hle => by
          rw [lt_of_lt_of_le hw wψ wθ (lt_of_le_of_lt hw hpred.2 wψ hle hpred.1) hψθ] at hxθ
          cases hxθ
        rw [ite_eq_right hnle] at hH
        by_cases hσρ : lt σ ρ = true
        · rw [lt_of_lt_of_le hw wψ wθ (lt_psi_of_H wψ (psi σ d) hw hH0
            (lt_trans hw wx'.2.1 wρ (lt_psi_index wx'.1 d) hσρ)) hψθ] at hxθ
          cases hxθ
        rw [ite_eq_right hσρ] at hH
        have hh := allLt_append (allLt_cons hH).2
        exact hpsi hw (le_of_not_lt wρ wx'.2.1 (Bool.eq_false_iff.mpr hσρ)) (allLt_cons hH).1
          hθσ hσ hd (ih σ (by size_omega) hσ (by size_omega) hh.2)
          (ih d (by size_omega) hd (by size_omega) hh.1)

/-- Moving a term from `C^θ(Wmax)` to `C^ν(Wmax)` for `ν < ρ`, when its coefficients with
respect to `ρ` lie below `c` and `ψ_ρ(c) ≤ θ`. -/
theorem hull_transfer {θ ν ρ c : Term} (wψ : wf (psi ρ c) = true) (wθ : wf θ = true)
    (wν : wf ν = true) (hψθ : le (psi ρ c) θ = true) (hνρ : lt ν ρ = true) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → lt x θ = true → size x < S → Wmax x) :
    ∀ x, Hull θ Wmax x → size x < S → allLt (H ρ x) c = true → Hull ν Wmax x :=
  coeff_induction (fun x => Hull ν Wmax x) wψ wθ hψθ S
    (fun x hx hxθ hs => wmax_hull (good x hx hxθ hs) wν) Hull.zero Hull.add Hull.inacc
    (fun hw hρσ _ _ _ _ hσ hd =>
      Hull.psi hw (lt_of_lt_of_le wν (wf_psi wψ).2.1 (wf_psi hw).2.1 hνρ hρσ) hσ hd)

/-- Case 2 of the proof of (18): a collapse with index at most `β` lying below `γ`. -/
theorem case_two {β γ π a : Term} (wβ : wf β = true) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → lt ζ γ = true → Wmax ζ) (hπβ : le π β = true)
    (hγπ : lt γ π = true) (hα : Hull γ Wmax (psi π a)) (hαγ : lt (psi π a) γ = true) :
    Wmax (psi π a) := by
  have wγ := hγH.wf_of
  have wπ := (wf_psi hα.wf_of).2.1
  have hnγ := nr_spec γ wγ
  cases hγH with
  | zero => rw [lt_zero_right] at hαγ; cases hαγ
  | mem hX _ _ => exact (wmax_good hX).2 _ hα hαγ
  | @add g₁ g₂ hw hg₁ _ =>
    exact wmax_bounded wγ hα (MIH g₁ hg₁ (lt_add_left hw))
      ((le_iff _ _).mpr ((lt_prin_add_iff rfl g₁ g₂).mp hαγ))
      (lt_trans (wf_add hw).2.1 hw hnγ.1 (lt_add_left hw) hnγ.2.2)
  | @inacc m e hw he =>
    rcases (lt_pi_iff m e π a).mp hαγ with ⟨_, h⟩ | ⟨_, h⟩
    · exact wmax_bounded wγ hα (MIH e he (lt_inacc_self hw)) ((le_iff _ _).mpr h)
        (lt_trans (wf_inacc hw).1 hw hnγ.1 (lt_inacc_self hw) hnγ.2.2)
    · rw [not_lt_of_le ((le_iff _ _).mpr h)] at hγπ; cases hγπ
  | @psi κ b hw hβκ _ _ =>
    exfalso
    have hπκ : lt π κ = true := lt_of_le_of_lt wπ wβ (wf_psi hw).2.1 hπβ hβκ
    rcases (lt_pp_iff π a κ b).mp hαγ with (⟨_, h⟩ | ⟨rfl, _⟩) | ⟨h, _⟩
    · exact lt_asymm h hγπ
    · exact ne_of_lt hπκ rfl
    · exact lt_asymm h hπκ

/-- Step 3 of the proof of Lemma 3.26: a good term below `η` lies in `Wmax`. -/
theorem step_three {η γ : Term} (hG : Good η)
    (h15 : ∀ b, Good (psi η b) → Wmax (psi η b)) (hγ : Good γ) (hγη : lt γ η = true)
    (Obs : ∀ δ, Wmax δ → le γ δ = true → Wmax γ) : Wmax γ := by
  have wη := hG.1.wf_of
  have wγ := hγ.1.wf_of
  cases γ with
  | zero => exact hG.2 zero Hull.zero hγη
  | add g₁ g₂ =>
    cases hγ.1 with
    | mem _ _ hlt => exact (ne_of_lt hlt rfl).elim
    | add hw hg₁ hg₂ =>
      exact hG.2 _ (Hull.add hw (wmax_hull (hγ.2 _ hg₁ (lt_add_left hw)) wη)
        (wmax_hull (hγ.2 _ hg₂ (lt_add_right hw)) wη)) hγη
  | inacc m e =>
    cases hγ.1 with
    | mem _ _ hlt => exact (ne_of_lt hlt rfl).elim
    | inacc hw he =>
      exact hG.2 _ (Hull.inacc hw (wmax_hull (hγ.2 _ he (lt_inacc_self hw)) wη)) hγη
  | psi ρ c =>
    cases hγ.1 with
    | mem _ _ hlt => exact (ne_of_lt hlt rfl).elim
    | psi hw _ hρ hc =>
      have hw' := wf_psi hw
      obtain ⟨k, e, rfl⟩ := isRT_inacc hw'.1
      have hρη' : Hull η Wmax (inacc k e) := by
        cases hρ with
        | mem hX _ _ => exact wmax_hull hX wη
        | inacc _ he => exact Hull.inacc hw'.2.1 (wmax_hull (hγ.2 e he (lt_psi_of_arg hw)) wη)
      rcases lt_trichotomy hw'.2.1 wη with hρη | rfl | hηρ
      · exact Obs _ (hG.2 _ hρη' hρη) (le_of_lt (lt_psi_index hw'.1 c))
      · exact h15 c hγ
      · exact hG.2 _ (Hull.psi hw hηρ hρη' (hull_transfer hw wγ wη (le_refl _) hηρ (size c + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) c hc (by omega) hw'.2.2.2)) hγη

/-- Arai's Lemma 3.26 for Jäger's system: the extension hypothesis holds for good terms whose
collapses, when good, are already in `Wmax`. -/
theorem hyp_of_good {η : Term} (hG : Good η)
    (h15 : ∀ b, Good (psi η b) → Wmax (psi η b)) : Hyp η := by
  have wη := hG.1.wf_of
  intro β wβ hle γ hW hγ
  have hnβ := nr_spec β wβ
  have key : ∀ γ, Acc (Rel (Hull β Wmax)) γ → Hull β Wmax γ → lt γ (nr β) = true → Wmax γ := by
    intro γ hacc
    induction hacc with
    | intro γ hacc' MIH0 =>
      intro hγH hγ
      have wγ := hγH.wf_of
      have MIH : ∀ ζ, Hull β Wmax ζ → lt ζ γ = true → Wmax ζ := fun ζ hζ hζγ =>
        MIH0 ζ ⟨hζ, hζγ⟩ hζ (lt_trans hζ.wf_of wγ hnβ.1 hζγ hγ)
      have Obs : ∀ δ, Wmax δ → le γ δ = true → Wmax γ := by
        intro δ hδ hγδ
        have wδ := wmax_wf hδ
        cases hδβ : lt δ β with
        | true =>
          exact wmax_bounded wδ (Hull.lower HW wδ wβ (le_of_lt hδβ) hγH) hδ hγδ
            (nr_spec δ wδ).2.2
        | false =>
          exact ((wmax_dist.2 β wβ ⟨δ, hδ, le_of_not_lt wβ wδ hδβ⟩ γ).mp
            ⟨⟨hγH, Acc.intro γ hacc'⟩, hγ⟩).1
      have G2 : ∀ α, Hull γ Wmax α → lt α γ = true → Wmax α := by
        intro α
        induction α using size_induction with
        | h α ihα =>
          intro hα hαγ
          cases hβnγ : lt β (nr γ) with
          | true => exact MIH α (Hull.sub_of_lt_nr HW wγ wβ hβnγ hα) hαγ
          | false =>
            have below : ∀ x, wf x = true → lt x α = true → lt x γ = true :=
              fun x wx h => lt_trans wx hα.wf_of wγ h hαγ
            cases hα with
            | zero => exact MIH zero Hull.zero hαγ
            | mem hX _ _ => exact hX
            | @add a b hw ha hb =>
              exact MIH _ (Hull.add hw
                (wmax_hull (ihα a (by size_omega) ha (below a (wf_add hw).2.1 (lt_add_left hw))) wβ)
                (wmax_hull (ihα b (by size_omega) hb
                  (below b (wf_add hw).2.2.1 (lt_add_right hw))) wβ)) hαγ
            | @inacc n d hw hd =>
              exact MIH _ (Hull.inacc hw (wmax_hull (ihα d (by size_omega) hd
                (below d (wf_inacc hw).1 (lt_inacc_self hw))) wβ)) hαγ
            | @psi π a hw hγπ hπ ha =>
              have hw' := wf_psi hw
              cases hβπ : lt β π with
              | false =>
                exact case_two wβ hγH MIH (le_of_not_lt hw'.2.1 wβ hβπ) hγπ
                  (Hull.psi hw hγπ hπ ha) hαγ
              | true =>
                obtain ⟨k, e, rfl⟩ := isRT_inacc hw'.1
                have hπ'' : Hull β Wmax (inacc k e) := by
                  cases hπ with
                  | mem hX _ _ => exact wmax_hull hX wβ
                  | inacc hwπ he =>
                    exact Hull.inacc hwπ (wmax_hull (ihα e (by size_omega) he
                      (below e (wf_inacc hw'.2.1).1 (lt_psi_of_arg hw))) wβ)
                exact MIH _ (Hull.psi hw hβπ hπ'' (hull_transfer hw wγ wβ (le_of_lt hαγ) hβπ _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega) hw'.2.2.2)) hαγ
      exact step_three hG h15 ⟨Hull.sub_of_lt_nr HW wβ wγ hγ hγH, G2⟩
        (lt_of_lt_of_le wγ hnβ.1 wη hγ hle) Obs
  exact key γ hW.2 hW.1 hγ

/-- Every good term belongs to the maximal distinguished set. -/
theorem wmax_of_good {η : Term} (hG : Good η) : Wmax η :=
  wmax_of_good_hyp hG (hyp_of_good hG (fun _ hgb => wmax_of_good_hyp hgb (hyp_of_good hgb
    (fun _ hgb' => absurd (wf_psi hgb'.1.wf_of).1 (by simp [isRT])))))

/-! ### Closure properties of `Wmax` -/

theorem wmax_zero : Wmax zero :=
  wmax_of_good ⟨Hull.zero, fun _ _ h => by rw [lt_zero_right] at h; cases h⟩

theorem wmax_inacc_arg {n : Nat} {e : Term} (h : Wmax (inacc n e)) : Wmax e := by
  cases (wmax_good h).1 with
  | mem _ _ hlt => exact (ne_of_lt hlt rfl).elim
  | inacc hw he => exact (wmax_good h).2 e he (lt_inacc_self hw)

theorem wmax_add {a b : Term} (hw : wf (add a b) = true) (ha : Wmax a) (hb : Wmax b) :
    Wmax (add a b) := by
  have key : ∀ b, Acc (Rel Wmax) b → Wmax b → wf (add a b) = true → Wmax (add a b) := by
    intro b hacc
    induction hacc with
    | intro b _ ih =>
      intro hb hw
      have hn := nr_spec _ hw
      have ha_lt := lt_trans (wmax_wf ha) hw hn.1 (lt_add_left hw) hn.2.2
      refine wmax_of_good ⟨Hull.add hw (wmax_hull ha hw) (wmax_hull hb hw), ?_⟩
      intro γ hγ hγlt
      rcases shape γ with rfl | ⟨γ₁, γ₂, rfl⟩ | pγ
      · exact wmax_zero
      · rw [lt_add_add] at hγlt
        by_cases e : γ₁ = a
        · subst e
          rw [ite_eq_left rfl] at hγlt
          cases hγ with
          | mem hX _ _ => exact hX
          | add hw' _ hγ₂ =>
            have hγ₂W := wmax_bounded hw hγ₂ hb (le_of_lt hγlt)
              (lt_trans (wmax_wf hb) hw hn.1 (lt_add_right hw) hn.2.2)
            exact ih γ₂ ⟨hγ₂W, hγlt⟩ hγ₂W hw'
        · rw [ite_eq_right e] at hγlt
          exact wmax_bounded hw hγ ha
            (le_of_lt (by rw [lt_add_prin (wf_add hw).1]; exact hγlt)) ha_lt
      · exact wmax_bounded hw hγ ha ((le_iff _ _).mpr ((lt_prin_add_iff pγ a b).mp hγlt)) ha_lt
  exact key b (wmax_acc hb) hb hw

theorem wmax_inacc : ∀ (n : Nat) (c : Term), Wmax c → wf (inacc n c) = true →
    Wmax (inacc n c) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    intro c hc
    have key : ∀ c, Acc (Rel Wmax) c → Wmax c → wf (inacc n c) = true → Wmax (inacc n c) := by
      intro c hacc
      induction hacc with
      | intro c _ ihc =>
        intro hc hw
        have hn := nr_spec _ hw
        have hc_lt := lt_trans (wmax_wf hc) hw hn.1 (lt_inacc_self hw) hn.2.2
        refine wmax_of_good ⟨Hull.inacc hw (wmax_hull hc hw), ?_⟩
        intro β
        induction β using size_induction with
        | h β ihβ =>
          intro hβ hβlt
          have below : ∀ x, wf x = true → lt x β = true → lt x (inacc n c) = true :=
            fun x wx h => lt_trans wx hβ.wf_of hw h hβlt
          cases hβ with
          | zero => exact wmax_zero
          | mem hX _ _ => exact hX
          | @add b₁ b₂ hw' hb₁ hb₂ =>
            exact wmax_add hw'
              (ihβ b₁ (by size_omega) hb₁ (below b₁ (wf_add hw').2.1 (lt_add_left hw')))
              (ihβ b₂ (by size_omega) hb₂ (below b₂ (wf_add hw').2.2.1 (lt_add_right hw')))
          | @inacc m d hw' hd =>
            have hdW := ihβ d (by size_omega) hd (below d (wf_inacc hw').1 (lt_inacc_self hw'))
            rcases Nat.lt_trichotomy m n with hmn | rfl | hmn
            · exact ihn m hmn d hdW hw'
            · rw [lt_ii_eq] at hβlt; exact ihc d ⟨hdW, hβlt⟩ hdW hw'
            · rw [lt_ii_gt hmn] at hβlt
              exact wmax_bounded hw (Hull.inacc hw' hd) hc (le_of_lt hβlt) hc_lt
          | @psi σ b hw' hσ hσH hbH =>
            rcases (lt_pi_iff n c σ b).mp hβlt with ⟨_, h⟩ | ⟨_, h⟩
            · exact wmax_bounded hw (Hull.psi hw' hσ hσH hbH) hc ((le_iff _ _).mpr h) hc_lt
            · rw [not_lt_of_le ((le_iff _ _).mpr h)] at hσ; cases hσ
    exact key c (wmax_acc hc) hc

theorem wmax_psi : ∀ a : Term, Wmax a → ∀ κ : Term, Wmax κ → wf (psi κ a) = true →
    Wmax (psi κ a) := by
  have key : ∀ a, Acc (Rel Wmax) a → Wmax a → ∀ κ, Wmax κ → wf (psi κ a) = true →
      Wmax (psi κ a) := by
    intro a hacc
    induction hacc with
    | intro a _ MIH0 =>
      intro ha κ hκ hw
      have MIH : ∀ b, Wmax b → lt b a = true → ∀ σ, Wmax σ → wf (psi σ b) = true →
          Wmax (psi σ b) := fun b hb hba σ hσ hwσ => MIH0 b ⟨hb, hba⟩ hb σ hσ hwσ
      obtain ⟨n, e, rfl⟩ := isRT_inacc (wf_psi hw).1
      have hnα := nr_spec _ hw
      refine wmax_of_good
        ⟨Hull.psi hw (lt_psi_index' n e a) (wmax_hull hκ hw) (wmax_hull ha hw), ?_⟩
      intro β1
      induction β1 using size_induction with
      | h β1 LIH =>
        intro hβ hβlt
        have below : ∀ x, wf x = true → lt x β1 = true → lt x (psi (inacc n e) a) = true :=
          fun x wx h => lt_trans wx hβ.wf_of hw h hβlt
        cases hβ with
        | zero => exact wmax_zero
        | mem hX _ _ => exact hX
        | @add b₁ b₂ hw₁ hb₁ hb₂ =>
          exact wmax_add hw₁
            (LIH b₁ (by size_omega) hb₁ (below b₁ (wf_add hw₁).2.1 (lt_add_left hw₁)))
            (LIH b₂ (by size_omega) hb₂ (below b₂ (wf_add hw₁).2.2.1 (lt_add_right hw₁)))
        | @inacc m d hw₁ hd =>
          exact wmax_inacc m d (LIH d (by size_omega) hd
            (below d (wf_inacc hw₁).1 (lt_inacc_self hw₁))) hw₁
        | @psi π b hw₁ hα1π hπ hb =>
          rcases (lt_pp_iff π b (inacc n e) a).mp hβlt with (⟨_, h⟩ | ⟨rfl, hba⟩) | ⟨hκπ, h⟩
          · exact (lt_asymm h hα1π).elim
          · -- `b` is built, above `ψ_κ(a)`, from collapses with arguments below `a`
            have hbW := coeff_induction Wmax hw₁ hw (le_of_lt hβlt) (size (psi (inacc n e) b))
              (fun x hx hxα hs => LIH x hs hx hxα) wmax_zero (wmax_add · · ·)
              (fun hw hb => wmax_inacc _ _ hb hw)
              (fun hwx _ hdb _ _ _ hσ hd => MIH _ hd (lt_trans (wf_psi hwx).2.2.1
                (wf_psi hw₁).2.2.1 (wmax_wf ha) hdb hba) _ hσ hwx)
              b hb (by size_omega) (wf_psi hw₁).2.2.2
            exact MIH b hbW hba (inacc n e) hκ hw₁
          · rcases (lt_pi_iff n e π b).mp h with ⟨_, h'⟩ | ⟨_, h'⟩
            · exact wmax_bounded hw (Hull.psi hw₁ hα1π hπ hb) (wmax_inacc_arg hκ)
                ((le_iff _ _).mpr h') (lt_trans (wmax_wf (wmax_inacc_arg hκ)) hw hnα.1
                  (lt_psi_of_arg hw) hnα.2.2)
            · rw [not_lt_of_le ((le_iff _ _).mpr h')] at hκπ; cases hκπ
  intro a ha
  exact key a (wmax_acc ha) ha

/-! ### Well-foundedness -/

/-- Every well-formed term of Jäger's notation system belongs to the maximal distinguished
set. -/
theorem wmax_of_wf : ∀ t : Term, wf t = true → Wmax t := by
  intro t
  induction t with
  | zero => exact fun _ => wmax_zero
  | add a b iha ihb => exact fun h => wmax_add h (iha (wf_add h).2.1) (ihb (wf_add h).2.2.1)
  | inacc n c ihc => exact fun h => wmax_inacc n c (ihc (wf_inacc h).1) h
  | psi u b ihu ihb => exact fun h => wmax_psi b (ihb (wf_psi h).2.2.1) u (ihu (wf_psi h).2.1) h

/-- Every well-formed term is accessible for `Term.lt` restricted to well-formed terms. -/
theorem acc_lt_of_wf {t : Term} (h : wf t = true) :
    Acc (fun x y : Term => wf x = true ∧ lt x y = true) t := by
  have key : ∀ t, Acc (Rel Wmax) t → Acc (fun x y : Term => wf x = true ∧ lt x y = true) t := by
    intro t hacc
    induction hacc with
    | intro t _ ih => exact Acc.intro t (fun x hx => ih x ⟨wmax_of_wf x hx.1, hx.2⟩)
  exact key t (wmax_acc (wmax_of_wf t h))

/-- `Term.lt` is a well-founded relation on the well-formed terms of Jäger's notation system. -/
theorem lt_wellFounded :
    WellFounded (fun a b : {t : Term // wf t = true} => lt a.1 b.1 = true) := by
  have key : ∀ t, Acc (Rel Wmax) t → ∀ ht : wf t = true,
      Acc (fun a b : {t : Term // wf t = true} => lt a.1 b.1 = true) ⟨t, ht⟩ := by
    intro t hacc
    induction hacc with
    | intro t _ ih => exact fun _ => Acc.intro _ (fun y hyt => ih y.1 ⟨wmax_of_wf y.1 y.2, hyt⟩ y.2)
  exact ⟨fun a => key a.1 (wmax_acc (wmax_of_wf a.1 a.2)) a.2⟩

/-- `Term.lt` is a strict well-ordering of the well-formed terms: irreflexive, transitive,
trichotomous and well-founded. -/
theorem lt_isWellOrder :
    (∀ a : {t : Term // wf t = true}, lt a.1 a.1 = false) ∧
    (∀ a b c : {t : Term // wf t = true},
      lt a.1 b.1 = true → lt b.1 c.1 = true → lt a.1 c.1 = true) ∧
    (∀ a b : {t : Term // wf t = true}, lt a.1 b.1 = true ∨ a = b ∨ lt b.1 a.1 = true) ∧
    WellFounded (fun a b : {t : Term // wf t = true} => lt a.1 b.1 = true) :=
  ⟨fun a => lt_irrefl a.1, fun a b c h1 h2 => lt_trans a.2 b.2 c.2 h1 h2,
    fun a b => (lt_trichotomy a.2 b.2).elim Or.inl
      (fun h => h.elim (fun e => Or.inr (Or.inl (Subtype.ext e))) (fun h => Or.inr (Or.inr h))),
    lt_wellFounded⟩

end OCF.Jaeger.Term

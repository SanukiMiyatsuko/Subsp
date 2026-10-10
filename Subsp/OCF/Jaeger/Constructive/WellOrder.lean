import Subsp.OCF.Jaeger.Constructive.Distinguished

/-! The constructive well-ordering proof for Jäger's notation system.

`wmax_of_good` shows `Good α → α ∈ Wmax` (Arai's Lemma 3.26 specialised to Jäger's system, where
collapsing terms are never regular).  Closure of `Wmax` under `0`, `+`, `I_n` and `ψ` follows, so
every `wf` term lies in `Wmax`, and `Term.lt` is well-founded on `wf` terms.  The proof depends
only on `propext` and `Quot.sound`. -/

namespace OCF.Jaeger.Term

/-- Moving a term from `C^θ(Wmax)` to `C^ν(Wmax)` for `ν < ρ`, when its coefficients with
respect to `ρ` lie below `c` and `ψ_ρ(c) ≤ θ`. -/
theorem hull_transfer {θ ν ρ c : Term} (wψ : wf (psi ρ c) = true) (wθ : wf θ = true)
    (wν : wf ν = true) (hψθ : le (psi ρ c) θ = true) (hνρ : lt ν ρ = true) (S : Nat)
    (good : ∀ x, Hull θ Wmax x → lt x θ = true → size x < S → Wmax x) :
    ∀ x, Hull θ Wmax x → size x < S → allLt (H ρ x) c = true → Hull ν Wmax x := by
  have wψ' := wf_psi wψ
  have wρ := wψ'.2.1
  have hpred := predR_spec wψ
  intro x
  induction x using size_induction with
  | h x ih =>
    intro hx hs hH
    cases hxθ : lt x θ with
    | true => exact wmax_hull (good x hx hxθ hs) wν
    | false =>
      cases hx with
      | zero => exact Hull.zero
      | mem _ _ hlt =>
        rw [hlt] at hxθ
        cases hxθ
      | @add a b hw ha hb =>
        rw [H_add] at hH
        exact Hull.add hw (ih a (by size_omega) ha (by size_omega) (allLt_append hH).1)
          (ih b (by size_omega) hb (by size_omega) (allLt_append hH).2)
      | @inacc n b hw hb =>
        rw [H_inacc] at hH
        exact Hull.inacc hw (ih b (by size_omega) hb (by size_omega) (allLt_append hH).2)
      | @psi σ d hw _ hσ hd =>
        have wx' := wf_psi hw
        have hH0 := hH
        rw [H_psi] at hH
        have hnle : ¬ (le (psi σ d) (predR ρ) = true) := by
          intro hle
          have h1 : lt (psi σ d) θ = true :=
            lt_of_lt_of_le hw wψ wθ (lt_of_le_of_lt hw hpred.2 wψ hle hpred.1) hψθ
          rw [h1] at hxθ
          cases hxθ
        rw [ite_eq_right hnle] at hH
        by_cases hσρ : lt σ ρ = true
        · exfalso
          have h1 := lt_psi_of_H wψ (psi σ d) hw hH0
            (lt_trans hw wx'.2.1 wρ (lt_psi_index wx'.1 d) hσρ)
          rw [lt_of_lt_of_le hw wψ wθ h1 hψθ] at hxθ
          cases hxθ
        · rw [ite_eq_right hσρ] at hH
          have hc := allLt_cons hH
          have hh := allLt_append hc.2
          have hρσ : le ρ σ = true := le_of_not_lt wρ wx'.2.1 (Bool.eq_false_iff.mpr hσρ)
          exact Hull.psi hw (lt_of_lt_of_le wν wρ wx'.2.1 hνρ hρσ)
            (ih σ (by size_omega) hσ (by size_omega) hh.2)
            (ih d (by size_omega) hd (by size_omega) hh.1)

/-- Case 2 of the proof of (18): a collapse with index at most `β` lying below `γ`. -/
theorem case_two {β γ π a : Term} (wβ : wf β = true) (hγH : Hull β Wmax γ)
    (MIH : ∀ ζ, Hull β Wmax ζ → lt ζ γ = true → Wmax ζ) (hπβ : le π β = true)
    (hγπ : lt γ π = true) (hα : Hull γ Wmax (psi π a)) (hαγ : lt (psi π a) γ = true) :
    Wmax (psi π a) := by
  have wγ := hγH.wf_of
  have wα := hα.wf_of
  have wπ := (wf_psi wα).2.1
  have hnγ := nr_spec γ wγ
  cases hγH with
  | zero =>
    rw [lt_zero_right] at hαγ
    cases hαγ
  | mem hX _ _ => exact (wmax_good hX).2 _ hα hαγ
  | @add g₁ g₂ hw hg₁ _ =>
    have wg := wf_add hw
    have hg₁W := MIH g₁ hg₁ (lt_add_left hw)
    have hle : le (psi π a) g₁ = true := (le_iff _ _).mpr ((lt_prin_add_iff rfl g₁ g₂).mp hαγ)
    exact wmax_bounded wγ hα hg₁W hle (lt_trans wg.2.1 hw hnγ.1 (lt_add_left hw) hnγ.2.2)
  | @inacc m e hw he =>
    have heW := MIH e he (lt_inacc_self hw)
    rcases (lt_pi_iff m e π a).mp hαγ with ⟨_, h⟩ | ⟨_, h⟩
    · exact wmax_bounded wγ hα heW ((le_iff _ _).mpr h)
        (lt_trans (wf_inacc hw).1 hw hnγ.1 (lt_inacc_self hw) hnγ.2.2)
    · exfalso
      rw [not_lt_of_le ((le_iff _ _).mpr h)] at hγπ
      cases hγπ
  | @psi κ b hw hβκ _ _ =>
    exfalso
    have hπκ : lt π κ = true := lt_of_le_of_lt wπ wβ (wf_psi hw).2.1 hπβ hβκ
    rcases (lt_pp_iff π a κ b).mp hαγ with (⟨_, h⟩ | ⟨e, _⟩) | ⟨h, _⟩
    · exact lt_asymm h hγπ
    · rw [e, lt_irrefl] at hπκ
      cases hπκ
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
    | mem _ _ hlt =>
      rw [lt_irrefl] at hlt
      cases hlt
    | add hw hg₁ hg₂ =>
      have h1 := hγ.2 _ hg₁ (lt_add_left hw)
      have h2 := hγ.2 _ hg₂ (lt_add_right hw)
      exact hG.2 _ (Hull.add hw (wmax_hull h1 wη) (wmax_hull h2 wη)) hγη
  | inacc m e =>
    cases hγ.1 with
    | mem _ _ hlt =>
      rw [lt_irrefl] at hlt
      cases hlt
    | inacc hw he =>
      have h1 := hγ.2 _ he (lt_inacc_self hw)
      exact hG.2 _ (Hull.inacc hw (wmax_hull h1 wη)) hγη
  | psi ρ c =>
    cases hγ.1 with
    | mem _ _ hlt =>
      rw [lt_irrefl] at hlt
      cases hlt
    | psi hw _ hρ hc =>
      have hw' := wf_psi hw
      obtain ⟨k, e, rfl⟩ := isRT_inacc hw'.1
      have heγ := lt_psi_of_arg hw
      have hρ' : Wmax (inacc k e) ∨ Wmax e := by
        cases hρ with
        | mem hX _ _ => exact Or.inl hX
        | inacc _ he => exact Or.inr (hγ.2 e he heγ)
      rcases lt_trichotomy hw'.2.1 wη with hρη | eρη | hηρ
      · have hρW : Wmax (inacc k e) := by
          rcases hρ' with h | h
          · exact h
          · exact hG.2 _ (Hull.inacc hw'.2.1 (wmax_hull h wη)) hρη
        exact Obs _ hρW (le_of_lt (lt_psi_index hw'.1 c))
      · subst eρη
        exact h15 c hγ
      · have hρη' : Hull η Wmax (inacc k e) := by
          rcases hρ' with h | h
          · exact wmax_hull h wη
          · exact Hull.inacc hw'.2.1 (wmax_hull h wη)
        have hcη := hull_transfer hw wγ wη (le_refl _) hηρ (size c + 1)
          (fun x hx hxγ _ => hγ.2 x hx hxγ) c hc (by omega) hw'.2.2.2
        exact hG.2 _ (Hull.psi hw hηρ hρη' hcη) hγη

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
      have hγη : lt γ η = true := lt_of_lt_of_le wγ hnβ.1 wη hγ hle
      have MIH : ∀ ζ, Hull β Wmax ζ → lt ζ γ = true → Wmax ζ := fun ζ hζ hζγ =>
        MIH0 ζ ⟨hζ, hζγ⟩ hζ (lt_trans hζ.wf_of wγ hnβ.1 hζγ hγ)
      have hWγ : WPart (Hull β Wmax) γ := ⟨hγH, Acc.intro γ hacc'⟩
      have Obs : ∀ δ, Wmax δ → le γ δ = true → Wmax γ := by
        intro δ hδ hγδ
        have wδ := wmax_wf hδ
        cases hδβ : lt δ β with
        | true =>
          exact wmax_bounded wδ (Hull.lower HW wδ wβ (le_of_lt hδβ) hγH) hδ hγδ
            (nr_spec δ wδ).2.2
        | false =>
          exact ((wmax_dist.2 β wβ ⟨δ, hδ, le_of_not_lt wβ wδ hδβ⟩ γ).mp ⟨hWγ, hγ⟩).1
      have hγγ : Hull γ Wmax γ := Hull.sub_of_lt_nr HW wβ wγ hγ hγH
      have hnγ := nr_spec γ wγ
      have G2 : ∀ α, Hull γ Wmax α → lt α γ = true → Wmax α := by
        intro α
        induction α using size_induction with
        | h α ihα =>
          intro hα hαγ
          cases hβnγ : lt β (nr γ) with
          | true => exact MIH α (Hull.sub_of_lt_nr HW wγ wβ hβnγ hα) hαγ
          | false =>
            cases hα with
            | zero => exact MIH zero Hull.zero hαγ
            | mem hX _ _ => exact hX
            | @add a b hw ha hb =>
              have wa' := wf_add hw
              have ha' := ihα a (by size_omega) ha (lt_trans wa'.2.1 hw wγ (lt_add_left hw) hαγ)
              have hb' := ihα b (by size_omega) hb
                (lt_trans wa'.2.2.1 hw wγ (lt_add_right hw) hαγ)
              exact MIH _ (Hull.add hw (wmax_hull ha' wβ) (wmax_hull hb' wβ)) hαγ
            | @inacc n d hw hd =>
              have hd' := ihα d (by size_omega) hd
                (lt_trans (wf_inacc hw).1 hw wγ (lt_inacc_self hw) hαγ)
              exact MIH _ (Hull.inacc hw (wmax_hull hd' wβ)) hαγ
            | @psi π a hw hγπ hπ ha =>
              have hw' := wf_psi hw
              cases hβπ : lt β π with
              | true =>
                obtain ⟨k, e, rfl⟩ := isRT_inacc hw'.1
                have we := (wf_inacc hw'.2.1).1
                have heα : lt e (psi (inacc k e) a) = true := lt_psi_of_arg hw
                have ha'' := hull_transfer hw wγ wβ (le_of_lt hαγ) hβπ _
                  (fun x hx hxγ hs => ihα x hs hx hxγ) a ha (by size_omega) hw'.2.2.2
                have hπ'' : Hull β Wmax (inacc k e) := by
                  cases hπ with
                  | mem hX _ _ => exact wmax_hull hX wβ
                  | inacc hwπ he =>
                    exact Hull.inacc hwπ
                      (wmax_hull (ihα e (by size_omega) he (lt_trans we hw wγ heα hαγ)) wβ)
                exact MIH _ (Hull.psi hw hβπ hπ'' ha'') hαγ
              | false =>
                exact case_two wβ hγH MIH (le_of_not_lt hw'.2.1 wβ hβπ) hγπ
                  (Hull.psi hw hγπ hπ ha) hαγ
      exact step_three hG h15 ⟨hγγ, G2⟩ hγη Obs
  exact key γ hW.2 hW.1 hγ

/-- Every good term belongs to the maximal distinguished set. -/
theorem wmax_of_good {η : Term} (hG : Good η) : Wmax η := by
  have h15 : ∀ b, Good (psi η b) → Wmax (psi η b) := by
    intro b hgb
    refine wmax_of_good_hyp hgb (hyp_of_good hgb ?_)
    intro b' hgb'
    exfalso
    have h := (wf_psi hgb'.1.wf_of).1
    simp [isRT] at h
  exact wmax_of_good_hyp hG (hyp_of_good hG h15)

/-! ### Closure properties of `Wmax` -/

theorem wmax_zero : Wmax zero := by
  refine wmax_of_good ⟨Hull.zero, ?_⟩
  intro β _ h
  rw [lt_zero_right] at h
  cases h

theorem wmax_inacc_arg {n : Nat} {e : Term} (h : Wmax (inacc n e)) : Wmax e := by
  have hg := wmax_good h
  cases hg.1 with
  | mem _ _ hlt =>
    rw [lt_irrefl] at hlt
    cases hlt
  | inacc hw he => exact hg.2 e he (lt_inacc_self hw)

theorem wmax_add {a b : Term} (hw : wf (add a b) = true) (ha : Wmax a) (hb : Wmax b) :
    Wmax (add a b) := by
  have key : ∀ b, Acc (Rel Wmax) b → Wmax b → wf (add a b) = true → Wmax (add a b) := by
    intro b hacc
    induction hacc with
    | intro b _ ih =>
      intro hb hw
      have wab := hw
      have hn := nr_spec _ wab
      have wa := wmax_wf ha
      have ha_lt := lt_trans wa wab hn.1 (lt_add_left wab) hn.2.2
      refine wmax_of_good ⟨Hull.add hw (wmax_hull ha wab) (wmax_hull hb wab), ?_⟩
      intro γ hγ hγlt
      have wγ := hγ.wf_of
      rcases shape γ with rfl | ⟨γ₁, γ₂, rfl⟩ | pγ
      · exact wmax_zero
      · rw [lt_add_add] at hγlt
        by_cases e : γ₁ = a
        · subst e
          rw [ite_eq_left rfl] at hγlt
          cases hγ with
          | mem hX _ _ => exact hX
          | add hw' _ hγ₂ =>
            have hγ₂W := wmax_bounded wab hγ₂ hb (le_of_lt hγlt)
              (lt_trans (wmax_wf hb) wab hn.1 (lt_add_right wab) hn.2.2)
            exact ih γ₂ ⟨hγ₂W, hγlt⟩ hγ₂W hw'
        · rw [ite_eq_right e] at hγlt
          have h' : lt (add γ₁ γ₂) a = true := by
            rw [lt_add_prin (wf_add wab).1]
            exact hγlt
          exact wmax_bounded wab hγ (ha) (le_of_lt h') ha_lt
      · have h' := (lt_prin_add_iff pγ a b).mp hγlt
        exact wmax_bounded wab hγ ha ((le_iff _ _).mpr h') ha_lt
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
        have wc := wmax_wf hc
        have hc_lt := lt_trans wc hw hn.1 (lt_inacc_self hw) hn.2.2
        refine wmax_of_good ⟨Hull.inacc hw (wmax_hull hc hw), ?_⟩
        intro β
        induction β using size_induction with
        | h β ihβ =>
          intro hβ hβlt
          cases hβ with
          | zero => exact wmax_zero
          | mem hX _ _ => exact hX
          | @add b₁ b₂ hw' hb₁ hb₂ =>
            have wb := wf_add hw'
            exact wmax_add hw'
              (ihβ b₁ (by size_omega) hb₁ (lt_trans wb.2.1 hw' hw (lt_add_left hw') hβlt))
              (ihβ b₂ (by size_omega) hb₂ (lt_trans wb.2.2.1 hw' hw (lt_add_right hw') hβlt))
          | @inacc m d hw' hd =>
            have hdW := ihβ d (by size_omega) hd
              (lt_trans (wf_inacc hw').1 hw' hw (lt_inacc_self hw') hβlt)
            rcases Nat.lt_trichotomy m n with hmn | hmn | hmn
            · exact ihn m hmn d hdW hw'
            · subst hmn
              have hdc : lt d c = true := by
                rw [lt_ii_eq] at hβlt
                exact hβlt
              exact ihc d ⟨hdW, hdc⟩ hdW hw'
            · have h' : lt (inacc m d) c = true := by
                rw [lt_ii_gt hmn] at hβlt
                exact hβlt
              exact wmax_bounded hw (Hull.inacc hw' hd) hc (le_of_lt h') hc_lt
          | @psi σ b hw' hσ hσH hbH =>
            rcases (lt_pi_iff n c σ b).mp hβlt with ⟨_, h⟩ | ⟨_, h⟩
            · exact wmax_bounded hw (Hull.psi hw' hσ hσH hbH) hc
                ((le_iff _ _).mpr h) hc_lt
            · exfalso
              rw [not_lt_of_le ((le_iff _ _).mpr h)] at hσ
              cases hσ
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
      have hw' := wf_psi hw
      obtain ⟨n, e, rfl⟩ := isRT_inacc hw'.1
      have wa := wmax_wf ha
      have hnα := nr_spec _ hw
      have heW : Wmax e := wmax_inacc_arg hκ
      have heα : lt e (psi (inacc n e) a) = true := lt_psi_of_arg hw
      refine wmax_of_good
        ⟨Hull.psi hw (lt_psi_index' n e a) (wmax_hull hκ hw) (wmax_hull ha hw), ?_⟩
      intro β1
      induction β1 using size_induction with
      | h β1 LIH =>
        intro hβ hβlt
        cases hβ with
        | zero => exact wmax_zero
        | mem hX _ _ => exact hX
        | @add b₁ b₂ hw₁ hb₁ hb₂ =>
          have wb := wf_add hw₁
          exact wmax_add hw₁
            (LIH b₁ (by size_omega) hb₁ (lt_trans wb.2.1 hw₁ hw (lt_add_left hw₁) hβlt))
            (LIH b₂ (by size_omega) hb₂ (lt_trans wb.2.2.1 hw₁ hw (lt_add_right hw₁) hβlt))
        | @inacc m d hw₁ hd =>
          exact wmax_inacc m d (LIH d (by size_omega) hd
            (lt_trans (wf_inacc hw₁).1 hw₁ hw (lt_inacc_self hw₁) hβlt)) hw₁
        | @psi π b hw₁ hα1π hπ hb =>
          have hw₁' := wf_psi hw₁
          rcases (lt_pp_iff π b (inacc n e) a).mp hβlt with (⟨_, h⟩ | ⟨eπ, hba⟩) | ⟨hκπ, h⟩
          · exfalso
            exact lt_asymm h hα1π
          · subst eπ
            have hpred := predR_spec hw₁
            have claim : ∀ x, Hull (psi (inacc n e) a) Wmax x →
                size x < size (psi (inacc n e) b) → allLt (H (inacc n e) x) b = true →
                  Wmax x := by
              intro x
              induction x using size_induction with
              | h x ihx =>
                intro hx hs hH
                cases hxα : lt x (psi (inacc n e) a) with
                | true => exact LIH x hs hx hxα
                | false =>
                  cases hx with
                  | zero => exact wmax_zero
                  | mem hX _ _ => exact hX
                  | @add x₁ x₂ hwx hx₁ hx₂ =>
                    rw [H_add] at hH
                    exact wmax_add hwx
                      (ihx x₁ (by size_omega) hx₁ (by size_omega) (allLt_append hH).1)
                      (ihx x₂ (by size_omega) hx₂ (by size_omega) (allLt_append hH).2)
                  | @inacc m d hwx hd =>
                    rw [H_inacc] at hH
                    exact wmax_inacc m d
                      (ihx d (by size_omega) hd (by size_omega) (allLt_append hH).2) hwx
                  | @psi σ c hwx _ hσ hc =>
                    have hwx' := wf_psi hwx
                    have hH0 := hH
                    rw [H_psi] at hH
                    have hnle : ¬ (le (psi σ c) (predR (inacc n e)) = true) := by
                      intro hle
                      have h1 := lt_of_le_of_lt hwx hpred.2 hw₁ hle hpred.1
                      have h2 := lt_trans hwx hw₁ hw h1 hβlt
                      rw [h2] at hxα
                      cases hxα
                    rw [ite_eq_right hnle] at hH
                    by_cases hσκ : lt σ (inacc n e) = true
                    · exfalso
                      have h1 := lt_psi_of_H hw₁ (psi σ c) hwx hH0
                        (lt_trans hwx hwx'.2.1 hw'.2.1 (lt_psi_index hwx'.1 c) hσκ)
                      have h2 := lt_trans hwx hw₁ hw h1 hβlt
                      rw [h2] at hxα
                      cases hxα
                    · rw [ite_eq_right hσκ] at hH
                      have hcl := allLt_cons hH
                      have hh := allLt_append hcl.2
                      have hcW := ihx c (by size_omega) hc (by size_omega) hh.1
                      have hσW := ihx σ (by size_omega) hσ (by size_omega) hh.2
                      exact MIH c hcW (lt_trans hwx'.2.2.1 hw₁'.2.2.1 wa hcl.1 hba) σ hσW hwx
            have hbW := claim b hb (by size_omega) hw₁'.2.2.2
            exact MIH b hbW hba (inacc n e) hκ hw₁
          · rcases (lt_pi_iff n e π b).mp h with ⟨_, h'⟩ | ⟨_, h'⟩
            · exact wmax_bounded hw (Hull.psi hw₁ hα1π hπ hb) heW ((le_iff _ _).mpr h')
                (lt_trans (wmax_wf heW) hw hnα.1 heα hnα.2.2)
            · exfalso
              rw [not_lt_of_le ((le_iff _ _).mpr h')] at hκπ
              cases hκπ
  intro a ha
  exact key a (wmax_acc ha) ha

/-! ### Well-foundedness -/

/-- Every well-formed term of Jäger's notation system belongs to the maximal distinguished
set. -/
theorem wmax_of_wf : ∀ t : Term, wf t = true → Wmax t := by
  intro t
  induction t with
  | zero =>
    intro _
    exact wmax_zero
  | add a b iha ihb =>
    intro h
    have h' := wf_add h
    exact wmax_add h (iha h'.2.1) (ihb h'.2.2.1)
  | inacc n c ihc =>
    intro h
    exact wmax_inacc n c (ihc (wf_inacc h).1) h
  | psi u b ihu ihb =>
    intro h
    have h' := wf_psi h
    exact wmax_psi b (ihb h'.2.2.1) u (ihu h'.2.1) h

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
    | intro t _ ih =>
      intro ht
      exact Acc.intro _ (fun y hyt => ih y.1 ⟨wmax_of_wf y.1 y.2, hyt⟩ y.2)
  exact ⟨fun a => key a.1 (wmax_acc (wmax_of_wf a.1 a.2)) a.2⟩

/-- `Term.lt` is a strict well-ordering of the well-formed terms: irreflexive, transitive,
trichotomous and well-founded. -/
theorem lt_isWellOrder :
    (∀ a : {t : Term // wf t = true}, lt a.1 a.1 = false) ∧
    (∀ a b c : {t : Term // wf t = true},
      lt a.1 b.1 = true → lt b.1 c.1 = true → lt a.1 c.1 = true) ∧
    (∀ a b : {t : Term // wf t = true}, lt a.1 b.1 = true ∨ a = b ∨ lt b.1 a.1 = true) ∧
    WellFounded (fun a b : {t : Term // wf t = true} => lt a.1 b.1 = true) := by
  refine ⟨fun a => lt_irrefl a.1, fun a b c h1 h2 => lt_trans a.2 b.2 c.2 h1 h2, ?_,
    lt_wellFounded⟩
  intro a b
  rcases lt_trichotomy a.2 b.2 with h | e | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Subtype.ext e))
  · exact Or.inr (Or.inr h)

end OCF.Jaeger.Term

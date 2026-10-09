import Subsp.multi.old.supp
import Subsp.multi.Uncollapse

/-! Inverses of the Buchholz-side operations used by the translation of `old`: `UE q` undoes
the collapse at index `q`, `UC K` undoes the multiplication by `Ω_K`, and `lpInv` undoes the
removal of a leading `1`. All of them keep normal forms and do not increase the exponent
depth `MT.deg`. -/

namespace OB

open T

/-- Inverse of `ec q` on terms of index at most `q`. -/
def UE (q : Nat) : T → T
  | Z => Z
  | P p h t =>
    if p = q then
      if (part q h).1 = Z then P p h t
      else if (part q h).2 = Z then T.add h t
      else T.add (part q h).1 (P p h t)
    else P p h t

/-- Inverse of `cardArg K` on a single argument below `ψ_K(1)`. -/
def uncardSmall (K : Nat) : T → Nat × T
  | Z => (0, Z)
  | P q h t =>
    if q = K then (K, t)
    else if q = 0 then (0, UE 0 (P q h t))
    else if h = Z then (q, UE q t)
    else (q, UE q (P q h t))

/-- Inverse of `cardArg K` on a single argument. -/
def uncardArg (K : Nat) (g : T) : Nat × T :=
  if P K (P 0 Z Z) Z ≤ g then (K, g) else uncardSmall K g


/-- Inverse of `ct K` on terms of index at least `K`. -/
def UC (K : Nat) : T → T
  | Z => Z
  | P q g r => if K < q then P q g (UC K r) else P (uncardArg K g).1 (uncardArg K g).2 (UC K r)

/-- Inverse of `oneDel`, avoiding a leading unit. -/
def lpInv : T → T
  | Z => P 0 Z Z
  | P 0 Z r => P 0 Z (P 0 Z r)
  | e => e

theorem oneDel_lpInv (e : T) : oneDel (lpInv e) = e := by
  match e with
  | Z | P 0 Z _ | P 0 (P _ _ _) _ | P (_ + 1) _ _ => rfl

theorem lpInv_ne_Z (e : T) : lpInv e ≠ Z := by
  match e with
  | Z | P 0 Z _ | P 0 (P _ _ _) _ | P (_ + 1) _ _ => intro h; cases h

theorem part_props (n : Nat) : ∀ t : T,
    MT.deg (part n t).1 ≤ MT.deg t ∧ MT.deg (part n t).2 ≤ MT.deg t
  | Z => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | P p a r => by
    obtain ⟨ih1, ih2⟩ := part_props n r
    by_cases hpn : p ≤ n
    · rw [part_P_le a r hpn]
      exact ⟨Nat.le_trans ih1 (Nat.le_max_right _ _),
        Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans ih2 (Nat.le_max_right _ _)⟩⟩
    · rw [part_P_gt a r hpn]
      exact ⟨Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans ih1 (Nat.le_max_right _ _)⟩,
        Nat.le_trans ih2 (Nat.le_max_right _ _)⟩

theorem add_NF1_split (n : Nat) : ∀ a b : T, T.isNF1 a → T.isNF1 b →
    (∀ p c, IsSummand p c a → n < p) → T.index_Prop1 n b → T.isNF1 (T.add a b)
  | Z, b, _, hb, _, _ => hb
  | P p x r, b, ha, hb, hsum, hib => by
    obtain ⟨hx, hr, hg, hh⟩ := T.isNF1_P_inv p x r ha
    rw [T.P_add_eq]
    refine T.isNF1.p p x _ hx (add_NF1_split n r b hr hb (fun p' c hs => hsum p' c (Or.inr hs)) hib)
      hg ?_
    cases r with
    | Z =>
      show T.head b ≤ P p x Z
      cases hib with
      | z => exact T.Z_le _
      | p q d e hq _ =>
        exact Or.inl (T.Lt.p_head _ _ _ _ _ _
          (Nat.lt_of_le_of_lt hq (hsum p x (Or.inl ⟨rfl, rfl⟩))))
    | P q d e => rw [T.head_add_ne_Z]; exact hh

theorem G1_below_head (q : Nat) (h : T) (hh : ∀ x ∈ T.G1 q h, x < h) : ∀ t : T, T.isNF1 t →
    T.head t ≤ P q h Z → T.index_Prop1 q t → ∀ x ∈ T.G1 q t, x ≤ h
  | Z, _, _, _, x, hx => by cases hx
  | P p g r, ht, hth, hti, x, hx => by
    obtain ⟨hg, hr, hgg, hrh⟩ := T.isNF1_P_inv p g r ht
    have hp : p ≤ q := by cases hti with | p _ _ _ h1 _ => exact h1
    have hri : T.index_Prop1 q r := by cases hti with | p _ _ _ _ h1 => exact h1
    have hrh2 : T.head r ≤ P q h Z := partial_order.trans _ _ _ hrh hth
    rcases Nat.eq_or_lt_of_le hp with rfl | hpq
    · have hgh : g ≤ h := by
        rcases hth with hlt | heq
        · cases hlt with
          | p_head _ _ _ _ _ _ h1 => exact absurd h1 (Nat.lt_irrefl _)
          | p_mid _ _ _ _ _ h1 => exact Or.inl h1
          | p_tail _ _ _ _ h1 => cases h1
        · injection heq with _ h2 _; exact Or.inr h2
      rcases (MT.G1_P_mem (Nat.le_refl p)).1 hx with rfl | hx | hx
      · exact hgh
      · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (hgg x hx) hgh)
      · exact G1_below_head p h hh r hr hrh2 hri x hx
    · rw [T.G1, ite_eq_right (Nat.not_le_of_lt hpq)] at hx
      exact G1_below_head q h hh r hr hrh2 hri x hx

theorem index_of_head_le {q p : Nat} {g r h : T} (ht : T.isNF1 (P p g r))
    (hth : T.head (P p g r) ≤ P q h Z) : T.index_Prop1 q (P p g r) :=
  isNF1_index q p g r ht (head_le_index p q g h hth)

theorem index_of_head_le' {q : Nat} {t h : T} (ht : T.isNF1 t) (hth : T.head t ≤ P q h Z) :
    T.index_Prop1 q t := by
  cases t with
  | Z => exact T.index_Prop1.z
  | P p g r => exact index_of_head_le ht hth

/-! ### Uncollapse -/

theorem UE_props (q : Nat) (e : T) (he : T.isNF1 e) (hi : T.index_Prop1 q e) :
    ec q (UE q e) = e ∧ T.isNF1 (UE q e) ∧ (∀ x ∈ T.G1 q (UE q e), x < UE q e) ∧
      MT.deg (UE q e) ≤ MT.deg e := by
  cases e with
  | Z => exact ⟨rfl, T.isNF1.z, fun x hx => (by cases hx), Nat.le_refl _⟩
  | P p h t =>
    obtain ⟨hh, ht, hgh, hth⟩ := T.isNF1_P_inv p h t he
    have hp : p ≤ q := by cases hi with | p _ _ _ h1 _ => exact h1
    have hti : T.index_Prop1 q t := by cases hi with | p _ _ _ _ h1 => exact h1
    have htlow : (part q t).1 = Z := by rw [part_of_index q t hti]
    by_cases hpq : p = q
    · subst hpq
      have htb := G1_below_head p h hgh t ht hth hti
      have hpe := part_add p h hh
      by_cases hH : (part p h).1 = Z
      · rw [UE, ite_eq_left rfl, ite_eq_left hH]
        have hhi : T.index_Prop1 p h := by
          have := part_second_index p h
          rwa [part_snd_of_fst_Z p h hH] at this
        have hhlt : h < P p h t := MT.lt_wrap p h t hhi hgh
        refine ⟨ec_of_index p _ hi, he, fun x hx => ?_, Nat.le_refl _⟩
        rcases (MT.G1_P_mem (Nat.le_refl p)).1 hx with rfl | hx | hx
        · exact hhlt
        · exact lt_trans_thm _ _ _ (hgh x hx) hhlt
        · exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) hhlt
      · have hd := part_props p h
        by_cases hL : (part p h).2 = Z
        · rw [UE, ite_eq_left rfl, ite_eq_right hH, ite_eq_left hL]
          have hh1 : (part p h).1 = h := by rw [hL, T.add_Z] at hpe; exact hpe
          have hhZ : h ≠ Z := by rw [← hh1]; exact hH
          refine ⟨?_, add_NF1_split p h t hh ht (fun p' c hs =>
            part_fst_summand_gt p h p' c (by rw [hh1]; exact hs)) hti, fun x hx => ?_, ?_⟩
          · rw [ec, part_add_split p h t (Prod.ext hh1 hL) htlow, ite_eq_right hhZ]
            show MT.stand (P p h t) = P p h t
            rw [MT.stand, MT.stand_of_NF1 ht, ite_eq_left hth]
          · rw [MT.G1_add, List.mem_append] at hx
            rcases hx with hx | hx
            · exact lt_of_lt_of_le_thm T _ _ _ (hgh x hx) (MT.add_self_le h t)
            · have htZ : t ≠ Z := by intro h1; rw [h1] at hx; cases hx
              exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) (add_lt_add_of_ne_Z h t htZ)
          · rw [MT.deg_add]
            exact Nat.max_le.2 ⟨Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _),
              Nat.le_max_right _ _⟩
        · rw [UE, ite_eq_left rfl, ite_eq_right hH, ite_eq_right hL]
          have hhlt : h < T.add (part p h).1 (P p h t) := by
            have := MT.add_left_lt (part p h).1 (part_snd_lt_wrap p h t hh hgh)
            rwa [hpe] at this
          refine ⟨?_, add_NF1_split p _ _ (part_NF p h hh).1 he (part_fst_summand_gt p h) hi,
            fun x hx => ?_, ?_⟩
          · have hPlow : (part p (P p h t)).1 = Z := by
              rw [part_P_le h t (Nat.le_refl p)]; exact htlow
            rw [ec, part_add_split p _ _ (part_first_fixed p h) hPlow, ite_eq_right hH]
            show MT.stand (P p (part p h).1 (P p h t)) = P p h t
            rw [MT.stand, MT.stand_of_NF1 he]
            have hlt : (part p h).1 < h := by
              have hlt := add_lt_add_of_ne_Z (part p h).1 (part p h).2 hL
              rwa [hpe] at hlt
            have hnot : ¬ T.head (P p h t) ≤ P p (part p h).1 Z := fun hle =>
              lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ (T.Lt.p_mid _ _ _ _ _ hlt) hle)
            rw [ite_eq_right hnot]
          · rw [MT.G1_add, List.mem_append] at hx
            rcases hx with hx | hx
            · exact lt_trans_thm _ _ _ (hgh x (G1_part_fst_subset p p h hh x hx)) hhlt
            · rcases (MT.G1_P_mem (Nat.le_refl p)).1 hx with rfl | hx | hx
              · exact hhlt
              · exact lt_trans_thm _ _ _ (hgh x hx) hhlt
              · exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) hhlt
          · rw [MT.deg_add]
            exact Nat.max_le.2 ⟨Nat.le_trans (Nat.le_trans hd.1 (Nat.le_succ _))
              (Nat.le_max_left _ _), Nat.le_refl _⟩
    · rw [UE, ite_eq_right hpq]
      refine ⟨ec_of_index q _ hi, he, fun x hx => ?_, Nat.le_refl _⟩
      have htp : T.index_Prop1 p t := index_of_head_le' ht hth
      rw [T.G1, ite_eq_right (fun h => hpq (Nat.le_antisymm hp h))] at hx
      rw [index_Prop1_G1_empty p t htp q (Nat.lt_of_le_of_ne hp hpq)] at hx
      cases hx

/-! ### Uncarding arguments -/

theorem small_head_shape (K : Nat) (q : Nat) (h t : T) (hlt : P q h t < P K (P 0 Z Z) Z) :
    q < K ∨ (q = K ∧ h = Z) := by
  cases hlt with
  | p_head _ _ _ _ _ _ hq => exact Or.inl hq
  | p_mid _ _ _ _ _ hh => exact Or.inr ⟨rfl, MT.lt_one_eq_Z hh⟩
  | p_tail _ _ _ _ ht => cases ht

theorem uncardArg_big (K : Nat) (g : T) (h : P K (P 0 Z Z) Z ≤ g) : uncardArg K g = (K, g) := by
  rw [uncardArg, ite_eq_left h]

theorem uncardArg_small (K : Nat) (g : T) (h : ¬ P K (P 0 Z Z) Z ≤ g) :
    uncardArg K g = uncardSmall K g := by
  rw [uncardArg, ite_eq_right h]

theorem uncard_props (K : Nat) (hK : 0 < K) (g : T) (hg : T.isNF1 g)
    (hgg : ∀ x ∈ T.G1 K g, x < g) :
    cardArg K (uncardArg K g).1 (uncardArg K g).2 = g ∧ (uncardArg K g).1 ≤ K ∧
      T.isNF1 (uncardArg K g).2 ∧
      (∀ x ∈ T.G1 (uncardArg K g).1 (uncardArg K g).2, x < (uncardArg K g).2) ∧
      MT.deg (uncardArg K g).2 ≤ MT.deg g := by
  by_cases hle : P K (P 0 Z Z) Z ≤ g
  · rw [uncardArg_big K g hle]
    refine ⟨?_, Nat.le_refl _, hg, hgg, Nat.le_refl _⟩
    apply cardArg_eq_self K K g (Nat.lt_irrefl K)
    intro ⟨_, hlt⟩
    rcases hle with hle | hle
    · exact lt_asymm_thm hlt hle
    · rw [hle] at hlt; exact lt_irrefl_thm _ hlt
  · rw [uncardArg_small K g hle]
    have hlt := MT.lt_of_not_le hle
    cases g with
    | Z =>
      refine ⟨?_, Nat.zero_le _, T.isNF1.z, fun x hx => (by cases hx), Nat.le_refl _⟩
      show cardArg K 0 Z = Z
      rw [cardArg_lt_case K 0 Z hK, ite_eq_left rfl]; rfl
    | P q h t =>
      obtain ⟨hh, ht, _, hth⟩ := T.isNF1_P_inv q h t hg
      rcases small_head_shape K q h t hlt with hqK | ⟨hqK, hh0⟩
      · have hgi : T.index_Prop1 q (P q h t) := isNF1_index q q h t hg (Nat.le_refl q)
        have hti : T.index_Prop1 q t := by cases hgi with | p _ _ _ _ h1 => exact h1
        rw [uncardSmall, ite_eq_right (Nat.ne_of_lt hqK)]
        by_cases hq0 : q = 0
        · subst hq0
          obtain ⟨h1, h2, h3, h4⟩ := UE_props 0 _ hg hgi
          rw [ite_eq_left rfl]
          refine ⟨?_, Nat.zero_le _, h2, h3, h4⟩
          show cardArg K 0 (UE 0 (P 0 h t)) = P 0 h t
          rw [cardArg_lt_case K 0 _ hqK, ite_eq_left rfl]; exact h1
        · rw [ite_eq_right hq0]
          by_cases hh0 : h = Z
          · subst hh0
            obtain ⟨h1, h2, h3, h4⟩ := UE_props q t ht hti
            rw [ite_eq_left rfl]
            refine ⟨?_, Nat.le_of_lt hqK, h2, h3, Nat.le_trans h4 (Nat.le_max_right _ _)⟩
            show cardArg K q (UE q t) = P q Z t
            rw [cardArg_lt_case K q _ hqK, ite_eq_right hq0, h1, MT.stand, MT.stand_of_NF1 ht,
              ite_eq_left hth]
          · obtain ⟨h1, h2, h3, h4⟩ := UE_props q _ hg hgi
            rw [ite_eq_right hh0]
            refine ⟨?_, Nat.le_of_lt hqK, h2, h3, h4⟩
            show cardArg K q (UE q (P q h t)) = P q h t
            rw [cardArg_lt_case K q _ hqK, ite_eq_right hq0, h1, MT.stand, MT.stand_of_NF1 hg]
            have hnot : ¬ T.head (P q h t) ≤ P q Z Z := by
              intro hle
              exact lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _
                (T.Lt.p_mid _ _ _ _ _ (MT.Z_lt_of_ne hh0)) hle)
            rw [ite_eq_right hnot]
      · subst hh0
        have hlt1 : t < P q (P 0 Z Z) Z := by
          cases t with
          | Z => exact T.Lt.Z_lt_P _ _ _
          | P p2 g2 r2 =>
            rcases hth with hth | hth
            · cases hth with
              | p_head _ _ _ _ _ _ h1 => exact T.Lt.p_head _ _ _ _ _ _ h1
              | p_mid _ _ _ _ _ h1 => exact absurd h1 lt_Z_inv
              | p_tail _ _ _ _ h1 => cases h1
            · injection hth with h1 h2 _
              subst h1; subst h2
              exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)
        have hti : T.index_Prop1 q t := index_of_head_le' ht hth
        have htZ : ∀ x ∈ T.G1 q t, x < t := by
          intro x hx
          rcases G1_below_head q Z (fun y hy => by cases hy) t ht hth hti x hx with h | h
          · exact absurd h lt_Z_inv
          · subst h
            cases t with
            | Z => cases hx
            | P _ _ _ => exact T.Lt.Z_lt_P _ _ _
        rw [uncardSmall, ite_eq_left hqK]
        refine ⟨?_, Nat.le_refl _, ht, hqK ▸ htZ, Nat.le_max_right _ _⟩
        show cardArg K K t = P q Z t
        rw [← hqK, cardArg_same_small q t hlt1]


theorem uncard_mono (K : Nat) (hK : 0 < K) (g1 g2 : T) (hg1 : T.isNF1 g1)
    (hgg1 : ∀ x ∈ T.G1 K g1, x < g1) (hg2 : T.isNF1 g2) (hgg2 : ∀ x ∈ T.G1 K g2, x < g2)
    (h : g2 ≤ g1) :
    P (uncardArg K g2).1 (uncardArg K g2).2 Z ≤ P (uncardArg K g1).1 (uncardArg K g1).2 Z := by
  obtain ⟨he1, hp1, hc1, hgc1, _⟩ := uncard_props K hK g1 hg1 hgg1
  obtain ⟨he2, hp2, hc2, hgc2, _⟩ := uncard_props K hK g2 hg2 hgg2
  rcases lt_total_thm (P (uncardArg K g2).1 (uncardArg K g2).2 Z)
      (P (uncardArg K g1).1 (uncardArg K g1).2 Z) with hlt | hlt | heq
  · exact Or.inl hlt
  · exfalso
    have hg12 : g1 < g2 := by
      rcases lt_inv _ _ _ _ _ _ hlt with hp | ⟨hp, hc⟩ | ⟨_, _, hz⟩
      · have := card_heads_lt K _ _ _ _ Z Z hp hc1 hgc1 hc2 hgc2
        rw [Nat.max_eq_right hp1, Nat.max_eq_right hp2, he1, he2] at this
        rcases lt_inv _ _ _ _ _ _ this with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
        · exact absurd h1 (Nat.lt_irrefl _)
        · exact h1
        · exact absurd h1 lt_Z_inv
      · rw [← hp] at he2 hgc2
        have hc3 := cardArg_lt_same K (uncardArg K g1).1 _ _ hc1 hgc1 hc2 hgc2 hc
        rwa [he1, he2] at hc3
      · exact absurd hz lt_Z_inv
    rcases h with h | h
    · exact lt_asymm_thm h hg12
    · rw [h] at hg12; exact lt_irrefl_thm _ hg12
  · exact Or.inr heq

/-! ### Uncarding sums -/

/-- The head summand produced by uncarding. -/
def ucHead (K q : Nat) (g : T) : Nat × T := if K < q then (q, g) else uncardArg K g

theorem UC_P (K q : Nat) (g r : T) : UC K (P q g r) = P (ucHead K q g).1 (ucHead K q g).2 (UC K r) := by
  rw [UC, ucHead]
  by_cases h : K < q
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem UC_add (K : Nat) : ∀ H L : T, (∀ p c, IsSummand p c H → K < p) →
    UC K (T.add H L) = T.add H (UC K L)
  | Z, L, _ => rfl
  | P q g r, L, hH => by
    rw [T.P_add_eq, T.P_add_eq, UC, ite_eq_left (hH q g (Or.inl ⟨rfl, rfl⟩)),
      UC_add K r L (fun p c hs => hH p c (Or.inr hs))]

theorem UC_deg (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d → MT.deg (UC K d) ≤ MT.deg d
  | Z, _ => Nat.le_refl _
  | P q g r, hd => by
    obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
    have ih := UC_deg K hK r hr
    rw [UC]
    by_cases hq : K < q
    · rw [ite_eq_left hq]
      exact Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans ih (Nat.le_max_right _ _)⟩
    · rw [ite_eq_right hq]
      obtain ⟨-, -, -, -, hdeg⟩ :=
        uncard_props K hK g hg fun x hx => hgg x (G1_antitone q K (Nat.le_of_not_gt hq) g x hx)
      exact Nat.max_le.2 ⟨Nat.le_trans (Nat.succ_le_succ hdeg) (Nat.le_max_left _ _),
        Nat.le_trans ih (Nat.le_max_right _ _)⟩

theorem UC_spec (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → K ≤ p) → ct K (UC K d) = d
  | Z, _, _ => rfl
  | P q g r, hd, hidx => by
    obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
    have ih := UC_spec K hK r hr (fun p c hs => hidx p c (Or.inr hs))
    have hKq := hidx q g (Or.inl ⟨rfl, rfl⟩)
    rw [UC]
    by_cases hq : K < q
    · rw [ite_eq_left hq, ct_P, Nat.max_eq_left (Nat.le_of_lt hq), ih, cardArg_above K q g hq]
    · rw [ite_eq_right hq]
      have hqK : q = K := Nat.le_antisymm (Nat.le_of_not_gt hq) hKq
      subst hqK
      obtain ⟨he, hp, -⟩ := uncard_props q hK g hg hgg
      rw [ct_P, Nat.max_eq_right hp, he, ih]

theorem UC_NF (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → K ≤ p) → T.isNF1 (UC K d)
  | Z, _, _ => T.isNF1.z
  | P q g r, hd, hidx => by
    have hprops (q : Nat) (g : T) (hg : T.isNF1 g) (hgg : ∀ x ∈ T.G1 q g, x < g)
        (hKq : K ≤ q) : T.isNF1 (ucHead K q g).2 ∧
          ∀ x ∈ T.G1 (ucHead K q g).1 (ucHead K q g).2, x < (ucHead K q g).2 := by
      rw [ucHead]
      by_cases h : K < q
      · rw [ite_eq_left h]; exact ⟨hg, hgg⟩
      · rw [ite_eq_right h]
        have hqK : q = K := Nat.le_antisymm (Nat.le_of_not_gt h) hKq
        subst hqK
        obtain ⟨-, -, h1, h2, -⟩ := uncard_props q hK g hg hgg
        exact ⟨h1, h2⟩
    obtain ⟨hg, hr, hgg, hrh⟩ := T.isNF1_P_inv q g r hd
    have hKq := hidx q g (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨hc, hgc⟩ := hprops q g hg hgg hKq
    rw [UC_P]
    refine T.isNF1.p _ _ _ hc (UC_NF K hK r hr (fun p c hs => hidx p c (Or.inr hs))) hgc ?_
    cases r with
    | Z => exact T.Z_le _
    | P q2 g2 r2 =>
      obtain ⟨hg2, _, hgg2, _⟩ := T.isNF1_P_inv q2 g2 r2 hr
      have hK2 := hidx q2 g2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      rw [UC_P]
      have hq21 := head_le_index q2 q g2 g hrh
      show P (ucHead K q2 g2).1 (ucHead K q2 g2).2 Z ≤ P (ucHead K q g).1 (ucHead K q g).2 Z
      by_cases h2 : K < q2
      · rw [ucHead, ite_eq_left h2, ucHead, ite_eq_left (Nat.lt_of_lt_of_le h2 hq21)]
        exact hrh
      · rw [ucHead, ite_eq_right h2]
        have hq2K : q2 = K := Nat.le_antisymm (Nat.le_of_not_gt h2) hK2
        subst hq2K
        have hp2 := (uncard_props q2 hK g2 hg2 hgg2).2.1
        by_cases h1 : q2 < q
        · rw [ucHead, ite_eq_left h1]
          exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hp2 h1))
        · rw [ucHead, ite_eq_right h1]
          have hqq : q = q2 := Nat.le_antisymm (Nat.le_of_not_gt h1) hq21
          subst hqq
          apply uncard_mono q hK g g2 hg hgg hg2 hgg2
          rcases hrh with h | h
          · cases h with
            | p_head _ _ _ _ _ _ h' => exact absurd h' (Nat.lt_irrefl _)
            | p_mid _ _ _ _ _ h' => exact Or.inl h'
            | p_tail _ _ _ _ h' => cases h'
          · injection h with _ h' _; exact Or.inr h'

theorem UC_index (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → p = K) → T.index_Prop1 K (UC K d)
  | Z, _, _ => T.index_Prop1.z
  | P q g r, hd, hidx => by
    obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
    have hqK := hidx q g (Or.inl ⟨rfl, rfl⟩)
    subst hqK
    rw [UC, ite_eq_right (Nat.lt_irrefl q)]
    exact T.index_Prop1.p _ _ _ (uncard_props q hK g hg hgg).2.1
      (UC_index q hK r hr (fun p c hs => hidx p c (Or.inr hs)))

/-! ### Summands of a single index -/

/-- Summands of index exactly `m`. -/
def idxPart (m : Nat) (c : T) : T := (part (m - 1) (part m c).2).1

theorem part_snd_split (m : Nat) (c : T) (hc : T.isNF1 c) :
    (part m c).2 = T.add (idxPart m c) (part (m - 1) c).2 := by
  have := part_add (m - 1) _ (part_NF m c hc).2
  rw [(part_part (m - 1) m (Nat.sub_le m 1) c).2.1] at this
  exact this.symm

theorem uncard_top_cases (K : Nat) (hK : 0 < K) (g : T) (hp : (uncardArg K g).1 = K) :
    ((uncardArg K g).2 = g ∧ P K (P 0 Z Z) Z ≤ g) ∨ (∃ t, g = P K Z t ∧ (uncardArg K g).2 = t) := by
  by_cases hle : P K (P 0 Z Z) Z ≤ g
  · rw [uncardArg_big K g hle]
    exact Or.inl ⟨rfl, hle⟩
  · rw [uncardArg_small K g hle] at hp ⊢
    cases g with
    | Z => exact absurd hp (Nat.ne_of_lt hK)
    | P q h t =>
      rcases small_head_shape K q h t (MT.lt_of_not_le hle) with hqK | ⟨hqK, hh0⟩
      · exfalso
        rw [uncardSmall, ite_eq_right (Nat.ne_of_lt hqK)] at hp
        by_cases hq0 : q = 0
        · rw [ite_eq_left hq0] at hp; exact Nat.ne_of_lt hK hp
        · rw [ite_eq_right hq0] at hp
          by_cases hh0 : h = Z
          · rw [ite_eq_left hh0] at hp; exact Nat.ne_of_lt hqK hp
          · rw [ite_eq_right hh0] at hp; exact Nat.ne_of_lt hqK hp
      · subst hh0
        refine Or.inr ⟨t, by rw [hqK], ?_⟩
        rw [uncardSmall, ite_eq_left hqK]


theorem UC_summand_inv (K : Nat) : ∀ L : T, ∀ p c, IsSummand p c (UC K L) →
    ∃ q g, IsSummand q g L ∧ ucHead K q g = (p, c)
  | Z, _, _, h => h.elim
  | P q g r, p, c, h => by
    rw [UC_P] at h
    rcases h with ⟨h1, h2⟩ | h
    · exact ⟨q, g, Or.inl ⟨rfl, rfl⟩, by rw [← h1, ← h2]⟩
    · obtain ⟨q2, g2, hs, he⟩ := UC_summand_inv K r p c h
      exact ⟨q2, g2, Or.inr hs, he⟩

theorem UC_top_good_core (K : Nat) (hK : 0 < K) (c H Ld : T) (hc : T.isNF1 c)
    (hgc : ∀ x ∈ T.G1 K c, x < c)
    (hH : (part K c).1 = H) (hHNF : T.isNF1 H) (hHfix : part K H = (H, Z))
    (hce : T.add H (part K c).2 = c)
    (hLdidx : ∀ p a, IsSummand p a Ld → p = K) (hLdc : ∀ p a, IsSummand p a Ld → IsSummand p a c)
    (hUNF : T.isNF1 (UC K Ld)) (heNF : T.isNF1 (T.add H (UC K Ld))) :
    ∀ x ∈ T.G1 K (T.add H (UC K Ld)), x < T.add H (UC K Ld) := by
  have hHle : H ≤ T.add H (UC K Ld) := MT.add_self_le _ _
  have hargs : SumAll (fun p c' => K ≤ p → c' < T.add H (UC K Ld) ∧
      ∀ y ∈ T.G1 K c', y < T.add H (UC K Ld)) (UC K Ld) := by
    apply SumAll_of_summand
    intro p c' hs hKp
    obtain ⟨q, g, hsq, hqg⟩ := UC_summand_inv K Ld p c' hs
    have hqK := hLdidx q g hsq
    subst hqK
    have hgc0 := hLdc q g hsq
    obtain ⟨hg, hgg⟩ := IsSummand_NF q g c hc hgc0
    have hggK : g ∈ T.G1 q c := G1_summand_mem q q g (Nat.le_refl q) c hgc0
    rw [ucHead, ite_eq_right (Nat.lt_irrefl q)] at hqg
    obtain ⟨-, hp, _, hgc', _⟩ := uncard_props q hK g hg hgg
    rw [hqg] at hp hgc'
    have hpq : p = q := Nat.le_antisymm hp hKp
    subst hpq
    have hgc'' : ∀ y ∈ T.G1 p c', y < c' := hgc'
    have hsumE : IsSummand p c' (T.add H (UC p Ld)) := IsSummand_add_right _ _ H _ hs
    have hpq' : (uncardArg p g).1 = p := by rw [hqg]
    have hlt : c' < T.add H (UC p Ld) := by
      rcases uncard_top_cases p hK g hpq' with ⟨hcg, _⟩ | ⟨t, hgt, hct⟩
      · rw [hqg] at hcg
        change c' = g at hcg
        subst hcg
        rcases part_lt_cases p c' c hg hc (hgc c' hggK) with h1 | ⟨h1, _⟩
        · rw [hH] at h1
          have : c' < H :=
            lt_of_part_lt_cases p c' H hg hHNF (Or.inl (by rw [hHfix]; exact h1))
          exact lt_of_lt_of_le_thm T _ _ _ this hHle
        · rw [hH] at h1
          have hgsplit : c' = T.add H (part p c').2 := by
            have := part_add p c' hg
            rw [h1] at this
            exact this.symm
          have hle : P p c' Z ≤ UC p Ld :=
            partial_order.trans _ _ _ (summand_le_head p c' _ hUNF hs) (MT.head_le_self _)
          have hlow : (part p c').2 < UC p Ld :=
            lt_of_lt_of_le_thm T _ _ _ (part_snd_lt_wrap p c' _ hg hgg) hle
          rw [hgsplit]
          exact MT.add_left_lt H hlow
      · rw [hqg] at hct
        change c' = t at hct
        subst hct
        subst hgt
        obtain ⟨_, ht, _, hth⟩ := T.isNF1_P_inv p Z c' hg
        have hti : T.index_Prop1 p c' := index_of_head_le' ht hth
        exact lt_of_lt_of_le_thm T _ _ _ (MT.lt_wrap p c' Z hti hgc'')
          (partial_order.trans _ _ _ (summand_le_head p c' _ heNF hsumE) (MT.head_le_self _))
    exact ⟨hlt, fun y hy => lt_trans_thm _ _ _ (hgc'' y hy) hlt⟩
  intro x hx
  rw [MT.G1_add, List.mem_append] at hx
  rcases hx with hx | hx
  · have hxc := hgc x (G1_part_fst_subset K K c hc x (by rw [hH]; exact hx))
    have hHne : H ≠ Z := by intro h; rw [h] at hx; cases hx
    have hxH := MT.lt_add_left_of_size_lt H _ x hHne (G1_size_lt K H x hx) (by rw [hce]; exact hxc)
    exact lt_of_lt_of_le_thm T _ _ _ hxH hHle
  · exact G1_of_SumAll K _ _ hargs x hx

/-- The top uncarded piece is good at its index. -/
theorem UC_top_good (K : Nat) (hK : 0 < K) (c : T) (hc : T.isNF1 c)
    (hgc : ∀ x ∈ T.G1 K c, x < c) :
    ∀ x ∈ T.G1 K (UC K (part (K - 1) c).1), x < UC K (part (K - 1) c).1 := by
  have hKK : K - 1 ≤ K := Nat.sub_le K 1
  have hK1 : K = K - 1 + 1 := (Nat.succ_pred_eq_of_pos hK).symm
  have hdNF := (part_NF (K - 1) c hc).1
  have hdidx : ∀ p a, IsSummand p a (part (K - 1) c).1 → K ≤ p := by
    intro p a hs
    have := part_fst_summand_gt (K - 1) c p a hs
    rw [hK1]; exact this
  have hd := part_add K _ hdNF
  rw [(part_part (K - 1) K hKK c).1, (part_part (K - 1) K hKK c).2.2] at hd
  have hHgt : ∀ p a, IsSummand p a (part K c).1 → K < p := part_fst_summand_gt K c
  have heq : UC K (part (K - 1) c).1 =
      T.add (part K c).1 (UC K (part (K - 1) (part K c).2).1) := by
    rw [← hd, UC_add K _ _ hHgt]
  have heNF := UC_NF K hK _ hdNF hdidx
  rw [heq] at heNF ⊢
  have hLdNF := (part_NF (K - 1) _ (part_NF K c hc).2).1
  have hLdidx : ∀ p a, IsSummand p a (part (K - 1) (part K c).2).1 → p = K := by
    intro p a hs
    have h1 := part_fst_summand_gt (K - 1) _ p a hs
    have h2 := (summands_of_part_snd K c p a (summands_of_part_fst (K - 1) _ p a hs)).2
    exact Nat.le_antisymm h2 (by rw [hK1]; exact h1)
  have hLdc : ∀ p a, IsSummand p a (part (K - 1) (part K c).2).1 → IsSummand p a c := by
    intro p a hs
    exact (summands_of_part_snd K c p a (summands_of_part_fst (K - 1) _ p a hs)).1
  have hUNF := UC_NF K hK _ hLdNF (fun p a hs => Nat.le_of_eq (hLdidx p a hs).symm)
  exact UC_top_good_core K hK c _ _ hc hgc rfl (part_NF K c hc).1 (part_first_fixed K c)
    (part_add K c hc) hLdidx hLdc hUNF heNF

/-! ### Pieces of a principal argument -/

theorem lpInv_good (K : Nat) (hK : 0 < K) (e : T) (he : T.isNF1 e)
    (hg : ∀ x ∈ T.G1 K e, x < e) : ∀ x ∈ T.G1 K (lpInv e), x < lpInv e := by
  have hK0 : ¬ K ≤ 0 := Nat.not_le_of_lt hK
  match e, he, hg with
  | Z, _, _ =>
    intro x hx
    change x ∈ T.G1 K (P 0 Z Z) at hx
    rw [T.G1, ite_eq_right hK0] at hx
    cases hx
  | P 0 Z t, he, hg =>
    intro x hx
    change x ∈ T.G1 K (P 0 Z (P 0 Z t)) at hx
    rw [T.G1, ite_eq_right hK0] at hx
    exact lt_trans_thm _ _ _ (hg x hx) (T.Lt.p_tail _ _ _ _ (MT.tail_lt_of_NF1 he))
  | P (_ + 1) _ _, _, hg => exact hg
  | P 0 (P _ _ _) _, _, hg => exact hg

theorem idxPart_props (i : Nat) (hi : 0 < i) (c : T) (hc : T.isNF1 c) :
    T.isNF1 (idxPart i c) ∧ (∀ p a, IsSummand p a (idxPart i c) → p = i) ∧
      MT.deg (idxPart i c) ≤ MT.deg c := by
  have hi1 : i = i - 1 + 1 := (Nat.succ_pred_eq_of_pos hi).symm
  refine ⟨(part_NF (i - 1) _ (part_NF i c hc).2).1, ?_, ?_⟩
  · intro p a hs
    have h1 := part_fst_summand_gt (i - 1) _ p a hs
    have h2 := (summands_of_part_snd i c p a (summands_of_part_fst (i - 1) _ p a hs)).2
    exact Nat.le_antisymm h2 (by rw [hi1]; exact h1)
  · exact Nat.le_trans (part_props (i - 1) _).1 (part_props i c).2

/-- The contribution of a coordinate translation at a lower index. -/
def TContr (i : Nat) (t : T) : T := if i = 0 then ec 0 t else ct i (ec i t)

/-- The coordinate translation required at a lower index. -/
def lowPiece (c : T) (i : Nat) : T :=
  if i = 0 then UE 0 (part 0 c).2 else UE i (UC i (idxPart i c))

theorem lowPiece_props (c : T) (hc : T.isNF1 c) (i : Nat) :
    T.isNF1 (lowPiece c i) ∧ (∀ x ∈ T.G1 i (lowPiece c i), x < lowPiece c i) ∧
      MT.deg (lowPiece c i) ≤ MT.deg c ∧
      TContr i (lowPiece c i) = (if i = 0 then (part 0 c).2 else idxPart i c) := by
  by_cases hi : i = 0
  · subst hi
    have hL := (part_NF 0 c hc).2
    have hLi := part_second_index 0 c
    rw [lowPiece, ite_eq_left rfl, TContr, ite_eq_left rfl, ite_eq_left rfl]
    obtain ⟨h1, h2, h3, h4⟩ := UE_props 0 _ hL hLi
    exact ⟨h2, h3, Nat.le_trans h4 (part_props 0 c).2, h1⟩
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    obtain ⟨hIn, hIi, hId⟩ := idxPart_props i hip c hc
    have hUn := UC_NF i hip _ hIn (fun p a hs => Nat.le_of_eq (hIi p a hs).symm)
    have hUi := UC_index i hip _ hIn hIi
    rw [lowPiece, ite_eq_right hi, TContr, ite_eq_right hi, ite_eq_right hi]
    obtain ⟨h1, h2, h3, h4⟩ := UE_props i _ hUn hUi
    refine ⟨h2, h3, Nat.le_trans h4 (Nat.le_trans (UC_deg i hip _ hIn) hId), ?_⟩
    rw [h1, UC_spec i hip _ hIn (fun p a hs => Nat.le_of_eq (hIi p a hs).symm)]

end OB

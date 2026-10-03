import Subsp.old.stop_inverse_target

/-! Surjectivity of the legacy translation onto Buchholz normal forms with indices below
the dimension. -/

namespace LegacyTranslation

open T

/-- Constructive choice of a vector from coordinatewise existence. -/
theorem vec_choice {A : Type} : ∀ (k : Nat) (R : Fin k → A → Prop),
    (∀ i, ∃ a, R i a) → ∃ v : new.Vec A k, ∀ i, R i (v.idx i)
  | 0, _, _ => ⟨.nil, fun i => i.elim0⟩
  | k + 1, R, h => by
      obtain ⟨v, hv⟩ := vec_choice k (fun i a => R i.castSucc a) (fun i => h i.castSucc)
      obtain ⟨a, ha⟩ := h (Fin.last k)
      refine ⟨.snoc k v a, fun i => ?_⟩
      by_cases hi : i.val < k
      · simp only [new.Vec.idx, hi, dite_true]
        exact hv ⟨i.val, hi⟩
      · simp only [new.Vec.idx, hi, dite_false]
        have hi' : i = Fin.last k := Fin.eq_of_val_eq (by have := i.isLt; simp; omega)
        rw [hi']
        exact ha

/-! Translations of explicit vectors. -/

theorem aux_low_eq {lam : Nat} (c : T) (hc : T.isNF1 c) : ∀ {m : Nat} (v : new.Vec (new.T lam) m),
    (∀ i : Fin m, Contr i.val (v.idx i) =
      (if i.val = 0 then (T.part 0 c).2 else idxPart i.val c)) →
    (transAux v).2 = (if m = 0 then T.Z else (T.part (m - 1) c).2)
  | _, .nil, _ => rfl
  | _, .snoc k v a, hv => by
      have hlast : Contr k a = (if k = 0 then (T.part 0 c).2 else idxPart k c) := by
        simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using hv (Fin.last k)
      have hpre : ∀ i : Fin k, Contr i.val (v.idx i) =
          (if i.val = 0 then (T.part 0 c).2 else idxPart i.val c) := by
        intro i
        simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using hv i.castSucc
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          simpa [Contr] using hlast
      | succ k =>
          rw [aux_lower_snoc, aux_low_eq c hc v hpre]
          simp only [Contr, Nat.succ_ne_zero, ite_false] at hlast
          simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, hlast]
          exact (part_snd_split (k + 1) c hc).symm

theorem aux_top_eq {lam : Nat} (c : T) (hc : T.isNF1 c) (K : Nat) (hK : 0 < K) :
    ∀ {k : Nat} (v : new.Vec (new.T lam) k), K < k →
    (∀ i : Fin k, i.val < K → Contr i.val (v.idx i) =
      (if i.val = 0 then (T.part 0 c).2 else idxPart i.val c)) →
    (∀ i : Fin k, i.val = K → v.idx i ≠ new.T.Z ∧
      T.card_times K (T.one_del (trans (v.idx i))) = (T.part (K - 1) c).1) →
    (∀ i : Fin k, K < i.val → v.idx i = new.T.Z) →
    (transAux v).1 = T.P K c T.Z
  | _, .nil, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | _, .snoc k v a, hk, hlow, htop, hzero => by
      have hlastIdx (P : new.T lam → Prop) (h : ∀ i : Fin (k + 1), i.val = k → P ((new.Vec.snoc k v a).idx i)) :
          P a := by
        simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using h (Fin.last k) rfl
      rcases Nat.lt_or_ge K k with hKk | hKk
      · -- the last coordinate lies above the top index
        have ha : a = new.T.Z := by
          simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using
            hzero (Fin.last k) hKk
        subst ha
        cases k with
        | zero => omega
        | succ k =>
            rw [aux_zero_tail]
            apply aux_top_eq c hc K hK v hKk
            · intro i hi
              simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
                hlow i.castSucc hi
            · intro i hi
              simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
                htop i.castSucc hi
            · intro i hi
              simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
                hzero i.castSucc hi
      · have hkK : k = K := by omega
        subst hkK
        obtain ⟨hane, hct⟩ := htop (Fin.last k) rfl
        simp only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] at hane hct
        cases k with
        | zero => omega
        | succ k =>
            rw [aux_head_snoc v a hane, hct]
            have hv := aux_low_eq c hc v (fun i => by
              simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using
                hlow i.castSucc i.isLt)
            simp only [Nat.succ_ne_zero, ite_false] at hv
            rw [hv]
            congr 1
            exact part_add (k + 1 - 1) c hc

/-! Unit translations. -/

theorem trans_zeros_P {lam : Nat} (b : new.T lam) :
    trans (new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) b) = T.P 0 T.Z (trans b) := by
  rw [trans_as_add, transAux_zeros, p_zero_add]

theorem zeros_coords {lam : Nat} (u : Nat) :
    ∀ i : Fin lam, new.T.isNFComp u ((new.Vec.ofFn lam (fun _ => (new.T.Z : new.T lam))).idx i) := by
  intro i
  rw [new.Vec.ofFn_idx]
  exact new.T.isNFComp_Z u

/-! Pieces of a principal argument. -/

theorem lpInv_good (K : Nat) (hK : 0 < K) (e : T) (he : T.isNF1 e)
    (hg : ∀ x ∈ T.G1 K e, x < e) : ∀ x ∈ T.G1 K (lpInv e), x < lpInv e := by
  match e, he, hg with
  | .Z, _, _ => intro x hx; simp [lpInv, T.G1, show ¬ K ≤ 0 by omega] at hx
  | .P 0 .Z t, he, hg =>
      intro x hx
      simp only [lpInv, T.G1, show ¬ K ≤ 0 by omega, ite_false] at hx
      exact lt_trans_thm _ _ _ (hg x (by simp only [T.G1, show ¬ K ≤ 0 by omega, ite_false]; exact hx))
        (T.Lt.p_tail _ _ _ _ (NF_tail_lt 0 T.Z t he))
  | .P (_ + 1) _ _, _, hg | .P 0 (.P _ _ _) _, _, hg => exact hg

theorem lpInv_ne_Z (e : T) : lpInv e ≠ T.Z := by
  match e with
  | .Z | .P 0 .Z _ | .P 0 (.P _ _ _) _ | .P (_ + 1) _ _ => intro h; cases h

theorem PZ_isNF {lam : Nat} (v : new.Vec (new.T lam) lam)
    (hv : ∀ i : Fin lam, new.T.isNFComp i.val (v.idx i)) : new.T.isNF (new.T.P v new.T.Z) :=
  new.T.isNF.p v _ (fun i => (hv i).1) .z (fun i => (hv i).2) (new.T.Z_le _)

theorem idxPart_props (i : Nat) (hi : 0 < i) (c : T) (hc : T.isNF1 c) :
    T.isNF1 (idxPart i c) ∧ (∀ p a, IsSummand p a (idxPart i c) → p = i) ∧
      degree (idxPart i c) ≤ degree c ∧
      (∀ l, DeepIdx l c → DeepIdx l (idxPart i c)) := by
  unfold idxPart
  refine ⟨(part_NF (i - 1) _ (part_NF i c hc).2).1, ?_, ?_, ?_⟩
  · intro p a hs
    have h1 := part_fst_summand_gt (i - 1) _ p a hs
    have h2 := (summands_of_part_snd i c p a (summands_of_part_fst (i - 1) _ p a hs)).2
    omega
  · exact Nat.le_trans (part_props 0 (i - 1) _).1 (part_props 0 i c).2.1
  · exact fun l hl => ((part_props l (i - 1) _).2.2 ((part_props l i c).2.2 hl).2).1

/-- The contribution of a coordinate translation at a lower index. -/
def TContr (i : Nat) (t : T) : T :=
  if i = 0 then T.early_collapse 0 t else T.card_times i (T.early_collapse i t)

/-- The source coordinate translation required at a lower index. -/
def lowPiece (c : T) (i : Nat) : T :=
  if i = 0 then UE 0 (T.part 0 c).2 else UE i (UC i (idxPart i c))

theorem lowPiece_props (c : T) (hc : T.isNF1 c) (i : Nat) :
    T.isNF1 (lowPiece c i) ∧ (∀ x ∈ T.G1 i (lowPiece c i), x < lowPiece c i) ∧
      degree (lowPiece c i) ≤ degree c ∧
      (∀ l, i ≤ l → DeepIdx l c → DeepIdx l (lowPiece c i)) ∧
      TContr i (lowPiece c i) = (if i = 0 then (T.part 0 c).2 else idxPart i c) := by
  by_cases hi : i = 0
  · subst hi
    have hL := (part_NF 0 c hc).2
    have hLi := part_second_index 0 c
    simp only [lowPiece, TContr, ite_true]
    obtain ⟨h1, h2, h3, h4, h5⟩ := UE_props 0 _ hL hLi
    exact ⟨h2, h3, Nat.le_trans h4 (part_props 0 0 c).2.1,
      fun l _ hl => h5 l ((part_props l 0 c).2.2 hl).2, h1⟩
  · have hip : 0 < i := Nat.pos_of_ne_zero hi
    obtain ⟨hIn, hIi, hId, hIl⟩ := idxPart_props i hip c hc
    have hUn := UC_NF i hip _ hIn (fun p a hs => (hIi p a hs).symm ▸ Nat.le_refl i)
    have hUi := UC_index i hip _ hIn hIi
    simp only [lowPiece, TContr, hi, ite_false]
    obtain ⟨h1, h2, h3, h4, h5⟩ := UE_props i _ hUn hUi
    obtain ⟨hd, hdi⟩ := UC_props i hip _ hIn
    refine ⟨h2, h3, Nat.le_trans h4 (Nat.le_trans hd hId),
      fun l hil hl => h5 l (hdi l hil (hIl l hl)), ?_⟩
    rw [h1, UC_spec i hip _ hIn (fun p a hs => (hIi p a hs).symm ▸ Nat.le_refl i)]

/-! Preimages of principal terms. -/

theorem principal_preimage {lam : Nat} (hlam : 0 < lam) (K : Nat) (c : T)
    (hy : T.isNF1 (T.P K c T.Z)) (hidx : DeepIdx (lam - 1) (T.P K c T.Z))
    (IH : ∀ y', degree y' ≤ degree c → T.isNF1 y' → DeepIdx (lam - 1) y' →
      ∃ a : new.T lam, new.T.isNF a ∧ trans a = y') :
    ∃ w : new.Vec (new.T lam) lam, (∀ i : Fin lam, new.T.isNFComp i.val (w.idx i)) ∧
      (transAux w).1 = T.P K c T.Z := by
  obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv K c T.Z hy
  obtain ⟨hKl, hcl, _⟩ := hidx
  have hKlam : K < lam := by omega
  by_cases hK : K = 0
  · subst hK
    obtain ⟨a0, ha0, hta0⟩ := IH c (Nat.le_refl _) hc hcl
    have ha0c : new.T.isNFComp 0 a0 :=
      reverse_transfer 0 a0 ha0 (by rw [hta0]; exact hgc)
    obtain ⟨w, hw⟩ := vec_choice lam
      (fun i a => (i.val = 0 → new.T.isNFComp 0 a ∧ trans a = c) ∧ (0 < i.val → a = new.T.Z))
      (fun i => by
        by_cases hi : i.val = 0
        · exact ⟨a0, fun _ => ⟨ha0c, hta0⟩, fun h => absurd hi (Nat.ne_of_gt h)⟩
        · exact ⟨new.T.Z, fun h => absurd h hi, fun _ => rfl⟩)
    refine ⟨w, fun i => ?_, ?_⟩
    · by_cases hi : i.val = 0
      · rw [hi]; exact ((hw i).1 hi).1
      · rw [(hw i).2 (Nat.pos_of_ne_zero hi)]; exact new.T.isNFComp_Z _
    · cases lam with
      | zero => omega
      | succ k =>
          rw [transAux_countable_head_exact w (fun i hi => (hw i).2 hi)]
          rw [((hw ⟨0, Nat.zero_lt_succ k⟩).1 rfl).2]
  · have hKp : 0 < K := Nat.pos_of_ne_zero hK
    have hdNF := (part_NF (K - 1) c hc).1
    have hdidx : ∀ p a, IsSummand p a (T.part (K - 1) c).1 → K ≤ p := by
      intro p a hs
      have := part_fst_summand_gt (K - 1) c p a hs
      omega
    have heNF := UC_NF K hKp _ hdNF hdidx
    have hegood := UC_top_good K hKp c hc hgc
    have hedeg : degree (UC K (T.part (K - 1) c).1) ≤ degree c :=
      Nat.le_trans (UC_props K hKp _ hdNF).1 (part_props 0 (K - 1) c).1
    have heidx : DeepIdx (lam - 1) (UC K (T.part (K - 1) c).1) :=
      (UC_props K hKp _ hdNF).2 (lam - 1) hKl ((part_props _ (K - 1) c).2.2 hcl).1
    obtain ⟨ae, hae, htae⟩ := IH _ hedeg heNF heidx
    -- the top coordinate
    have htop : ∃ aK : new.T lam, new.T.isNF aK ∧ new.T.isNFComp K aK ∧
        trans aK = lpInv (UC K (T.part (K - 1) c).1) ∧ aK ≠ new.T.Z := by
      have hlg := lpInv_good K hKp _ heNF hegood
      have hlne := lpInv_ne_Z (UC K (T.part (K - 1) c).1)
      have hzNF : new.T.isNF (new.T.P (new.Vec.ofFn lam (fun _ => (new.T.Z : new.T lam))) new.T.Z) :=
        PZ_isNF _ fun i => zeros_coords i.val i
      have hpre : ∃ aK : new.T lam, new.T.isNF aK ∧
          trans aK = lpInv (UC K (T.part (K - 1) c).1) := by
        cases hE : UC K (T.part (K - 1) c).1 with
        | Z =>
            refine ⟨new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z, hzNF, ?_⟩
            rw [trans_zeros_P]; rfl
        | P p h t =>
            cases p with
            | succ p => exact ⟨ae, hae, by rw [htae, hE]; rfl⟩
            | zero =>
                cases h with
                | P _ _ _ => exact ⟨ae, hae, by rw [htae, hE]; rfl⟩
                | Z =>
                    refine ⟨new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) ae, ?_, ?_⟩
                    · apply new.T.isNF.p _ _ (fun i => (zeros_coords 0 i).1) hae
                        (fun i => (zeros_coords i.val i).2)
                      cases hae' : ae with
                      | Z => exact new.T.Z_le _
                      | P w' b' =>
                          rw [hae'] at hae htae
                          obtain ⟨p', a', he', _⟩ := aux_principal w'
                          rw [trans_as_add, he', p_zero_add, hE] at htae
                          injection htae with h1 h2 _
                          subst h1; subst h2
                          obtain ⟨hw', _, _⟩ := new.T.isNF_P_inv w' b' hae
                          have heq := trans_injective_NF _ _ (PZ_isNF w' hw') hzNF
                            (by rw [trans_as_add, he', trans_zeros_P]; rfl)
                          show new.T.P w' new.T.Z ≤ _
                          rw [heq]
                          exact new.T.le_refl _
                    · rw [trans_zeros_P, htae, hE]; rfl
      obtain ⟨aK, haK, htaK⟩ := hpre
      exact ⟨aK, haK, reverse_transfer K aK haK (by rw [htaK]; exact hlg), htaK,
        fun h => hlne (by rw [← htaK, h]; rfl)⟩
    obtain ⟨aK, haK, haKc, htaK, haKne⟩ := htop
    have hlow : ∀ i : Nat, i < K → ∃ a : new.T lam, new.T.isNF a ∧ new.T.isNFComp i a ∧
        trans a = lowPiece c i := by
      intro i hiK
      obtain ⟨hn, hg, hd, hl, _⟩ := lowPiece_props c hc i
      obtain ⟨a, ha, hta⟩ := IH _ hd hn (hl (lam - 1) (by omega) hcl)
      exact ⟨a, ha, reverse_transfer i a ha (by rw [hta]; exact hg), hta⟩
    obtain ⟨w, hw⟩ := vec_choice lam
      (fun i a => (i.val < K → new.T.isNFComp i.val a ∧ trans a = lowPiece c i.val) ∧
        (i.val = K → new.T.isNFComp K a ∧ trans a = lpInv (UC K (T.part (K - 1) c).1) ∧
          a ≠ new.T.Z) ∧
        (K < i.val → a = new.T.Z))
      (fun i => by
        rcases Nat.lt_trichotomy i.val K with hi | hi | hi
        · obtain ⟨a, _, hac, hta⟩ := hlow i.val hi
          exact ⟨a, fun _ => ⟨hac, hta⟩, fun h => absurd h (Nat.ne_of_lt hi),
            fun h => absurd hi (Nat.lt_asymm h)⟩
        · exact ⟨aK, fun h => absurd hi (Nat.ne_of_lt h), fun _ => ⟨haKc, htaK, haKne⟩,
            fun h => absurd hi (Nat.ne_of_gt h)⟩
        · exact ⟨new.T.Z, fun h => absurd hi (Nat.lt_asymm h), fun h => absurd h (Nat.ne_of_gt hi),
            fun _ => rfl⟩)
    refine ⟨w, fun i => ?_, ?_⟩
    · rcases Nat.lt_trichotomy i.val K with hi | hi | hi
      · exact ((hw i).1 hi).1
      · rw [hi]; exact ((hw i).2.1 hi).1
      · rw [(hw i).2.2 hi]; exact new.T.isNFComp_Z _
    · apply aux_top_eq c hc K hKp w hKlam
      · intro i hi
        have := ((hw i).1 hi).2
        have hc2 := (lowPiece_props c hc i.val).2.2.2.2
        simp only [Contr, TContr] at hc2 ⊢
        rw [this]
        exact hc2
      · intro i hi
        obtain ⟨_, ht, hne⟩ := (hw i).2.1 hi
        refine ⟨hne, ?_⟩
        rw [ht, one_del_lpInv]
        exact UC_spec K hKp _ hdNF hdidx
      · intro i hi
        exact (hw i).2.2 hi

theorem trans_PZ_eq {lam : Nat} (v : new.Vec (new.T lam) lam) :
    trans (new.T.P v new.T.Z) = (transAux v).1 := by
  obtain ⟨p, a, he, _⟩ := aux_principal v
  rw [trans_as_add, he, p_zero_add]
  rfl

theorem trans_surj_aux {lam : Nat} (hlam : 0 < lam) : ∀ (n : Nat) (y : T), degree y ≤ n →
    T.isNF1 y → DeepIdx (lam - 1) y → ∃ a : new.T lam, new.T.isNF a ∧ trans a = y
  | 0, y, hd, _, _ => by
      cases y with
      | Z => exact ⟨new.T.Z, new.T.isNF.z, rfl⟩
      | P p c r => exact absurd (Nat.le_trans (Nat.le_max_left _ _) hd) (Nat.not_succ_le_zero _)
  | n + 1, y, hd, hy, hi => by
      induction y with
      | Z => exact ⟨new.T.Z, new.T.isNF.z, rfl⟩
      | P K c r _ ihr =>
          obtain ⟨hc, hr, hgc, hrh⟩ := T.isNF1_P_inv K c r hy
          obtain ⟨hKl, hcl, hrl⟩ := hi
          have hdeg : degree c ≤ n := Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_max_left _ _) hd)
          have hdr : degree r ≤ n + 1 := Nat.le_trans (Nat.le_max_right _ _) hd
          obtain ⟨w, hw, hwe⟩ := principal_preimage hlam K c
            (.p K c T.Z hc .z hgc (T.Z_le _)) ⟨hKl, hcl, trivial⟩
            (fun y' hd' hy' hi' => trans_surj_aux hlam n y' (Nat.le_trans hd' hdeg) hy' hi')
          obtain ⟨ar, har, htar⟩ := ihr hdr hr hrl
          have hwNF := PZ_isNF w hw
          refine ⟨new.T.P w ar, new.T.isNF.p w ar (fun i => (hw i).1) har (fun i => (hw i).2) ?_, ?_⟩
          · cases har' : ar with
            | Z => exact new.T.Z_le _
            | P w' b' =>
                rw [har'] at har htar
                obtain ⟨hw', _, _⟩ := new.T.isNF_P_inv w' b' har
                have hw'NF := PZ_isNF w' hw'
                have hle : trans (new.T.P w' new.T.Z) ≤ trans (new.T.P w new.T.Z) := by
                  rw [trans_PZ_eq, trans_PZ_eq, hwe, ← trans_P_head w' b', htar]
                  exact hrh
                show new.T.P w' new.T.Z ≤ new.T.P w new.T.Z
                rcases hle with hlt | heq
                · exact Or.inl ((trans_lt_iff _ _ hw'NF hwNF).mpr hlt)
                · rw [trans_injective_NF _ _ hw'NF hwNF heq]
                  exact new.T.le_refl _
          · rw [trans_as_add, hwe, p_zero_add, htar]

end LegacyTranslation

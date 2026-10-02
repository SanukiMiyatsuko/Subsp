import Subsp.old.stop_good_target

/-! Normal forms and order preservation of the legacy translation on indexed normal forms. -/

namespace LegacyTranslation

open T

theorem SumAll_and3 (P1 P2 P3 : Nat → T → Prop) :
    ∀ t, SumAll P1 t → SumAll P2 t → SumAll P3 t →
      SumAll (fun p c => P1 p c ∧ P2 p c ∧ P3 p c) t
  | .Z, _, _, _ => trivial
  | .P _ _ r, ⟨h1, r1⟩, ⟨h2, r2⟩, ⟨h3, r3⟩ => ⟨⟨h1, h2, h3⟩, SumAll_and3 P1 P2 P3 r r1 r2 r3⟩

theorem part_add_distrib (n : Nat) : ∀ a b : T,
    T.part n (T.add a b) =
      (T.add (T.part n a).1 (T.part n b).1, T.add (T.part n a).2 (T.part n b).2)
  | .Z, b => by simp only [T.part, zero_add]
  | .P p c r, b => by
      rw [T.P_add_eq]
      have ih := part_add_distrib n r b
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true, ih, T.P_add_eq]
      · simp only [T.part, hp, ite_false, ih, T.P_add_eq]

theorem part_card_times (n : Nat) : ∀ s : T,
    (T.part n (T.card_times n s)).1 = (T.part n s).1 ∧
      (T.part n (T.card_times n s)).2 = T.card_times n (T.part n s).2
  | .Z => ⟨rfl, rfl⟩
  | .P p a r => by
      have ih := part_card_times n r
      rw [card_times_P]
      by_cases hp : p ≤ n
      · have hm : max p n = n := Nat.max_eq_right hp
        simp only [T.part, hm, Nat.le_refl, hp, ite_true, ih, card_times_P]
        exact ⟨trivial, trivial⟩
      · have hm : max p n = p := Nat.max_eq_left (by omega)
        have hca : cardArg n p a = a := by
          unfold cardArg
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp only [T.part, hm, hp, ite_false, ih, hca]
        exact ⟨trivial, trivial⟩

theorem part_one_del_fst (n : Nat) (t : T) : (T.part n (T.one_del t)).1 = (T.part n t).1 := by
  cases t with
  | Z => rfl
  | P p a b =>
      cases p with
      | zero => cases a <;> simp [T.one_del, T.part]
      | succ p => rfl

theorem G1_part_snd_subset (u n : Nat) : ∀ s x : T, x ∈ T.G1 u (T.part n s).2 → x ∈ T.G1 u s
  | .Z, x, hx => hx
  | .P p a r, x, hx => by
      have ih := G1_part_snd_subset u n r x
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true] at hx
        by_cases hu : u ≤ p
        · simp only [T.G1, hu, ite_true, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (ih hx)
        · simp only [T.G1, hu, ite_false] at hx ⊢
          exact ih hx
      · simp only [T.part, hp, ite_false] at hx
        by_cases hu : u ≤ p <;> simp [T.G1, hu, ih hx]

/-- The low part of a principal argument is below the principal term. -/
theorem part_snd_lt_wrap (K : Nat) (X : T) (hg : ∀ y ∈ T.G1 K X, y < X) :
    (T.part K X).2 < T.P K X T.Z := by
  have hi := part_second_index K X
  cases hp : (T.part K X).2 with
  | Z => exact T.Lt.Z_lt_P _ _ _
  | P q d e =>
      rw [hp] at hi
      cases hi with
      | p _ _ _ hq _ =>
          rcases Nat.eq_or_lt_of_le hq with rfl | hq
          · apply T.Lt.p_mid
            apply hg d
            apply G1_part_snd_subset q q X d
            rw [hp]
            simp [T.G1]
          · exact T.Lt.p_head _ _ _ _ _ _ hq

/-! Bounds for the auxiliary vector translation. -/

def CoordHyp {lam : Nat} (u : Nat) (C : T) (i : Nat) (x : new.T lam) : Prop :=
  (∀ y ∈ T.G1 u (T.card_times i (T.early_collapse i (trans x))), y < C) ∧
  (u ≤ i → ∀ y ∈ T.G1 u (T.card_times i (T.one_del (trans x))), y < C) ∧
  (i = 0 → ∀ y ∈ T.G1 u (T.early_collapse 0 (trans x)), y < C) ∧
  (i = 0 → u = 0 → ∀ y ∈ T.G1 u (trans x), y < C)

theorem aux_support_bounded {lam : Nat} (u : Nat) (C : T) : ∀ {k : Nat}
    (v : new.Vec (new.T lam) k),
    (∀ i : Fin k, CoordHyp u C i.val (v.idx i)) →
    (∀ y ∈ T.G1 u (transAux v).2, y < C) ∧
      ∀ p a, (transAux v).1 = T.P p a T.Z → u ≤ p → ∀ y ∈ T.G1 u a, y < C
  | _, .nil, _ => by
      refine ⟨fun y hy => by simp [transAux, T.G1] at hy, ?_⟩
      intro p a he _ y hy
      change T.P 0 T.Z T.Z = T.P p a T.Z at he
      cases he
      cases hy
  | _, .snoc k v a, hv => by
      have hlast : CoordHyp u C k a := by
        simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using hv (Fin.last k)
      have hpre : ∀ i : Fin k, CoordHyp u C i.val (v.idx i) := by
        intro i
        simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using hv i.castSucc
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          refine ⟨hlast.2.2.1 rfl, ?_⟩
          intro p b he hup y hy
          cases he
          exact hlast.2.2.2 rfl (Nat.eq_zero_of_le_zero hup) y hy
      | succ k =>
          have ih := aux_support_bounded u C v hpre
          refine ⟨?_, ?_⟩
          · rw [aux_lower_snoc]
            intro y hy
            rw [G1_add, List.mem_append] at hy
            rcases hy with hy | hy
            · exact hlast.1 y hy
            · exact ih.1 y hy
          · intro p b he hup y hy
            by_cases haz : a = new.T.Z
            · subst a
              rw [aux_zero_tail] at he
              exact ih.2 p b he hup y hy
            · rw [aux_head_snoc v a haz] at he
              cases he
              rw [G1_add, List.mem_append] at hy
              rcases hy with hy | hy
              · exact hlast.2.1 hup y hy
              · exact ih.1 y hy

theorem coord_hyp_of {lam : Nat} (u : Nat) (C : T) (i : Nat) (x : new.T lam)
    (hx : GoodAt i x)
    (hxC : u ≤ i → trans x < C)
    (hsum : u ≤ i → SumAll (CardCond i u (· < C)) (trans x)) :
    CoordHyp u C i x := by
  have hR : ∀ a b : T, a ≤ b → b < C → a < C := fun a b h1 h2 => lt_of_le_of_lt_thm T _ _ _ h1 h2
  have hec := early_collapse_closed i (trans x) hx.1 hx.2
  by_cases hui : u ≤ i
  · refine ⟨early_card_support_bounded i u hui (· < C) hR (trans x) hx.1 (hxC hui) (hsum hui),
      fun _ => card_times_support_bounded i u hui (· < C) hR _ (one_del_NF _ hx.1)
        (hR _ _ (one_del_le _ hx.1) (hxC hui)) (SumAll_one_del _ _ (hsum hui)), ?_, ?_⟩
    · intro hi0 y hy
      subst i
      have hu0 : u = 0 := Nat.eq_zero_of_le_zero hui
      subst u
      rcases early_collapse_support_exact 0 0 (trans x) (Nat.le_refl 0) hx.1 y hy with h | h
      · rw [h]
        exact hR _ _ (part_first_le 0 _ hx.1) (hxC hui)
      · exact lt_trans_thm _ _ _ (hx.2 y h) (hxC hui)
    · intro hi0 hu0 y hy
      subst i
      subst hu0
      exact lt_trans_thm _ _ _ (hx.2 y hy) (hxC hui)
  · have hui' : i < u := Nat.lt_of_not_le hui
    refine ⟨?_, fun h => absurd h hui, ?_, fun hi0 hu0 => absurd (hu0 ▸ hi0 ▸ Nat.le_refl 0) hui⟩
    · have hidx := card_times_index i i _ hec.2
      rw [Nat.max_self] at hidx
      rw [index_Prop1_G1_empty i _ hidx u hui']
      intro y hy
      cases hy
    · intro hi0
      subst i
      rw [index_Prop1_G1_empty 0 _ hec.2 u hui']
      intro y hy
      cases hy

/-- The high part of a principal argument is the high part of its top coordinate. -/
theorem aux_head_high {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    VecGood v →
    ∀ p a, (transAux v).1 = T.P p a T.Z →
      (T.part p a).1 = T.Z ∨
        ∃ i : Fin k, i.val = p ∧ (T.part p a).1 = (T.part p (trans (v.idx i))).1
  | _, .nil, _ => by
      intro p a he
      change T.P 0 T.Z T.Z = T.P p a T.Z at he
      cases he
      exact Or.inl rfl
  | _, .snoc k v a, hv => by
      intro p b he
      have hpre := VecGood_prefix v a hv
      have hlast := VecGood_last v a hv
      cases k with
      | zero =>
          cases v
          rw [aux_single] at he
          cases he
          exact Or.inr ⟨Fin.last 0, rfl, by simp [new.Vec.idx]⟩
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            rw [aux_zero_tail] at he
            rcases aux_head_high v hpre p b he with h | ⟨i, hi, h⟩
            · exact Or.inl h
            · refine Or.inr ⟨i.castSucc, hi, ?_⟩
              simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using h
          · rw [aux_head_snoc v a haz] at he
            cases he
            apply Or.inr
            refine ⟨Fin.last (k + 1), rfl, ?_⟩
            have hlow := aux_lower_closed v hpre
            rw [part_add_distrib, part_of_index (k + 1) _
              (Rank1Termination.index_mono (by omega) _ hlow.2.1), T.add_Z,
              (part_card_times (k + 1) _).1, part_one_del_fst]
            simp [new.Vec.idx]

/-! Bounds for supports of principal arguments. -/

theorem deep_bound {lam : Nat} (N : Nat)
    (hgood : ∀ s : new.T lam, new.T.size s < N → ∀ u, new.T.isNFComp u s → GoodAt u s)
    (u : Nat) (C : T) :
    ∀ x : new.T lam, new.T.size x ≤ N → new.T.isNF x →
      (∀ z ∈ new.T.Gi u x, trans z < C) →
      SumAll (fun p c => u ≤ p → ∀ y ∈ T.G1 u c, y < C) (trans x) ∧
        SumAll (fun p c => u ≤ p → (T.part p c).1 = T.Z ∨ (T.part p c).1 < C) (trans x) := by
  intro x
  induction x using (measure new.T.size).wf.induction with
  | h x ih =>
      intro hsz hx hsupp
      cases x with
      | Z => exact ⟨trivial, trivial⟩
      | P w b =>
          obtain ⟨hw, hb, _⟩ := new.T.isNF_P_inv w b hx
          have hcoordSz (i : Fin lam) : new.T.size (w.idx i) < N :=
            Nat.lt_of_lt_of_le (new.T.idx_size_lt_P w b i) hsz
          have hgw (i : Fin lam) : GoodAt i.val (w.idx i) := hgood _ (hcoordSz i) i.val (hw i)
          have hvg : VecGood w := hgw
          obtain ⟨K, X, he, _⟩ := aux_principal w
          have htr : trans (new.T.P w b) = T.P K X (trans b) := by
            rw [trans_as_add, he, p_zero_add]
          have ihb := ih b (new.T.add_size_lt_P w b)
            (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P w b)) hsz) hb
            (fun z hz => hsupp z (source_tail_support_mem_Gi u w b z hz))
          rw [htr]
          -- coordinate hypotheses
          have hcoord (i : Fin lam) : CoordHyp u C i.val (w.idx i) := by
            apply coord_hyp_of u C i.val (w.idx i) (hgw i)
            · intro hui
              exact hsupp _ (source_coord_mem_Gi u w b i hui)
            · intro hui
              have ihi := ih (w.idx i) (new.T.idx_size_lt_P w b i)
                (Nat.le_of_lt (hcoordSz i)) (hw i).1
                (fun z hz => hsupp z (source_coord_support_mem_Gi u w b z i hui hz))
              have hself := SumAll_G1_self i.val (trans (w.idx i))
              have h1 : SumAll (fun p c => i.val ≤ p → c < C) (trans (w.idx i)) := by
                apply SumAll_mono _ _ _ _ hself
                intro p c h hip
                exact lt_trans_thm _ _ _ ((hgw i).2 c (h hip))
                  (hsupp _ (source_coord_mem_Gi u w b i hui))
              apply SumAll_mono _ _ _ _ (SumAll_and3 _ _ _ _ h1 ihi.1 ihi.2)
              intro p c ⟨h1, h2, h3⟩
              refine ⟨h1, h2, fun hup _ => ?_⟩
              rcases h3 hup with h | h
              · rw [h]
                exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le _)
                  (hsupp _ (source_coord_mem_Gi u w b i hui))
              · exact h
          have hvb := aux_support_bounded u C w hcoord
          refine ⟨⟨hvb.2 K X he, ihb.1⟩, ⟨?_, ihb.2⟩⟩
          intro hup
          rcases aux_head_high w hvg K X he with h | ⟨i, hi, h⟩
          · exact Or.inl h
          · apply Or.inr
            rw [h]
            subst hi
            exact lt_of_le_of_lt_thm T _ _ _ (part_first_le _ _ (hgw i).1)
              (hsupp _ (source_coord_mem_Gi u w b i hup))

/-! Arguments of principal summands. -/

theorem summand_args_lt {lam : Nat} (N : Nat)
    (hgood : ∀ s : new.T lam, new.T.size s < N → ∀ u, new.T.isNFComp u s → GoodAt u s)
    (u : Nat) (TS : T) (hTS : T.isNF1 TS) (hTSne : T.Z < TS) :
    ∀ b : new.T lam, new.T.size b ≤ N → new.T.isNF b →
      (∀ z ∈ new.T.Gi u b, trans z < TS) →
      (∀ p c, IsSummand p c (trans b) → IsSummand p c TS) →
      SumAll (fun p c => u ≤ p → c < TS) (trans b) := by
  intro b
  induction b using (measure new.T.size).wf.induction with
  | h b ih =>
      intro hsz hb hsupp hsumm
      cases b with
      | Z => exact trivial
      | P w b =>
          obtain ⟨hw, hb', _⟩ := new.T.isNF_P_inv w b hb
          have hgw (i : Fin lam) : GoodAt i.val (w.idx i) :=
            hgood _ (Nat.lt_of_lt_of_le (new.T.idx_size_lt_P w b i) hsz) i.val (hw i)
          have hvg : VecGood w := hgw
          obtain ⟨K, X, he, _⟩ := aux_principal w
          have htr : trans (new.T.P w b) = T.P K X (trans b) := by
            rw [trans_as_add, he, p_zero_add]
          have hhead := aux_head_closed w hvg
          rw [he] at hhead
          obtain ⟨hX, _, hgX, _⟩ := T.isNF1_P_inv K X T.Z hhead
          rw [htr] at hsumm ⊢
          refine ⟨fun hup => ?_, ih b (new.T.add_size_lt_P w b)
            (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P w b)) hsz) hb'
            (fun z hz => hsupp z (source_tail_support_mem_Gi u w b z hz))
            (fun p c hs => hsumm p c (Or.inr hs))⟩
          have hsum : IsSummand K X TS := hsumm K X (Or.inl ⟨rfl, rfl⟩)
          have hlow := part_snd_lt_wrap K X hgX
          rcases aux_head_high w hvg K X he with h | ⟨i, hi, h⟩
          · exact summand_arg_lt K X T.Z TS hTS hX .z hsum hTSne (by rw [h]; rfl) hlow
          · subst hi
            exact summand_arg_lt _ X (trans (w.idx i)) TS hTS hX (hgw i).1 hsum
              (hsupp _ (source_coord_mem_Gi u w b i hup)) h.symm hlow

/-! The main simultaneous induction. -/

theorem good_all {lam : Nat} : ∀ s : new.T lam,
    (new.T.isNF s → T.isNF1 (trans s)) ∧ (∀ u, new.T.isNFComp u s → GoodAt u s) := by
  intro s
  induction s using (measure new.T.size).wf.induction with
  | h s ih =>
      have hgood : ∀ z : new.T lam, new.T.size z < new.T.size s →
          ∀ u, new.T.isNFComp u z → GoodAt u z := fun z hz => (ih z hz).2
      have hNF : new.T.isNF s → T.isNF1 (trans s) := by
        intro hs
        cases s with
        | Z => exact T.isNF1.z
        | P v a => exact NF_step v a hs (fun z hz => (ih z hz).1) hgood
      refine ⟨hNF, fun u hs => ⟨hNF hs.1, ?_⟩⟩
      have hsupp : ∀ z ∈ new.T.Gi u s, trans z < trans s := by
        intro z hz
        exact order_preserve_bounded (new.T.size s) hgood z s
          (Nat.le_of_lt (new.T.Gi_size_lt u s z hz)) (Nat.le_refl _)
          (new.T.isNF_Gi s hs.1 u z hz) hs.1 (hs.2 z hz)
      cases s with
      | Z => intro y hy; cases hy
      | P v a =>
          have hne : T.Z < trans (new.T.P v a) := by
            obtain ⟨K, X, he, _⟩ := aux_principal v
            rw [trans_as_add, he, p_zero_add]
            exact T.Lt.Z_lt_P _ _ _
          have h1 := summand_args_lt (new.T.size (new.T.P v a)) hgood u _ (hNF hs.1) hne
            (new.T.P v a) (Nat.le_refl _) hs.1 hsupp (fun _ _ h => h)
          have h2 := (deep_bound (new.T.size (new.T.P v a)) hgood u _ (new.T.P v a)
            (Nat.le_refl _) hs.1 hsupp).1
          apply G1_of_SumAll u (· < trans (new.T.P v a))
          apply SumAll_mono _ _ _ _ (SumAll_and3 _ _ _ _ h1 h2 h2)
          intro p c ⟨h1, h2, _⟩ hup
          exact ⟨h1 hup, h2 hup⟩

theorem trans_isNF1 {lam : Nat} (s : new.T lam) (hs : new.T.isNF s) : T.isNF1 (trans s) :=
  (good_all s).1 hs

theorem trans_good {lam : Nat} (u : Nat) (s : new.T lam) (hs : new.T.isNFComp u s) :
    GoodAt u s :=
  (good_all s).2 u hs

theorem trans_lt_of_lt {lam : Nat} (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t)
    (h : s < t) : trans s < trans t :=
  order_preserve_bounded (max (new.T.size s) (new.T.size t))
    (fun z _ u hz => trans_good u z hz) s t (Nat.le_max_left _ _) (Nat.le_max_right _ _) hs ht h

theorem trans_lt_iff {lam : Nat} (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
    s < t ↔ trans s < trans t := by
  refine ⟨trans_lt_of_lt s t hs ht, fun h => ?_⟩
  rcases new.T_total s t with h' | h' | h'
  · exact h'
  · exact False.elim (lt_asymm_thm h (trans_lt_of_lt t s ht hs h'))
  · subst h'
    exact False.elim (lt_irrefl_thm _ h)

theorem trans_injective_NF {lam : Nat} (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t)
    (h : trans s = trans t) : s = t := by
  rcases new.T_total s t with h' | h' | h'
  · have := trans_lt_of_lt s t hs ht h'
    rw [h] at this
    exact False.elim (lt_irrefl_thm _ this)
  · have := trans_lt_of_lt t s ht hs h'
    rw [h] at this
    exact False.elim (lt_irrefl_thm _ this)
  · exact h'

end LegacyTranslation

import Subsp.old.stop_reverse
import Subsp.old.stop_source_dim

/-! Reverse transfer, assembled by downward induction on the support level. -/

namespace LegacyTranslation

open T

theorem G1_summand_mem (u p : Nat) (a : T) (hup : u ≤ p) : ∀ t : T, IsSummand p a t →
    a ∈ T.G1 u t
  | .Z, h => h.elim
  | .P q b r, h => by
      rcases h with ⟨rfl, rfl⟩ | h
      · simp [T.G1, hup]
      · have := G1_summand_mem u p a hup r h
        by_cases hq : u ≤ q <;> simp [T.G1, hq, this]

/-- Visibility invariant: arguments of principal summands are dominated by `V`. -/
def SInv {lam : Nat} (u : Nat) (V : List T) : new.T lam → Prop
  | .Z => True
  | .P w b =>
      (∀ p a, (transAux w).1 = T.P p a T.Z → u ≤ p →
        (∀ y ∈ T.G1 u a, DomBy V y) ∧
          (p = u → (T.part u a).1 ≠ T.Z → DomBy V (T.part u a).1)) ∧
      SInv u V b

theorem SInv_of_summands {lam : Nat} (u : Nat) (V : List T) : ∀ x : new.T lam,
    (∀ p a, IsSummand p a (trans x) → u ≤ p →
      (∀ y ∈ T.G1 u a, DomBy V y) ∧
        (p = u → (T.part u a).1 ≠ T.Z → DomBy V (T.part u a).1)) →
    SInv u V x
  | .Z, _ => trivial
  | .P w b, h => by
      obtain ⟨X, he, htr⟩ := trans_P_headIdx w b
      refine ⟨fun p a he' hup => ?_,
        SInv_of_summands u V b (fun p a hs hup => h p a (by rw [htr]; exact Or.inr hs) hup)⟩
      rw [he] at he'
      injection he' with h1 h2 _
      subst h1
      subst h2
      exact h _ _ (by rw [htr]; exact Or.inl ⟨rfl, rfl⟩) hup

theorem SInv_top {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A) :
    SInv u (T.G1 u (trans A)) A := by
  have hAnf := trans_isNF1 A hA
  apply SInv_of_summands
  intro p a hs hup
  have hmem := G1_summand_mem u p a hup _ hs
  refine ⟨fun y hy => DomBy_of_mem _ _ (G1_summand_subset u p a hup _ hs y hy),
    fun _ _ => ⟨a, hmem, part_first_le u a (IsSummand_NF p a _ hAnf hs).1⟩⟩

theorem deepDom {lam : Nat} (u : Nat) (V : List T) {q c : new.T lam} (hr : Reach u q c) :
    new.T.isNF q → SInv u V q → (T.part u (trans c)).1 ≠ T.Z →
      DomBy V (T.part u (trans c)).1 := by
  induction hr with
  | here w b i hi =>
      intro hq hinv hne
      obtain ⟨hw, _, _⟩ := new.T.isNF_P_inv w b hq
      have hvg : VecGood w := fun i => trans_good i.val (w.idx i) (hw i)
      obtain ⟨p, a, he, _⟩ := aux_principal w
      have hci := hw i
      rw [hi] at hci
      have hcg := trans_good u (w.idx i) hci
      rcases Nat.lt_trichotomy p u with hp | hp | hp
      · have hz := aux_above_zero w p a he i (by omega)
        rw [hz] at hne
        exact False.elim (hne rfl)
      · subst hp
        have heq := aux_head_high_eq w hvg p a he i hi
        rw [← heq] at hne ⊢
        exact (hinv.1 p a he (Nat.le_refl _)).2 rfl hne
      · have hcon := (aux_contr_G1 u w).2 p a he
        have hd := high_dom_early_collapse u (trans (w.idx i)) hcg.1 hne
        have hdomA : DomBy (T.G1 u a) (T.part u (trans (w.idx i))).1 := by
          by_cases hu0 : u = 0
          · subst hu0
            exact DomBy_mono _ _ (fun v hv => hcon.1 i (by omega) v
              (by simpa [Contr, hi] using hv)) _ hd.1
          · exact DomBy_mono _ _ (fun v hv => hcon.1 i (by omega) v
              (by simpa [Contr, hi, hu0] using hv)) _ hd.2
        exact DomBy_trans _ _ (fun v hv => (hinv.1 p a he (by omega)).1 v hv) _ hdomA
  | tail w b c _ ih =>
      intro hq hinv hne
      exact ih (new.T.isNF_P_inv w b hq).2.1 hinv.2 hne
  | deep w b c i hi hr ih =>
      intro hq hinv hne
      obtain ⟨hw, _, _⟩ := new.T.isNF_P_inv w b hq
      obtain ⟨p, a, he, _⟩ := aux_principal w
      have hne' : w.idx i ≠ new.T.Z := Reach_ne_Z u hr
      have hip : i.val ≤ p := by
        rcases Nat.lt_or_ge p i.val with h | h
        · exact False.elim (hne' (aux_above_zero w p a he i h))
        · exact h
      have hg := trans_good i.val (w.idx i) (hw i)
      have hcon := (aux_contr_G1 u w).2 p a he
      have hdomA := hinv.1 p a he (by omega)
      apply ih (hw i).1 _ hne
      apply SInv_of_summands u V (w.idx i)
      intro p' a' hs hup'
      have hi0 : i.val ≠ 0 := by omega
      rcases Nat.lt_or_ge i.val p with hlt | hge
      · have hsub : ∀ v ∈ T.G1 u (T.card_times i.val (T.early_collapse i.val (trans (w.idx i)))),
            v ∈ T.G1 u a := fun v hv => hcon.1 i hlt v (by simpa [Contr, hi0] using hv)
        refine ⟨fun y hy => ?_, fun hpu hne2 => ?_⟩
        · exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (early_card_summand_dom i.val u p' (trans (w.idx i)) a' hg.1 hg.2 hs hup'
              (by omega) y hy))
        · subst p'
          exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (early_card_summand_high_dom i.val u (trans (w.idx i)) a' hg.1 hs (by omega) hne2))
      · have hip' : i.val = p := by omega
        have hcon2 := hcon.2.1 i hip'
        rw [← hip'] at hcon2
        have hsub : ∀ v ∈ T.G1 u (T.card_times i.val (T.one_del (trans (w.idx i)))),
            v ∈ T.G1 u a := fun v hv => hcon2 v (by simpa [TopContr, hi0] using hv)
        refine ⟨fun y hy => ?_, fun hpu hne2 => ?_⟩
        · exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (one_del_card_summand_dom i.val u p' (trans (w.idx i)) a' hg.1 hs hup'
              (by omega) y hy))
        · subst p'
          exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (one_del_card_summand_high_dom i.val u (trans (w.idx i)) a' hg.1 hs (by omega) hne2))

/-! Suffixes of a source sum. -/

inductive Suffix {lam : Nat} : new.T lam → new.T lam → Prop where
  | refl (x : new.T lam) : Suffix x x
  | step (w : new.Vec (new.T lam) lam) (b x : new.T lam) : Suffix x b → Suffix x (new.T.P w b)

theorem Suffix_tail {lam : Nat} {w : new.Vec (new.T lam) lam} {b A : new.T lam}
    (h : Suffix (new.T.P w b) A) : Suffix b A := by
  generalize hx : new.T.P w b = x at h
  induction h with
  | refl => subst hx; exact .step w b b (.refl b)
  | step w' b' x _ ih => exact .step w' b' b (ih hx)

theorem Suffix_summand {lam : Nat} {x A : new.T lam} (h : Suffix x A) :
    ∀ p a, IsSummand p a (trans x) → IsSummand p a (trans A) := by
  induction h with
  | refl => exact fun _ _ h => h
  | step w b x _ ih =>
      intro p a hs
      obtain ⟨X, _, htr⟩ := trans_P_headIdx w b
      rw [htr]
      exact Or.inr (ih p a hs)

theorem Suffix_srcPart_size {lam : Nat} (j : Nat) {x A : new.T lam} (h : Suffix x A) :
    new.T.size (srcPart j x).1 ≤ new.T.size (srcPart j A).1 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step w b x _ ih =>
      by_cases hj : j < headIdx w
      · simp only [srcPart, hj, ite_true, new.T.size]; omega
      · simp only [srcPart, hj, ite_false]; exact ih

theorem Reach_size {lam : Nat} (u : Nat) {x c : new.T lam} (h : Reach u x c) :
    new.T.size c < new.T.size x := by
  induction h with
  | here w b i _ => exact new.T.idx_size_lt_P w b i
  | tail w b c _ ih => exact Nat.lt_trans ih (new.T.add_size_lt_P w b)
  | deep w b c i _ _ ih => exact Nat.lt_trans ih (new.T.idx_size_lt_P w b i)

theorem Z_lt_of_ne {lam : Nat} (s : new.T lam) (h : s ≠ new.T.Z) : new.T.Z < s := by
  cases s with
  | Z => exact False.elim (h rfl)
  | P w b => rfl

/-! The key comparison: reached index-`u` coordinates are below the ambient term. -/

theorem reach_lt {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A)
    (hgood : ∀ y ∈ T.G1 u (trans A), y < trans A) (c : new.T lam) (hc : Reach u A c) :
    c < A := by
  have hAnf := trans_isNF1 A hA
  have hcnf : new.T.isNF c := (Reach_comp u hc hA).1.1
  have hcnf1 := trans_isNF1 c hcnf
  have hAne : new.T.Z < A := Z_lt_of_ne A (Reach_ne_Z u hc)
  have hdom : (T.part u (trans c)).1 ≠ T.Z → (T.part u (trans c)).1 < trans A := by
    intro hne
    obtain ⟨v, hv, hle⟩ := deepDom u _ hc hA (SInv_top u A hA) hne
    exact lt_of_le_of_lt_thm T _ _ _ hle (hgood v hv)
  have prefixArg : ∀ (x : new.T lam), Suffix x A → ∀ w b, x = new.T.P w b →
      u < headIdx w → new.T.size c < new.T.size (srcPart u x).1 → c < A := by
    intro x hsx w b hx hu hsz
    obtain ⟨X, _, htr⟩ := trans_P_headIdx w b
    have hsum : IsSummand (headIdx w) X (trans A) :=
      Suffix_summand hsx _ _ (by rw [hx, htr]; exact Or.inl ⟨rfl, rfl⟩)
    have hhead : T.P (headIdx w) X T.Z ≤ trans A :=
      partial_order.trans _ _ _ (summand_le_head _ _ _ hAnf hsum) (head_le_self _)
    have hsA := Suffix_srcPart_size u hsx
    have hsc := srcPart_size u c
    rcases new.T_total c A with h | h | h
    · exact h
    · exfalso
      have htr' := trans_lt_of_lt A c hA hcnf h
      by_cases hz : (T.part u (trans c)).1 = T.Z
      · have hcp : trans c = (T.part u (trans c)).2 := by
          have := part_add u _ hcnf1
          rw [hz, zero_add] at this
          exact this.symm
        have hidx := part_second_index u (trans c)
        rw [← hcp] at hidx
        have hlt : trans c < trans A :=
          lt_of_lt_of_le_thm T _ _ _ (index_Prop1_lt_succ u _ hidx)
            (partial_order.trans _ _ _ (head_base_le (u + 1) _ X hu) hhead)
        exact lt_asymm_thm hlt htr'
      · have hH := hdom hz
        rcases part_lt_cases u (trans A) (trans c) hAnf hcnf1 htr' with h1 | ⟨h1, _⟩
        · have hHnf := (part_NF u (trans c) hcnf1).1
          have : trans A < (T.part u (trans c)).1 :=
            lt_of_part_lt_cases u _ _ hAnf hHnf (Or.inl (by rw [part_first_fixed]; exact h1))
          exact lt_asymm_thm this hH
        · have hs1 : (srcPart u A).1 = (srcPart u c).1 := by
            apply trans_injective_NF _ _ (srcPart_NF u A hA).1 (srcPart_NF u c hcnf).1
            rw [srcPart_trans, srcPart_trans, h1]
          rw [hs1] at hsA
          omega
    · exfalso
      subst h
      omega
  have main : ∀ x c', Reach u x c' → c' = c → Suffix x A → c < A := by
    intro x c' hr
    induction hr with
    | here w b i hi =>
        intro hceq hsx
        subst hceq
        obtain ⟨p, a, he, _⟩ := aux_principal w
        have hhp := headIdx_eq w p a he
        rcases Nat.lt_trichotomy p u with hp | hp | hp
        · rw [aux_above_zero w p a he i (by omega)]
          exact hAne
        · subst hp
          obtain ⟨X, he', htr⟩ := trans_P_headIdx w b
          rw [he, hhp] at he'
          injection he' with _ hXa _
          subst a
          have hsum : IsSummand p X (trans A) :=
            Suffix_summand hsx _ _ (by rw [htr, hhp]; exact Or.inl ⟨rfl, rfl⟩)
          have hXA : X < trans A := hgood X (G1_summand_mem p p X (Nat.le_refl _) _ hsum)
          have hhead : T.P p X T.Z ≤ trans A :=
            partial_order.trans _ _ _ (summand_le_head _ _ _ hAnf hsum) (head_le_self _)
          apply (trans_lt_iff _ _ hcnf hA).mpr
          by_cases hp0 : p = 0
          · subst hp0
            cases lam with
            | zero => exact i.elim0
            | succ k =>
                have hX := aux_head_countable w X he
                have hi0 : i = ⟨0, Nat.zero_lt_succ k⟩ := Fin.eq_of_val_eq hi
                rw [hi0, ← hX]
                exact hXA
          · have hcon := ((aux_contr_G1 p w).2 p X he).2.2 i hi (Nat.pos_of_ne_zero hp0)
            simp only [TopContr, hp0, ite_false] at hcon
            have hle1 := partial_order.trans _ _ _
              (card_times_self_le p _ (one_del_NF _ hcnf1)) hcon
            cases htc : trans (w.idx i) with
            | Z => exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le _) hXA
            | P q d e =>
                rw [htc] at hle1
                cases q with
                | zero =>
                    cases d with
                    | Z =>
                        exact lt_of_lt_of_le_thm T _ _ _
                          (T.Lt.p_head _ _ _ _ _ _ (Nat.pos_of_ne_zero hp0)) hhead
                    | P _ _ _ => exact lt_of_le_of_lt_thm T _ _ _ hle1 hXA
                | succ q => exact lt_of_le_of_lt_thm T _ _ _ hle1 hXA
        · have hj : u < headIdx w := by rw [hhp]; exact hp
          apply prefixArg (new.T.P w b) hsx w b rfl hj
          have hlt := new.Vec.idx_size_lt w i
          simp only [srcPart, hj, ite_true, new.T.size]
          omega
    | tail w b c'' _ ih =>
        intro hceq hsx
        exact ih hceq (Suffix_tail hsx)
    | deep w b c'' i hi hr _ =>
        intro hceq hsx
        subst hceq
        obtain ⟨p, a, he, _⟩ := aux_principal w
        have hhp := headIdx_eq w p a he
        have hne' : w.idx i ≠ new.T.Z := Reach_ne_Z u hr
        have hip : i.val ≤ p := by
          rcases Nat.lt_or_ge p i.val with h | h
          · exact False.elim (hne' (aux_above_zero w p a he i h))
          · exact h
        have hsz := Reach_size u hr
        have hj : u < headIdx w := by rw [hhp]; omega
        apply prefixArg (new.T.P w b) hsx w b rfl hj
        have hlt := new.Vec.idx_size_lt w i
        simp only [srcPart, hj, ite_true, new.T.size]
        omega
  exact main A c hc rfl (.refl A)

theorem rt_step {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A)
    (hgood : ∀ y ∈ T.G1 u (trans A), y < trans A) (h1 : new.T.isNFComp (u + 1) A) :
    new.T.isNFComp u A := by
  refine ⟨hA, fun z hz => ?_⟩
  rcases Gi_split u A z hz with h | ⟨c, hc, hzc⟩
  · exact h1.2 z h
  · have hclt := reach_lt u A hA hgood c hc
    obtain ⟨hcc, _⟩ := Reach_comp u hc hA
    rcases hzc with rfl | hzc
    · exact hclt
    · exact strict_partial_order.trans _ _ _ (hcc.2 z hzc) hclt

theorem reverse_transfer_aux {lam : Nat} : ∀ (k u : Nat), u + k = lam →
    ∀ A : new.T lam, new.T.isNF A →
      (∀ y ∈ T.G1 u (trans A), y < trans A) → new.T.isNFComp u A
  | 0, u, h, A, hA, _ => new.T.isNFComp_above_dim u (by omega) A hA
  | k + 1, u, h, A, hA, hg =>
      rt_step u A hA hg (reverse_transfer_aux k (u + 1) (by omega) A hA
        (fun y hy => hg y (G1_antitone u (u + 1) (Nat.le_succ u) _ y hy)))

/-- Buchholz goodness of the translation implies indexed goodness of the source. -/
theorem reverse_transfer {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A)
    (hg : ∀ y ∈ T.G1 u (trans A), y < trans A) : new.T.isNFComp u A := by
  by_cases hu : lam ≤ u
  · exact new.T.isNFComp_above_dim u hu A hA
  · exact reverse_transfer_aux (lam - u) u (by omega) A hA hg

end LegacyTranslation

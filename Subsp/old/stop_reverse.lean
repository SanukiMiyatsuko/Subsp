import Subsp.old.stop_reverse_target

/-! Reverse transfer: Buchholz goodness of a translation implies indexed goodness of the
source term. -/

namespace LegacyTranslation

open T

/-! Coordinates of index `u` reached through coordinates of larger index. -/

inductive Reach {lam : Nat} (u : Nat) : new.T lam → new.T lam → Prop where
  | here (w : new.Vec (new.T lam) lam) (b : new.T lam) (i : Fin lam) (hi : i.val = u) :
      Reach u (new.T.P w b) (w.idx i)
  | tail (w : new.Vec (new.T lam) lam) (b c : new.T lam) :
      Reach u b c → Reach u (new.T.P w b) c
  | deep (w : new.Vec (new.T lam) lam) (b c : new.T lam) (i : Fin lam) (hi : u + 1 ≤ i.val) :
      Reach u (w.idx i) c → Reach u (new.T.P w b) c

theorem Gi_split {lam : Nat} (u : Nat) : ∀ x z : new.T lam, z ∈ new.T.Gi u x →
    z ∈ new.T.Gi (u + 1) x ∨ ∃ c, Reach u x c ∧ (z = c ∨ z ∈ new.T.Gi u c) := by
  intro x
  induction x using (measure new.T.size).wf.induction with
  | h x ih =>
      intro z hz
      cases x with
      | Z => cases hz
      | P w b =>
          rcases (new.T.mem_Gi_P u w b z).mp hz with ⟨i, hui, hzi⟩ | hzb
          · rcases Nat.eq_or_lt_of_le hui with hiu | hiu
            · exact Or.inr ⟨w.idx i, .here w b i hiu.symm, hzi⟩
            · rcases hzi with rfl | hzi
              · exact Or.inl ((new.T.mem_Gi_P (u + 1) w b _).mpr (Or.inl ⟨i, hiu, Or.inl rfl⟩))
              · rcases ih (w.idx i) (new.T.idx_size_lt_P w b i) z hzi with h | ⟨c, hc, hzc⟩
                · exact Or.inl ((new.T.mem_Gi_P (u + 1) w b _).mpr (Or.inl ⟨i, hiu, Or.inr h⟩))
                · exact Or.inr ⟨c, .deep w b c i hiu hc, hzc⟩
          · rcases ih b (new.T.add_size_lt_P w b) z hzb with h | ⟨c, hc, hzc⟩
            · exact Or.inl ((new.T.mem_Gi_P (u + 1) w b _).mpr (Or.inr h))
            · exact Or.inr ⟨c, .tail w b c hc, hzc⟩

theorem Reach_comp {lam : Nat} (u : Nat) {x c : new.T lam} (h : Reach u x c) :
    new.T.isNF x → new.T.isNFComp u c ∧ new.T.size c < new.T.size x := by
  induction h with
  | here w b i hi =>
      intro hx
      refine ⟨?_, new.T.idx_size_lt_P w b i⟩
      have := (new.T.isNF_P_inv w b hx).1 i
      rwa [hi] at this
  | tail w b c _ ih =>
      intro hx
      obtain ⟨hc, hs⟩ := ih (new.T.isNF_P_inv w b hx).2.1
      exact ⟨hc, Nat.lt_trans hs (new.T.add_size_lt_P w b)⟩
  | deep w b c i _ _ ih =>
      intro hx
      obtain ⟨hc, hs⟩ := ih ((new.T.isNF_P_inv w b hx).1 i).1
      exact ⟨hc, Nat.lt_trans hs (new.T.idx_size_lt_P w b i)⟩

theorem Reach_ne_Z {lam : Nat} (u : Nat) {x c : new.T lam} (h : Reach u x c) : x ≠ new.T.Z := by
  cases h <;> intro he <;> cases he

/-! Structure of principal translations. -/

theorem aux_above_zero {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    ∀ p a, (transAux v).1 = T.P p a T.Z → ∀ i : Fin k, p < i.val → v.idx i = new.T.Z
  | _, .nil, _, _, _, i, _ => i.elim0
  | _, .snoc k v a, p, b, he, i, hi => by
      cases k with
      | zero =>
          cases v
          rw [aux_single] at he
          cases he
          have : i.val = 0 := by have := i.isLt; omega
          omega
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            rw [aux_zero_tail] at he
            by_cases hik : i.val < k + 1
            · simp only [new.Vec.idx, hik, dite_true]
              exact aux_above_zero v p b he ⟨i.val, hik⟩ hi
            · simp [new.Vec.idx, hik]
          · rw [aux_head_snoc v a haz] at he
            cases he
            have := i.isLt
            omega

theorem aux_top_le {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    ∀ p a, (transAux v).1 = T.P p a T.Z → p ≤ k - 1 := by
  intro k v p a he
  obtain ⟨p', a', he', hp'⟩ := aux_principal v
  rw [he] at he'
  cases he'
  exact hp'

theorem aux_head_high_eq {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    VecGood v →
    ∀ p a, (transAux v).1 = T.P p a T.Z →
      ∀ i : Fin k, i.val = p → (T.part p a).1 = (T.part p (trans (v.idx i))).1
  | _, .nil, _, _, _, _, i, _ => i.elim0
  | _, .snoc k v a, hv, p, b, he, i, hi => by
      have hpre := VecGood_prefix v a hv
      cases k with
      | zero =>
          cases v
          rw [aux_single] at he
          cases he
          have : i = Fin.last 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
          subst this
          simp [new.Vec.idx]
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            rw [aux_zero_tail] at he
            have hp := aux_top_le v p b he
            have hik : i.val < k + 1 := by omega
            simp only [new.Vec.idx, hik, dite_true]
            exact aux_head_high_eq v hpre p b he ⟨i.val, hik⟩ hi
          · rw [aux_head_snoc v a haz] at he
            cases he
            have hil : i = Fin.last (k + 1) := Fin.eq_of_val_eq (by simp; omega)
            subst hil
            have hlow := aux_lower_closed v hpre
            rw [part_add_distrib, part_of_index (k + 1) _
              (Rank1Termination.index_mono (by omega) _ hlow.2.1), T.add_Z,
              (part_card_times (k + 1) _).1, part_one_del_fst]
            simp [new.Vec.idx]

def Contr {lam : Nat} (i : Nat) (x : new.T lam) : T :=
  if i = 0 then T.early_collapse 0 (trans x) else T.card_times i (T.early_collapse i (trans x))

def TopContr {lam : Nat} (i : Nat) (x : new.T lam) : T :=
  if i = 0 then trans x else T.card_times i (T.one_del (trans x))

theorem aux_contr_G1 {lam : Nat} (u : Nat) : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    (∀ i : Fin k, ∀ y ∈ T.G1 u (Contr i.val (v.idx i)), y ∈ T.G1 u (transAux v).2) ∧
    ∀ p a, (transAux v).1 = T.P p a T.Z →
      (∀ i : Fin k, i.val < p → ∀ y ∈ T.G1 u (Contr i.val (v.idx i)), y ∈ T.G1 u a) ∧
      (∀ i : Fin k, i.val = p → ∀ y ∈ T.G1 u (TopContr p (v.idx i)), y ∈ T.G1 u a) ∧
      (∀ i : Fin k, i.val = p → 0 < p → TopContr p (v.idx i) ≤ a)
  | _, .nil => ⟨fun i => i.elim0, fun _ _ _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | _, .snoc k v a => by
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          refine ⟨?_, ?_⟩
          · intro i y hy
            have : i = Fin.last 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
            subst this
            simpa [Contr, new.Vec.idx] using hy
          · intro p b he
            cases he
            refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_, fun _ _ h => absurd h (Nat.lt_irrefl 0)⟩
            intro i _ y hy
            have : i = Fin.last 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
            subst this
            simpa [TopContr, new.Vec.idx] using hy
      | succ k =>
          have ih := aux_contr_G1 u v
          have hlast (i : Fin (k + 1 + 1)) (hi : ¬ i.val < k + 1) :
              (new.Vec.snoc (k + 1) v a).idx i = a := by simp [new.Vec.idx, hi]
          have hcast (i : Fin (k + 1 + 1)) (hi : i.val < k + 1) :
              (new.Vec.snoc (k + 1) v a).idx i = v.idx ⟨i.val, hi⟩ := by simp [new.Vec.idx, hi]
          refine ⟨?_, ?_⟩
          · intro i y hy
            rw [aux_lower_snoc, G1_add, List.mem_append]
            by_cases hi : i.val < k + 1
            · rw [hcast i hi] at hy
              exact Or.inr (ih.1 ⟨i.val, hi⟩ y hy)
            · rw [hlast i hi] at hy
              have hiv : i.val = k + 1 := by have := i.isLt; omega
              rw [hiv] at hy
              exact Or.inl (by simpa [Contr] using hy)
          · intro p b he
            by_cases haz : a = new.T.Z
            · subst a
              rw [aux_zero_tail] at he
              have hp := aux_top_le v p b he
              have hv := ih.2 p b he
              refine ⟨fun i hi y hy => ?_, fun i hi y hy => ?_, fun i hi hp0 => ?_⟩
              · have hik : i.val < k + 1 := by omega
                rw [hcast i hik] at hy
                exact hv.1 ⟨i.val, hik⟩ hi y hy
              · have hik : i.val < k + 1 := by omega
                rw [hcast i hik] at hy
                exact hv.2.1 ⟨i.val, hik⟩ hi y hy
              · have hik : i.val < k + 1 := by omega
                rw [hcast i hik]
                exact hv.2.2 ⟨i.val, hik⟩ hi hp0
            · rw [aux_head_snoc v a haz] at he
              cases he
              refine ⟨fun i hi y hy => ?_, fun i hi y hy => ?_, fun i hi _ => ?_⟩
              · rw [hcast i hi] at hy
                rw [G1_add, List.mem_append]
                exact Or.inr (ih.1 ⟨i.val, hi⟩ y hy)
              · have hik : ¬ i.val < k + 1 := by omega
                rw [hlast i hik] at hy
                rw [G1_add, List.mem_append]
                exact Or.inl (by simpa [TopContr] using hy)
              · have hik : ¬ i.val < k + 1 := by omega
                rw [hlast i hik]
                simpa [TopContr] using add_self_le _ _

theorem aux_head_countable {lam : Nat} {k : Nat} (v : new.Vec (new.T lam) (k + 1))
    (a : T) (he : (transAux v).1 = T.P 0 a T.Z) :
    a = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  have hz := aux_above_zero v 0 a he
  rw [transAux_countable_head_exact v (fun i hi => hz i hi)] at he
  cases he
  rfl

/-! Splitting a source term by the index of its principal summands. -/

def headIdx {lam : Nat} (w : new.Vec (new.T lam) lam) : Nat :=
  match (transAux w).1 with
  | .P p _ _ => p
  | .Z => 0

theorem headIdx_eq {lam : Nat} (w : new.Vec (new.T lam) lam) (p : Nat) (a : T)
    (he : (transAux w).1 = T.P p a T.Z) : headIdx w = p := by
  simp [headIdx, he]

def srcPart {lam : Nat} (j : Nat) : new.T lam → new.T lam × new.T lam
  | .Z => (.Z, .Z)
  | .P w b =>
      if j < headIdx w then (.P w (srcPart j b).1, (srcPart j b).2)
      else ((srcPart j b).1, .P w (srcPart j b).2)

theorem trans_P_headIdx {lam : Nat} (w : new.Vec (new.T lam) lam) (b : new.T lam) :
    ∃ X, (transAux w).1 = T.P (headIdx w) X T.Z ∧ trans (new.T.P w b) = T.P (headIdx w) X (trans b) := by
  obtain ⟨p, a, he, _⟩ := aux_principal w
  rw [headIdx_eq w p a he]
  exact ⟨a, he, by rw [trans_as_add, he, p_zero_add]⟩

theorem srcPart_trans {lam : Nat} (j : Nat) : ∀ s : new.T lam,
    trans (srcPart j s).1 = (T.part j (trans s)).1
  | .Z => rfl
  | .P w b => by
      obtain ⟨X, he, htr⟩ := trans_P_headIdx w b
      have ih := srcPart_trans j b
      rw [htr]
      by_cases hj : j < headIdx w
      · simp only [srcPart, hj, ite_true, T.part, show ¬ headIdx w ≤ j by omega, ite_false]
        obtain ⟨X', he', htr'⟩ := trans_P_headIdx w (srcPart j b).1
        rw [htr', ih]
        rw [he] at he'
        cases he'
        rfl
      · simp only [srcPart, hj, ite_false, T.part, show headIdx w ≤ j by omega, ite_true]
        exact ih

theorem srcPart_size {lam : Nat} (j : Nat) : ∀ s : new.T lam,
    new.T.size (srcPart j s).1 ≤ new.T.size s
  | .Z => Nat.le_refl _
  | .P w b => by
      have ih := srcPart_size j b
      by_cases hj : j < headIdx w
      · simp only [srcPart, hj, ite_true, new.T.size]; omega
      · simp only [srcPart, hj, ite_false, new.T.size]; omega

theorem headIdx_mono {lam : Nat} (w w' : new.Vec (new.T lam) lam)
    (hw : ∀ i : Fin lam, new.T.isNFComp i.val (w.idx i))
    (hw' : ∀ i : Fin lam, new.T.isNFComp i.val (w'.idx i))
    (h : new.T.P w' new.T.Z ≤ new.T.P w new.T.Z) : headIdx w' ≤ headIdx w := by
  have hn := new.T.isNF.p w new.T.Z (fun i => (hw i).1) new.T.isNF.z (fun i => (hw i).2) (new.T.Z_le _)
  have hn' := new.T.isNF.p w' new.T.Z (fun i => (hw' i).1) new.T.isNF.z (fun i => (hw' i).2) (new.T.Z_le _)
  obtain ⟨X, he, htr⟩ := trans_P_headIdx w new.T.Z
  obtain ⟨X', he', htr'⟩ := trans_P_headIdx w' new.T.Z
  have hle : trans (new.T.P w' new.T.Z) ≤ trans (new.T.P w new.T.Z) := by
    rcases h with h | h
    · exact Or.inl (trans_lt_of_lt _ _ hn' hn h)
    · rw [new.T_eq_sound _ _ h]; exact Or.inr rfl
  rw [htr, htr'] at hle
  exact head_le_index _ _ _ _ hle

theorem srcPart_NF {lam : Nat} (j : Nat) : ∀ s : new.T lam, new.T.isNF s →
    new.T.isNF (srcPart j s).1 ∧
      (∀ w b, s = new.T.P w b → headIdx w ≤ j → (srcPart j s).1 = new.T.Z)
  | .Z, _ => ⟨new.T.isNF.z, fun _ _ h => by cases h⟩
  | .P w b, hs => by
      obtain ⟨hw, hb, hh⟩ := new.T.isNF_P_inv w b hs
      have ih := srcPart_NF j b hb
      have hbz : ∀ w' b', b = new.T.P w' b' → headIdx w' ≤ headIdx w := by
        intro w' b' hbe
        subst hbe
        obtain ⟨hw', _, _⟩ := new.T.isNF_P_inv w' b' hb
        exact headIdx_mono w w' hw hw' hh
      refine ⟨?_, ?_⟩
      · by_cases hj : j < headIdx w
        · simp only [srcPart, hj, ite_true]
          refine new.T.isNF.p w _ (fun i => (hw i).1) ih.1 (fun i => (hw i).2) ?_
          cases hbe : b with
          | Z => simp only [srcPart]; exact new.T.Z_le _
          | P w' b' =>
              rw [hbe] at hh
              by_cases hj' : j < headIdx w'
              · simp only [srcPart, hj', ite_true]
                exact hh
              · rw [← hbe, ih.2 w' b' hbe (by omega)]
                exact new.T.Z_le _
        · simp only [srcPart, hj, ite_false]
          exact ih.1
      · intro w0 b0 he hj
        have hw0 : w0 = w := by injection he with h1 h2; exact h1.symm
        subst hw0
        simp only [srcPart, show ¬ j < headIdx w0 by omega, ite_false]
        cases hbe : b with
        | Z => rfl
        | P w' b' => rw [← hbe]; exact ih.2 w' b' hbe (Nat.le_trans (hbz w' b' hbe) hj)

end LegacyTranslation

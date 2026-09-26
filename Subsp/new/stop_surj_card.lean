import Subsp.new.stop_surj_uncollapse

open T

namespace StopSurjCard

open StopSurjMeasure

def Small (B s : T) : Prop := s < B ∧ ∀ y, y ∈ T.G1 0 s → y < B

theorem small_inv (B : T) (p : Nat) (a b : T) (hnf : T.isNF1 (T.P p a b))
    (h : Small B (T.P p a b)) : Small B a ∧ Small B b := by
  have hmem : a ∈ T.G1 0 (T.P p a b) := by
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))
  constructor
  · refine ⟨h.2 a hmem, ?_⟩
    intro y hy
    apply h.2 y
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_left _ (List.mem_append_right _ hy)
  · refine ⟨lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 p a b hnf) h.1, ?_⟩
    intro y hy
    apply h.2 y
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_right _ hy

def Good1 (s : T) : Prop := ∀ y, y ∈ T.G1 1 s → y < s

def OneChain : T → Prop
  | T.Z => True
  | T.P p _ b => p = 1 ∧ OneChain b

theorem card_head (s : T) : T.card_times 1 (T.head s) = T.head (T.card_times 1 s) := by
  cases s with
  | Z => rfl
  | P p a b =>
      rw [T.head, T.card_times.eq_3, T.card_times.eq_3]
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [ite_eq_left hp]
        change T.add (T.P 1 _ T.Z) T.Z = T.head (T.add (T.P 1 _ T.Z) _)
        rw [T.add_Z, T.P_add_eq, T.head]
      · intro hp
        rw [ite_eq_right hp]
        change T.add (T.P 1 _ T.Z) T.Z = T.head (T.add (T.P 1 _ T.Z) _)
        rw [T.add_Z, T.P_add_eq, T.head]

theorem head_nf (s : T) (hs : T.isNF1 s) : T.isNF1 (T.head s) := by
  cases hs with
  | z => exact T.isNF1.z
  | p p a b ha hb hg hh =>
      exact T.isNF1.p p a T.Z ha T.isNF1.z hg (T.Z_le _)

theorem head_idx (s : T) (hs : T.index_Prop1 1 s) : T.index_Prop1 1 (T.head s) := by
  cases hs with
  | z => exact T.index_Prop1.z
  | p p a b hp hb => exact T.index_Prop1.p p a T.Z hp T.index_Prop1.z

theorem card_reflect_le (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (hsi : T.index_Prop1 1 s) (hti : T.index_Prop1 1 t)
    (h : T.card_times 1 s ≤ T.card_times 1 t) : s ≤ t := by
  cases lt_total_thm s t with
  | inl hst => exact Or.inl hst
  | inr hr =>
      cases hr with
      | inl hts =>
          have hc := c1_card_times_mono_index1 t s ht hti hs hsi hts
          exact False.elim (lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ hc h))
      | inr he => exact Or.inr he

theorem index1_good_lt_wrap (a b : T) (hi : T.index_Prop1 1 a) (hg : Good1 a) :
    a < T.P 1 a b := by
  cases a with
  | Z => exact T.Lt.Z_lt_P 1 T.Z b
  | P p c d =>
      cases hi with
      | p _ _ _ hp hd =>
          cases p with
          | zero => exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
          | succ p =>
              have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hp)
              cases hp0
              have hc : c ∈ T.G1 1 (T.P 1 c d) := by
                rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1)]
                exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self c))
              exact T.Lt.p_mid 1 c _ d b (hg c hc)

theorem below_mul_support (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) :
    T.index_Prop1 1 a ∧ ∀ y, y ∈ T.G1 1 a → y = T.Z := by
  induction a generalizing k with
  | Z =>
      refine ⟨T.index_Prop1.z, ?_⟩
      intro y hy
      cases hy
  | P p c d ihc ihd =>
      cases k with
      | zero => exact False.elim (lt_Z_inv ha)
      | succ k =>
          rw [mul_succ_shape 1 T.Z k] at ha
          have hn := T.isNF1_P_inv p c d hnf
          cases lt_inv p c d 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) ha with
          | inl hp =>
              have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
              cases hp0
              have hi := isNF1_index 0 0 c d hnf (Nat.le_refl 0)
              refine ⟨Rank1Termination.index_mono (Nat.zero_le 1) _ hi, ?_⟩
              intro y hy
              rw [index_Prop1_G1_empty 0 _ hi 1 (Nat.zero_lt_succ 0)] at hy
              cases hy
          | inr hr =>
              cases hr with
              | inl hm => exact False.elim (lt_Z_inv hm.2)
              | inr ht =>
                  have hp1 := ht.1
                  have hc0 := ht.2.1
                  cases hp1
                  cases hc0
                  have hd := ihd hn.2.1 k ht.2.2
                  refine ⟨T.index_Prop1.p 1 T.Z d (Nat.le_refl 1) hd.1, ?_⟩
                  intro y hy
                  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1)] at hy
                  cases List.mem_append.mp hy with
                  | inl hl =>
                      cases List.mem_append.mp hl with
                      | inl he => exact List.mem_singleton.mp he
                      | inr he => cases he
                  | inr he => exact hd.2 y he

theorem below_mul_good (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) : Good1 a := by
  intro y hy
  have he := (below_mul_support a hnf k ha).2 y hy
  rw [he]
  cases a with
  | Z => cases hy
  | P p c d => exact T.Lt.Z_lt_P p c d

#print axioms below_mul_support

theorem principal_inverse (q : T) (hnf : T.isNF1 q) (k : Nat)
    (hq : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) :
    ∃ p a, p ≤ 1 ∧ T.isNF1 a ∧
      (∀ y, y ∈ T.G1 p a → y < a) ∧
      (p = 1 → T.index_Prop1 1 a ∧ Good1 a) ∧
      T.card_times 1 (T.P p a T.Z) = T.P 1 q T.Z ∧
      (∀ b, T.P p a b < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z) ∧
      degree a ≤ degree q ∧ (p = 1 → a < q) ∧
      ∀ B, T.part B = (B, T.Z) → Small B q → Small B a := by
  rw [mul_succ_shape 1 T.Z k] at hq
  cases q with
  | Z =>
      refine ⟨0, T.Z, Nat.zero_le 1, T.isNF1.z, ?_, ?_, rfl, ?_, Nat.le_refl 0, ?_, ?_⟩
      · intro y hy
        cases hy
      · intro h
        cases h
      · intro b
        exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
      · intro h
        cases h
      · intro B hfix hsmall
        exact hsmall
  | P p a b =>
      cases lt_inv p a b 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) hq with
      | inl hp =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
          cases hp0
          have hi := isNF1_index 0 0 a b hnf (Nat.le_refl 0)
          cases StopUncollapse.exists_uncollapse (T.P 0 a b) hnf hi with
          | intro x hx =>
              refine ⟨0, x, Nat.zero_le 1, hx.1, hx.2.1, ?_, ?_, ?_, hx.2.2.2.2, ?_, ?_⟩
              · intro h
                cases h
              · rw [T.card_times.eq_3, ite_eq_left rfl]
                change T.add (T.P 1 (T.early_collapse x) T.Z) T.Z = _
                rw [T.add_Z, hx.2.2.1]
              · intro tail
                exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
              · intro h
                cases h
              · intro B hfix hsmall
                have hxb := hx.2.2.2.1 B hfix hsmall.2 hsmall.1
                refine ⟨hxb, ?_⟩
                intro y hy
                exact lt_trans_thm _ _ _ (hx.2.1 y hy) hxb
      | inr hr =>
          cases hr with
          | inl hm => exact False.elim (lt_Z_inv hm.2)
          | inr ht =>
              have hp1 := ht.1
              have ha0 := ht.2.1
              cases hp1
              cases ha0
              have hbNF := (T.isNF1_P_inv 1 T.Z b hnf).2.1
              have hbIdx := (below_mul_support b hbNF k ht.2.2).1
              have hbG := below_mul_good b hbNF k ht.2.2
              refine ⟨1, b, Nat.le_refl 1, hbNF, hbG, ?_, ?_, ?_,
                degree_tail_le 1 T.Z b, ?_, ?_⟩
              · intro _
                exact ⟨hbIdx, hbG⟩
              · rw [T.card_times.eq_3, ite_eq_right (by intro h; cases h)]
                change T.add (T.P 1 (T.add (T.P 1 T.Z T.Z) b) T.Z) T.Z = _
                rw [T.add_Z, T.P_add_eq, T.add.eq_1]
              · intro tail
                exact T.Lt.p_mid 1 _ _ _ _ ht.2.2
              · intro _
                exact gc_tail_lt_of_NF1 1 T.Z b hnf
              · intro B hfix hsmall
                exact (small_inv B 1 T.Z b hnf hsmall).2

theorem card_append (p : Nat) (a b : T) :
    T.card_times 1 (T.P p a b) = T.add (T.card_times 1 (T.P p a T.Z)) (T.card_times 1 b) := by
  have hh := ca_card_times_add 1 (T.P p a T.Z) b
  rw [T.P_add_eq, T.add.eq_1] at hh
  exact hh

theorem exists_uncard (h : T) (hnf : T.isNF1 h) (hc : OneChain h) (k : Nat)
    (hb : h < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z) :
    ∃ s, T.isNF1 s ∧ T.index_Prop1 1 s ∧ Good1 s ∧ T.card_times 1 s = h ∧
      s < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z ∧
      degree s ≤ degree h ∧
      ∀ B, T.part B = (B, T.Z) → Small B h → Small B s := by
  induction h with
  | Z =>
      refine ⟨T.Z, T.isNF1.z, T.index_Prop1.z, ?_, rfl, T.Lt.Z_lt_P 1 _ T.Z,
        Nat.le_refl 0, ?_⟩
      · intro y hy
        cases hy
      · intro B hfix hsmall
        exact hsmall
  | P p q r ihq ihr =>
      have hp1 := hc.1
      cases hp1
      have hn := T.isNF1_P_inv 1 q r hnf
      have hrb : r < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z :=
        lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 1 q r hnf) hb
      have hqb : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
        cases lt_inv 1 q r 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z hb with
        | inl h => exact False.elim (Nat.lt_irrefl 1 h)
        | inr hr =>
            cases hr with
            | inl hm => exact hm.2
            | inr ht => exact False.elim (lt_Z_inv ht.2.2)
      cases ihr hn.2.1 hc.2 hrb with
      | intro sr hsr =>
          cases principal_inverse q hn.1 k hqb with
          | intro j hj =>
              cases hj with
              | intro a ha =>
                  have hheadNF : T.isNF1 (T.P j a T.Z) :=
                    T.isNF1.p j a T.Z ha.2.1 T.isNF1.z ha.2.2.1 (T.Z_le _)
                  have hheadIdx : T.index_Prop1 1 (T.P j a T.Z) :=
                    T.index_Prop1.p j a T.Z ha.1 T.index_Prop1.z
                  have hcardHead : T.card_times 1 (T.head sr) ≤
                      T.card_times 1 (T.P j a T.Z) := by
                    rw [card_head, hsr.2.2.2.1, ha.2.2.2.2.1]
                    exact hn.2.2.2
                  have hhead := card_reflect_le (T.head sr) (T.P j a T.Z)
                    (head_nf sr hsr.1) hheadNF (head_idx sr hsr.2.1) hheadIdx hcardHead
                  have hsNF : T.isNF1 (T.P j a sr) :=
                    T.isNF1.p j a sr ha.2.1 hsr.1 ha.2.2.1 hhead
                  refine ⟨T.P j a sr, hsNF, T.index_Prop1.p j a sr ha.1 hsr.2.1,
                    ?_, ?_, ?_, ?_, ?_⟩
                  · intro y hy
                    have htail : sr < T.P j a sr := gc_tail_lt_of_NF1 j a sr hsNF
                    cases j with
                    | zero =>
                        rw [T.G1.eq_2, ite_eq_right (Nat.not_succ_le_zero 0)] at hy
                        exact lt_trans_thm _ _ _ (hsr.2.2.1 y hy) htail
                    | succ j =>
                        have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ ha.1)
                        cases hj0
                        have haGood := ha.2.2.2.1 rfl
                        have halt := index1_good_lt_wrap a sr haGood.1 haGood.2
                        rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1)] at hy
                        cases List.mem_append.mp hy with
                        | inl hl =>
                            cases List.mem_append.mp hl with
                            | inl he =>
                                rw [List.mem_singleton.mp he]
                                exact halt
                            | inr he => exact lt_trans_thm _ _ _ (haGood.2 y he) halt
                        | inr he => exact lt_trans_thm _ _ _ (hsr.2.2.1 y he) htail
                  · rw [card_append, ha.2.2.2.2.1, hsr.2.2.2.1, T.P_add_eq, T.add.eq_1]
                  · exact ha.2.2.2.2.2.1 sr
                  · have haDeg := ha.2.2.2.2.2.2.1
                    have hsrDeg := hsr.2.2.2.2.2.1
                    change max (degree a + 1) (degree sr) ≤ max (degree q + 1) (degree r)
                    exact Nat.max_le.mpr
                      ⟨Nat.le_trans (Nat.add_le_add_right haDeg 1) (Nat.le_max_left _ _),
                        Nat.le_trans hsrDeg (Nat.le_max_right _ _)⟩
                  · intro B hfix hsmall
                    have hinv := small_inv B 1 q r hnf hsmall
                    have hasmall := ha.2.2.2.2.2.2.2.2 B hfix hinv.1
                    have hsrsmall := hsr.2.2.2.2.2.2 B hfix hinv.2
                    constructor
                    · cases j with
                      | zero =>
                          have hidx := isNF1_index 0 0 a sr hsNF (Nat.le_refl 0)
                          have hBne : B ≠ T.Z := by
                            intro hB
                            rw [hB] at hsmall
                            exact lt_Z_inv hsmall.1
                          exact ec_index0_lt_posfixed _ B hidx hfix hBne
                      | succ j =>
                          have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ ha.1)
                          cases hj0
                          have haq := ha.2.2.2.2.2.2.2.1 rfl
                          exact lt_trans_thm _ _ _ (T.Lt.p_mid 1 a q sr r haq) hsmall.1
                    · intro y hy
                      rw [T.G1.eq_2, ite_eq_left (Nat.zero_le j)] at hy
                      cases List.mem_append.mp hy with
                      | inl hl =>
                          cases List.mem_append.mp hl with
                          | inl he =>
                              rw [List.mem_singleton.mp he]
                              exact hasmall.1
                          | inr he => exact hasmall.2 y he
                      | inr he => exact hsrsmall.2 y he

#print axioms exists_uncard

end StopSurjCard

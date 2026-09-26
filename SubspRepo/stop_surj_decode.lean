import Subsp.new.stop_nf_order_c

open T

def T.unec : T → T
| T.Z => T.Z
| T.P 0 a b =>
    if h : a ≠ T.Z ∧ T.part a = (a, T.Z) then T.add a b
    else T.P 0 a b
| T.P (p + 1) a b => T.P (p + 1) a b

theorem surj_part_add_fixed : ∀ a b : T,
    T.part a = (a, T.Z) → T.part b = (T.Z, b) →
      T.part (T.add a b) = (a, b) := by
  intro a
  induction a with
  | Z =>
      intro b ha hb
      rw [T.add]
      exact hb
  | P p c d ihc ihd =>
      intro b hfix hb
      apply Decidable.byCases (p := p = 0)
      · intro hp
        rw [T.part, ite_eq_left hp] at hfix
        have hbad : T.Z = T.P p c d := congrArg Prod.fst hfix
        cases hbad
      · intro hp
        rw [T.part, ite_eq_right hp] at hfix
        cases hdpart : T.part d with
        | mk x y =>
            rw [hdpart] at hfix
            have hx : x = d := by
              have heq : T.P p c x = T.P p c d := congrArg Prod.fst hfix
              cases heq
              rfl
            have hy : y = T.Z := congrArg Prod.snd hfix
            have hdFix : T.part d = (d, T.Z) := by
              rw [hdpart, hx, hy]
            have hrec := ihd b hdFix hb
            rw [T.P_add_eq]
            rw [T.part, ite_eq_right hp, hrec]

#print axioms surj_part_add_fixed

theorem surj_part_zero_of_head_le_P0 (b a : T)
    (hhead : T.head b ≤ T.P 0 a T.Z) :
    T.part b = (T.Z, b) := by
  cases b with
  | Z => rfl
  | P p c d =>
      rw [T.head] at hhead
      have hp0 : p = 0 := by
        cases hhead with
        | inl hlt =>
            cases lt_inv p c T.Z 0 a T.Z hlt with
            | inl hp => exact False.elim (Nat.not_lt_zero p hp)
            | inr hr =>
                cases hr with
                | inl hm => exact hm.1
                | inr ht => exact ht.1
        | inr heq =>
            cases heq
            rfl
      rw [T.part, ite_eq_left hp0]

#print axioms surj_part_zero_of_head_le_P0

theorem surj_unec_P0_section (a b : T)
    (hs : T.isNF1 (T.P 0 a b)) :
    T.early_collapse (T.unec (T.P 0 a b)) = T.P 0 a b := by
  have hinv := T.isNF1_P_inv 0 a b hs
  have hbPart : T.part b = (T.Z, b) :=
    surj_part_zero_of_head_le_P0 b a hinv.2.2.2
  rw [T.unec]
  apply Decidable.byCases (p := a ≠ T.Z ∧ T.part a = (a, T.Z))
  · intro h
    rw [dite_eq_left h]
    have hp : T.part (T.add a b) = (a, b) :=
      surj_part_add_fixed a b h.2 hbPart
    rw [T.early_collapse, hp, ite_eq_right h.1]
    have hstand : T.stand (T.P 0 a b) = T.P 0 a b :=
      bridge_stand_eq_self_of_NF1 (T.P 0 a b) hs
    exact hstand
  · intro h
    rw [dite_eq_right h]
    rw [T.early_collapse, T.part, ite_eq_left rfl]

#print axioms surj_unec_P0_section

def T.oneChain : T → Prop
| T.Z => True
| T.P p q r => p = 1 ∧ T.oneChain r

def T.uncard1 : T → T
| T.Z => T.Z
| T.P 1 q r =>
    let tr := T.uncard1 r
    match q with
    | T.Z => T.P 0 T.Z tr
    | T.P 0 a b => T.P 0 (T.unec (T.P 0 a b)) tr
    | T.P 1 T.Z qt => T.P 1 qt tr
    | _ => T.Z
| _ => T.Z

theorem surj_uncard1_section (k : Nat) :
    ∀ h : T, T.isNF1 h → T.oneChain h →
      h < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z →
      T.card_times 1 (T.uncard1 h) = h := by
  intro h
  induction h with
  | Z =>
      intro hnf hchain hbound
      rw [T.uncard1, T.card_times]
  | P p q r ihq ihr =>
      intro hnf hchain hbound
      have hp : p = 1 := hchain.1
      cases hp
      have hinv := T.isNF1_P_inv 1 q r hnf
      have hqNF : T.isNF1 q := hinv.1
      have hrNF : T.isNF1 r := hinv.2.1
      have hrChain : T.oneChain r := hchain.2
      have hrLt : r < T.P 1 q r := gc_tail_lt_of_NF1 1 q r hnf
      have hrBound : r < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z :=
        lt_trans_thm r (T.P 1 q r)
          (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z)
          hrLt hbound
      have hrec := ihr hrNF hrChain hrBound
      have hqBound : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat k) := by
        cases lt_inv 1 q r 1
            (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z hbound with
        | inl hhead =>
            exact False.elim (Nat.lt_irrefl 1 hhead)
        | inr hor =>
            cases hor with
            | inl hmid => exact hmid.2
            | inr htail =>
                exact False.elim (lt_Z_inv htail.2.2)
      cases k with
      | zero =>
          rw [T.ofNat.eq_1, T.mul.eq_1] at hqBound
          exact False.elim (lt_Z_inv hqBound)
      | succ k =>
          rw [mul_succ_shape 1 T.Z k] at hqBound
          cases q with
          | Z =>
              rw [T.uncard1]
              rw [T.card_times.eq_3, ite_eq_left rfl]
              rw [← add_eq_hAdd
                (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0))
                (T.early_collapse T.Z)]
              rw [T.ofNat.eq_1, T.mul.eq_1, T.add.eq_1]
              have hez : T.early_collapse T.Z = T.Z := rfl
              rw [hez]
              rw [← add_eq_hAdd
                (T.P 1 T.Z T.Z)
                (T.card_times 1 (T.uncard1 r))]
              rw [T.P_add_eq, T.add.eq_1, hrec]
          | P q0 qa qb =>
              cases lt_inv q0 qa qb 1 T.Z
                  (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) hqBound with
              | inl hhead =>
                  have hq0 : q0 = 0 :=
                    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hhead)
                  cases hq0
                  have hec : T.early_collapse (T.unec (T.P 0 qa qb)) =
                      T.P 0 qa qb :=
                    surj_unec_P0_section qa qb hqNF
                  rw [T.uncard1]
                  rw [T.card_times.eq_3, ite_eq_left rfl]
                  rw [← add_eq_hAdd
                    (T.mul (T.P 1 T.Z T.Z) (T.ofNat 0))
                    (T.early_collapse (T.unec (T.P 0 qa qb)))]
                  rw [T.ofNat.eq_1, T.mul.eq_1, T.add.eq_1, hec]
                  rw [← add_eq_hAdd
                    (T.P 1 (T.P 0 qa qb) T.Z)
                    (T.card_times 1 (T.uncard1 r))]
                  rw [T.P_add_eq, T.add.eq_1, hrec]
              | inr hor =>
                  cases hor with
                  | inl hmid =>
                      exact False.elim (lt_Z_inv hmid.2)
                  | inr htail =>
                      have hq0 : q0 = 1 := htail.1
                      have hqa : qa = T.Z := htail.2.1
                      cases hq0
                      cases hqa
                      rw [T.uncard1]
                      rw [T.card_times.eq_3, ite_eq_right (by
                        intro hzero
                        cases hzero)]
                      rw [← add_eq_hAdd
                        (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1)) qb]
                      rw [mul_succ_shape 1 T.Z 0, T.P_add_eq]
                      rw [T.ofNat.eq_1, T.mul.eq_1, T.add.eq_1]
                      rw [← add_eq_hAdd
                        (T.P 1 (T.P 1 T.Z qb) T.Z)
                        (T.card_times 1 (T.uncard1 r))]
                      rw [T.P_add_eq, T.add.eq_1, hrec]

#print axioms surj_uncard1_section

theorem surj_part_fst_oneChain_mul (k : Nat) :
    ∀ c : T,
      c < T.mul (T.P 1 T.Z T.Z) (T.ofNat k) →
        T.oneChain (T.part c).1 := by
  induction k with
  | zero =>
      intro c h
      rw [T.ofNat.eq_1, T.mul.eq_1] at h
      exact False.elim (lt_Z_inv h)
  | succ k ih =>
      intro c h
      rw [mul_succ_shape 1 T.Z k] at h
      cases c with
      | Z =>
          change True
          exact True.intro
      | P p a b =>
          cases lt_inv p a b 1 T.Z
              (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) h with
          | inl hp =>
              have hp0 : p = 0 :=
                Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
              rw [T.part, ite_eq_left hp0]
              change True
              exact True.intro
          | inr hor =>
              cases hor with
              | inl hmid =>
                  exact False.elim (lt_Z_inv hmid.2)
              | inr htail =>
                  have hp1 : p = 1 := htail.1
                  have ha0 : a = T.Z := htail.2.1
                  have hb : b < T.mul (T.P 1 T.Z T.Z) (T.ofNat k) :=
                    htail.2.2
                  have hrec := ih b hb
                  cases hp1
                  cases ha0
                  rw [T.part, ite_eq_right (by
                    intro hzero
                    cases hzero)]
                  cases hpart : T.part b with
                  | mk x y =>
                      rw [hpart] at hrec
                      exact ⟨rfl, hrec⟩

#print axioms surj_part_fst_oneChain_mul

theorem surj_mul_lt_wrap (k : Nat) :
    T.mul (T.P 1 T.Z T.Z) (T.ofNat k) <
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z := by
  cases k with
  | zero =>
      rw [T.ofNat.eq_1, T.mul.eq_1]
      exact T.Lt.Z_lt_P 1 T.Z T.Z
  | succ k =>
      rw [mul_succ_shape 1 T.Z k]
      have hz : T.Z < T.P 1 T.Z
          (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) :=
        T.Lt.Z_lt_P 1 T.Z
          (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
      exact T.Lt.p_mid 1 T.Z
        (T.P 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)))
        (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z hz

#print axioms surj_mul_lt_wrap

theorem surj_part_fst_uncard_section (k : Nat) (c : T)
    (hcNF : T.isNF1 c)
    (hcBound : c < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) :
    T.card_times 1 (T.uncard1 (T.part c).1) = (T.part c).1 := by
  have hpartNF : T.isNF1 (T.part c).1 :=
    (nfaux_part_NF1 c hcNF).1
  have hchain : T.oneChain (T.part c).1 :=
    surj_part_fst_oneChain_mul k c hcBound
  have hle : (T.part c).1 ≤ c := bridge_part_fst_le_self c
  have hltMul : (T.part c).1 <
      T.mul (T.P 1 T.Z T.Z) (T.ofNat k) :=
    lt_of_le_of_lt_thm T (T.part c).1 c
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) hle hcBound
  have hwrap := surj_mul_lt_wrap k
  have hbound : (T.part c).1 <
      T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z :=
    lt_trans_thm (T.part c).1
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
      (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z)
      hltMul hwrap
  exact surj_uncard1_section k (T.part c).1 hpartNF hchain hbound

#print axioms surj_part_fst_uncard_section

theorem surj_head_lt_pos_of_index0 (p : Nat) (c b : T)
    (hp : 0 < p) (hb : T.index_Prop1 0 b) :
    T.head b < T.P p c T.Z := by
  cases b with
  | Z =>
      rw [T.head]
      exact T.Lt.Z_lt_P p c T.Z
  | P q e f =>
      cases hb with
      | p _ _ _ hq htail =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          cases hq0
          rw [T.head]
          exact T.Lt.p_head 0 p e c T.Z T.Z hp

#print axioms surj_head_lt_pos_of_index0

theorem surj_add_fixed_index0_NF : ∀ a b : T,
    T.isNF1 a → T.isNF1 b →
    T.part a = (a, T.Z) → T.index_Prop1 0 b →
      T.isNF1 (T.add a b) := by
  intro a
  induction a with
  | Z =>
      intro b ha hb hfix hidx
      rw [T.add]
      exact hb
  | P p c d ihc ihd =>
      intro b ha hb hfix hidx
      have hpne : p ≠ 0 := by
        intro hp0
        rw [T.part, ite_eq_left hp0] at hfix
        have hbad : T.Z = T.P p c d := congrArg Prod.fst hfix
        cases hbad
      have hp : 0 < p := Nat.pos_of_ne_zero hpne
      have hinv := T.isNF1_P_inv p c d ha
      have hdFix : T.part d = (d, T.Z) := by
        rw [T.part, ite_eq_right hpne] at hfix
        cases hpart : T.part d with
        | mk x y =>
            rw [hpart] at hfix
            have hx : x = d := by
              have heq : T.P p c x = T.P p c d := congrArg Prod.fst hfix
              cases heq
              rfl
            have hy : y = T.Z := congrArg Prod.snd hfix
            exact Prod.ext hx hy
      have htailNF : T.isNF1 (T.add d b) :=
        ihd b hinv.2.1 hb hdFix hidx
      have hhead : T.head (T.add d b) ≤ T.P p c T.Z := by
        cases d with
        | Z =>
            rw [T.add]
            exact Or.inl (surj_head_lt_pos_of_index0 p c b hp hidx)
        | P q e f =>
            rw [T.P_add_eq]
            have heq : T.head (T.P q e (T.add f b)) =
                T.head (T.P q e f) := rfl
            rw [heq]
            exact hinv.2.2.2
      rw [T.P_add_eq]
      exact T.isNF1.p p c (T.add d b)
        hinv.1 htailNF hinv.2.2.1 hhead

#print axioms surj_add_fixed_index0_NF

theorem surj_P0_lt_unec_add (a b : T)
    (ha : a ≠ T.Z) (hfix : T.part a = (a, T.Z)) :
    T.P 0 a b < T.add a b := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d =>
      have hpne : p ≠ 0 := by
        intro hp0
        rw [T.part, ite_eq_left hp0] at hfix
        have hbad : T.Z = T.P p c d := congrArg Prod.fst hfix
        cases hbad
      have hp : 0 < p := Nat.pos_of_ne_zero hpne
      rw [T.P_add_eq]
      exact T.Lt.p_head 0 p (T.P p c d) c b (T.add d b) hp

#print axioms surj_P0_lt_unec_add

theorem surj_unec_good0 (s : T)
    (hs : T.isNF1 s)
    (hi : T.index_Prop1 0 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    T.isNF1 (T.unec s) ∧
      (∀ x : T, x ∈ T.G1 0 (T.unec s) → x < T.unec s) ∧
      T.early_collapse (T.unec s) = s := by
  cases s with
  | Z =>
      constructor
      · exact T.isNF1.z
      · constructor
        · intro x hx
          rw [T.unec, T.G1.eq_1] at hx
          cases hx
        · rfl
  | P p a b =>
      cases hi with
      | p _ _ _ hp htailIdx =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          cases hp0
          have hinv := T.isNF1_P_inv 0 a b hs
          have hbPart : T.part b = (T.Z, b) :=
            surj_part_zero_of_head_le_P0 b a hinv.2.2.2
          rw [T.unec]
          apply Decidable.byCases (p := a ≠ T.Z ∧ T.part a = (a, T.Z))
          · intro h
            rw [dite_eq_left h]
            have hbIdx : T.index_Prop1 0 b :=
              bridge_part_second_index0 b T.Z b hinv.2.1 hbPart
            have hnfAdd : T.isNF1 (T.add a b) :=
              surj_add_fixed_index0_NF a b hinv.1 hinv.2.1 h.2 hbIdx
            have hslt : T.P 0 a b < T.add a b :=
              surj_P0_lt_unec_add a b h.1 h.2
            constructor
            · exact hnfAdd
            · constructor
              · intro x hx
                rw [bridge_G1_add_eq] at hx
                cases List.mem_append.mp hx with
                | inl hxa =>
                    have hxS : x ∈ T.G1 0 (T.P 0 a b) := by
                      rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                      exact List.mem_append_left (T.G1 0 b)
                        (List.mem_append_right [a] hxa)
                    exact lt_trans_thm x (T.P 0 a b) (T.add a b)
                      (hg x hxS) hslt
                | inr hxb =>
                    have hxS : x ∈ T.G1 0 (T.P 0 a b) := by
                      rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
                      exact List.mem_append_right ([a] ++ T.G1 0 a) hxb
                    exact lt_trans_thm x (T.P 0 a b) (T.add a b)
                      (hg x hxS) hslt
              · have hsec := surj_unec_P0_section a b hs
                rw [T.unec, dite_eq_left h] at hsec
                exact hsec
          · intro h
            rw [dite_eq_right h]
            constructor
            · exact hs
            · constructor
              · exact hg
              · have hsec := surj_unec_P0_section a b hs
                rw [T.unec, dite_eq_right h] at hsec
                exact hsec

#print axioms surj_unec_good0

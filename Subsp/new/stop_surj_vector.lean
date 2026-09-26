import Subsp.new.stop_surj_card

open T StopSurjMeasure StopSurjCard

namespace StopSurjVector

def level : Nat → T
  | 0 => T.P 0 T.Z T.Z
  | k + 1 => T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z

def vcons {A : Type} {k : Nat} (a : A) : new.Vec A k → new.Vec A (k + 1)
  | .nil => .snoc 0 .nil a
  | .snoc n xs x => .snoc (n + 1) (vcons a xs) x

def hsum {lam : Nat} : {k : Nat} → new.Vec (new.T lam) k → T
  | 0, .nil => T.Z
  | _ + 1, .snoc m xs x => T.add (T.card_times m (T.early_collapse (trans x))) (hsum xs)

def hfound {lam : Nat} : {k : Nat} → new.Vec (new.T lam) k → Bool
  | 0, .nil => false
  | _ + 1, .snoc _ xs x =>
      match x with
      | new.T.Z => hfound xs
      | new.T.P _ _ => true

theorem vcons_toList {A : Type} {k : Nat} (a : A) (v : new.Vec A k) :
    new.Vec.toList (vcons a v) = a :: new.Vec.toList v := by
  induction v with
  | nil => rfl
  | snoc n xs x ih =>
      rw [vcons, new.Vec.toList, ih]
      rfl

theorem transAux_vcons {lam k : Nat} (a : new.T lam) (v : new.Vec (new.T lam) k) :
    transAux (vcons a v) = (hfound v, hsum v, trans a) := by
  induction v with
  | nil => rfl
  | snoc n xs x ih =>
      rw [vcons, transAux.eq_3, ih, hsum]
      cases x with
      | Z => rfl
      | P ls add => rfl

theorem hsum_vcons {lam k : Nat} (a : new.T lam) (v : new.Vec (new.T lam) k) :
    hsum (vcons a v) = T.add (T.card_times 1 (hsum v)) (T.early_collapse (trans a)) := by
  induction v with
  | nil =>
      rw [vcons, hsum, hsum, tc_card_times_zero]
      change T.add (T.early_collapse (trans a)) T.Z =
        T.add (T.card_times 1 T.Z) (T.early_collapse (trans a))
      rw [T.add_Z, T.card_times.eq_1, T.add.eq_1]
  | snoc n xs x ih =>
      rw [vcons, hsum, ih, hsum, ca_card_times_add, ca_card_times_one_comp,
        Rank1Termination.add_assoc]

theorem hsum_zero_of_not_found {lam k : Nat} (v : new.Vec (new.T lam) k)
    (hf : hfound v = false) : hsum v = T.Z := by
  induction v with
  | nil => rfl
  | snoc n xs x ih =>
      cases x with
      | Z =>
          change hfound xs = false at hf
          rw [hsum, _root_.trans.eq_1]
          change T.add (T.card_times n T.Z) (hsum xs) = T.Z
          rw [T.card_times.eq_1, T.add.eq_1, ih hf]
      | P v a => cases hf

theorem part_small (B s : T) (hnf : T.isNF1 s) (hs : Small B s) :
    Small B (T.part s).1 ∧ Small B (T.part s).2 := by
  have hfst : (T.part s).1 < B := lt_of_le_of_lt_thm T _ _ _
    (bridge_part_fst_le_self s) hs.1
  have hsndle : (T.part s).2 ≤ s := by
    clear hfst
    induction s with
    | Z => exact Or.inr rfl
    | P p a b iha ihb =>
        apply Decidable.byCases (p := p = 0)
        · intro hp
          rw [T.part, ite_eq_left hp]
          exact Or.inr rfl
        · intro hp
          rw [T.part, ite_eq_right hp]
          have hbNF := (T.isNF1_P_inv p a b hnf).2.1
          have hbSmall := (small_inv B p a b hnf hs).2
          have hb := ihb hbNF hbSmall
          exact Or.inl (lt_of_le_of_lt_thm T _ _ _ hb (gc_tail_lt_of_NF1 p a b hnf))
  have hsnd := lt_of_le_of_lt_thm T _ _ _ hsndle hs.1
  have hg : ∀ y, y ∈ T.G1 0 (T.part s).1 ∨ y ∈ T.G1 0 (T.part s).2 → y < B := by
    intro y hy
    apply hs.2 y
    have hadd := bridge_part_add s
    rw [← hadd, bridge_G1_add_eq]
    exact List.mem_append.mpr hy
  exact ⟨⟨hfst, fun y hy => hg y (Or.inl hy)⟩,
    ⟨hsnd, fun y hy => hg y (Or.inr hy)⟩⟩

theorem part_oneChain (s : T) (hi : T.index_Prop1 1 s) : OneChain (T.part s).1 := by
  induction hi with
  | z => exact True.intro
  | p p a b hp hb ih =>
      cases p with
      | zero => exact True.intro
      | succ p =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hp)
          cases hp0
          rw [T.part, ite_eq_right (by intro h; cases h)]
          exact ⟨rfl, ih⟩

theorem index0_of_lt_level_one (s : T) (hs : T.isNF1 s) (hb : s < level 1) :
    T.index_Prop1 0 s := by
  cases s with
  | Z => exact T.index_Prop1.z
  | P p a b =>
      change T.P p a b < T.P 1 T.Z T.Z at hb
      cases lt_inv p a b 1 T.Z T.Z hb with
      | inl hp =>
          exact isNF1_index 0 p a b hs (Nat.le_of_lt_succ hp)
      | inr hr =>
          cases hr with
          | inl hm => exact False.elim (lt_Z_inv hm.2)
          | inr ht => exact False.elim (lt_Z_inv ht.2.2)

theorem exists_hsum {lam : Nat} (C : T) (hC : T.part C = (C, T.Z)) (n : Nat)
    (pre : ∀ x : T, T.isNF1 x → StopUncollapse.Good x → degree x ≤ n → Small C x →
      ∃ sx : new.T lam, new.T.isNFComp sx ∧ trans sx = x)
    (k : Nat) (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 1 s)
    (hb : s < level k) (hd : degree s ≤ n) (hsmall : Small C s) :
    ∃ v : new.Vec (new.T lam) k,
      (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧ hsum v = s ∧
      ∀ B, T.part B = (B, T.Z) → Small B s →
        ∀ x, x ∈ new.Vec.toList v → trans x < B := by
  induction k generalizing s with
  | zero =>
      have hz := bridge_lt_P0ZZ_eq_Z s hb
      cases hz
      refine ⟨new.Vec.nil, ?_, rfl, ?_⟩
      · intro x hx
        cases hx
      · intro B hB hS x hx
        cases hx
  | succ k ih =>
      cases k with
      | zero =>
          have hsIdx := index0_of_lt_level_one s hnf hb
          cases StopUncollapse.exists_uncollapse s hnf hsIdx with
          | intro u hu =>
              have huC := hu.2.2.2.1 C hC hsmall.2 hsmall.1
              have huSmall : Small C u := ⟨huC, fun y hy =>
                lt_trans_thm _ _ _ (hu.2.1 y hy) huC⟩
              cases pre u hu.1 hu.2.1 (Nat.le_trans hu.2.2.2.2 hd) huSmall with
              | intro su hsu =>
                  refine ⟨new.Vec.snoc 0 new.Vec.nil su, ?_, ?_, ?_⟩
                  · intro x hx
                    have he : x = su := List.mem_singleton.mp hx
                    rw [he]
                    exact hsu.1
                  · rw [hsum, hsum, T.add_Z, tc_card_times_zero, hsu.2, hu.2.2.1]
                  · intro B hB hS x hx
                    have he : x = su := List.mem_singleton.mp hx
                    rw [he, hsu.2]
                    exact hu.2.2.2.1 B hB hS.2 hS.1
      | succ k =>
          let H := (T.part s).1
          let L := (T.part s).2
          have hparts := bridge_part_NF1 s hnf
          have hSC := part_small C s hnf hsmall
          have hHbound : H < level (k + 2) := lt_of_le_of_lt_thm T _ _ _
            (bridge_part_fst_le_self s) hb
          cases exists_uncard H hparts.1 (part_oneChain s hi) k hHbound with
          | intro r hr =>
              have hrC := hr.2.2.2.2.2.2 C hC hSC.1
              have hrd : degree r ≤ n := Nat.le_trans hr.2.2.2.2.2.1
                (Nat.le_trans (degree_part s).1 hd)
              cases ih r hr.1 hr.2.1 hr.2.2.2.2.1 hrd hrC with
              | intro vr hvr =>
                  have hLi := ec_part_snd_index0 s hnf
                  cases StopUncollapse.exists_uncollapse L hparts.2 hLi with
                  | intro u hu =>
                      have huC := hu.2.2.2.1 C hC hSC.2.2 hSC.2.1
                      have huSmall : Small C u := ⟨huC, fun y hy =>
                        lt_trans_thm _ _ _ (hu.2.1 y hy) huC⟩
                      have hud : degree u ≤ n := Nat.le_trans hu.2.2.2.2
                        (Nat.le_trans (degree_part s).2 hd)
                      cases pre u hu.1 hu.2.1 hud huSmall with
                      | intro su hsu =>
                          refine ⟨vcons su vr, ?_, ?_, ?_⟩
                          · intro x hx
                            rw [vcons_toList] at hx
                            cases List.mem_cons.mp hx with
                            | inl he => rw [he]; exact hsu.1
                            | inr hm => exact hvr.1 x hm
                          · rw [hsum_vcons, hvr.2.1, hr.2.2.2.1, hsu.2, hu.2.2.1]
                            exact bridge_part_add s
                          · intro B hB hS x hx
                            have hPS := part_small B s hnf hS
                            rw [vcons_toList] at hx
                            cases List.mem_cons.mp hx with
                            | inl he =>
                                rw [he, hsu.2]
                                exact hu.2.2.2.1 B hB hPS.2.2 hPS.2.1
                            | inr hm =>
                                exact hvr.2.2 B hB (hr.2.2.2.2.2.2 B hB hPS.1) x hm

#print axioms exists_hsum

end StopSurjVector

import Subsp.new.stop_surj_vector
import Subsp.new.stop_trans_bounds
import Subsp.new.stop_ot_base

open T StopSurjMeasure StopSurjCard StopSurjVector

namespace StopSurjPrincipal

def unone : T → T
  | T.Z => T.P 0 T.Z T.Z
  | T.P 0 T.Z b => T.P 0 T.Z (T.P 0 T.Z b)
  | t => t

theorem unone_section (s : T) : T.one_del (unone s) = s := by
  cases s with
  | Z => rfl
  | P p a b =>
      cases p with
      | zero => cases a with
          | Z => rfl
          | P q c d => rfl
      | succ p => rfl

theorem unone_ne (s : T) : unone s ≠ T.Z := by
  cases s with
  | Z => intro h; cases h
  | P p a b =>
      cases p with
      | zero => cases a with
          | Z => intro h; cases h
          | P q c d => intro h; cases h
      | succ p => intro h; cases h

theorem unone_props (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 1 s)
    (hne : s ≠ T.Z) :
    T.isNF1 (unone s) ∧ T.index_Prop1 1 (unone s) ∧ degree (unone s) ≤ degree s ∧
      (∀ k, s < level (k + 1) → unone s < level (k + 1)) ∧
      ∀ B, T.part B = (B, T.Z) → Small B s → Small B (unone s) := by
  cases s with
  | Z => exact False.elim (hne rfl)
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z =>
              change T.isNF1 (T.P 0 T.Z (T.P 0 T.Z b)) ∧ _
              have houtNF : T.isNF1 (T.P 0 T.Z (T.P 0 T.Z b)) :=
                T.isNF1.p 0 T.Z (T.P 0 T.Z b) T.isNF1.z hnf
                  (fun y hy => by cases hy) (Or.inr rfl)
              refine ⟨houtNF, T.index_Prop1.p 0 T.Z _ (Nat.zero_le 1) hi, ?_, ?_, ?_⟩
              · change max 1 (max 1 (degree b)) ≤ max 1 (degree b)
                exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩
              · intro k hb
                exact T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)
              · intro B hB hsmall
                have hBne : B ≠ T.Z := by
                  intro hz
                  rw [hz] at hsmall
                  exact lt_Z_inv hsmall.1
                refine ⟨ec_index0_lt_posfixed _ B
                  (isNF1_index 0 0 T.Z _ houtNF (Nat.le_refl 0)) hB hBne, ?_⟩
                intro y hy
                change y ∈ T.G1 0 (T.P 0 T.Z (T.P 0 T.Z b)) at hy
                rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)] at hy
                cases List.mem_append.mp hy with
                | inl hl =>
                    cases List.mem_append.mp hl with
                    | inl he =>
                        rw [List.mem_singleton.mp he]
                        exact tc_Z_lt_of_ne B hBne
                    | inr he => cases he
                | inr he => exact hsmall.2 y he
          | P q c d =>
              refine ⟨hnf, hi, Nat.le_refl _, ?_, ?_⟩
              · intro k hb; exact hb
              · intro B hB hsmall; exact hsmall
      | succ p =>
          refine ⟨hnf, hi, Nat.le_refl _, ?_, ?_⟩
          · intro k hb; exact hb
          · intro B hB hsmall; exact hsmall

theorem transAux_zeros {lam : Nat} (k : Nat) :
    transAux (new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))) = (false, T.Z, T.Z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [new.Vec.ofFn]
      cases k with
      | zero => rfl
      | succ k =>
          rw [transAux.eq_3, ih]
          change (false, T.add (T.card_times k T.Z) T.Z, T.Z) = _
          rw [T.card_times.eq_1, T.add.eq_1]

theorem trans_one (lam : Nat) : trans (new.T.ofNat (lam := lam) 1) = T.P 0 T.Z T.Z := by
  change trans (new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z) = _
  rw [_root_.trans.eq_2, transAux_zeros]
  rfl

theorem hsum_zeros {lam : Nat} (k : Nat) :
    hsum (new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))) = T.Z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [new.Vec.ofFn, hsum, ih]
      change T.add (T.card_times k T.Z) T.Z = T.Z
      rw [T.card_times.eq_1, T.add.eq_1]

theorem unit_vector {lam : Nat} (k : Nat) :
    ∃ v : new.Vec (new.T lam) (k + 1),
      (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧
      hsum v = T.P 0 T.Z T.Z ∧
      ∀ B, T.part B = (B, T.Z) → B ≠ T.Z →
        ∀ x, x ∈ new.Vec.toList v → trans x < B := by
  let zs : new.Vec (new.T lam) k := new.Vec.ofFn k (fun _ => new.T.Z)
  have hzmem : ∀ x, x ∈ new.Vec.toList zs → x = new.T.Z := by
    intro x hx
    cases new.Vec.mem_toList_exists_idx zs x hx with
    | intro i he =>
        rw [← he]
        exact new.Vec.ofFn_idx k (fun _ => new.T.Z) i
  refine ⟨vcons (new.T.ofNat 1) zs, ?_, ?_, ?_⟩
  · intro x hx
    rw [vcons_toList] at hx
    cases List.mem_cons.mp hx with
    | inl he => rw [he]; exact ot_new_ofNat_NFComp 1
    | inr hm => rw [hzmem x hm]; exact new.T.isNFComp_Z
  · rw [hsum_vcons, hsum_zeros, T.card_times.eq_1, T.add.eq_1, trans_one]
    rfl
  · intro B hB hBne x hx
    rw [vcons_toList] at hx
    cases List.mem_cons.mp hx with
    | inl he =>
        rw [he, trans_one]
        exact ec_index0_lt_posfixed _ B (T.index_Prop1.p 0 T.Z T.Z
          (Nat.le_refl 0) T.index_Prop1.z) hB hBne
    | inr hm =>
        rw [hzmem x hm]
        exact tc_Z_lt_of_ne B hBne

theorem higher_preimage (k : Nat) (C : T) (hC : T.part C = (C, T.Z)) (a : T)
    (ha : T.isNF1 a) (hai : T.index_Prop1 1 a) (hb : a < level (k + 2)) (haC : Small C a)
    (pre : ∀ x : T, T.isNF1 x → StopUncollapse.Good x → degree x ≤ degree a → Small C x →
      ∃ sx : new.T (k + 2), new.T.isNFComp sx ∧ trans sx = x) :
    ∃ v : new.Vec (new.T (k + 2)) (k + 2),
      (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧
      trans (new.T.P v new.T.Z) = T.P 1 a T.Z ∧
      ∀ B, T.part B = (B, T.Z) → Small B a →
        ∀ x, x ∈ new.Vec.toList v → trans x < B := by
  let H := (T.part a).1
  let L := (T.part a).2
  have hNF := bridge_part_NF1 a ha
  have hSmall := part_small C a ha haC
  have hHb : H < level (k + 2) := lt_of_le_of_lt_thm T _ _ _
    (bridge_part_fst_le_self a) hb
  cases exists_uncard H hNF.1 (part_oneChain a hai) k hHb with
  | intro r hr =>
      have hv : ∃ v : new.Vec (new.T (k + 2)) (k + 1),
          (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧
          T.one_del (hsum v) = r ∧ hsum v ≠ T.Z ∧
          ∀ B, T.part B = (B, T.Z) → Small B a →
            ∀ x, x ∈ new.Vec.toList v → trans x < B := by
        apply Decidable.byCases (p := r = T.Z)
        · intro hrz
          cases unit_vector (lam := k + 2) k with
          | intro v hv =>
              refine ⟨v, hv.1, ?_, ?_, ?_⟩
              · rw [hv.2.1, hrz]
                rfl
              · rw [hv.2.1]
                intro h; cases h
              · intro B hB hS x hx
                have hBne : B ≠ T.Z := by
                  intro hz
                  rw [hz] at hS
                  exact lt_Z_inv hS.1
                exact hv.2.2 B hB hBne x hx
        · intro hrne
          have hu := unone_props r hr.1 hr.2.1 hrne
          have hrC := hr.2.2.2.2.2.2 C hC hSmall.1
          have huC := hu.2.2.2.2 C hC hrC
          have hud : degree (unone r) ≤ degree a := Nat.le_trans hu.2.2.1
            (Nat.le_trans hr.2.2.2.2.2.1 (degree_part a).1)
          cases exists_hsum C hC (degree a) pre (k + 1) (unone r)
              hu.1 hu.2.1 (hu.2.2.2.1 k hr.2.2.2.2.1) hud huC with
          | intro v hv =>
              refine ⟨v, hv.1, ?_, ?_, ?_⟩
              · rw [hv.2.1, unone_section]
              · rw [hv.2.1]
                exact unone_ne r
              · intro B hB hS x hx
                have hp := part_small B a ha hS
                exact hv.2.2 B hB (hu.2.2.2.2 B hB (hr.2.2.2.2.2.2 B hB hp.1)) x hx
      cases hv with
      | intro v hv =>
          cases StopUncollapse.exists_uncollapse L hNF.2 (ec_part_snd_index0 a ha) with
          | intro u hu =>
              have huC := hu.2.2.2.1 C hC hSmall.2.2 hSmall.2.1
              have huc : Small C u := ⟨huC, fun y hy => lt_trans_thm _ _ _ (hu.2.1 y hy) huC⟩
              cases pre u hu.1 hu.2.1 (Nat.le_trans hu.2.2.2.2 (degree_part a).2) huc with
              | intro su hsu =>
                  refine ⟨vcons su v, ?_, ?_, ?_⟩
                  · intro x hx
                    rw [vcons_toList] at hx
                    cases List.mem_cons.mp hx with
                    | inl he => rw [he]; exact hsu.1
                    | inr hm => exact hv.1 x hm
                  · have hf : hfound v = true := by
                      cases he : hfound v with
                      | false => exact False.elim (hv.2.2.1 (hsum_zero_of_not_found v he))
                      | true => rfl
                    rw [_root_.trans.eq_2, transAux_vcons, hf]
                    change T.P 1 (T.add (T.card_times 1 (T.one_del (hsum v)))
                      (T.early_collapse (trans su))) T.Z = T.P 1 a T.Z
                    rw [hv.2.1, hr.2.2.2.1, hsu.2, hu.2.2.1, bridge_part_add]
                  · intro B hB hS x hx
                    rw [vcons_toList] at hx
                    cases List.mem_cons.mp hx with
                    | inl he =>
                        rw [he, hsu.2]
                        have hp := part_small B a ha hS
                        exact hu.2.2.2.1 B hB hp.2.2 hp.2.1
                    | inr hm => exact hv.2.2.2 B hB hS x hm

#print axioms higher_preimage

end StopSurjPrincipal

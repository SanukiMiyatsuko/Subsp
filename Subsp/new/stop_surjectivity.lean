import Subsp.new.stop_ot
import Subsp.new.stop_inverse

/-! Translation into SubNF and constructive surjectivity in every dimension. -/

/-! The target subtype and soundness of translation. -/

section SubNFImage

def T.isSubNF (n : Nat) (s : T) :=
  isNF1 s ∧ s < P 0 (ot_trans_bound n) Z

theorem OT_imp_NF1 (lam : Nat) (s : new.T lam) : new.T.isOT lam s → T.isSubNF lam (trans s) := by
  intro hs
  have hnf := ot_new_isOT_sound lam s hs
  constructor
  · exact NF_is_NF1 lam s hnf.1
  · cases lam with
    | zero =>
        cases s with
        | Z => exact T.Lt.Z_lt_P 0 _ T.Z
        | P v add =>
            cases v with
            | nil =>
                change T.P 0 T.Z (trans add) < T.P 0 (T.P 0 T.Z T.Z) T.Z
                exact T.Lt.p_mid 0 _ _ _ _ (T.Lt.Z_lt_P 0 T.Z T.Z)
    | succ k =>
        cases s with
        | Z => exact T.Lt.Z_lt_P 0 _ T.Z
        | P v add =>
            let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
            have hv : v = ot_v0 k (v.idx i0) := by
              apply ot_vec_ext
              intro i
              unfold ot_v0
              rw [new.Vec.ofFn_idx]
              by_cases hi : i.val = 0
              · rw [ite_eq_left hi]
                have heq : i = i0 := Fin.eq_of_val_eq hi
                rw [heq]
              · rw [ite_eq_right hi]
                cases k with
                | zero =>
                    exact False.elim (hi (Nat.eq_zero_of_le_zero
                      (Nat.le_of_lt_succ i.isLt)))
                | succ k =>
                    have hk : 1 < k + 1 + 1 :=
                      Nat.succ_lt_succ (Nat.zero_lt_succ k)
                    exact ot_bound_coords_zero v add (hnf.2 hk)
                      i (Nat.pos_of_ne_zero hi)
            have ha := new.T.isNF_P_coord_NFComp v add hnf.1 i0
            have hb := ot_trans_global_bound (v.idx i0) ha.1 (Nat.zero_lt_succ k)
            have htrans : trans (new.T.P v add) = T.P 0 (trans (v.idx i0)) (trans add) := by
              rw [← ot_trans_v0 k (v.idx i0) add, ← hv]
            rw [htrans]
            exact T.Lt.p_mid 0 _ _ _ _ hb

def T.SubNF (lam : Nat) := { t : T // isSubNF lam t }

end SubNFImage

/-! Reconstruction in dimensions zero and one. -/

section LowDimensionalSurjectivity

open T

namespace StopSurjLow

def B1 : T := T.P 0 (T.P 1 T.Z T.Z) T.Z
def C1 : T := T.P 1 T.Z T.Z

def v1 (a : new.T 1) : new.Vec (new.T 1) 1 :=
  new.Vec.snoc 0 new.Vec.nil a

theorem trans_v1 (a b : new.T 1) :
    trans (new.T.P (v1 a) b) = T.P 0 (trans a) (trans b) := by
  exact ot_trans_v0 0 a b

theorem lt_B1_inv (p : Nat) (a b : T)
    (h : T.P p a b < B1) : p = 0 ∧ a < C1 := by
  unfold B1 at h
  unfold C1
  rcases lt_inv p a b 0 (T.P 1 T.Z T.Z) T.Z h with hp | (hm | ht)
  · exact False.elim (Nat.not_lt_zero p hp)
  · exact ⟨hm.1, hm.2⟩
  · exact False.elim (lt_Z_inv ht.2.2)

theorem lt_C1_head_zero (p : Nat) (a b : T)
    (h : T.P p a b < C1) : p = 0 := by
  unfold C1 at h
  rcases lt_inv p a b 1 T.Z T.Z h with hp | (hm | ht)
  · exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hp)
  · exact False.elim (lt_Z_inv hm.2)
  · exact False.elim (lt_Z_inv ht.2.2)

theorem trans_G_lam1 {s y : new.T 1}
    (hy : y ∈ new.T.G s) : trans y ∈ T.G1 0 (trans s) := by
  induction s using new.T.rec
      (motive_2 := fun _ v => ∀ x, x ∈ new.Vec.toList v →
        ∀ y, y ∈ new.T.G x → trans y ∈ T.G1 0 (trans x)) generalizing y with
  | Z => cases hy
  | P ls add ihls ihadd =>
      cases ls with
      | snoc _ xs a =>
          cases xs with
          | nil =>
              change trans y ∈ T.G1 0 (trans (new.T.P (v1 a) add))
              rw [trans_v1, T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
              rcases (new.T.mem_G_P (v1 a) add y).mp hy with hc | htail
              · obtain ⟨i, hi⟩ := hc
                have hi0 : i = ⟨0, Nat.zero_lt_succ 0⟩ :=
                  Fin.eq_of_val_eq (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
                cases hi0
                apply List.mem_append_left
                rcases hi with heq | hga
                · change y = a at heq
                  rw [heq]
                  exact List.mem_append_left _ (List.mem_singleton_self _)
                · exact List.mem_append_right _ (ihls a (List.mem_singleton_self a) y hga)
              · exact List.mem_append_right _ (ihadd htail)
  | nil x hx y _ => cases hx
  | snoc _ xs x ihxs ihx z hz y hy =>
      rcases List.mem_append.mp hz with hz | hz
      · exact ihxs z hz y hy
      · have hzx := List.mem_singleton.mp hz
        cases hzx
        exact ihx hy

theorem surj1_pair :
    ∀ a : T, T.isNF1 a →
      ((a < B1 → ∃ s : new.T 1, new.T.isNF s ∧ trans s = a) ∧
       ((∀ y : T, y ∈ T.G1 0 a → y < a) → a < C1 →
          ∃ s : new.T 1, new.T.isNFComp s ∧ trans s = a)) := by
  intro a
  induction a with
  | Z =>
      intro _
      exact ⟨fun _ => ⟨new.T.Z, new.T.isNF.z, rfl⟩,
        fun _ _ => ⟨new.T.Z, new.T.isNFComp_Z, rfl⟩⟩
  | P p c d ihc ihd =>
      intro hnf
      have hinv := T.isNF1_P_inv p c d hnf
      have hpre : T.P p c d < B1 →
          ∃ s : new.T 1, new.T.isNF s ∧ trans s = T.P p c d := by
        intro hb
        have hshape := lt_B1_inv p c d hb
        have hp0 := hshape.1
        cases hp0
        obtain ⟨sc, hsc⟩ := (ihc hinv.1).2 hinv.2.2.1 hshape.2
        have hdB := lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 0 c d hnf) hb
        obtain ⟨sd, hsd⟩ := (ihd hinv.2.1).1 hdB
        have hv : ∀ x, x ∈ new.Vec.toList (v1 sc) → new.T.isNFComp x := by
          intro x hx
          rw [List.mem_singleton.mp hx]
          exact hsc.1
        have hpNF : new.T.isNF (new.T.P (v1 sc) new.T.Z) :=
          new.T.isNF.p (v1 sc) new.T.Z (fun x hx => (hv x hx).1)
            new.T.isNF.z (fun x hx => (hv x hx).2) (new.T.Z_le _)
        have hheadTrans : trans (new.T.head sd) ≤ trans (new.T.P (v1 sc) new.T.Z) := by
          rw [tc_trans_head, trans_v1, hsd.2, hsc.2]
          exact hinv.2.2.2
        have hhead := gnf_reflect_le (new.T.head sd) (new.T.P (v1 sc) new.T.Z)
          (nfcore_head_NF sd hsd.1) hpNF hheadTrans
        refine ⟨new.T.P (v1 sc) sd,
          new.T.isNF.p (v1 sc) sd (fun x hx => (hv x hx).1)
            hsd.1 (fun x hx => (hv x hx).2) hhead, ?_⟩
        rw [trans_v1, hsc.2, hsd.2]
      refine ⟨hpre, ?_⟩
      intro hgood hcBound
      have hp0 := lt_C1_head_zero p c d hcBound
      cases hp0
      have hcMem : c ∈ T.G1 0 (T.P 0 c d) := by
        rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self c))
      have hcLt := lt_trans_thm _ _ _ (hgood c hcMem) hcBound
      obtain ⟨s, hs⟩ := hpre (T.Lt.p_mid 0 c C1 d T.Z hcLt)
      refine ⟨s, ⟨hs.1, ?_⟩, hs.2⟩
      intro y hy
      have hyNF := (new.T.isNF_G_isNFComp s hs.1 y hy).1
      apply (gnf_order_embedding y s hyNF hs.1).mpr
      have hmem := trans_G_lam1 hy
      rw [hs.2] at hmem ⊢
      exact hgood (trans y) hmem

def B0 : T := T.P 0 (T.P 0 T.Z T.Z) T.Z

theorem trans_v0 (b : new.T 0) :
    trans (new.T.P new.Vec.nil b) = T.P 0 T.Z (trans b) := by
  rw [_root_.trans.eq_2, transAux.eq_1]
  rfl

theorem lt_B0_inv (p : Nat) (a b : T)
    (h : T.P p a b < B0) : p = 0 ∧ a < T.P 0 T.Z T.Z := by
  unfold B0 at h
  rcases lt_inv p a b 0 (T.P 0 T.Z T.Z) T.Z h with hp | (hm | ht)
  · exact False.elim (Nat.not_lt_zero p hp)
  · exact ⟨hm.1, hm.2⟩
  · exact False.elim (lt_Z_inv ht.2.2)

theorem surj_SubNF0_raw :
    ∀ t : T, T.isNF1 t → t < B0 →
      ∃ s : new.T 0, new.T.isNF s ∧ trans s = t := by
  intro t
  induction t with
  | Z =>
      intro _ _
      exact ⟨new.T.Z, new.T.isNF.z, rfl⟩
  | P p a b iha ihb =>
      intro hnf hbound
      have hinv := T.isNF1_P_inv p a b hnf
      have hshape := lt_B0_inv p a b hbound
      have hp0 := hshape.1
      cases hp0
      have haZ := bridge_lt_P0ZZ_eq_Z a hshape.2
      cases haZ
      have hbBound := lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 0 T.Z b hnf) hbound
      obtain ⟨sb, hsb⟩ := ihb hinv.2.1 hbBound
      have hpNF : new.T.isNF (new.T.P new.Vec.nil new.T.Z) := by
        apply new.T.isNF_PZ_of_coords
        intro i
        exact i.elim0
      have hheadTrans : trans (new.T.head sb) ≤ trans (new.T.P new.Vec.nil new.T.Z) := by
        rw [tc_trans_head, trans_v0, hsb.2]
        exact hinv.2.2.2
      have hhead := gnf_reflect_le (new.T.head sb) (new.T.P new.Vec.nil new.T.Z)
        (nfcore_head_NF sb hsb.1) hpNF hheadTrans
      refine ⟨new.T.P new.Vec.nil sb,
        new.T.isNF.p new.Vec.nil sb (fun x hx => by cases hx)
          hsb.1 (fun x hx => by cases hx) hhead, ?_⟩
      rw [trans_v0, hsb.2]

end StopSurjLow

end LowDimensionalSurjectivity

/-! Reconstruction of higher coordinates and principal terms. -/

section VectorReconstruction

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
    clear hfst hs
    induction hnf with
    | z => exact Or.inr rfl
    | p p a b ha hb hg hh _ ihb =>
        by_cases hp : p = 0
        · rw [T.part, ite_eq_left hp]
          exact Or.inr rfl
        · rw [T.part, ite_eq_right hp]
          exact Or.inl (lt_of_le_of_lt_thm T _ _ _ ihb
            (gc_tail_lt_of_NF1 p a b (T.isNF1.p p a b ha hb hg hh)))
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
  | p p a b hp _ ih =>
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
      rcases lt_inv p a b 1 T.Z T.Z hb with hp | (hm | ht)
      · exact isNF1_index 0 p a b hs (Nat.le_of_lt_succ hp)
      · exact False.elim (lt_Z_inv hm.2)
      · exact False.elim (lt_Z_inv ht.2.2)

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
      · intro B _ _ x hx
        cases hx
  | succ k ih =>
      cases k with
      | zero =>
          have hsIdx := index0_of_lt_level_one s hnf hb
          obtain ⟨u, hu⟩ := StopUncollapse.exists_uncollapse s hnf hsIdx
          have huC := hu.2.2.2.1 C hC hsmall.2 hsmall.1
          have huSmall : Small C u := ⟨huC, fun y hy =>
            lt_trans_thm _ _ _ (hu.2.1 y hy) huC⟩
          obtain ⟨su, hsu⟩ := pre u hu.1 hu.2.1 (Nat.le_trans hu.2.2.2.2 hd) huSmall
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
          obtain ⟨r, hr⟩ := exists_uncard H hparts.1 (part_oneChain s hi) k hHbound
          have hrC := hr.2.2.2.2.2.2 C hC hSC.1
          have hrd : degree r ≤ n := Nat.le_trans hr.2.2.2.2.2.1
            (Nat.le_trans (degree_part s).1 hd)
          obtain ⟨vr, hvr⟩ := ih r hr.1 hr.2.1 hr.2.2.2.2.1 hrd hrC
          have hLi := ec_part_snd_index0 s hnf
          obtain ⟨u, hu⟩ := StopUncollapse.exists_uncollapse L hparts.2 hLi
          have huC := hu.2.2.2.1 C hC hSC.2.2 hSC.2.1
          have huSmall : Small C u := ⟨huC, fun y hy =>
            lt_trans_thm _ _ _ (hu.2.1 y hy) huC⟩
          have hud : degree u ≤ n := Nat.le_trans hu.2.2.2.2
            (Nat.le_trans (degree_part s).2 hd)
          obtain ⟨su, hsu⟩ := pre u hu.1 hu.2.1 hud huSmall
          refine ⟨vcons su vr, ?_, ?_, ?_⟩
          · intro x hx
            rw [vcons_toList] at hx
            rcases List.mem_cons.mp hx with he | hm
            · rw [he]; exact hsu.1
            · exact hvr.1 x hm
          · rw [hsum_vcons, hvr.2.1, hr.2.2.2.1, hsu.2, hu.2.2.1]
            exact bridge_part_add s
          · intro B hB hS x hx
            have hPS := part_small B s hnf hS
            rw [vcons_toList] at hx
            rcases List.mem_cons.mp hx with he | hm
            · rw [he, hsu.2]
              exact hu.2.2.2.1 B hB hPS.2.2 hPS.2.1
            · exact hvr.2.2 B hB (hr.2.2.2.2.2.2 B hB hPS.1) x hm

end StopSurjVector

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
              · intro k _
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
                rcases List.mem_append.mp hy with hl | he
                · cases List.mem_append.mp hl with
                  | inl he =>
                      rw [List.mem_singleton.mp he]
                      exact tc_Z_lt_of_ne B hBne
                  | inr he => cases he
                · exact hsmall.2 y he
          | P q c d =>
              refine ⟨hnf, hi, Nat.le_refl _, ?_, ?_⟩
              · intro k hb; exact hb
              · intro B _ hsmall; exact hsmall
      | succ p =>
          refine ⟨hnf, hi, Nat.le_refl _, ?_, ?_⟩
          · intro k hb; exact hb
          · intro B _ hsmall; exact hsmall

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
    obtain ⟨i, he⟩ := new.Vec.mem_toList_exists_idx zs x hx
    rw [← he]
    exact new.Vec.ofFn_idx k (fun _ => new.T.Z) i
  refine ⟨vcons (new.T.ofNat 1) zs, ?_, ?_, ?_⟩
  · intro x hx
    rw [vcons_toList] at hx
    rcases List.mem_cons.mp hx with he | hm
    · rw [he]; exact ot_new_ofNat_NFComp 1
    · rw [hzmem x hm]; exact new.T.isNFComp_Z
  · rw [hsum_vcons, hsum_zeros, T.card_times.eq_1, T.add.eq_1, trans_one]
    rfl
  · intro B hB hBne x hx
    rw [vcons_toList] at hx
    rcases List.mem_cons.mp hx with he | hm
    · rw [he, trans_one]
      exact ec_index0_lt_posfixed _ B (T.index_Prop1.p 0 T.Z T.Z
        (Nat.le_refl 0) T.index_Prop1.z) hB hBne
    · rw [hzmem x hm]
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
  obtain ⟨r, hr⟩ := exists_uncard H hNF.1 (part_oneChain a hai) k hHb
  have hv : ∃ v : new.Vec (new.T (k + 2)) (k + 1),
      (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧
      T.one_del (hsum v) = r ∧ hsum v ≠ T.Z ∧
      ∀ B, T.part B = (B, T.Z) → Small B a →
        ∀ x, x ∈ new.Vec.toList v → trans x < B := by
    apply Decidable.byCases (p := r = T.Z)
    · intro hrz
      obtain ⟨v, hv⟩ := unit_vector (lam := k + 2) k
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
  obtain ⟨v, hv⟩ := hv
  obtain ⟨u, hu⟩ := StopUncollapse.exists_uncollapse L hNF.2 (ec_part_snd_index0 a ha)
  have huC := hu.2.2.2.1 C hC hSmall.2.2 hSmall.2.1
  have huc : Small C u := ⟨huC, fun y hy => lt_trans_thm _ _ _ (hu.2.1 y hy) huC⟩
  obtain ⟨su, hsu⟩ := pre u hu.1 hu.2.1 (Nat.le_trans hu.2.2.2.2 (degree_part a).2) huc
  refine ⟨vcons su v, ?_, ?_, ?_⟩
  · intro x hx
    rw [vcons_toList] at hx
    rcases List.mem_cons.mp hx with he | hm
    · rw [he]; exact hsu.1
    · exact hv.1 x hm
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
    rcases List.mem_cons.mp hx with he | hm
    · rw [he, hsu.2]
      have hp := part_small B a ha hS
      exact hu.2.2.2.1 B hB hp.2.2 hp.2.1
    · exact hv.2.2.2 B hB hS x hm

end StopSurjPrincipal

end VectorReconstruction

/-! Support preservation and induction on exponent depth. -/

section GeneralReconstruction

open T StopSurjMeasure StopSurjCard StopSurjVector StopSurjPrincipal

namespace StopSurjSupport

/-- A recovered coordinate is controlled either by a target support term or by
every fixed positive-index bound on the support of the target's high part. -/
def Supported (t y : T) : Prop :=
  (∃ z, z ∈ T.G1 0 t ∧ y ≤ z) ∨
  (∀ B, T.part B = (B, T.Z) →
    (∀ z, z ∈ T.G1 0 (T.part t).1 → z < B) → y < B)

def Preimage {lam : Nat} (t : T) (s : new.T lam) : Prop :=
  new.T.isNF s ∧ trans s = t ∧ ∀ y, y ∈ new.T.G s → Supported t (trans y)

theorem supported_le (t x y : T) (hxy : x ≤ y) (hy : Supported t y) : Supported t x := by
  rcases hy with hw | h
  · obtain ⟨z, hz⟩ := hw
    exact Or.inl ⟨z, hz.1, partial_order.trans x y z hxy hz.2⟩
  · apply Or.inr
    intro B hB hG
    exact lt_of_le_of_lt_thm T _ _ _ hxy (h B hB hG)

theorem comp_of_preimage {lam : Nat} (t : T) (s : new.T lam)
    (hs : Preimage t s) (hg : StopUncollapse.Good t) : new.T.isNFComp s := by
  refine ⟨hs.1, ?_⟩
  intro y hy
  have hynf := (new.T.isNF_G_isNFComp s hs.1 y hy).1
  apply (gnf_order_embedding y s hynf hs.1).mpr
  rw [hs.2.1]
  rcases hs.2.2 y hy with hw | h
  · obtain ⟨z, hz⟩ := hw
    exact lt_of_le_of_lt_thm T _ _ _ hz.2 (hg z hz.1)
  · exact lt_of_lt_of_le_thm T _ _ _
      (h (T.part t).1 (bridge_part_fst_fixed t) (sg_good0_part_fst t hg))
      (bridge_part_fst_le_self t)

theorem supported_tail (p : Nat) (a b y : T) (hnf : T.isNF1 (T.P p a b))
    (h : Supported b y) : Supported (T.P p a b) y := by
  rcases h with hw | h
  · obtain ⟨z, hz⟩ := hw
    refine Or.inl ⟨z, ?_, hz.2⟩
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
    exact List.mem_append_right _ hz.1
  · cases p with
    | zero =>
        have hi := isNF1_index 0 0 a b hnf (Nat.le_refl 0)
        have hbidx : T.index_Prop1 0 b := by
          cases hi with
          | p _ _ _ hp hb => exact hb
        have hp := StopUncollapse.part_of_index0 b hbidx
        have hbad : y < T.Z := h T.Z rfl (by
          intro z hz
          rw [hp] at hz
          cases hz)
        exact False.elim (lt_Z_inv hbad)
    | succ p =>
        apply Or.inr
        intro B hB hG
        apply h B hB
        intro z hz
        apply hG z
        rw [T.part, ite_eq_right (Nat.succ_ne_zero p)]
        change z ∈ T.G1 0 (T.P (p + 1) a (T.part b).1)
        rw [T.G1.eq_2, ite_eq_left (Nat.zero_le (p + 1))]
        exact List.mem_append_right _ hz

theorem supported_middle (p : Nat) (a b x : T) (hxa : x ≤ a) : Supported (T.P p a b) x := by
  refine Or.inl ⟨a, ?_, hxa⟩
  rw [T.G1.eq_2, ite_eq_left (Nat.zero_le p)]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))

theorem supported_higher (a b x : T)
    (h : ∀ B, T.part B = (B, T.Z) → Small B a → x < B) : Supported (T.P 1 a b) x := by
  apply Or.inr
  intro B hB hG
  apply h B hB
  have hG' : ∀ z, z ∈ T.G1 0 (T.P 1 a (T.part b).1) → z < B := by
    intro z hz
    apply hG z
    rw [T.part, ite_eq_right (by intro h; cases h)]
    exact hz
  constructor
  · apply hG' a
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1)]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self a))
  · intro z hz
    apply hG' z
    rw [T.G1.eq_2, ite_eq_left (Nat.zero_le 1)]
    exact List.mem_append_left _ (List.mem_append_right _ hz)

theorem assemble {lam : Nat} (p : Nat) (a b : T) (hnf : T.isNF1 (T.P p a b))
    (v : new.Vec (new.T lam) lam) (sb : new.T lam)
    (hv : ∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x)
    (htrans : trans (new.T.P v new.T.Z) = T.P p a T.Z)
    (hsb : Preimage b sb)
    (hcoord : ∀ x, x ∈ new.Vec.toList v → Supported (T.P p a b) (trans x)) :
    Preimage (T.P p a b) (new.T.P v sb) := by
  have hpNF : new.T.isNF (new.T.P v new.T.Z) := by
    apply new.T.isNF_PZ_of_coords
    intro i
    exact hv (v.idx i) (new.Vec.idx_mem_toList v i)
  have hheadT : trans (new.T.head sb) ≤ trans (new.T.P v new.T.Z) := by
    rw [tc_trans_head, hsb.2.1, htrans]
    exact (T.isNF1_P_inv p a b hnf).2.2.2
  have hhead := gnf_reflect_le (new.T.head sb) (new.T.P v new.T.Z)
    (nfcore_head_NF sb hsb.1) hpNF hheadT
  have hsNF : new.T.isNF (new.T.P v sb) := new.T.isNF.p v sb
    (fun x hx => (hv x hx).1) hsb.1 (fun x hx => (hv x hx).2) hhead
  refine ⟨hsNF, ?_, ?_⟩
  · rw [tc_trans_P_add, htrans, hsb.2.1, T.P_add_eq, T.add.eq_1]
  · intro y hy
    rcases (new.T.mem_G_P v sb y).mp hy with hc | ht
    · obtain ⟨i, hi⟩ := hc
      have hmem := new.Vec.idx_mem_toList v i
      rcases hi with he | hg
      · rw [he]; exact hcoord (v.idx i) hmem
      · have hxi := hv (v.idx i) hmem
        have hyNF := (new.T.isNF_G_isNFComp (v.idx i) hxi.1 y hg).1
        have hlt := (gnf_order_embedding y (v.idx i) hyNF hxi.1).mp (hxi.2 y hg)
        exact supported_le _ _ _ (Or.inl hlt) (hcoord (v.idx i) hmem)
    · exact supported_tail p a b (trans y) hnf (hsb.2.2 y ht)

end StopSurjSupport

open T StopSurjMeasure StopSurjCard StopSurjVector StopSurjPrincipal StopSurjSupport

namespace StopSurjGeneral

theorem index1_of_lt_principal (a c : T) (hnf : T.isNF1 a)
    (ha : a < T.P 1 c T.Z) : T.index_Prop1 1 a := by
  cases a with
  | Z => exact T.index_Prop1.z
  | P p u v =>
      apply isNF1_index 1 p u v hnf
      rcases lt_inv p u v 1 c T.Z ha with hp | (hm | ht)
      · exact Nat.le_of_lt hp
      · rw [hm.1]; exact Nat.le_refl 1
      · exact False.elim (lt_Z_inv ht.2.2)

/-- Induct on exponent depth, then on the tail. The inverse collapse and inverse
cardinal operations preserve depth, so all coordinates use the outer hypothesis.
The support invariant recovers `isNFComp` when the input has bounded support. -/
theorem exists_preimage (k : Nat) (t : T) (hnf : T.isNF1 t)
    (hsmall : Small (ot_trans_bound (k + 2)) t) :
    ∃ s : new.T (k + 2), Preimage t s := by
  let C := ot_trans_bound (k + 2)
  have hC : T.part C = (C, T.Z) := rfl
  let motive : Nat → Prop := fun n =>
    ∀ t : T, degree t ≤ n → T.isNF1 t → Small C t →
      ∃ s : new.T (k + 2), Preimage t s
  have main : ∀ n, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro t
      induction t with
      | Z =>
          intro _ _ _
          refine ⟨new.T.Z, new.T.isNF.z, rfl, ?_⟩
          intro y hy
          cases hy
      | P p a b _ ihb =>
          intro hd hn hS
          have hparts := T.isNF1_P_inv p a b hn
          have hPS := small_inv C p a b hn hS
          have hda : degree a < n := Nat.lt_of_lt_of_le (degree_middle_lt p a b) hd
          have pre : ∀ x : T, T.isNF1 x → StopUncollapse.Good x → degree x ≤ degree a → Small C x →
              ∃ sx : new.T (k + 2), new.T.isNFComp sx ∧ trans sx = x := by
            intro x hx hg hdx hxc
            obtain ⟨sx, hsx⟩ := ih (degree x) (Nat.lt_of_le_of_lt hdx hda) x (Nat.le_refl _) hx hxc
            exact ⟨sx, comp_of_preimage x sx hsx hg, hsx.2.1⟩
          obtain ⟨sb, hsb⟩ := ihb (Nat.le_trans (degree_tail_le p a b) hd) hparts.2.1 hPS.2
          cases p with
          | zero =>
              obtain ⟨sa, hsa⟩ := pre a hparts.1 hparts.2.2.1 (Nat.le_refl _) hPS.1
              let v := ot_v0 (k + 1) sa
              have hvi : ∀ i : Fin (k + 2), new.T.isNFComp (v.idx i) ∧
                  Supported (T.P 0 a b) (trans (v.idx i)) := by
                intro i
                unfold v ot_v0
                rw [new.Vec.ofFn_idx]
                by_cases hi : i.val = 0
                · rw [ite_eq_left hi]
                  refine ⟨hsa.1, ?_⟩
                  rw [hsa.2]
                  exact supported_middle 0 a b a (Or.inr rfl)
                · rw [ite_eq_right hi]
                  exact ⟨new.T.isNFComp_Z, supported_middle 0 a b T.Z (T.Z_le a)⟩
              have hv : ∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x ∧
                  Supported (T.P 0 a b) (trans x) := by
                intro x hx
                obtain ⟨i, he⟩ := new.Vec.mem_toList_exists_idx v x hx
                rw [← he]; exact hvi i
              have htrans : trans (new.T.P v new.T.Z) = T.P 0 a T.Z := by
                rw [ot_trans_v0, hsa.2]
                rfl
              exact ⟨new.T.P v sb, assemble 0 a b hn v sb
                (fun x hx => (hv x hx).1) htrans hsb (fun x hx => (hv x hx).2)⟩
          | succ p =>
              have hshape : p + 1 = 1 ∧ a < level (k + 2) := by
                change Small (T.P 1 (level (k + 2)) T.Z) (T.P (p + 1) a b) at hS
                rcases lt_inv (p + 1) a b 1 (level (k + 2)) T.Z hS.1 with hp | (hm | ht)
                · exact False.elim (Nat.not_lt_zero p (Nat.lt_of_succ_lt_succ hp))
                · exact hm
                · exact False.elim (lt_Z_inv ht.2.2)
              have hp0 : p = 0 := Nat.succ.inj hshape.1
              cases hp0
              have hai := index1_of_lt_principal a _ hparts.1 hshape.2
              obtain ⟨v, hv⟩ := higher_preimage k C hC a hparts.1 hai hshape.2 hPS.1 pre
              refine ⟨new.T.P v sb, assemble 1 a b hn v sb hv.1 hv.2.1 hsb ?_⟩
              intro x hx
              exact supported_higher a b (trans x) (fun B hB hSm => hv.2.2 B hB hSm x hx))
  exact main (degree t) t (Nat.le_refl _) hnf hsmall

end StopSurjGeneral

end GeneralReconstruction

/-! Surjectivity onto SubNF for every dimension. -/

section SurjectivityInterface

theorem exists_OT_of_SubNF_zero (t : T) (ht : T.isSubNF 0 t) :
    ∃ s, new.T.isOT 0 s ∧ trans s = t := by
  obtain ⟨s, hs⟩ := StopSurjLow.surj_SubNF0_raw t ht.1 ht.2
  refine ⟨s, ?_, hs.2⟩
  apply (new.T.OT_iff_NF 0 s).mpr
  refine ⟨hs.1, ?_⟩
  intro h
  exact False.elim (Nat.not_lt_zero 1 h)

theorem exists_OT_of_SubNF_one (t : T) (ht : T.isSubNF 1 t) :
    ∃ s, new.T.isOT 1 s ∧ trans s = t := by
  obtain ⟨s, hs⟩ := (StopSurjLow.surj1_pair t ht.1).1 ht.2
  refine ⟨s, ?_, hs.2⟩
  apply (new.T.OT_iff_NF 1 s).mpr
  refine ⟨hs.1, ?_⟩
  intro h
  exact False.elim (Nat.lt_irrefl 1 h)

theorem ot_bound_NF (lam : Nat) : new.T.isNF (ot_bound lam) := by
  apply new.T.isNF_PZ_of_coords
  intro i
  rw [new.Vec.ofFn_idx]
  by_cases hi : i.val = 1
  · rw [ite_eq_left hi]
    exact ot_new_ofNat_NFComp 1
  · rw [ite_eq_right hi]
    exact new.T.isNFComp_Z

theorem transAux_ot_bound {lam : Nat} (k : Nat) (u : new.T lam)
    (hu : trans u = T.P 0 T.Z T.Z) :
    transAux (new.Vec.ofFn (k + 2) (fun i => if i.val = 1 then u else new.T.Z)) =
      (true, T.P 0 T.Z T.Z, T.Z) := by
  induction k with
  | zero =>
      change transAux (new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil new.T.Z) u) = _
      rw [transAux.eq_3, transAux.eq_2]
      cases u with
      | Z => cases hu
      | P v a => rw [hu]; rfl
  | succ k ih =>
      rw [new.Vec.ofFn]
      have hlast : (Fin.last (k + 2)).val ≠ 1 :=
        Nat.ne_of_gt (Nat.succ_lt_succ (Nat.zero_lt_succ k))
      rw [ite_eq_right hlast]
      change transAux (new.Vec.snoc (k + 2)
        (new.Vec.ofFn (k + 2) (fun i => if i.val = 1 then u else new.T.Z)) new.T.Z) = _
      rw [transAux.eq_3, ih]
      change (true, T.add (T.card_times (k + 1) T.Z) (T.P 0 T.Z T.Z), T.Z) = _
      rw [T.card_times.eq_1, T.add.eq_1]

theorem trans_ot_bound (k : Nat) : trans (ot_bound (k + 2)) = T.P 1 T.Z T.Z := by
  unfold ot_bound
  rw [_root_.trans.eq_2, transAux_ot_bound k (ot_unit (k + 2))
    (StopSurjPrincipal.trans_one (k + 2))]
  rfl

theorem exists_OT_of_SubNF_succ_succ (k : Nat) (t : T)
    (ht : T.isSubNF (k + 2) t) :
    ∃ s, new.T.isOT (k + 2) s ∧ trans s = t := by
  have hsmall : StopSurjCard.Small (ot_trans_bound (k + 2)) t ∧ t < T.P 1 T.Z T.Z := by
    cases t with
    | Z =>
        refine ⟨⟨T.Lt.Z_lt_P 1 _ T.Z, ?_⟩, T.Lt.Z_lt_P 1 T.Z T.Z⟩
        intro y hy
        cases hy
    | P p a b =>
        have hb : T.P p a b < T.P 0 (ot_trans_bound (k + 2)) T.Z := ht.2
        have hshape : p = 0 ∧ a < ot_trans_bound (k + 2) := by
          rcases lt_inv p a b 0 (ot_trans_bound (k + 2)) T.Z hb with hp | (hm | htail)
          · exact False.elim (Nat.not_lt_zero p hp)
          · exact hm
          · exact False.elim (lt_Z_inv htail.2.2)
        have hp0 := hshape.1
        cases hp0
        refine ⟨⟨T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0), ?_⟩,
          T.Lt.p_head 0 1 _ _ _ _ (Nat.zero_lt_succ 0)⟩
        intro y hy
        have hya := StopUncollapse.support_le_of_head (T.P 0 a b) a ht.1 (Or.inr rfl) y hy
        exact lt_of_le_of_lt_thm T _ _ _ hya hshape.2
  obtain ⟨s, hs⟩ := StopSurjGeneral.exists_preimage k t ht.1 hsmall.1
  have hsb : s < ot_bound (k + 2) := by
    apply (order_embeding (k + 2) s (ot_bound (k + 2)) hs.1 (ot_bound_NF (k + 2))).mpr
    rw [hs.2.1, trans_ot_bound]
    exact hsmall.2
  refine ⟨s, ?_, hs.2.1⟩
  exact (new.T.OT_iff_NF (k + 2) s).mpr ⟨hs.1, fun _ => hsb⟩

theorem exists_OT_of_SubNF (lam : Nat) (t : T)
    (ht : T.isSubNF lam t) :
    ∃ s, new.T.isOT lam s ∧ trans s = t := by
  cases lam with
  | zero => exact exists_OT_of_SubNF_zero t ht
  | succ k =>
      cases k with
      | zero => exact exists_OT_of_SubNF_one t ht
      | succ k => exact exists_OT_of_SubNF_succ_succ k t ht

end SurjectivityInterface

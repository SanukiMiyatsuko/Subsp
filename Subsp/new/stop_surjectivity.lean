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
  refine ⟨NF_is_NF1 lam s hnf.1, ?_⟩
  cases lam with
  | zero =>
      cases s with
      | Z => exact T.Lt.Z_lt_P _ _ _
      | P v a => cases v; exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)
  | succ k =>
      cases s with
      | Z => exact T.Lt.Z_lt_P _ _ _
      | P v a =>
          let i0 : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
          have hv : v = ot_v0 k (v.idx i0) := by
            apply ot_vec_ext
            intro i
            simp only [ot_v0, new.Vec.ofFn_idx]
            split
            · exact congrArg v.idx (Fin.ext ‹_›)
            · exact ot_bound_coords_zero v a (hnf.2 (by omega)) i (by omega)
          have ha := new.T.isNF_P_coord_NFComp v a hnf.1 i0
          rw [hv, ot_trans_v0]
          exact T.Lt.p_mid _ _ _ _ _ (ot_trans_global_bound (v.idx i0) ha.1 (Nat.zero_lt_succ k))

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
  cases h with
  | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
  | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
  | p_tail _ _ _ _ h => cases h

theorem lt_C1_head_zero (p : Nat) (a b : T)
    (h : T.P p a b < C1) : p = 0 := by
  cases h with
  | p_head _ _ _ _ _ _ h => omega
  | p_mid _ _ _ _ _ h => cases h
  | p_tail _ _ _ _ h => cases h

theorem trans_G_lam1 {s y : new.T 1}
    (hy : y ∈ new.T.G s) : trans y ∈ T.G1 0 (trans s) := by
  induction s using new.T.rec
      (motive_2 := fun _ v => ∀ x ∈ new.Vec.toList v, ∀ y ∈ new.T.G x, trans y ∈ T.G1 0 (trans x)) generalizing y with
  | Z => cases hy
  | P ls a ihls iha =>
      cases ls with
      | snoc _ xs c =>
          cases xs
          change trans y ∈ T.G1 0 (trans (new.T.P (v1 c) a))
          rw [trans_v1]
          simp [new.T.G, new.T.G.res] at hy
          simp [T.G1]
          rcases hy with rfl | hy | hy
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (ihls c (by simp [new.Vec.toList]) y hy))
          · exact Or.inr (Or.inr (iha hy))
  | nil x hx y _ => cases hx
  | snoc _ xs x ihxs ihx z hz y hy =>
      rcases List.mem_append.mp hz with hz | hz
      · exact ihxs z hz y hy
      · obtain rfl := List.mem_singleton.mp hz; exact ihx hy

theorem surj1_pair :
    ∀ a : T, T.isNF1 a →
      ((a < B1 → ∃ s : new.T 1, new.T.isNF s ∧ trans s = a) ∧
       ((∀ y : T, y ∈ T.G1 0 a → y < a) → a < C1 →
          ∃ s : new.T 1, new.T.isNFComp s ∧ trans s = a)) := by
  intro a
  induction a with
  | Z => exact fun _ => ⟨fun _ => ⟨new.T.Z, new.T.isNF.z, rfl⟩,
      fun _ _ => ⟨new.T.Z, new.T.isNFComp_Z, rfl⟩⟩
  | P p c d ihc ihd =>
      intro hn
      have hi := T.isNF1_P_inv p c d hn
      have hpre : T.P p c d < B1 → ∃ s : new.T 1, new.T.isNF s ∧ trans s = T.P p c d := by
        intro hb
        obtain ⟨rfl, hc⟩ := lt_B1_inv p c d hb
        obtain ⟨sc, hsc, hec⟩ := (ihc hi.1).2 hi.2.2.1 hc
        obtain ⟨sd, hsd, hed⟩ := (ihd hi.2.1).1 (lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 _ _ _ hn) hb)
        have hv : ∀ x ∈ new.Vec.toList (v1 sc), new.T.isNFComp x := by simpa [v1, new.Vec.toList] using hsc
        have hp := new.T.isNF.p (v1 sc) new.T.Z (fun x hx => (hv x hx).1) new.T.isNF.z (fun x hx => (hv x hx).2) (new.T.Z_le _)
        have hh := gnf_reflect_le (new.T.head sd) _ (nfcore_head_NF sd hsd) hp
          (by rw [tc_trans_head, trans_v1, hed, hec]; exact hi.2.2.2)
        exact ⟨new.T.P (v1 sc) sd,
          new.T.isNF.p _ _ (fun x hx => (hv x hx).1) hsd (fun x hx => (hv x hx).2) hh,
          by rw [trans_v1, hec, hed]⟩
      refine ⟨hpre, fun hg hb => ?_⟩
      obtain rfl := lt_C1_head_zero p c d hb
      have hc := lt_trans_thm _ _ _ (hg c (bridge_mid_mem_G1_zero c d)) hb
      obtain ⟨s, hs, he⟩ := hpre (T.Lt.p_mid _ _ _ _ _ hc)
      refine ⟨s, ⟨hs, ?_⟩, he⟩
      intro y hy
      apply (gnf_order_embedding y s (new.T.isNF_G_isNFComp s hs y hy).1 hs).mpr
      have hm := trans_G_lam1 hy
      rw [he] at hm ⊢
      exact hg (trans y) hm

def B0 : T := T.P 0 (T.P 0 T.Z T.Z) T.Z

theorem trans_v0 (b : new.T 0) :
    trans (new.T.P new.Vec.nil b) = T.P 0 T.Z (trans b) := by
  rfl

theorem lt_B0_inv (p : Nat) (a b : T)
    (h : T.P p a b < B0) : p = 0 ∧ a < T.P 0 T.Z T.Z := by
  cases h with
  | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
  | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
  | p_tail _ _ _ _ h => cases h

theorem surj_SubNF0_raw :
    ∀ t : T, T.isNF1 t → t < B0 →
      ∃ s : new.T 0, new.T.isNF s ∧ trans s = t := by
  intro t
  induction t with
  | Z => exact fun _ _ => ⟨new.T.Z, new.T.isNF.z, rfl⟩
  | P p a b _ ih =>
      intro hn hb
      obtain ⟨rfl, ha⟩ := lt_B0_inv p a b hb
      obtain rfl := bridge_lt_P0ZZ_eq_Z a ha
      have hi := T.isNF1_P_inv _ _ _ hn
      obtain ⟨sb, hnf, he⟩ := ih hi.2.1 (lt_trans_thm _ _ _ (gc_tail_lt_of_NF1 _ _ _ hn) hb)
      have hp := new.T.isNF_PZ_of_coords new.Vec.nil (fun i => i.elim0)
      have hh := gnf_reflect_le (new.T.head sb) (new.T.P new.Vec.nil new.T.Z) (nfcore_head_NF sb hnf) hp
        (by rw [tc_trans_head, trans_v0, he]; exact hi.2.2.2)
      exact ⟨new.T.P new.Vec.nil sb, new.T.isNF.p _ _ (by intro x hx; cases hx) hnf (by intro x hx; cases hx) hh,
        by rw [trans_v0, he]⟩

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
  | snoc n xs x ih => simp [vcons, new.Vec.toList, ih]

theorem transAux_vcons {lam k : Nat} (a : new.T lam) (v : new.Vec (new.T lam) k) :
    transAux (vcons a v) = (hfound v, hsum v, trans a) := by
  induction v with
  | nil => rfl
  | snoc n xs x ih => rw [vcons, transAux.eq_3, ih, hsum]; cases x <;> rfl

theorem hsum_vcons {lam k : Nat} (a : new.T lam) (v : new.Vec (new.T lam) k) :
    hsum (vcons a v) = T.add (T.card_times 1 (hsum v)) (T.early_collapse (trans a)) := by
  induction v with
  | nil => simp [vcons, hsum, tc_card_times_zero, T.add_Z, T.card_times, T.add.eq_1]
  | snoc n xs x ih => rw [vcons, hsum, ih, hsum, ca_card_times_add, ca_card_times_one_comp, Rank1Termination.add_assoc]

theorem hsum_zero_of_not_found {lam k : Nat} (v : new.Vec (new.T lam) k)
    (hf : hfound v = false) : hsum v = T.Z := by
  induction v with
  | nil => rfl
  | snoc n xs x ih =>
      cases x with
      | Z => exact ih hf
      | P v a => cases hf

theorem part_small (B s : T) (hnf : T.isNF1 s) (hs : Small B s) :
    Small B (T.part s).1 ∧ Small B (T.part s).2 := by
  have hsnd : (T.part s).2 ≤ s := by
    clear hs
    induction hnf with
    | z => exact Or.inr rfl
    | p p a b ha hb hg hh _ ih =>
        by_cases hp : p = 0
        · simp only [T.part, ite_eq_left hp]; exact Or.inr rfl
        · simp only [T.part, ite_eq_right hp]
          exact partial_order.trans _ _ _ ih (T.isNF1_tail_le _ (T.isNF1.p p a b ha hb hg hh) _ _ _ rfl)
  have hg : ∀ y, y ∈ T.G1 0 (T.part s).1 ∨ y ∈ T.G1 0 (T.part s).2 → y < B := by
    intro y hy
    apply hs.2
    rw [← bridge_part_add s, bridge_G1_add_eq, List.mem_append]
    exact hy
  exact ⟨⟨lt_of_le_of_lt_thm T _ _ _ (bridge_part_fst_le_self s) hs.1, fun y hy => hg y (Or.inl hy)⟩,
    lt_of_le_of_lt_thm T _ _ _ hsnd hs.1, fun y hy => hg y (Or.inr hy)⟩

theorem part_oneChain (s : T) (hi : T.index_Prop1 1 s) : OneChain (T.part s).1 := by
  induction hi with
  | z => trivial
  | p p a b hp _ ih =>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
      · trivial
      · exact ⟨rfl, ih⟩

theorem index0_of_lt_level_one (s : T) (hs : T.isNF1 s) (hb : s < level 1) :
    T.index_Prop1 0 s := by
  cases hb with
  | Z_lt_P => exact T.index_Prop1.z
  | p_head p _ a _ b _ hp => exact isNF1_index 0 p a b hs (Nat.le_of_lt_succ hp)
  | p_mid _ _ _ _ _ h => cases h
  | p_tail _ _ _ _ h => cases h

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
      obtain rfl := bridge_lt_P0ZZ_eq_Z s hb
      exact ⟨new.Vec.nil, (by intro x hx; cases hx), rfl, by intro B _ _ x hx; cases hx⟩
  | succ k ih =>
      cases k with
      | zero =>
          obtain ⟨u, hu, hgu, hec, hbound, hdu⟩ := StopUncollapse.exists_uncollapse s hnf (index0_of_lt_level_one s hnf hb)
          have huC := hbound C hC hsmall.2 hsmall.1
          obtain ⟨su, hsu, he⟩ := pre u hu hgu (Nat.le_trans hdu hd) ⟨huC, fun y hy => lt_trans_thm _ _ _ (hgu y hy) huC⟩
          refine ⟨new.Vec.snoc 0 new.Vec.nil su, ?_, ?_, ?_⟩
          · simpa [new.Vec.toList] using hsu
          · rw [hsum, hsum, T.add_Z, tc_card_times_zero, he, hec]
          · intro B hB hS x hx
            rw [List.mem_singleton.mp hx, he]
            exact hbound B hB hS.2 hS.1
      | succ k =>
          have hp := bridge_part_NF1 s hnf
          have hSC := part_small C s hnf hsmall
          obtain ⟨r, hr, hir, _, he, hb, hdr, hsmallr⟩ := exists_uncard _ hp.1 (part_oneChain s hi) k
            (lt_of_le_of_lt_thm T _ _ _ (bridge_part_fst_le_self s) hb)
          obtain ⟨vr, hvr, her, hbr⟩ := ih r hr hir hb
            (Nat.le_trans hdr (Nat.le_trans (degree_part s).1 hd)) (hsmallr C hC hSC.1)
          obtain ⟨u, hu, hgu, hec, hbu, hdu⟩ := StopUncollapse.exists_uncollapse _ hp.2 (ec_part_snd_index0 s hnf)
          have huC := hbu C hC hSC.2.2 hSC.2.1
          obtain ⟨su, hsu, heu⟩ := pre u hu hgu (Nat.le_trans hdu (Nat.le_trans (degree_part s).2 hd))
            ⟨huC, fun y hy => lt_trans_thm _ _ _ (hgu y hy) huC⟩
          refine ⟨vcons su vr, ?_, ?_, ?_⟩
          · simpa [vcons_toList] using And.intro hsu hvr
          · rw [hsum_vcons, her, he, heu, hec, bridge_part_add]
          · intro B hB hS x hx
            have hPS := part_small B s hnf hS
            rw [vcons_toList, List.mem_cons] at hx
            rcases hx with rfl | hx
            · rw [heu]; exact hbu B hB hPS.2.2 hPS.2.1
            · exact hbr B hB (hsmallr B hB hPS.1) x hx

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
  | P p a b => cases p <;> cases a <;> rfl

theorem unone_ne (s : T) : unone s ≠ T.Z := by
  cases s with
  | Z => intro h; cases h
  | P p a b => cases p <;> cases a <;> intro h <;> cases h

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
              have hout := T.isNF1.p 0 T.Z (T.P 0 T.Z b) T.isNF1.z hnf (by intro y hy; cases hy) (Or.inr rfl)
              refine ⟨hout, T.index_Prop1.p _ _ _ (Nat.zero_le 1) hi, ?_, ?_, ?_⟩
              · change max 1 (max 1 (degree b)) ≤ max 1 (degree b)
                exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩
              · exact fun k _ => T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
              · intro B hB hs
                have hn : B ≠ T.Z := by intro h; rw [h] at hs; exact lt_Z_inv hs.1
                refine ⟨ec_index0_lt_posfixed _ B (isNF1_index 0 0 T.Z _ hout (Nat.le_refl 0)) hB hn, ?_⟩
                intro y hy
                simp [unone, T.G1] at hy
                rcases hy with rfl | hy
                · exact tc_Z_lt_of_ne B hn
                · exact hs.2 y (by simp [T.G1, hy])
          | P q c d => exact ⟨hnf, hi, Nat.le_refl _, fun _ hb => hb, fun _ _ hs => hs⟩
      | succ p => exact ⟨hnf, hi, Nat.le_refl _, fun _ hb => hb, fun _ _ hs => hs⟩

theorem transAux_zeros {lam : Nat} (k : Nat) :
    transAux (new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))) = (false, T.Z, T.Z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [new.Vec.ofFn]
      cases k with
      | zero => rfl
      | succ k => rw [transAux.eq_3, ih]; rfl

theorem trans_one (lam : Nat) : trans (new.T.ofNat (lam := lam) 1) = T.P 0 T.Z T.Z := by
  simp [new.T.ofNat, _root_.trans.eq_2, _root_.trans.eq_1, transAux_zeros]

theorem hsum_zeros {lam : Nat} (k : Nat) :
    hsum (new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))) = T.Z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [new.Vec.ofFn, hsum, ih]; rfl

theorem unit_vector {lam : Nat} (k : Nat) :
    ∃ v : new.Vec (new.T lam) (k + 1),
      (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧
      hsum v = T.P 0 T.Z T.Z ∧
      ∀ B, T.part B = (B, T.Z) → B ≠ T.Z →
        ∀ x, x ∈ new.Vec.toList v → trans x < B := by
  let zs := new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))
  have hzmem : ∀ x ∈ new.Vec.toList zs, x = new.T.Z := by
    intro x hx
    obtain ⟨i, rfl⟩ := new.Vec.mem_toList_exists_idx zs x hx
    exact new.Vec.ofFn_idx _ _ i
  refine ⟨vcons (new.T.ofNat 1) zs, ?_, ?_, ?_⟩
  · intro x hx
    rw [vcons_toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ot_new_ofNat_NFComp 1
    · rw [hzmem x hx]; exact new.T.isNFComp_Z
  · rw [hsum_vcons, hsum_zeros, T.card_times.eq_1, T.add.eq_1, trans_one]; rfl
  · intro B hB hn x hx
    rw [vcons_toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [trans_one]
      exact ec_index0_lt_posfixed _ B (T.index_Prop1.p _ _ _ (Nat.le_refl _) T.index_Prop1.z) hB hn
    · rw [hzmem x hx]; exact tc_Z_lt_of_ne B hn

theorem higher_preimage (k : Nat) (C : T) (hC : T.part C = (C, T.Z)) (a : T)
    (ha : T.isNF1 a) (hai : T.index_Prop1 1 a) (hb : a < level (k + 2)) (haC : Small C a)
    (pre : ∀ x : T, T.isNF1 x → StopUncollapse.Good x → degree x ≤ degree a → Small C x →
      ∃ sx : new.T (k + 2), new.T.isNFComp sx ∧ trans sx = x) :
    ∃ v : new.Vec (new.T (k + 2)) (k + 2),
      (∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x) ∧
      trans (new.T.P v new.T.Z) = T.P 1 a T.Z ∧
      ∀ B, T.part B = (B, T.Z) → Small B a →
        ∀ x, x ∈ new.Vec.toList v → trans x < B := by
  have hp := bridge_part_NF1 a ha
  have hSmall := part_small C a ha haC
  obtain ⟨r, hr, hir, _, her, hbr, hdr, hsmallr⟩ := exists_uncard _ hp.1 (part_oneChain a hai) k
    (lt_of_le_of_lt_thm T _ _ _ (bridge_part_fst_le_self a) hb)
  obtain ⟨v, hv, hdel, hne, hbound⟩ : ∃ v : new.Vec (new.T (k + 2)) (k + 1),
      (∀ x ∈ new.Vec.toList v, new.T.isNFComp x) ∧ T.one_del (hsum v) = r ∧ hsum v ≠ T.Z ∧
      (∀ B, T.part B = (B, T.Z) → Small B a → ∀ x ∈ new.Vec.toList v, trans x < B) := by
    by_cases hz : r = T.Z
    · obtain ⟨v, hv, he, hb⟩ := unit_vector (lam := k + 2) k
      refine ⟨v, hv, by rw [he, hz]; rfl, ?_, ?_⟩
      · rw [he]; intro h; cases h
      · exact fun B hB hS => hb B hB (by intro h; rw [h] at hS; exact lt_Z_inv hS.1)
    · obtain ⟨hu, hiu, hdu, hbu, hsmallu⟩ := unone_props r hr hir hz
      obtain ⟨v, hv, he, hb⟩ := exists_hsum C hC (degree a) pre (k + 1) (unone r) hu hiu (hbu k hbr)
        (Nat.le_trans hdu (Nat.le_trans hdr (degree_part a).1)) (hsmallu C hC (hsmallr C hC hSmall.1))
      refine ⟨v, hv, by rw [he, unone_section], by rw [he]; exact unone_ne r, ?_⟩
      exact fun B hB hS => hb B hB (hsmallu B hB (hsmallr B hB (part_small B a ha hS).1))
  obtain ⟨u, hu, hgu, hec, hbu, hdu⟩ := StopUncollapse.exists_uncollapse _ hp.2 (ec_part_snd_index0 a ha)
  have huC := hbu C hC hSmall.2.2 hSmall.2.1
  obtain ⟨su, hsu, heu⟩ := pre u hu hgu (Nat.le_trans hdu (degree_part a).2)
    ⟨huC, fun y hy => lt_trans_thm _ _ _ (hgu y hy) huC⟩
  refine ⟨vcons su v, ?_, ?_, ?_⟩
  · simpa [vcons_toList] using And.intro hsu hv
  · have hf : hfound v = true := by
      cases he : hfound v with
      | false => exact False.elim (hne (hsum_zero_of_not_found v he))
      | true => rfl
    rw [_root_.trans.eq_2, transAux_vcons, hf]
    change T.P 1 (T.add (T.card_times 1 (T.one_del (hsum v))) (T.early_collapse (trans su))) T.Z = _
    rw [hdel, her, heu, hec, bridge_part_add]
  · intro B hB hS x hx
    rw [vcons_toList, List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [heu]
      have hPS := part_small B a ha hS
      exact hbu B hB hPS.2.2 hPS.2.1
    · exact hbound B hB hS x hx

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
  rcases hy with ⟨z, hz, h⟩ | h
  · exact Or.inl ⟨z, hz, partial_order.trans _ _ _ hxy h⟩
  · exact Or.inr (fun B hB hG => lt_of_le_of_lt_thm T _ _ _ hxy (h B hB hG))

theorem comp_of_preimage {lam : Nat} (t : T) (s : new.T lam)
    (hs : Preimage t s) (hg : StopUncollapse.Good t) : new.T.isNFComp s := by
  refine ⟨hs.1, ?_⟩
  intro y hy
  apply (gnf_order_embedding y s (new.T.isNF_G_isNFComp s hs.1 y hy).1 hs.1).mpr
  rw [hs.2.1]
  rcases hs.2.2 y hy with ⟨z, hz, hle⟩ | h
  · exact lt_of_le_of_lt_thm T _ _ _ hle (hg z hz)
  · exact lt_of_lt_of_le_thm T _ _ _
      (h (T.part t).1 (bridge_part_fst_fixed t) (sg_good0_part_fst t hg)) (bridge_part_fst_le_self t)

theorem supported_tail (p : Nat) (a b y : T) (hnf : T.isNF1 (T.P p a b))
    (h : Supported b y) : Supported (T.P p a b) y := by
  rcases h with ⟨z, hz, hyz⟩ | h
  · exact Or.inl ⟨z, by simp [T.G1, hz], hyz⟩
  · cases p with
    | zero =>
        have hi := isNF1_index 0 0 a b hnf (Nat.le_refl 0)
        cases hi with
        | p _ _ _ _ hb =>
            exact False.elim (lt_Z_inv (h T.Z rfl (by simp [StopUncollapse.part_of_index0 b hb, T.G1])))
    | succ p =>
        exact Or.inr (fun B hB hG => h B hB (fun z hz => hG z (by simp [T.part, T.G1, hz])))

theorem supported_middle (p : Nat) (a b x : T) (hxa : x ≤ a) : Supported (T.P p a b) x := by
  exact Or.inl ⟨a, by simp [T.G1], hxa⟩

theorem supported_higher (a b x : T)
    (h : ∀ B, T.part B = (B, T.Z) → Small B a → x < B) : Supported (T.P 1 a b) x := by
  apply Or.inr
  intro B hB hG
  apply h B hB
  simp [T.part, T.G1] at hG
  exact ⟨hG.1, fun z hz => hG.2 z (Or.inl hz)⟩

theorem assemble {lam : Nat} (p : Nat) (a b : T) (hnf : T.isNF1 (T.P p a b))
    (v : new.Vec (new.T lam) lam) (sb : new.T lam)
    (hv : ∀ x, x ∈ new.Vec.toList v → new.T.isNFComp x)
    (htrans : trans (new.T.P v new.T.Z) = T.P p a T.Z)
    (hsb : Preimage b sb)
    (hcoord : ∀ x, x ∈ new.Vec.toList v → Supported (T.P p a b) (trans x)) :
    Preimage (T.P p a b) (new.T.P v sb) := by
  have hp := new.T.isNF_PZ_of_coords v (fun i => hv _ (new.Vec.idx_mem_toList v i))
  have hh := gnf_reflect_le (new.T.head sb) _ (nfcore_head_NF sb hsb.1) hp
    (by rw [tc_trans_head, hsb.2.1, htrans]; exact (T.isNF1_P_inv _ _ _ hnf).2.2.2)
  refine ⟨new.T.isNF.p v sb (fun x hx => (hv x hx).1) hsb.1 (fun x hx => (hv x hx).2) hh, ?_, ?_⟩
  · rw [tc_trans_P_add, htrans, hsb.2.1, T.P_add_eq, T.add.eq_1]
  · intro y hy
    rcases (new.T.mem_G_P v sb y).mp hy with ⟨i, hi⟩ | ht
    · have hm := new.Vec.idx_mem_toList v i
      rcases hi with rfl | hi
      · exact hcoord _ hm
      · have hx := hv _ hm
        have hynf := (new.T.isNF_G_isNFComp _ hx.1 y hi).1
        exact supported_le _ _ _ (Or.inl ((gnf_order_embedding y _ hynf hx.1).mp (hx.2 y hi))) (hcoord _ hm)
    · exact supported_tail p a b _ hnf (hsb.2.2 y ht)

end StopSurjSupport

open T StopSurjMeasure StopSurjCard StopSurjVector StopSurjPrincipal StopSurjSupport

namespace StopSurjGeneral

theorem index1_of_lt_principal (a c : T) (hnf : T.isNF1 a)
    (ha : a < T.P 1 c T.Z) : T.index_Prop1 1 a := by
  cases a with
  | Z => exact T.index_Prop1.z
  | P p u v => exact isNF1_index 1 p u v hnf (head_le_index p 1 u c (T.head_mono ha))

/-- Induct on exponent depth, then on the tail. The inverse collapse and inverse
cardinal operations preserve depth, so all coordinates use the outer hypothesis.
The support invariant recovers `isNFComp` when the input has bounded support. -/
theorem exists_preimage (k : Nat) (t : T) (hnf : T.isNF1 t)
    (hsmall : Small (ot_trans_bound (k + 2)) t) :
    ∃ s : new.T (k + 2), Preimage t s := by
  let C := ot_trans_bound (k + 2)
  have hC : T.part C = (C, T.Z) := rfl
  suffices H : ∀ n (t : T), degree t ≤ n → T.isNF1 t → Small C t → ∃ s : new.T (k + 2), Preimage t s by
    exact H (degree t) t (Nat.le_refl _) hnf hsmall
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro t
      induction t with
      | Z => exact fun _ _ _ => ⟨new.T.Z, new.T.isNF.z, rfl, by intro y hy; cases hy⟩
      | P p a b _ ihb =>
          intro hd hn hS
          have hp := T.isNF1_P_inv p a b hn
          have hPS := small_inv C p a b hn hS
          have hda := Nat.lt_of_lt_of_le (degree_middle_lt p a b) hd
          have pre : ∀ x, T.isNF1 x → StopUncollapse.Good x → degree x ≤ degree a → Small C x →
              ∃ sx : new.T (k + 2), new.T.isNFComp sx ∧ trans sx = x := by
            intro x hx hg hdx hxc
            obtain ⟨sx, hsx⟩ := ih (degree x) (Nat.lt_of_le_of_lt hdx hda) x (Nat.le_refl _) hx hxc
            exact ⟨sx, comp_of_preimage x sx hsx hg, hsx.2.1⟩
          obtain ⟨sb, hsb⟩ := ihb (Nat.le_trans (degree_tail_le p a b) hd) hp.2.1 hPS.2
          cases p with
          | zero =>
              obtain ⟨sa, hsa, he⟩ := pre a hp.1 hp.2.2.1 (Nat.le_refl _) hPS.1
              let v := ot_v0 (k + 1) sa
              have hv : ∀ x ∈ new.Vec.toList v, new.T.isNFComp x ∧ Supported (T.P 0 a b) (trans x) := by
                intro x hx
                obtain ⟨i, rfl⟩ := new.Vec.mem_toList_exists_idx v x hx
                simp only [v, ot_v0, new.Vec.ofFn_idx]
                split
                · exact ⟨hsa, by rw [he]; exact supported_middle 0 a b a (Or.inr rfl)⟩
                · exact ⟨new.T.isNFComp_Z, supported_middle 0 a b T.Z (T.Z_le a)⟩
              exact ⟨new.T.P v sb, assemble 0 a b hn v sb (fun x hx => (hv x hx).1)
                (by rw [ot_trans_v0, he]; rfl) hsb (fun x hx => (hv x hx).2)⟩
          | succ p =>
              have hshape : p + 1 = 1 ∧ a < level (k + 2) := by
                change Small (T.P 1 (level (k + 2)) T.Z) (T.P (p + 1) a b) at hS
                cases hS.1 with
                | p_head _ _ _ _ _ _ h => exfalso; omega
                | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
                | p_tail _ _ _ _ h => cases h
              have hp0 : p = 0 := by omega
              subst p
              obtain ⟨v, hv, he, hbound⟩ := higher_preimage k C hC a hp.1
                (index1_of_lt_principal a _ hp.1 hshape.2) hshape.2 hPS.1 pre
              exact ⟨new.T.P v sb, assemble 1 a b hn v sb hv he hsb
                (fun x hx => supported_higher a b _ (fun B hB hSm => hbound B hB hSm x hx))⟩

end StopSurjGeneral

end GeneralReconstruction

/-! Surjectivity onto SubNF for every dimension. -/

section SurjectivityInterface

theorem exists_OT_of_SubNF_zero (t : T) (ht : T.isSubNF 0 t) :
    ∃ s, new.T.isOT 0 s ∧ trans s = t := by
  obtain ⟨s, hs, he⟩ := StopSurjLow.surj_SubNF0_raw t ht.1 ht.2
  exact ⟨s, (new.T.OT_iff_NF 0 s).mpr ⟨hs, by intro h; exfalso; omega⟩, he⟩

theorem exists_OT_of_SubNF_one (t : T) (ht : T.isSubNF 1 t) :
    ∃ s, new.T.isOT 1 s ∧ trans s = t := by
  obtain ⟨s, hs, he⟩ := (StopSurjLow.surj1_pair t ht.1).1 ht.2
  exact ⟨s, (new.T.OT_iff_NF 1 s).mpr ⟨hs, by intro h; exfalso; omega⟩, he⟩

theorem ot_bound_NF (lam : Nat) : new.T.isNF (ot_bound lam) := by
  apply new.T.isNF_PZ_of_coords
  intro i
  simp only [new.Vec.ofFn_idx]
  split
  · exact ot_new_ofNat_NFComp 1
  · exact new.T.isNFComp_Z

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
      simp only [Fin.val_last, Fin.val_castSucc, show k + 2 ≠ 1 by omega, ite_false]
      rw [transAux.eq_3, ih]
      rfl

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
    | Z => exact ⟨⟨T.Lt.Z_lt_P _ _ _, by intro y hy; cases hy⟩, T.Lt.Z_lt_P _ _ _⟩
    | P p a b =>
        have hshape : p = 0 ∧ a < ot_trans_bound (k + 2) := by
          cases ht.2 with
          | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
          | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
          | p_tail _ _ _ _ h => cases h
        obtain ⟨rfl, ha⟩ := hshape
        refine ⟨⟨T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0), ?_⟩,
          T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)⟩
        exact fun y hy => lt_of_le_of_lt_thm T _ _ _ (StopUncollapse.support_le_of_head _ a ht.1 (Or.inr rfl) y hy) ha
  obtain ⟨s, hs⟩ := StopSurjGeneral.exists_preimage k t ht.1 hsmall.1
  refine ⟨s, (new.T.OT_iff_NF (k + 2) s).mpr ⟨hs.1, fun _ => ?_⟩, hs.2.1⟩
  apply (order_embeding (k + 2) s (ot_bound (k + 2)) hs.1 (ot_bound_NF (k + 2))).mpr
  rw [hs.2.1, trans_ot_bound]
  exact hsmall.2

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

import Subsp.multi.Uncollapse
import Subsp.multi.new.trans

/-! Surjectivity of the `new` translation onto the Buchholz normal forms below
`ψ_0(Ω^{Ω^ω})`. -/

namespace new

open MT

/-! ### Bounded support -/

/-- `s` and its level-zero support lie below `B`. -/
def Small (B s : T) : Prop := s < B ∧ ∀ y, y ∈ T.G1 0 s → y < B

theorem small_inv {B : T} {p : Nat} {a b : T} (hnf : T.isNF1 (T.P p a b))
    (h : Small B (T.P p a b)) : Small B a ∧ Small B b := by
  have hG : ∀ y, y ∈ T.G1 0 (T.P p a b) → y < B := h.2
  refine ⟨⟨hG a ((G1_P_mem (Nat.zero_le p)).2 (Or.inl rfl)),
    fun y hy => hG y ((G1_P_mem (Nat.zero_le p)).2 (Or.inr (Or.inl hy)))⟩,
    lt_trans_thm _ _ _ (tail_lt_of_NF1 hnf) h.1,
    fun y hy => hG y ((G1_P_mem (Nat.zero_le p)).2 (Or.inr (Or.inr hy)))⟩

theorem part_snd_le (s : T) (hnf : T.isNF1 s) : (part s).2 ≤ s := by
  induction hnf with
  | z => exact Or.inr rfl
  | p p a b ha hb hg hh _ ih =>
    by_cases hp : p = 0
    · simp only [part, ite_eq_left hp]; exact Or.inr rfl
    · simp only [part, ite_eq_right hp]
      exact partial_order.trans _ _ _ ih (T.isNF1_tail_le _ (T.isNF1.p p a b ha hb hg hh) _ _ _ rfl)

theorem part_small (B s : T) (hnf : T.isNF1 s) (hs : Small B s) :
    Small B (part s).1 ∧ Small B (part s).2 := by
  have hg : ∀ y, y ∈ T.G1 0 (part s).1 ∨ y ∈ T.G1 0 (part s).2 → y < B := by
    intro y hy
    apply hs.2
    rw [← part_add s, G1_add, List.mem_append]
    exact hy
  exact ⟨⟨lt_of_le_of_lt_thm T _ _ _ (part_fst_le_self s) hs.1, fun y hy => hg y (Or.inl hy)⟩,
    lt_of_le_of_lt_thm T _ _ _ (part_snd_le s hnf) hs.1, fun y hy => hg y (Or.inr hy)⟩

/-! ### Inverting multiplication by `Ω` -/

def Good1 (s : T) : Prop := ∀ y, y ∈ T.G1 1 s → y < s

def OneChain : T → Prop
  | T.Z => True
  | T.P p _ b => p = 1 ∧ OneChain b

theorem part_oneChain (s : T) (hi : T.index_Prop1 1 s) : OneChain (part s).1 := by
  induction hi with
  | z => trivial
  | p p a b hp _ ih =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl
    · trivial
    · exact ⟨rfl, ih⟩

theorem card_append1 (p : Nat) (a b : T) :
    card 1 (T.P p a b) = T.add (card 1 (T.P p a T.Z)) (card 1 b) := by
  rw [show T.P p a b = T.add (T.P p a T.Z) b from by rw [T.P_add_eq]; rfl, card_add_gen]

theorem card1_single (p : Nat) (a : T) : ∃ m, card 1 (T.P p a T.Z) = T.P 1 m T.Z := by
  cases p with
  | zero => exact ⟨_, by rw [card_P0, card_Z]⟩
  | succ p =>
    show ∃ m, (if p + 1 = 0 then _ else _) + card 1 T.Z = T.P 1 m T.Z
    rw [card_Z, hadd_eq, T.add_Z]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem card_head (s : T) : card 1 (T.head s) = T.head (card 1 s) := by
  cases s with
  | Z => rfl
  | P p a b =>
    obtain ⟨m, hm⟩ := card1_single p a
    show card 1 (T.P p a T.Z) = _
    rw [card_append1 p a b, hm, T.P_add_eq]
    rfl

theorem head_nf {s : T} (hs : T.isNF1 s) : T.isNF1 (T.head s) := by
  cases hs with
  | z => exact T.isNF1.z
  | p p a b ha hb hg hh => exact T.isNF1.p p a T.Z ha T.isNF1.z hg (T.Z_le _)

theorem head_idx {s : T} (hs : T.index_Prop1 1 s) : T.index_Prop1 1 (T.head s) := by
  cases hs with
  | z => exact T.index_Prop1.z
  | p p a b hp hb => exact T.index_Prop1.p p a T.Z hp T.index_Prop1.z

theorem card1_lt {s t : T} (hs : T.isNF1 s) (hi : T.index_Prop1 1 s) (ht : T.isNF1 t)
    (hj : T.index_Prop1 1 t) (h : s < t) : card 1 s < card 1 t := by
  have := card1_append_lt T.Z T.Z hs hi ht hj h T.index_Prop1.z
  rwa [T.add_Z, T.add_Z] at this

theorem card1_reflect_le {s t : T} (hs : T.isNF1 s) (ht : T.isNF1 t) (hsi : T.index_Prop1 1 s)
    (hti : T.index_Prop1 1 t) (h : card 1 s ≤ card 1 t) : s ≤ t := by
  rcases lt_total_thm s t with hst | hts | he
  · exact Or.inl hst
  · exact absurd (lt_of_lt_of_le_thm T _ _ _ (card1_lt ht hti hs hsi hts) h) (lt_irrefl_thm _)
  · exact Or.inr he

theorem below_mul_support (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) :
    T.index_Prop1 1 a ∧ ∀ y, y ∈ T.G1 1 a → y = T.Z := by
  induction k generalizing a with
  | zero => exact absurd ha lt_Z_inv
  | succ k ih =>
    rw [mul_succ_shape] at ha
    cases ha with
    | Z_lt_P => exact ⟨T.index_Prop1.z, by intro y hy; cases hy⟩
    | p_head p _ c _ d _ hp =>
      have hp0 : p = 0 := by omega
      subst p
      have hi := isNF1_index 0 0 c d hnf (Nat.le_refl 0)
      exact ⟨Rank1Termination.index_mono (Nat.zero_le 1) _ hi,
        by rw [index_Prop1_G1_empty 0 _ hi 1 (by omega)]; intro y hy; cases hy⟩
    | p_mid _ _ _ _ _ h => exact absurd h lt_Z_inv
    | p_tail _ _ d _ h =>
      have hd := ih d (T.isNF1_P_inv _ _ _ hnf).2.1 h
      refine ⟨T.index_Prop1.p _ _ _ (Nat.le_refl _) hd.1, ?_⟩
      intro y hy
      rcases (G1_P_mem (Nat.le_refl 1)).1 hy with rfl | hy | hy
      · rfl
      · cases hy
      · exact hd.2 y hy

theorem below_mul_good (a : T) (hnf : T.isNF1 a) (k : Nat)
    (ha : a < T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) : Good1 a := by
  intro y hy
  rw [(below_mul_support a hnf k ha).2 y hy]
  apply Z_lt_of_ne
  rintro rfl; cases hy

/-- One summand before multiplication by `Ω`. -/
theorem principal_inverse (q : T) (hnf : T.isNF1 q) (k : Nat)
    (hq : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) :
    ∃ p a, p ≤ 1 ∧ T.isNF1 a ∧ (∀ y, y ∈ T.G1 p a → y < a) ∧
      (p = 1 → T.index_Prop1 1 a ∧ Good1 a) ∧
      card 1 (T.P p a T.Z) = T.P 1 q T.Z ∧
      (∀ b, T.P p a b < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z) ∧
      deg a ≤ deg q ∧ (p = 1 → a < q) ∧
      ∀ B, part B = (B, T.Z) → Small B q → Small B a := by
  rw [mul_succ_shape] at hq
  cases hq with
  | Z_lt_P =>
    refine ⟨0, T.Z, Nat.zero_le 1, T.isNF1.z, ?_, ?_, ?_, ?_, Nat.le_refl 0, ?_, ?_⟩
    · intro y hy; cases hy
    · intro h; cases h
    · rw [card_P0, collapse_Z, card_Z, shift_zero]
    · exact fun b => T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
    · intro h; cases h
    · exact fun _ _ h => h
  | p_head p _ a _ b _ hp =>
    have hp0 : p = 0 := by omega
    subst p
    obtain ⟨x, hxNF, hg, hec, hbound, hd⟩ :=
      exists_uncollapse _ hnf (isNF1_index 0 0 a b hnf (Nat.le_refl 0))
    refine ⟨0, x, Nat.zero_le 1, hxNF, hg, ?_, ?_, ?_, hd, ?_, ?_⟩
    · intro h; cases h
    · rw [card_P0, hec, card_Z, shift_zero]
    · exact fun tail => T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
    · intro h; cases h
    · intro B hf hs
      have hx := hbound B hf hs.2 hs.1
      exact ⟨hx, fun y hy => lt_trans_thm _ _ _ (hg y hy) hx⟩
  | p_mid _ _ _ _ _ h => exact absurd h lt_Z_inv
  | p_tail _ _ b _ h =>
    have hb := (T.isNF1_P_inv _ _ _ hnf).2.1
    have hi := (below_mul_support b hb k h).1
    have hg := below_mul_good b hb k h
    refine ⟨1, b, Nat.le_refl 1, hb, hg, fun _ => ⟨hi, hg⟩, ?_,
      fun tail => T.Lt.p_mid _ _ _ _ _ h, deg_tail_le 1 T.Z b,
      fun _ => tail_lt_of_NF1 hnf, fun B _ hs => (small_inv hnf hs).2⟩
    rw [card_one_P1, card_Z, shift_succ, shift_zero]

theorem exists_uncard (h : T) (hnf : T.isNF1 h) (hc : OneChain h) (k : Nat)
    (hb : h < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z) :
    ∃ s, T.isNF1 s ∧ T.index_Prop1 1 s ∧ Good1 s ∧ card 1 s = h ∧
      s < T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z ∧ deg s ≤ deg h ∧
      ∀ B, part B = (B, T.Z) → Small B h → Small B s := by
  induction h with
  | Z =>
    exact ⟨T.Z, hnf, T.index_Prop1.z, (by intro y hy; cases hy), card_Z 1,
      T.Lt.Z_lt_P _ _ _, Nat.le_refl _, fun _ _ hs => hs⟩
  | P p q r _ ih =>
    obtain ⟨rfl, hcr⟩ := hc
    have hn := T.isNF1_P_inv 1 q r hnf
    have hqb : q < T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
      cases hb with
      | p_head _ _ _ _ _ _ h => exact absurd h (Nat.lt_irrefl _)
      | p_mid _ _ _ _ _ h => exact h
      | p_tail _ _ _ _ h => cases h
    obtain ⟨sr, hrNF, hrIdx, hrG, hrcard, hrlt, hrdeg, hrsmall⟩ :=
      ih hn.2.1 hcr (lt_trans_thm _ _ _ (tail_lt_of_NF1 hnf) hb)
    obtain ⟨j, a, hj, haNF, haG, hagood, hacard, halt, hadeg, haq, hasmall⟩ :=
      principal_inverse q hn.1 k hqb
    have hheadNF := T.isNF1.p j a T.Z haNF T.isNF1.z haG (T.Z_le _)
    have hheadIdx := T.index_Prop1.p j a T.Z hj T.index_Prop1.z
    have hhead := card1_reflect_le (head_nf hrNF) hheadNF (head_idx hrIdx) hheadIdx
      (by rw [card_head, hrcard, hacard]; exact hn.2.2.2)
    have hsNF := T.isNF1.p j a sr haNF hrNF haG hhead
    refine ⟨T.P j a sr, hsNF, T.index_Prop1.p _ _ _ hj hrIdx, ?_, ?_, halt sr, ?_, ?_⟩
    · intro y hy
      have htail := tail_lt_of_NF1 hsNF
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
      · exact lt_trans_thm _ _ _ (hrG y (by
          simp only [T.G1, show ¬ (1 ≤ 0) from by omega, ite_false] at hy; exact hy)) htail
      · have ha := hagood rfl
        have hawrap := lt_wrap 1 a sr ha.1 ha.2
        rcases (G1_P_mem (Nat.le_refl 1)).1 hy with rfl | hy | hy
        · exact hawrap
        · exact lt_trans_thm _ _ _ (ha.2 y hy) hawrap
        · exact lt_trans_thm _ _ _ (hrG y hy) htail
    · rw [card_append1, hacard, hrcard, T.P_add_eq]; rfl
    · rw [deg, deg]
      exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.add_le_add_right hadeg 1) (Nat.le_max_left _ _),
        Nat.le_trans hrdeg (Nat.le_max_right _ _)⟩
    · intro B hf hs
      have hi := small_inv hnf hs
      have ha := hasmall B hf hi.1
      have hr := hrsmall B hf hi.2
      constructor
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
        · exact index0_lt_fixed (isNF1_index 0 0 a sr hsNF (Nat.le_refl 0)) hf
            (by intro h; rw [h] at hs; exact lt_Z_inv hs.1)
        · exact lt_trans_thm _ _ _ (T.Lt.p_mid _ _ _ _ _ (haq rfl)) hs.1
      · intro y hy
        rcases (G1_P_mem (Nat.zero_le j)).1 hy with rfl | hy | hy
        · exact ha.1
        · exact ha.2 y hy
        · exact hr.2 y hy

/-! ### Order reflection -/

theorem tr_reflect_lt {s t : multi.T} (hs : NF s) (ht : NF t) (h : tr s < tr t) : s < t := by
  rcases multi.T.lt_trichotomy s t with hst | hst | hts
  · exact hst
  · have he : tr s = tr t := by rw [← tr_norm s, hst, tr_norm]
    rw [he] at h; exact absurd h (lt_irrefl_thm _)
  · exact absurd h (lt_asymm_thm (tr_mono ht hs hts))

theorem tr_reflect_le {s t : multi.T} (hs : NF s) (ht : NF t) (h : tr s ≤ tr t) : s ≤ t := by
  rcases multi.T.lt_trichotomy s t with hst | hst | hts
  · exact Or.inl hst
  · exact Or.inr ((multi.compareT_eq_iff s t).2 hst)
  · rcases h with h | h
    · exact absurd h (lt_asymm_thm (tr_mono ht hs hts))
    · exact absurd (h ▸ tr_mono ht hs hts) (lt_irrefl_thm _)

theorem Gd_of_NFComp {x : multi.T} (h : NFComp x) : Gd x := (main x).2.2 h

/-! ### Coordinate functions -/

def vOf (f : Nat → multi.T) : Nat → multi.V multi.T
  | 0 => .emp
  | n + 1 => .snoc (f n) (vOf f n)

theorem vOf_length (f : Nat → multi.T) : ∀ n, (vOf f n).length = n
  | 0 => rfl
  | n + 1 => by show (vOf f n).length + 1 = n + 1; rw [vOf_length f n]

theorem get0_vOf (f : Nat → multi.T) : ∀ n j, multi.V.get0 (vOf f n) j = if j < n then f j else multi.T.Z
  | 0, j => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | n + 1, j => by
    show (if j = (vOf f n).length then f n else multi.V.get0 (vOf f n) j) = _
    rw [vOf_length, get0_vOf f n j]
    by_cases hj : j = n
    · rw [ite_eq_left hj, ite_eq_left (by omega), hj]
    · rw [ite_eq_right hj]
      by_cases hjn : j < n
      · rw [ite_eq_left hjn, ite_eq_left (by omega)]
      · rw [ite_eq_right hjn, ite_eq_right (by omega)]

def fcons (u : multi.T) (f : Nat → multi.T) : Nat → multi.T
  | 0 => u
  | m + 1 => f m

/-- The blocks `Ω^m · collapse(tr (f m))` for `m < k`. -/
def hsUp (f : Nat → multi.T) : Nat → T
  | 0 => T.Z
  | k + 1 => T.add (card k (collapse (tr (f k)))) (hsUp f k)

theorem sUp_eq_hsUp (g : Nat → multi.T) : ∀ k, sUp g (k + 1) = hsUp (fun m => g (m + 1)) k
  | 0 => rfl
  | k + 1 => by
    show T.add (card k (collapse (tr (g (k + 1))))) (sUp g (k + 1)) = _
    rw [sUp_eq_hsUp g k]; rfl

theorem hsUp_cons (u : multi.T) (f : Nat → multi.T) (hf : ∀ m, Gd (f m)) :
    ∀ k, hsUp (fcons u f) (k + 1) = T.add (card 1 (hsUp f k)) (collapse (tr u))
  | 0 => by
    show T.add (card 0 (collapse (tr u))) T.Z = _
    rw [card_zero, T.add_Z, show hsUp f 0 = T.Z from rfl, card_Z, add_Z_left]
  | k + 1 => by
    show T.add (card (k + 1) (collapse (tr (f k)))) (hsUp (fcons u f) (k + 1)) = _
    rw [hsUp_cons u f hf k, show hsUp f (k + 1) =
      T.add (card k (collapse (tr (f k)))) (hsUp f k) from rfl, card_add_gen,
      card_one_comp k (hf k).collapse.2, add_assoc]

theorem hsUp_congr {f g : Nat → multi.T} :
    ∀ k, (∀ m, m < k → f m = g m) → hsUp f k = hsUp g k
  | 0, _ => rfl
  | k + 1, h => by
    show T.add _ (hsUp f k) = T.add _ (hsUp g k)
    rw [h k (Nat.lt_succ_self k), hsUp_congr k (fun m hm => h m (by omega))]

/-- `Ω^k`-levels used to bound coordinate sums. -/
def level : Nat → T
  | 0 => T.P 0 T.Z T.Z
  | k + 1 => T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) T.Z

theorem index0_of_lt_level_one {s : T} (hs : T.isNF1 s) (hb : s < level 1) : T.index_Prop1 0 s := by
  cases hb with
  | Z_lt_P => exact T.index_Prop1.z
  | p_head p _ a _ b _ hp => exact isNF1_index 0 p a b hs (Nat.le_of_lt_succ hp)
  | p_mid _ _ _ _ _ h => cases h
  | p_tail _ _ _ _ h => cases h

theorem tr_ofNat_one : tr (multi.T.ofNat 1) = T.P 0 T.Z T.Z := by
  show tr (multi.T.P multi.V.emp multi.T.Z) = _
  rw [tr_P, tr_Z, T.add_Z]
  unfold prin
  rw [show sumN (multi.V.emp : multi.V multi.T) = T.Z from rfl, ite_eq_left rfl,
    show a0N (multi.V.emp : multi.V multi.T) = T.Z from rfl]

/-- Coordinates realizing a given sum of blocks. -/
theorem exists_hsum (C : T) (hC : part C = (C, T.Z)) (n : Nat)
    (pre : ∀ x : T, T.isNF1 x → (∀ y, y ∈ T.G1 0 x → y < x) → deg x ≤ n → Small C x →
      ∃ sx : multi.T, NFComp sx ∧ tr sx = x)
    (k : Nat) (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 1 s)
    (hb : s < level k) (hd : deg s ≤ n) (hsmall : Small C s) :
    ∃ f : Nat → multi.T, (∀ m, NFComp (f m)) ∧ (∀ m, k ≤ m → f m = multi.T.Z) ∧
      hsUp f k = s ∧
      ∀ B, part B = (B, T.Z) → Small B s → ∀ m, tr (f m) < B := by
  induction k generalizing s with
  | zero =>
    have hz := lt_one_eq_Z hb
    subst hz
    refine ⟨fun _ => multi.T.Z, fun _ => NFComp_Z, fun _ _ => rfl, rfl, ?_⟩
    intro B _ hS m
    rw [tr_Z]; exact hS.1
  | succ k ih =>
    cases k with
    | zero =>
      obtain ⟨u, hu, hgu, hec, hbound, hdu⟩ :=
        exists_uncollapse s hnf (index0_of_lt_level_one hnf hb)
      have huC := hbound C hC hsmall.2 hsmall.1
      obtain ⟨su, hsu, he⟩ := pre u hu hgu (Nat.le_trans hdu hd)
        ⟨huC, fun y hy => lt_trans_thm _ _ _ (hgu y hy) huC⟩
      refine ⟨fcons su (fun _ => multi.T.Z), fun m => ?_, fun m hm => ?_, ?_, ?_⟩
      · cases m with
        | zero => exact hsu
        | succ m => exact NFComp_Z
      · cases m with
        | zero => omega
        | succ m => rfl
      · show T.add (card 0 (collapse (tr su))) T.Z = s
        rw [card_zero, T.add_Z, he, hec]
      · intro B hB hS m
        cases m with
        | zero => show tr su < B; rw [he]; exact hbound B hB hS.2 hS.1
        | succ m => show tr multi.T.Z < B; rw [tr_Z]; exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le s) hS.1
    | succ k =>
      have hp := part_NF1 hnf
      have hSC := part_small C s hnf hsmall
      obtain ⟨r, hr, hir, _, he, hbr, hdr, hsmallr⟩ := exists_uncard _ hp.1 (part_oneChain s hi) k
        (lt_of_le_of_lt_thm T _ _ _ (part_fst_le_self s) hb)
      obtain ⟨fr, hfr, hfrz, her, hbfr⟩ := ih r hr hir hbr
        (Nat.le_trans hdr (Nat.le_trans (deg_part_fst s) hd)) (hsmallr C hC hSC.1)
      obtain ⟨u, hu, hgu, hec, hbu, hdu⟩ := exists_uncollapse _ hp.2 (part_snd_index0 hnf)
      have huC := hbu C hC hSC.2.2 hSC.2.1
      have hdeg2 : deg (part s).2 ≤ deg s := by
        have h := deg_add (part s).1 (part s).2
        rw [part_add] at h
        rw [h]; exact Nat.le_max_right _ _
      obtain ⟨su, hsu, heu⟩ := pre u hu hgu (Nat.le_trans hdu (Nat.le_trans hdeg2 hd))
        ⟨huC, fun y hy => lt_trans_thm _ _ _ (hgu y hy) huC⟩
      refine ⟨fcons su fr, fun m => ?_, fun m hm => ?_, ?_, ?_⟩
      · cases m with
        | zero => exact hsu
        | succ m => exact hfr m
      · cases m with
        | zero => omega
        | succ m => exact hfrz m (by omega)
      · rw [hsUp_cons su fr (fun m => Gd_of_NFComp (hfr m)), her, he, heu, hec, part_add]
      · intro B hB hS m
        have hPS := part_small B s hnf hS
        cases m with
        | zero => show tr su < B; rw [heu]; exact hbu B hB hPS.2.2 hPS.2.1
        | succ m => exact hbfr B hB (hsmallr B hB hPS.1) m

/-! ### Principal preimages -/

def unone : T → T
  | T.Z => T.P 0 T.Z T.Z
  | T.P 0 T.Z b => T.P 0 T.Z (T.P 0 T.Z b)
  | t => t

theorem unone_section (s : T) : oneDel (unone s) = s := by
  cases s with
  | Z => rfl
  | P p a b => cases p <;> cases a <;> rfl

theorem unone_ne (s : T) : unone s ≠ T.Z := by
  cases s with
  | Z => intro h; cases h
  | P p a b => cases p <;> cases a <;> intro h <;> cases h

theorem unone_props (s : T) (hnf : T.isNF1 s) (hi : T.index_Prop1 1 s) (hne : s ≠ T.Z) :
    T.isNF1 (unone s) ∧ T.index_Prop1 1 (unone s) ∧ deg (unone s) ≤ deg s ∧
      (∀ k, s < level (k + 1) → unone s < level (k + 1)) ∧
      ∀ B, part B = (B, T.Z) → Small B s → Small B (unone s) := by
  cases s with
  | Z => exact absurd rfl hne
  | P p a b =>
    cases p with
    | zero =>
      cases a with
      | Z =>
        have hout := T.isNF1.p 0 T.Z (T.P 0 T.Z b) T.isNF1.z hnf (by intro y hy; cases hy)
          (Or.inr rfl)
        refine ⟨hout, T.index_Prop1.p _ _ _ (Nat.zero_le 1) hi, ?_, ?_, ?_⟩
        · show max (deg T.Z + 1) (max (deg T.Z + 1) (deg b)) ≤ max (deg T.Z + 1) (deg b)
          exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_refl _⟩
        · exact fun k _ => T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)
        · intro B hB hs
          have hn : B ≠ T.Z := by intro h; rw [h] at hs; exact lt_Z_inv hs.1
          refine ⟨index0_lt_fixed (isNF1_index 0 0 T.Z _ hout (Nat.le_refl 0)) hB hn, ?_⟩
          intro y hy
          rcases (G1_P_mem (Nat.le_refl 0)).1 hy with rfl | hy | hy
          · exact Z_lt_of_ne hn
          · cases hy
          · exact hs.2 y hy
      | P q c d => exact ⟨hnf, hi, Nat.le_refl _, fun _ hb => hb, fun _ _ hs => hs⟩
    | succ p => exact ⟨hnf, hi, Nat.le_refl _, fun _ hb => hb, fun _ _ hs => hs⟩

theorem sumN_vOf (f : Nat → multi.T) (K : Nat) :
    sumN (vOf f (K + 1)) = hsUp (fun m => f (m + 1)) K := by
  rw [sumN_eq _ (K + 1) (Nat.le_of_eq (vOf_length f (K + 1))), sUp_eq_hsUp]
  apply hsUp_congr
  intro m hm
  rw [get0_vOf, ite_eq_left (by omega)]

theorem a0N_vOf (f : Nat → multi.T) (K : Nat) : a0N (vOf f (K + 1)) = tr (f 0) := by
  rw [a0N_eq, get0_vOf, ite_eq_left (by omega)]

theorem higher_preimage (k : Nat) (C : T) (hC : part C = (C, T.Z)) (a : T)
    (ha : T.isNF1 a) (hai : T.index_Prop1 1 a) (hb : a < level (k + 2)) (haC : Small C a)
    (pre : ∀ x : T, T.isNF1 x → (∀ y, y ∈ T.G1 0 x → y < x) → deg x ≤ deg a → Small C x →
      ∃ sx : multi.T, NFComp sx ∧ tr sx = x) :
    ∃ v : multi.V multi.T, (∀ j, NFComp (multi.V.get0 v j)) ∧ prin v = T.P 1 a T.Z ∧
      ∀ B, part B = (B, T.Z) → Small B a → ∀ j, tr (multi.V.get0 v j) < B := by
  have hp := part_NF1 ha
  have hSmall := part_small C a ha haC
  obtain ⟨r, hr, hir, _, her, hbr, hdr, hsmallr⟩ := exists_uncard _ hp.1 (part_oneChain a hai) k
    (lt_of_le_of_lt_thm T _ _ _ (part_fst_le_self a) hb)
  obtain ⟨K, g, hg, hdel, hne, hbound⟩ : ∃ K, ∃ g : Nat → multi.T, (∀ m, NFComp (g m)) ∧
      oneDel (hsUp g K) = r ∧ hsUp g K ≠ T.Z ∧
      (∀ B, part B = (B, T.Z) → Small B a → ∀ m, tr (g m) < B) := by
    by_cases hz : r = T.Z
    · refine ⟨1, fun _ => multi.T.ofNat 1, fun _ => NFComp_ofNat 1, ?_, ?_, ?_⟩
      · show oneDel (T.add (card 0 (collapse (tr (multi.T.ofNat 1)))) T.Z) = r
        rw [card_zero, T.add_Z, tr_ofNat_one, collapse_of_index0
          (T.index_Prop1.p _ _ _ (Nat.le_refl 0) T.index_Prop1.z), hz]; rfl
      · show T.add (card 0 (collapse (tr (multi.T.ofNat 1)))) T.Z ≠ T.Z
        rw [card_zero, T.add_Z, tr_ofNat_one, collapse_of_index0
          (T.index_Prop1.p _ _ _ (Nat.le_refl 0) T.index_Prop1.z)]
        intro h; cases h
      · intro B hB hS m
        rw [tr_ofNat_one]
        exact index0_lt_fixed (T.index_Prop1.p _ _ _ (Nat.le_refl _) T.index_Prop1.z) hB
          (by intro h; rw [h] at hS; exact lt_Z_inv hS.1)
    · obtain ⟨hu, hiu, hdu, hbu, hsmallu⟩ := unone_props r hr hir hz
      obtain ⟨g, hg, _, he, hb⟩ := exists_hsum C hC (deg a) pre (k + 1) (unone r) hu hiu
        (hbu k hbr) (Nat.le_trans hdu (Nat.le_trans hdr (deg_part_fst a)))
        (hsmallu C hC (hsmallr C hC hSmall.1))
      exact ⟨k + 1, g, hg, by rw [he, unone_section], by rw [he]; exact unone_ne r,
        fun B hB hS => hb B hB (hsmallu B hB (hsmallr B hB (part_small B a ha hS).1))⟩
  obtain ⟨u, hu, hgu, hec, hbu, hdu⟩ := exists_uncollapse _ hp.2 (part_snd_index0 ha)
  have huC := hbu C hC hSmall.2.2 hSmall.2.1
  have hdeg2 : deg (part a).2 ≤ deg a := by
    have h := deg_add (part a).1 (part a).2
    rw [part_add] at h
    rw [h]; exact Nat.le_max_right _ _
  obtain ⟨su, hsu, heu⟩ := pre u hu hgu (Nat.le_trans hdu hdeg2)
    ⟨huC, fun y hy => lt_trans_thm _ _ _ (hgu y hy) huC⟩
  refine ⟨vOf (fcons su g) (K + 1), fun j => ?_, ?_, ?_⟩
  · rw [get0_vOf]
    split
    · cases j with
      | zero => exact hsu
      | succ j => exact hg j
    · exact NFComp_Z
  · unfold prin
    rw [sumN_vOf, a0N_vOf]
    have hfg : (fun m => fcons su g (m + 1)) = g := rfl
    rw [hfg, ite_eq_right hne, hdel]
    show T.P 1 (T.add (card 1 r) (collapse (tr su))) T.Z = _
    rw [her, heu, hec, part_add]
  · intro B hB hS j
    rw [get0_vOf]
    split
    · cases j with
      | zero =>
        show tr su < B
        rw [heu]
        have hPS := part_small B a ha hS
        exact hbu B hB hPS.2.2 hPS.2.1
      | succ j => exact hbound B hB hS j
    · rw [tr_Z]; exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le a) hS.1

/-! ### Supported coordinates -/

/-- A recovered coordinate is controlled by a support element of the target, or by every
fixed bound on the support of the target's uncountable prefix. -/
def Supported (t y : T) : Prop :=
  (∃ z, z ∈ T.G1 0 t ∧ y ≤ z) ∨
  (∀ B, part B = (B, T.Z) → (∀ z, z ∈ T.G1 0 (part t).1 → z < B) → y < B)

def Preimage (t : T) (s : multi.T) : Prop :=
  NF s ∧ tr s = t ∧ ∀ y, y ∈ G s → Supported t (tr y)

theorem supported_le {t x y : T} (hxy : x ≤ y) (hy : Supported t y) : Supported t x := by
  rcases hy with ⟨z, hz, h⟩ | h
  · exact Or.inl ⟨z, hz, partial_order.trans _ _ _ hxy h⟩
  · exact Or.inr (fun B hB hG => lt_of_le_of_lt_thm T _ _ _ hxy (h B hB hG))

theorem comp_of_preimage {t : T} {s : multi.T} (hs : Preimage t s)
    (hg : ∀ y, y ∈ T.G1 0 t → y < t) : NFComp s := by
  refine ⟨hs.1, fun y hy => ?_⟩
  apply tr_reflect_lt (NF_G_comp hs.1 y hy).1 hs.1
  rw [hs.2.1]
  rcases hs.2.2 y hy with ⟨z, hz, hle⟩ | h
  · exact lt_of_le_of_lt_thm T _ _ _ hle (hg z hz)
  · exact lt_of_lt_of_le_thm T _ _ _ (h (part t).1 (part_fst_fixed t) (good_part_fst hg))
      (part_fst_le_self t)

theorem supported_tail (p : Nat) (a b y : T) (hnf : T.isNF1 (T.P p a b)) (h : Supported b y) :
    Supported (T.P p a b) y := by
  rcases h with ⟨z, hz, hyz⟩ | h
  · exact Or.inl ⟨z, (G1_P_mem (Nat.zero_le p)).2 (Or.inr (Or.inr hz)), hyz⟩
  · cases p with
    | zero =>
      have hi := isNF1_index 0 0 a b hnf (Nat.le_refl 0)
      cases hi with
      | p _ _ _ _ hb =>
        have := h T.Z rfl (by rw [part_of_index0 hb]; intro z hz; cases hz)
        exact absurd this lt_Z_inv
    | succ p =>
      refine Or.inr (fun B hB hG => h B hB (fun z hz => hG z ?_))
      have hpt : (part (T.P (p + 1) a b)).1 = T.P (p + 1) a (part b).1 := by
        simp [part]
      rw [hpt]
      exact (G1_P_mem (Nat.zero_le _)).2 (Or.inr (Or.inr hz))

theorem supported_middle (p : Nat) (a b x : T) (hxa : x ≤ a) : Supported (T.P p a b) x :=
  Or.inl ⟨a, (G1_P_mem (Nat.zero_le p)).2 (Or.inl rfl), hxa⟩

theorem supported_higher (a b x : T) (h : ∀ B, part B = (B, T.Z) → Small B a → x < B) :
    Supported (T.P 1 a b) x := by
  apply Or.inr
  intro B hB hG
  have hpt : (part (T.P 1 a b)).1 = T.P 1 a (part b).1 := by simp [part]
  rw [hpt] at hG
  exact h B hB ⟨hG a ((G1_P_mem (Nat.zero_le 1)).2 (Or.inl rfl)),
    fun z hz => hG z ((G1_P_mem (Nat.zero_le 1)).2 (Or.inr (Or.inl hz)))⟩

theorem NF_hd {s : multi.T} (hs : NF s) : NF (multi.T.hd s) := by
  cases s with
  | Z => exact NF.z
  | P v a =>
    obtain ⟨hv, _, hg, _⟩ := hs.inv
    exact NF.p v multi.T.Z hv NF.z hg (multi.T.Z_le _)

theorem assemble (p : Nat) (a b : T) (hnf : T.isNF1 (T.P p a b)) (v : multi.V multi.T)
    (sb : multi.T) (hv : ∀ j, NFComp (multi.V.get0 v j)) (htrans : prin v = T.P p a T.Z)
    (hsb : Preimage b sb)
    (hcoord : ∀ j, multi.V.get0 v j ≠ multi.T.Z →
      Supported (T.P p a b) (tr (multi.V.get0 v j))) :
    Preimage (T.P p a b) (multi.T.P v sb) := by
  have hp := NF_PZ_of_comps hv
  have htrPZ : tr (multi.T.P v multi.T.Z) = T.P p a T.Z := by
    rw [tr_P, tr_Z, T.add_Z, htrans]
  have hh : multi.T.hd sb ≤ multi.T.P v multi.T.Z := by
    apply tr_reflect_le (NF_hd hsb.1) hp
    rw [← hd_tr, hsb.2.1, htrPZ]
    exact (T.isNF1_P_inv _ _ _ hnf).2.2.2
  refine ⟨NF.p v sb (fun j => (hv j).1) hsb.1 (fun j => (hv j).2) hh, ?_, ?_⟩
  · rw [tr_P, htrans, hsb.2.1, T.P_add_eq]; rfl
  · intro y hy
    rcases mem_G_P.1 hy with ⟨j, ⟨hne, rfl⟩ | hG⟩ | ht
    · exact hcoord j hne
    · have hne : multi.V.get0 v j ≠ multi.T.Z := by
        intro hz; rw [hz, G_Z] at hG; cases hG
      exact supported_le (Or.inl (tr_mono (NF_G_comp (hv j).1 y hG).1 (hv j).1 ((hv j).2 y hG)))
        (hcoord j hne)
    · exact supported_tail p a b _ hnf (hsb.2.2 y ht)

/-! ### Preimages by induction on exponent depth -/

theorem part_nbound : part nbound = (nbound, T.Z) := rfl

theorem lt_level_of_lt_vb {a : T} (ha : T.isNF1 a) (h : a < vb) : ∃ k, a < level (k + 2) := by
  cases a with
  | Z => exact ⟨0, T.Lt.Z_lt_P _ _ _⟩
  | P p c d =>
    cases h with
    | p_head _ _ _ _ _ _ hp => exact ⟨0, T.Lt.p_head _ _ _ _ _ _ hp⟩
    | p_mid _ _ _ _ _ hc =>
      obtain ⟨k, e, rfl, he⟩ := shift_decomp_omega c (T.isNF1_P_inv _ _ _ ha).1 hc
      refine ⟨k, T.Lt.p_mid _ _ _ _ _ ?_⟩
      have h := shift_level_lt k (k + 1) (Nat.lt_succ_self k) (y := T.Z) he
      rw [show shift (k + 1) T.Z = T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) from T.add_Z _] at h
      exact h
    | p_tail _ _ _ _ h => cases h

theorem index1_of_lt_P1 {a : T} (c : T) (hnf : T.isNF1 a) (ha : a < T.P 1 c T.Z) :
    T.index_Prop1 1 a := by
  cases a with
  | Z => exact T.index_Prop1.z
  | P p u w => exact isNF1_index 1 p u w hnf (head_le_index p 1 u c (T.head_mono ha))

theorem exists_preimage (t : T) (hnf : T.isNF1 t) (hsmall : Small nbound t) :
    ∃ s, Preimage t s := by
  suffices H : ∀ n (t : T), deg t ≤ n → T.isNF1 t → Small nbound t → ∃ s, Preimage t s from
    H (deg t) t (Nat.le_refl _) hnf hsmall
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t
    induction t with
    | Z =>
      exact fun _ _ _ => ⟨multi.T.Z, NF.z, tr_Z, by intro y hy; rw [G_Z] at hy; cases hy⟩
    | P p a b _ ihb =>
      intro hd hn hS
      have hp := T.isNF1_P_inv p a b hn
      have hPS := small_inv hn hS
      have hda := Nat.lt_of_lt_of_le (deg_mid_lt p a b) hd
      have pre : ∀ x, T.isNF1 x → (∀ y, y ∈ T.G1 0 x → y < x) → deg x ≤ deg a →
          Small nbound x → ∃ sx : multi.T, NFComp sx ∧ tr sx = x := by
        intro x hx hg hdx hxc
        obtain ⟨sx, hsx⟩ := ih (deg x) (Nat.lt_of_le_of_lt hdx hda) x (Nat.le_refl _) hx hxc
        exact ⟨sx, comp_of_preimage hsx hg, hsx.2.1⟩
      obtain ⟨sb, hsb⟩ := ihb (Nat.le_trans (deg_tail_le p a b) hd) hp.2.1 hPS.2
      cases p with
      | zero =>
        obtain ⟨sa, hsa, he⟩ := pre a hp.1 hp.2.2.1 (Nat.le_refl _) hPS.1
        refine ⟨multi.T.P (vOf (fcons sa (fun _ => multi.T.Z)) 1) sb,
          assemble 0 a b hn _ sb (fun j => ?_) ?_ hsb (fun j hj => ?_)⟩
        · rw [get0_vOf]
          split
          · cases j with
            | zero => exact hsa
            | succ j => exact NFComp_Z
          · exact NFComp_Z
        · unfold prin
          rw [show (1 : Nat) = 0 + 1 from rfl, sumN_vOf, a0N_vOf]
          show T.P 0 (tr sa) T.Z = _
          rw [he]
        · rw [get0_vOf] at hj ⊢
          split at hj
          · rename_i hj0
            have : j = 0 := by omega
            subst this
            show Supported _ (tr sa)
            rw [he]
            exact supported_middle 0 a b a (Or.inr rfl)
          · exact absurd rfl hj
      | succ p =>
        have hshape : p + 1 = 1 ∧ a < vb := by
          cases hS.1 with
          | p_head _ _ _ _ _ _ h => exfalso; omega
          | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
          | p_tail _ _ _ _ h => cases h
        have hp0 : p = 0 := by omega
        subst p
        obtain ⟨k, hk⟩ := lt_level_of_lt_vb hp.1 hshape.2
        obtain ⟨v, hv, he, hbound⟩ := higher_preimage k nbound part_nbound a hp.1
          (index1_of_lt_P1 _ hp.1 hshape.2) hk hPS.1 pre
        exact ⟨multi.T.P v sb, assemble 1 a b hn v sb hv he hsb
          (fun j _ => supported_higher a b _ (fun B hB hSm => hbound B hB hSm j))⟩

/-- Every Buchholz normal form below `ψ_0(Ω^{Ω^ω})` is the translation of a countable
normal form. -/
theorem surj (u : T) (hu : T.isNF1 u) (hub : u < bound) : ∃ s, (NF s ∧ s < otb) ∧ tr s = u := by
  have hsmall : Small nbound u := by
    cases u with
    | Z => exact ⟨T.Lt.Z_lt_P _ _ _, by intro y hy; cases hy⟩
    | P p c d =>
      have hp : p = 0 ∧ c < nbound := by
        cases hub with
        | p_head _ _ _ _ _ _ h => exact absurd h (Nat.not_lt_zero _)
        | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
        | p_tail _ _ _ _ h => cases h
      obtain ⟨rfl, hc⟩ := hp
      exact ⟨T.Lt.p_head _ _ _ _ _ _ (by omega),
        fun y hy => lt_of_le_of_lt_thm T _ _ _ (support_le_of_head hu (Or.inr rfl) y hy) hc⟩
  obtain ⟨s, hs⟩ := exists_preimage u hu hsmall
  refine ⟨s, ⟨hs.1, ?_⟩, hs.2.1⟩
  cases s with
  | Z => exact multi.T.Z_lt_P _ _
  | P v a =>
    have hzero : ∀ j, 1 ≤ j → multi.V.get0 v j = multi.T.Z := by
      intro j hj
      by_cases hne0 : multi.V.get0 v j = multi.T.Z
      · exact hne0
      exfalso
      have hne := hne0
      have hS : sumN v ≠ T.Z := by
        rw [sumN_eq v (v.length + j + 1) (by omega)]
        exact sUp_ne_Z hj (by omega) hne
      have htr := hs.2.1
      rw [tr_P] at htr
      unfold prin at htr
      rw [ite_eq_right hS, T.P_add_eq] at htr
      rw [← htr] at hub
      cases hub with
      | p_head _ _ _ _ _ _ h => exact absurd h (by omega)
    apply multi.T.P_lt_P_of_vlt
    apply multi.V.lt_of_pivot 1
    · intro j hj
      rw [hzero j (by omega), get0_otb_vec, ite_eq_right (by omega)]
      exact multi.compareT_ZZ
    · rw [hzero 1 (Nat.le_refl 1), get0_otb_vec, ite_eq_left rfl]
      exact multi.T.Z_lt_P _ _

end new

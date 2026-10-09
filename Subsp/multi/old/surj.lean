import Subsp.multi.old.trans
import Subsp.multi.old.inv

/-! Surjectivity of the `old` translation onto the Buchholz normal forms below `Ω`.

The key step is the reverse transfer: if the translation of a normal form lies above its
level-`u` support, then the source term lies above its support at index `u`. -/

namespace old

open OB

/-! ### Supports vanish above the size -/

theorem vlength_le_vsize : ∀ v : multi.V multi.T, v.length ≤ multi.V.size v
  | .emp => Nat.le_refl 0
  | .snoc a ax => by
    show ax.length + 1 ≤ multi.T.size a + multi.V.size ax + 1
    have := vlength_le_vsize ax
    omega

theorem G_large (u : Nat) (s : multi.T) (hs : s.size ≤ u) : ∀ y, y ∉ G u s := by
  induction s using (measure multi.T.size).wf.induction with
  | h s ih =>
    intro y hy
    cases s with
    | Z => rw [G_Z] at hy; cases hy
    | P v a =>
      have hvl : v.length < u := by
        have h1 := vlength_le_vsize v
        have h2 : (multi.T.P v a).size = multi.V.size v + a.size + 1 := rfl
        omega
      rcases mem_G_P.1 hy with ⟨j, huj, hj⟩ | ht
      · rw [multi.V.get0_ge v j (by omega)] at hj
        rcases hj with ⟨h, _⟩ | h
        · exact h rfl
        · rw [G_Z] at h; cases h
      · exact ih a (multi.T.size_lt_P_right v a)
          (Nat.le_trans (Nat.le_of_lt (multi.T.size_lt_P_right v a)) hs) y ht

/-! ### Coordinates of index `u` reached through coordinates of larger index -/

inductive Reach (u : Nat) : multi.T → multi.T → Prop
  | here (v : multi.V multi.T) (a : multi.T) (hne : multi.V.get0 v u ≠ multi.T.Z) :
      Reach u (multi.T.P v a) (multi.V.get0 v u)
  | tail (v : multi.V multi.T) (a c : multi.T) : Reach u a c → Reach u (multi.T.P v a) c
  | deep (v : multi.V multi.T) (a c : multi.T) (j : Nat) (hj : u + 1 ≤ j) :
      Reach u (multi.V.get0 v j) c → Reach u (multi.T.P v a) c

theorem G_split (u : Nat) : ∀ x z : multi.T, z ∈ G u x →
    z ∈ G (u + 1) x ∨ ∃ c, Reach u x c ∧ (z = c ∨ z ∈ G u c) := by
  intro x
  induction x using (measure multi.T.size).wf.induction with
  | h x ih =>
    intro z hz
    cases x with
    | Z => rw [G_Z] at hz; cases hz
    | P w b =>
      rcases mem_G_P.1 hz with ⟨j, huj, hzj⟩ | hzb
      · rcases Nat.eq_or_lt_of_le huj with hju | hju
        · subst hju
          have hne : multi.V.get0 w u ≠ multi.T.Z := by
            rcases hzj with ⟨h, _⟩ | h
            · exact h
            · intro h0; rw [h0, G_Z] at h; cases h
          refine Or.inr ⟨multi.V.get0 w u, Reach.here w b hne, ?_⟩
          rcases hzj with ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr h
        · rcases hzj with ⟨hne, rfl⟩ | hzj
          · exact Or.inl (G_coord_mem hju hne)
          · rcases ih _ (multi.T.size_get0_lt_P w j b) z hzj with h | ⟨c, hc, hzc⟩
            · exact Or.inl (G_in_coord hju h)
            · exact Or.inr ⟨c, Reach.deep w b c j hju hc, hzc⟩
      · rcases ih b (multi.T.size_lt_P_right w b) z hzb with h | ⟨c, hc, hzc⟩
        · exact Or.inl (G_in_tail h)
        · exact Or.inr ⟨c, Reach.tail w b c hc, hzc⟩

theorem Reach_comp {u : Nat} {x c : multi.T} (h : Reach u x c) : NF x → NFComp u c := by
  induction h with
  | here w b _ => intro hx; exact hx.comp u
  | tail w b c _ ih => intro hx; exact ih hx.inv.2.1
  | deep w b c j _ _ ih => intro hx; exact ih (hx.inv.1 j)

theorem Reach_nsize {u : Nat} {x c : multi.T} (h : Reach u x c) :
    multi.T.nsize c < multi.T.nsize x := by
  induction h with
  | here w b _ => exact multi.T.nsize_get0_lt w u b
  | tail w b c _ ih => exact Nat.lt_trans ih (multi.T.nsize_tail_lt w b)
  | deep w b c j _ _ ih => exact Nat.lt_trans ih (multi.T.nsize_get0_lt w j b)

theorem Reach_ne_Z {u : Nat} {x c : multi.T} (h : Reach u x c) : x ≠ multi.T.Z := by
  cases h <;> intro he <;> cases he

/-! ### Structure of principal translations -/

theorem headS_above_zero (f : Nat → multi.T) :
    ∀ k p X, headS f k = T.P p X T.Z → ∀ j, p < j → j < k → f j = multi.T.Z
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | 1, p, X, he, j, hpj, hj => by
    change T.P 0 (tr (f 0)) T.Z = T.P p X T.Z at he
    injection he with hp _ _
    omega
  | k + 2, p, X, he, j, hpj, hj => by
    by_cases hz : f (k + 1) = multi.T.Z
    · rw [headS_two_Z hz] at he
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | hj'
      · exact headS_above_zero f (k + 1) p X he j hpj hj'
      · rw [hj']; exact hz
    · rw [headS_two_ne hz] at he
      injection he with hp _ _
      omega

theorem above_zero {w : multi.V multi.T} {p : Nat} {X : T} (he : auxH w = T.P p X T.Z) :
    ∀ j, p < j → multi.V.get0 w j = multi.T.Z := by
  intro j hpj
  by_cases hj : j < w.length
  · rw [auxH_eq_length] at he
    exact headS_above_zero _ w.length p X he j hpj hj
  · exact multi.V.get0_ge w j (Nat.le_of_not_lt hj)

theorem head_countable {w : multi.V multi.T} {X : T} (he : auxH w = T.P 0 X T.Z) :
    X = tr (multi.V.get0 w 0) := by
  have hz := above_zero he
  have h1 := headS_zeros (multi.V.get0 w) 1 (fun j hj => hz j hj) w.length
  rw [← auxH_eq w (1 + w.length) (by omega), he] at h1
  change T.P 0 X T.Z = T.P 0 (tr (multi.V.get0 w 0)) T.Z at h1
  injection h1

/-- The contribution of the top coordinate of index `i`. -/
def TopContr (i : Nat) (t : T) : T := if i = 0 then t else ct i (oneDel t)

theorem lowS_contr (u : Nat) (f : Nat → multi.T) :
    ∀ k i, i < k → ∀ y ∈ T.G1 u (TContr i (tr (f i))), y ∈ T.G1 u (lowS f k)
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | 1, i, hi => by
    have hi0 : i = 0 := by omega
    subst hi0
    intro y hy
    rw [TContr, ite_eq_left rfl] at hy
    exact hy
  | k + 2, i, hi => by
    intro y hy
    rw [lowS_two, MT.G1_add, List.mem_append]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
    · exact Or.inr (lowS_contr u f (k + 1) i hi' y hy)
    · subst hi'
      rw [TContr, ite_eq_right (Nat.succ_ne_zero k)] at hy
      exact Or.inl hy

theorem headS_contr (u : Nat) (f : Nat → multi.T) :
    ∀ k, 1 ≤ k → ∀ p X, headS f k = T.P p X T.Z →
      (∀ i, i < p → ∀ y ∈ T.G1 u (TContr i (tr (f i))), y ∈ T.G1 u X) ∧
      (∀ y ∈ T.G1 u (TopContr p (tr (f p))), y ∈ T.G1 u X) ∧
      (0 < p → TopContr p (tr (f p)) ≤ X)
  | 0, hk, _, _, _ => absurd hk (Nat.not_succ_le_zero 0)
  | 1, _, p, X, he => by
    change T.P 0 (tr (f 0)) T.Z = T.P p X T.Z at he
    injection he with hp hX _
    subst hp; subst hX
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun y hy => ?_,
      fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [TopContr, ite_eq_left rfl] at hy
    exact hy
  | k + 2, _, p, X, he => by
    by_cases hz : f (k + 1) = multi.T.Z
    · rw [headS_two_Z hz] at he
      exact headS_contr u f (k + 1) (Nat.succ_pos k) p X he
    · rw [headS_two_ne hz] at he
      injection he with hp hX _
      subst hp; subst hX
      refine ⟨fun i hi y hy => ?_, fun y hy => ?_, fun _ => ?_⟩
      · rw [MT.G1_add, List.mem_append]
        exact Or.inr (lowS_contr u f (k + 1) i hi y hy)
      · rw [TopContr, ite_eq_right (Nat.succ_ne_zero k)] at hy
        rw [MT.G1_add, List.mem_append]
        exact Or.inl hy
      · rw [TopContr, ite_eq_right (Nat.succ_ne_zero k)]
        exact MT.add_self_le _ _

theorem headS_high_eq (f : Nat → multi.T) :
    ∀ k, 1 ≤ k → ∀ p X, headS f k = T.P p X T.Z →
      (∀ j, Gd j (f j)) → (part p X).1 = (part p (tr (f p))).1
  | 0, hk, _, _, _, _ => absurd hk (Nat.not_succ_le_zero 0)
  | 1, _, p, X, he, _ => by
    change T.P 0 (tr (f 0)) T.Z = T.P p X T.Z at he
    injection he with hp hX _
    rw [← hp, ← hX]
  | k + 2, _, p, X, he, hf => by
    rcases headS_high f hf (k + 2) p X he with h | h
    · by_cases hz : f (k + 1) = multi.T.Z
      · rw [headS_two_Z hz] at he
        exact headS_high_eq f (k + 1) (Nat.succ_pos k) p X he hf
      · rw [headS_two_ne hz] at he
        injection he with hp hX _
        subst hp; subst hX
        rw [part_add_distrib, part_of_index (k + 1) _
          (Rank1Termination.index_mono (Nat.le_succ k) _ (lowS_closed f hf (k + 1)).2.1), T.add_Z,
          (part_ct (k + 1) _).1, part_oneDel_fst]
    · exact h

/-- The index of the principal summand of a vector. -/
def hIdx : T → Nat
  | .Z => 0
  | .P p _ _ => p

def headIdx (w : multi.V multi.T) : Nat := hIdx (auxH w)

theorem auxH_headIdx (w : multi.V multi.T) : ∃ X, auxH w = T.P (headIdx w) X T.Z := by
  obtain ⟨p, X, he⟩ := auxH_shape w
  refine ⟨X, ?_⟩
  rw [headIdx, he]; rfl

theorem tr_headIdx (w : multi.V multi.T) (b : multi.T) :
    ∃ X, auxH w = T.P (headIdx w) X T.Z ∧ tr (multi.T.P w b) = T.P (headIdx w) X (tr b) := by
  obtain ⟨X, he⟩ := auxH_headIdx w
  exact ⟨X, he, by rw [tr_P, he, p_zero_add]⟩

theorem headIdx_eq {w : multi.V multi.T} {p : Nat} {X : T} (he : auxH w = T.P p X T.Z) :
    headIdx w = p := by
  rw [headIdx, he]; rfl

/-! ### Splitting a source term by the index of its principal summands -/

def srcPart (j : Nat) : multi.T → multi.T × multi.T
  | .Z => (.Z, .Z)
  | .P w b => if j < headIdx w then (.P w (srcPart j b).1, (srcPart j b).2)
      else ((srcPart j b).1, .P w (srcPart j b).2)

theorem srcPart_P_lt {j : Nat} {w : multi.V multi.T} (b : multi.T) (h : j < headIdx w) :
    (srcPart j (multi.T.P w b)).1 = multi.T.P w (srcPart j b).1 := by
  rw [srcPart, ite_eq_left h]

theorem srcPart_P_ge {j : Nat} {w : multi.V multi.T} (b : multi.T) (h : ¬ j < headIdx w) :
    (srcPart j (multi.T.P w b)).1 = (srcPart j b).1 := by
  rw [srcPart, ite_eq_right h]

theorem srcPart_trans (j : Nat) : ∀ s : multi.T, tr (srcPart j s).1 = (part j (tr s)).1
  | .Z => by show tr multi.T.Z = (part j (tr multi.T.Z)).1; rw [tr_Z]; rfl
  | .P w b => by
    obtain ⟨X, he, htr⟩ := tr_headIdx w b
    have ih := srcPart_trans j b
    rw [htr]
    by_cases hj : j < headIdx w
    · rw [srcPart_P_lt b hj, part_P_gt X (tr b) (Nat.not_le_of_lt hj)]
      obtain ⟨X', he', htr'⟩ := tr_headIdx w (srcPart j b).1
      rw [htr', ih]
      rw [he] at he'
      injection he' with _ hXX _
      rw [hXX]
    · rw [srcPart_P_ge b hj, part_P_le X (tr b) (Nat.le_of_not_lt hj)]
      exact ih

theorem nsize_P (w : multi.V multi.T) (x : multi.T) :
    multi.T.nsize (multi.T.P w x) = multi.V.size (multi.V.norm w) + multi.T.nsize x + 1 := by
  show (multi.T.norm (multi.T.P w x)).size = _
  rw [multi.T.norm_P]; rfl

theorem srcPart_nsize (j : Nat) : ∀ s : multi.T,
    multi.T.nsize (srcPart j s).1 ≤ multi.T.nsize s
  | .Z => Nat.le_refl _
  | .P w b => by
    have ih := srcPart_nsize j b
    by_cases hj : j < headIdx w
    · rw [srcPart_P_lt b hj, nsize_P, nsize_P]; omega
    · rw [srcPart_P_ge b hj]
      exact Nat.le_trans ih (Nat.le_of_lt (multi.T.nsize_tail_lt w b))

theorem tr_injective {s t : multi.T} (hs : NF s) (ht : NF t) (h : tr s = tr t) :
    multi.compareT s t = .eq := by
  rcases multi.T.lt_trichotomy s t with hst | heq | hts
  · have := tr_mono hs ht hst; rw [h] at this; exact absurd this (lt_irrefl_thm _)
  · exact (multi.compareT_eq_iff s t).2 heq
  · have := tr_mono ht hs hts; rw [h] at this; exact absurd this (lt_irrefl_thm _)

theorem tr_PZ (w : multi.V multi.T) : tr (multi.T.P w multi.T.Z) = auxH w := by
  rw [tr_P, tr_Z, T.add_Z]

theorem headIdx_mono {w w' : multi.V multi.T} (hw : ∀ i, NFComp i (multi.V.get0 w i))
    (hw' : ∀ i, NFComp i (multi.V.get0 w' i))
    (h : multi.T.P w' multi.T.Z ≤ multi.T.P w multi.T.Z) : headIdx w' ≤ headIdx w := by
  have hn := NF_PZ_of_comps hw
  have hn' := NF_PZ_of_comps hw'
  obtain ⟨X, he⟩ := auxH_headIdx w
  obtain ⟨X', he'⟩ := auxH_headIdx w'
  have hle : tr (multi.T.P w' multi.T.Z) ≤ tr (multi.T.P w multi.T.Z) := by
    rcases h with h | h
    · exact Or.inl (tr_mono hn' hn h)
    · exact Or.inr (tr_congr h)
  rw [tr_PZ, tr_PZ, he, he'] at hle
  exact head_le_index _ _ _ _ hle

theorem srcPart_NF (j : Nat) : ∀ s : multi.T, NF s →
    NF (srcPart j s).1 ∧
      (∀ w b, s = multi.T.P w b → headIdx w ≤ j → (srcPart j s).1 = multi.T.Z)
  | .Z, _ => ⟨NF.z, fun _ _ h => by cases h⟩
  | .P w b, hs => by
    obtain ⟨hw, hb, hg, hh⟩ := hs.inv
    have ih := srcPart_NF j b hb
    have hbz : ∀ w' b', b = multi.T.P w' b' → headIdx w' ≤ headIdx w := by
      intro w' b' hbe
      subst hbe
      exact headIdx_mono (fun i => hs.comp i) (fun i => hb.comp i) hh
    refine ⟨?_, ?_⟩
    · by_cases hj : j < headIdx w
      · rw [srcPart_P_lt b hj]
        refine NF.p w _ hw ih.1 hg ?_
        cases hbe : b with
        | Z => show multi.T.hd (srcPart j multi.T.Z).1 ≤ _; exact multi.T.Z_le _
        | P w' b' =>
          rw [hbe] at hh ih
          by_cases hj' : j < headIdx w'
          · rw [srcPart_P_lt b' hj']; exact hh
          · rw [ih.2 w' b' rfl (Nat.le_of_not_lt hj')]; exact multi.T.Z_le _
      · rw [srcPart_P_ge b hj]; exact ih.1
    · intro w0 b0 he hj
      injection he with h1 h2
      subst h1; subst h2
      rw [srcPart_P_ge b (Nat.not_lt_of_le hj)]
      cases hbe : b with
      | Z => rfl
      | P w' b' =>
        rw [hbe] at ih
        exact ih.2 w' b' rfl (Nat.le_trans (hbz w' b' hbe) hj)

/-! ### Visibility of reached coordinates -/

/-- Arguments of principal summands at levels at least `u` are dominated by `Vl`. -/
def SInv (u : Nat) (Vl : List T) : multi.T → Prop
  | .Z => True
  | .P w b => (∀ p a, auxH w = T.P p a T.Z → u ≤ p →
        (∀ y ∈ T.G1 u a, DomBy Vl y) ∧ (p = u → (part u a).1 ≠ T.Z → DomBy Vl (part u a).1)) ∧
      SInv u Vl b

theorem SInv_of_summands (u : Nat) (Vl : List T) : ∀ x : multi.T,
    (∀ p a, IsSummand p a (tr x) → u ≤ p →
      (∀ y ∈ T.G1 u a, DomBy Vl y) ∧ (p = u → (part u a).1 ≠ T.Z → DomBy Vl (part u a).1)) →
    SInv u Vl x
  | .Z, _ => trivial
  | .P w b, h => by
    obtain ⟨X, he, htr⟩ := tr_headIdx w b
    refine ⟨fun p a he' hup => ?_,
      SInv_of_summands u Vl b (fun p a hs hup => h p a (by rw [htr]; exact Or.inr hs) hup)⟩
    rw [he] at he'
    injection he' with hp ha _
    subst hp; subst ha
    exact h _ _ (by rw [htr]; exact Or.inl ⟨rfl, rfl⟩) hup

theorem SInv_top (u : Nat) (A : multi.T) (hA : NF A) : SInv u (T.G1 u (tr A)) A := by
  have hAnf := NF_good hA
  apply SInv_of_summands
  intro p a hs hup
  have hmem := G1_summand_mem u p a hup _ hs
  exact ⟨fun y hy => DomBy_of_mem _ _ (G1_summand_subset u p a hup _ hs y hy),
    fun _ _ => ⟨a, hmem, part_first_le u a (IsSummand_NF p a _ hAnf hs).1⟩⟩

theorem deepDom (u : Nat) (Vl : List T) {q c : multi.T} (hr : Reach u q c) :
    NF q → SInv u Vl q → (part u (tr c)).1 ≠ T.Z → DomBy Vl (part u (tr c)).1 := by
  induction hr with
  | here w b hne =>
    intro hq hinv hH
    have hvg : ∀ j, Gd j (multi.V.get0 w j) := fun j => Gd_of_NFComp (hq.comp j)
    obtain ⟨X, he⟩ := auxH_headIdx w
    have hcg := hvg u
    rcases Nat.lt_trichotomy (headIdx w) u with hp | hp | hp
    · exact absurd (above_zero he u hp) hne
    · have heq : (part (headIdx w) X).1 = (part (headIdx w) (tr (multi.V.get0 w (headIdx w)))).1 := by
        rw [auxH_eq w (w.length + 1) (Nat.le_succ _)] at he
        exact headS_high_eq _ _ (Nat.succ_pos _) _ X he hvg
      rw [hp] at heq he
      rw [← heq] at hH ⊢
      exact (hinv.1 u X he (Nat.le_refl _)).2 rfl hH
    · have hcon := headS_contr u (multi.V.get0 w) (w.length + 1) (Nat.succ_pos _) _ X
        (by rw [← auxH_eq w (w.length + 1) (Nat.le_succ _)]; exact he)
      have hd := high_dom_ec u (tr (multi.V.get0 w u)) hcg.1 hH
      have hdomA : DomBy (T.G1 u X) (part u (tr (multi.V.get0 w u))).1 := by
        by_cases hu0 : u = 0
        · subst hu0
          exact DomBy_mono _ _ (fun v hv => hcon.1 0 hp v (by rw [TContr, ite_eq_left rfl]; exact hv))
            _ hd.1
        · exact DomBy_mono _ _ (fun v hv => hcon.1 u hp v (by rw [TContr, ite_eq_right hu0]; exact hv))
            _ hd.2
      exact DomBy_trans _ _ (fun v hv => (hinv.1 _ X he (Nat.le_of_lt hp)).1 v hv) _ hdomA
  | tail w b c _ ih =>
    intro hq hinv hH
    exact ih hq.inv.2.1 hinv.2 hH
  | deep w b c j hj hr ih =>
    intro hq hinv hH
    obtain ⟨X, he⟩ := auxH_headIdx w
    have hne' : multi.V.get0 w j ≠ multi.T.Z := Reach_ne_Z hr
    have hjp : j ≤ headIdx w := Nat.le_of_not_gt fun h => hne' (above_zero he j h)
    have hg := Gd_of_NFComp (hq.comp j)
    have hcon := headS_contr u (multi.V.get0 w) (w.length + 1) (Nat.succ_pos _) _ X
      (by rw [← auxH_eq w (w.length + 1) (Nat.le_succ _)]; exact he)
    have hdomA := hinv.1 _ X he (by omega)
    have hj0 : j ≠ 0 := by omega
    apply ih (hq.inv.1 j) _ hH
    apply SInv_of_summands u Vl (multi.V.get0 w j)
    intro p' a' hs hup'
    rcases Nat.lt_or_ge j (headIdx w) with hlt | hge
    · have hsub : ∀ v ∈ T.G1 u (ct j (ec j (tr (multi.V.get0 w j)))), v ∈ T.G1 u X :=
        fun v hv => hcon.1 j hlt v (by rw [TContr, ite_eq_right hj0]; exact hv)
      refine ⟨fun y hy => ?_, fun hpu hne2 => ?_⟩
      · exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
          (early_card_summand_dom j u p' (tr (multi.V.get0 w j)) a' hg.1 hg.2 hs hup'
            (by omega) y hy))
      · subst hpu
        exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
          (early_card_summand_high_dom j _ (tr (multi.V.get0 w j)) a' hg.1 hs (by omega) hne2))
    · have hjp' : j = headIdx w := Nat.le_antisymm hjp hge
      have hsub : ∀ v ∈ T.G1 u (ct j (oneDel (tr (multi.V.get0 w j)))), v ∈ T.G1 u X := by
        intro v hv
        have h2 := hcon.2.1
        rw [← hjp', TopContr, ite_eq_right hj0] at h2
        exact h2 v hv
      refine ⟨fun y hy => ?_, fun hpu hne2 => ?_⟩
      · exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
          (oneDel_card_summand_dom j u p' (tr (multi.V.get0 w j)) a' hg.1 hs hup' (by omega) y hy))
      · subst hpu
        exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
          (oneDel_card_summand_high_dom j _ (tr (multi.V.get0 w j)) a' hg.1 hs (by omega) hne2))

/-! ### Suffixes of a source sum -/

inductive Suffix : multi.T → multi.T → Prop
  | refl (x : multi.T) : Suffix x x
  | step (w : multi.V multi.T) (b x : multi.T) : Suffix x b → Suffix x (multi.T.P w b)

theorem Suffix_tail {w : multi.V multi.T} {b A : multi.T} (h : Suffix (multi.T.P w b) A) :
    Suffix b A := by
  generalize hx : multi.T.P w b = x at h
  induction h with
  | refl => subst hx; exact Suffix.step w b b (Suffix.refl b)
  | step w' b' x _ ih => exact Suffix.step w' b' b (ih hx)

theorem Suffix_summand {x A : multi.T} (h : Suffix x A) :
    ∀ p a, IsSummand p a (tr x) → IsSummand p a (tr A) := by
  induction h with
  | refl => exact fun _ _ h => h
  | step w b x _ ih =>
    intro p a hs
    obtain ⟨X, _, htr⟩ := tr_headIdx w b
    rw [htr]
    exact Or.inr (ih p a hs)

theorem Suffix_srcPart_nsize (j : Nat) {x A : multi.T} (h : Suffix x A) :
    multi.T.nsize (srcPart j x).1 ≤ multi.T.nsize (srcPart j A).1 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step w b x _ ih =>
    by_cases hj : j < headIdx w
    · rw [srcPart_P_lt b hj, nsize_P]; omega
    · rw [srcPart_P_ge b hj]; exact ih

/-! ### Reached coordinates lie below the ambient term -/

theorem reach_lt (u : Nat) (A : multi.T) (hA : NF A)
    (hgood : ∀ y ∈ T.G1 u (tr A), y < tr A) (c : multi.T) (hc : Reach u A c) : c < A := by
  have hAnf := NF_good hA
  have hcnf : NF c := (Reach_comp hc hA).1
  have hcnf1 := NF_good hcnf
  have hdom : (part u (tr c)).1 ≠ T.Z → (part u (tr c)).1 < tr A := by
    intro hne
    obtain ⟨v, hv, hle⟩ := deepDom u _ hc hA (SInv_top u A hA) hne
    exact lt_of_le_of_lt_thm T _ _ _ hle (hgood v hv)
  have prefixArg : ∀ x, Suffix x A → ∀ w b, x = multi.T.P w b → u < headIdx w →
      multi.T.nsize c < multi.T.nsize (srcPart u x).1 → c < A := by
    intro x hsx w b hx hu hsz
    obtain ⟨X, _, htr⟩ := tr_headIdx w b
    have hsum : IsSummand (headIdx w) X (tr A) :=
      Suffix_summand hsx _ _ (by rw [hx, htr]; exact Or.inl ⟨rfl, rfl⟩)
    have hhead : T.P (headIdx w) X T.Z ≤ tr A :=
      partial_order.trans _ _ _ (summand_le_head _ _ _ hAnf hsum) (MT.head_le_self _)
    have hsA := Suffix_srcPart_nsize u hsx
    have hsc := srcPart_nsize u c
    have hsAA := srcPart_nsize u A
    rcases multi.T.lt_trichotomy c A with h | h | h
    · exact h
    · exfalso
      have hn : multi.T.nsize c = multi.T.nsize A := by unfold multi.T.nsize; rw [h]
      omega
    · exfalso
      have htr' := tr_mono hA hcnf h
      by_cases hz : (part u (tr c)).1 = T.Z
      · have hcp : tr c = (part u (tr c)).2 := by
          have := part_add u _ hcnf1
          rw [hz] at this
          exact this.symm
        have hidx := part_second_index u (tr c)
        rw [← hcp] at hidx
        have hlt : tr c < tr A :=
          lt_of_lt_of_le_thm T _ _ _ (index_Prop1_lt_succ u _ hidx)
            (partial_order.trans _ _ _ (head_base_le (u + 1) _ X hu) hhead)
        exact lt_asymm_thm hlt htr'
      · have hH := hdom hz
        rcases part_lt_cases u (tr A) (tr c) hAnf hcnf1 htr' with h1 | ⟨h1, _⟩
        · have hHnf := (part_NF u (tr c) hcnf1).1
          have : tr A < (part u (tr c)).1 :=
            lt_of_part_lt_cases u _ _ hAnf hHnf (Or.inl (by rw [part_first_fixed]; exact h1))
          exact lt_asymm_thm this hH
        · have hs1 : multi.T.nsize (srcPart u A).1 = multi.T.nsize (srcPart u c).1 := by
            apply multi.T.nsize_congr
            apply tr_injective (srcPart_NF u A hA).1 (srcPart_NF u c hcnf).1
            rw [srcPart_trans, srcPart_trans, h1]
          omega
  have main : ∀ x c', Reach u x c' → c' = c → Suffix x A → c < A := by
    intro x c' hr
    induction hr with
    | here w b hne =>
      intro hceq hsx
      subst hceq
      obtain ⟨X, he, htr⟩ := tr_headIdx w b
      rcases Nat.lt_trichotomy (headIdx w) u with hp | hp | hp
      · exact absurd (above_zero he u hp) hne
      · have hsum : IsSummand (headIdx w) X (tr A) :=
          Suffix_summand hsx _ _ (by rw [htr]; exact Or.inl ⟨rfl, rfl⟩)
        rw [hp] at hsum he
        have hXA : X < tr A := hgood X (G1_summand_mem u u X (Nat.le_refl _) _ hsum)
        have hhead : T.P u X T.Z ≤ tr A :=
          partial_order.trans _ _ _ (summand_le_head _ _ _ hAnf hsum) (MT.head_le_self _)
        apply tr_reflect_lt hcnf hA
        by_cases hp0 : u = 0
        · subst hp0
          rw [← head_countable he]
          exact hXA
        · have hcon := (headS_contr u (multi.V.get0 w) (w.length + 1) (Nat.succ_pos _) u X
            (by rw [← auxH_eq w (w.length + 1) (Nat.le_succ _)]; exact he)).2.2
            (Nat.pos_of_ne_zero hp0)
          rw [TopContr, ite_eq_right hp0] at hcon
          have hle1 := partial_order.trans _ _ _ (ct_self_le u _ (oneDel_NF _ hcnf1)) hcon
          rcases oneDel_cases (tr (multi.V.get0 w u)) with h | ⟨e, he', _⟩
          · rw [h] at hle1
            exact lt_of_le_of_lt_thm T _ _ _ hle1 hXA
          · rw [he']
            exact lt_of_lt_of_le_thm T _ _ _ (T.Lt.p_head _ _ _ _ _ _ (Nat.pos_of_ne_zero hp0))
              hhead
      · apply prefixArg (multi.T.P w b) hsx w b rfl hp
        rw [srcPart_P_lt b hp]
        exact multi.T.nsize_get0_lt w u _
    | tail w b c'' _ ih =>
      intro hceq hsx
      exact ih hceq (Suffix_tail hsx)
    | deep w b c'' j hj hr _ =>
      intro hceq hsx
      subst hceq
      obtain ⟨X, he, _⟩ := tr_headIdx w b
      have hne' : multi.V.get0 w j ≠ multi.T.Z := Reach_ne_Z hr
      have hjp : j ≤ headIdx w := Nat.le_of_not_gt fun h => hne' (above_zero he j h)
      have hup : u < headIdx w := by omega
      apply prefixArg (multi.T.P w b) hsx w b rfl hup
      rw [srcPart_P_lt b hup]
      exact Nat.lt_trans (Reach_nsize hr) (multi.T.nsize_get0_lt w j _)
  exact main A c hc rfl (Suffix.refl A)

/-- Buchholz goodness of the translation implies indexed goodness of the source. -/
theorem reverse_transfer (u : Nat) (A : multi.T) (hA : NF A)
    (hg : ∀ y ∈ T.G1 u (tr A), y < tr A) : NFComp u A := by
  suffices H : ∀ k u, A.size ≤ u + k → (∀ y ∈ T.G1 u (tr A), y < tr A) → NFComp u A from
    H A.size u (Nat.le_add_left _ _) hg
  intro k
  induction k with
  | zero => intro u hu _; exact ⟨hA, fun z hz => absurd hz (G_large u A hu z)⟩
  | succ k ih =>
    intro u hu hg
    have h1 := ih (u + 1) (by omega) (fun y hy => hg y (G1_antitone u (u + 1) (Nat.le_succ u) _ y hy))
    refine ⟨hA, fun z hz => ?_⟩
    rcases G_split u A z hz with h | ⟨c, hc, hzc⟩
    · exact h1.2 z h
    · have hclt := reach_lt u A hA hg c hc
      rcases hzc with rfl | hzc
      · exact hclt
      · exact multi.T.lt_trans ((Reach_comp hc hA).2 z hzc) hclt

/-! ### Explicit vectors -/

def vOf (f : Nat → multi.T) : Nat → multi.V multi.T
  | 0 => .emp
  | n + 1 => .snoc (f n) (vOf f n)

theorem vOf_length (f : Nat → multi.T) : ∀ n, (vOf f n).length = n
  | 0 => rfl
  | n + 1 => by show (vOf f n).length + 1 = n + 1; rw [vOf_length f n]

theorem get0_vOf (f : Nat → multi.T) :
    ∀ n j, multi.V.get0 (vOf f n) j = if j < n then f j else multi.T.Z
  | 0, j => by rw [ite_eq_right (Nat.not_lt_zero j)]; rfl
  | n + 1, j => by
    show (if j = (vOf f n).length then f n else multi.V.get0 (vOf f n) j) = _
    rw [vOf_length, get0_vOf f n j]
    by_cases hjn : j = n
    · rw [ite_eq_left hjn, ite_eq_left (by omega), hjn]
    · rw [ite_eq_right hjn]
      by_cases hj : j < n
      · rw [ite_eq_left hj, ite_eq_left (by omega)]
      · rw [ite_eq_right hj, ite_eq_right (by omega)]

/-- Constructive choice of finitely many coordinates. -/
theorem fun_choice (R : Nat → multi.T → Prop) :
    ∀ K, (∀ i, i < K → ∃ a, R i a) → ∃ f : Nat → multi.T, ∀ i, i < K → R i (f i)
  | 0, _ => ⟨fun _ => multi.T.Z, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | K + 1, h => by
    obtain ⟨f, hf⟩ := fun_choice R K (fun i hi => h i (Nat.lt_succ_of_lt hi))
    obtain ⟨a, ha⟩ := h K (Nat.lt_succ_self K)
    refine ⟨fun i => if i = K then a else f i, fun i hi => ?_⟩
    show R i (if i = K then a else f i)
    by_cases hiK : i = K
    · rw [ite_eq_left hiK, hiK]; exact ha
    · rw [ite_eq_right hiK]; exact hf i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hiK)

theorem auxH_vOf (f : Nat → multi.T) (n : Nat) : auxH (vOf f n) = headS f n := by
  rw [auxH_eq_length, vOf_length]
  apply headS_congr
  intro j hj
  rw [get0_vOf, ite_eq_left hj]
  exact multi.T.eqv_refl _

/-! ### Translations of explicit vectors -/

theorem lowS_eq_parts (c : T) (hc : T.isNF1 c) (f : Nat → multi.T) :
    ∀ m, (∀ i, i < m → TContr i (tr (f i)) = (if i = 0 then (part 0 c).2 else idxPart i c)) →
      lowS f m = (if m = 0 then T.Z else (part (m - 1) c).2)
  | 0, _ => rfl
  | 1, h => by
    have h0 := h 0 Nat.one_pos
    rw [TContr, ite_eq_left rfl, ite_eq_left rfl] at h0
    show ec 0 (tr (f 0)) = (if (1 : Nat) = 0 then T.Z else (part 0 c).2)
    rw [ite_eq_right (Nat.succ_ne_zero 0), h0]
  | m + 2, h => by
    have ih := lowS_eq_parts c hc f (m + 1) (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self _)))
    have hm := h (m + 1) (Nat.lt_succ_self _)
    rw [TContr, ite_eq_right (Nat.succ_ne_zero m), ite_eq_right (Nat.succ_ne_zero m)] at hm
    rw [lowS_two, hm, ih, ite_eq_right (Nat.succ_ne_zero m), ite_eq_right (Nat.succ_ne_zero (m + 1))]
    show T.add (idxPart (m + 1) c) (part (m + 1 - 1) c).2 = (part (m + 1) c).2
    rw [part_snd_split (m + 1) c hc]

theorem headS_top_eq (c : T) (hc : T.isNF1 c) (K : Nat) (hK : 0 < K) (f : Nat → multi.T)
    (hlow : ∀ i, i < K → TContr i (tr (f i)) = (if i = 0 then (part 0 c).2 else idxPart i c))
    (htop : f K ≠ multi.T.Z ∧ ct K (oneDel (tr (f K))) = (part (K - 1) c).1) :
    headS f (K + 1) = T.P K c T.Z := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, (Nat.succ_pred_eq_of_pos hK).symm⟩
  rw [headS_two_ne htop.1, htop.2, lowS_eq_parts c hc f (k + 1) hlow,
    ite_eq_right (Nat.succ_ne_zero k)]
  show T.P (k + 1) (T.add (part k c).1 (part k c).2) T.Z = _
  rw [part_add k c hc]

theorem NF_P_emp (a : multi.T) (ha : NF a) (hh : multi.T.hd a ≤ multi.T.P multi.V.emp multi.T.Z) :
    NF (multi.T.P multi.V.emp a) :=
  NF.p _ _ (fun _ => NF.z) ha (fun j y hy => by
    rw [show multi.V.get0 multi.V.emp j = multi.T.Z from rfl, G_Z] at hy; cases hy) hh

theorem tr_P_emp (a : multi.T) : tr (multi.T.P multi.V.emp a) = T.P 0 T.Z (tr a) := by
  rw [tr_P]
  show T.add (T.P 0 T.Z T.Z) (tr a) = _
  rw [p_zero_add]

/-! ### Preimages of principal terms -/

theorem principal_preimage (K : Nat) (c : T) (hy : T.isNF1 (T.P K c T.Z))
    (IH : ∀ y', MT.deg y' ≤ MT.deg c → T.isNF1 y' → ∃ a : multi.T, NF a ∧ tr a = y') :
    ∃ w : multi.V multi.T, (∀ i, NFComp i (multi.V.get0 w i)) ∧ auxH w = T.P K c T.Z := by
  obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv K c T.Z hy
  by_cases hK : K = 0
  · subst hK
    obtain ⟨a0, ha0, hta0⟩ := IH c (Nat.le_refl _) hc
    have ha0c : NFComp 0 a0 := reverse_transfer 0 a0 ha0 (by rw [hta0]; exact hgc)
    refine ⟨multi.V.snoc a0 multi.V.emp, fun i => ?_, ?_⟩
    · rw [get0_single]
      by_cases hi : i = 0
      · rw [ite_eq_left hi, hi]; exact ha0c
      · rw [ite_eq_right hi]; exact NFComp_Z i
    · rw [auxH_single, hta0]
  · have hKp : 0 < K := Nat.pos_of_ne_zero hK
    have hK1 : K = K - 1 + 1 := (Nat.succ_pred_eq_of_pos hKp).symm
    have hdNF := (part_NF (K - 1) c hc).1
    have hdidx : ∀ p a, IsSummand p a (part (K - 1) c).1 → K ≤ p := by
      intro p a hs
      have := part_fst_summand_gt (K - 1) c p a hs
      rw [hK1]; exact this
    have heNF := UC_NF K hKp _ hdNF hdidx
    have hegood := UC_top_good K hKp c hc hgc
    have hedeg : MT.deg (UC K (part (K - 1) c).1) ≤ MT.deg c :=
      Nat.le_trans (UC_deg K hKp _ hdNF) (part_props (K - 1) c).1
    obtain ⟨ae, hae, htae⟩ := IH _ hedeg heNF
    -- the top coordinate
    have hpre : ∃ aK : multi.T, NF aK ∧ tr aK = lpInv (UC K (part (K - 1) c).1) := by
      generalize hE : UC K (part (K - 1) c).1 = E at htae
      match E, htae with
      | T.Z, _ =>
        refine ⟨multi.T.P multi.V.emp multi.T.Z, NF_P_emp _ NF.z (multi.T.Z_le _), ?_⟩
        rw [tr_P_emp, tr_Z]; rfl
      | T.P (p + 1) h t, htae => exact ⟨ae, hae, by rw [htae]; rfl⟩
      | T.P 0 (T.P q h' t') t, htae => exact ⟨ae, hae, by rw [htae]; rfl⟩
      | T.P 0 T.Z t, htae =>
        refine ⟨multi.T.P multi.V.emp ae, NF_P_emp _ hae ?_, ?_⟩
        · cases hae' : ae with
          | Z => exact multi.T.Z_le _
          | P w' b' =>
            rw [hae'] at hae htae
            obtain ⟨p', X', he', htr'⟩ := tr_P_eq w' b'
            rw [htr'] at htae
            injection htae with hp' hX' _
            subst hp'; subst hX'
            have hw' : NF (multi.T.P w' multi.T.Z) := NF_PZ_of_comps (fun i => hae.comp i)
            have hemp : NF (multi.T.P multi.V.emp multi.T.Z) := NF_P_emp _ NF.z (multi.T.Z_le _)
            apply tr_reflect_le hw' hemp
            rw [tr_PZ, he', tr_P_emp, tr_Z]
            exact Or.inr rfl
        · rw [tr_P_emp, htae]; rfl
    obtain ⟨aK, haK, htaK⟩ := hpre
    have haKc : NFComp K aK :=
      reverse_transfer K aK haK (by rw [htaK]; exact lpInv_good K hKp _ heNF hegood)
    have haKne : aK ≠ multi.T.Z := fun h => lpInv_ne_Z (UC K (part (K - 1) c).1)
      (by rw [← htaK, h, tr_Z])
    have hlow : ∀ i, i < K → ∃ a : multi.T, NFComp i a ∧ tr a = lowPiece c i := by
      intro i _
      obtain ⟨hn, hg, hd, _⟩ := lowPiece_props c hc i
      obtain ⟨a, ha, hta⟩ := IH _ hd hn
      exact ⟨a, reverse_transfer i a ha (by rw [hta]; exact hg), hta⟩
    obtain ⟨f, hf⟩ := fun_choice
      (fun i a => (i < K → NFComp i a ∧ tr a = lowPiece c i) ∧
        (i = K → NFComp K a ∧ tr a = lpInv (UC K (part (K - 1) c).1) ∧ a ≠ multi.T.Z))
      (K + 1) (fun i hi => by
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
        · obtain ⟨a, hac, hta⟩ := hlow i hi'
          exact ⟨a, fun _ => ⟨hac, hta⟩, fun h => absurd h (Nat.ne_of_lt hi')⟩
        · exact ⟨aK, fun h => absurd hi' (Nat.ne_of_lt h), fun _ => ⟨haKc, htaK, haKne⟩⟩)
    refine ⟨vOf f (K + 1), fun i => ?_, ?_⟩
    · rw [get0_vOf]
      by_cases hi : i < K + 1
      · rw [ite_eq_left hi]
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | hi'
        · exact ((hf i hi).1 hi').1
        · rw [hi']; exact ((hf K (Nat.lt_succ_self K)).2 rfl).1
      · rw [ite_eq_right hi]; exact NFComp_Z i
    · rw [auxH_vOf]
      apply headS_top_eq c hc K hKp f
      · intro i hi
        rw [((hf i (Nat.lt_succ_of_lt hi)).1 hi).2]
        exact (lowPiece_props c hc i).2.2.2
      · obtain ⟨_, ht, hne⟩ := (hf K (Nat.lt_succ_self K)).2 rfl
        refine ⟨hne, ?_⟩
        rw [ht, oneDel_lpInv]
        exact UC_spec K hKp _ hdNF hdidx

theorem trans_surj_aux : ∀ (n : Nat) (y : T), MT.deg y ≤ n → T.isNF1 y →
    ∃ a : multi.T, NF a ∧ tr a = y
  | 0, y, hd, _ => by
    cases y with
    | Z => exact ⟨multi.T.Z, NF.z, tr_Z⟩
    | P p c r => exact absurd (Nat.le_trans (Nat.le_max_left _ _) hd) (Nat.not_succ_le_zero _)
  | n + 1, y, hd, hy => by
    induction y with
    | Z => exact ⟨multi.T.Z, NF.z, tr_Z⟩
    | P K c r _ ihr =>
      obtain ⟨hc, hr, hgc, hrh⟩ := T.isNF1_P_inv K c r hy
      have hdeg : MT.deg c ≤ n := Nat.le_of_succ_le_succ (Nat.le_trans (Nat.le_max_left _ _) hd)
      have hdr : MT.deg r ≤ n + 1 := Nat.le_trans (Nat.le_max_right _ _) hd
      obtain ⟨w, hw, hwe⟩ := principal_preimage K c (T.isNF1.p K c T.Z hc T.isNF1.z hgc (T.Z_le _))
        (fun y' hd' hy' => trans_surj_aux n y' (Nat.le_trans hd' hdeg) hy')
      obtain ⟨ar, har, htar⟩ := ihr hdr hr
      have hwNF := NF_PZ_of_comps hw
      refine ⟨multi.T.P w ar, NF.p w ar (fun i => (hw i).1) har (fun i => (hw i).2) ?_, ?_⟩
      · cases har' : ar with
        | Z => exact multi.T.Z_le _
        | P w' b' =>
          rw [har'] at har htar
          have hw'NF : NF (multi.T.P w' multi.T.Z) := NF_PZ_of_comps (fun i => har.comp i)
          apply tr_reflect_le hw'NF hwNF
          rw [tr_PZ, tr_PZ, hwe, ← head_tr w' b', htar]
          exact hrh
      · rw [tr_P, hwe, htar, p_zero_add]

/-- Every Buchholz normal form below `Ω` is the translation of a countable normal form. -/
theorem surj (u : T) (hu : T.isNF1 u) (hub : u < T.P 1 T.Z T.Z) :
    ∃ s, (NF s ∧ s < otb) ∧ tr s = u := by
  obtain ⟨s, hs, hts⟩ := trans_surj_aux (MT.deg u) u (Nat.le_refl _) hu
  refine ⟨s, ⟨hs, ?_⟩, hts⟩
  cases s with
  | Z => exact multi.T.Z_lt_P _ _
  | P v a =>
    obtain ⟨X, he, htr⟩ := tr_headIdx v a
    have hp0 : headIdx v = 0 := by
      rw [← hts, htr] at hub
      rcases lt_inv _ _ _ _ _ _ hub with h | ⟨_, h⟩ | ⟨_, _, h⟩
      · exact Nat.lt_one_iff.1 h
      · exact absurd h lt_Z_inv
      · exact absurd h lt_Z_inv
    rw [hp0] at he
    have hzero : ∀ j, 1 ≤ j → multi.V.get0 v j = multi.T.Z := fun j hj => above_zero he j hj
    apply multi.T.P_lt_P_of_vlt
    apply multi.V.lt_of_pivot 1
    · intro j hj
      rw [hzero j (by omega), get0_otb_vec, ite_eq_right (by omega)]
      exact multi.compareT_ZZ
    · rw [hzero 1 (Nat.le_refl 1), get0_otb_vec, ite_eq_left rfl]
      exact multi.T.Z_lt_P _ _

end old

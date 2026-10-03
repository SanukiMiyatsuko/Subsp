import Subsp.old.stop_indexed_nf

/-! Closure of indexed legacy normal forms under fundamental sequences, via support
domination on intervals (`IDom`), and the source-side bound of OT terms. -/

namespace new

theorem T.le_of_not_lt {lam : Nat} {a b : T lam} (h : ¬ a < b) : b ≤ a := by
  rcases T_total a b with h' | h' | rfl
  · exact absurd h' h
  · exact Or.inl h'
  · exact T.le_refl _

theorem Vec.ext_idx {lam m : Nat} (v w : Vec (T lam) m) (h : ∀ i : Fin m, v.idx i = w.idx i) :
    v = w := by
  induction m with
  | zero => cases v; cases w; rfl
  | succ k ih =>
      cases v with
      | snoc _ vs vx =>
        cases w with
        | snoc _ ws wx =>
          rw [ih vs ws fun i => by simpa [Vec.idx, i.isLt] using h i.castSucc,
            show vx = wx by simpa [Vec.idx] using h (Fin.last k)]

instance T.decLt {lam : Nat} (x y : T lam) : Decidable (x < y) :=
  inferInstanceAs (Decidable (T.lt x y))

theorem T.vector_rel_of_P_le_P {lam : Nat} (v w : Vec (T lam) lam) (a b : T lam)
    (h : T.P v a ≤ T.P w b) : compareVec v w = Ordering.lt ∨ v = w := by
  rcases h with h | h
  · change (match compareVec v w with | .eq => compareT a b | ord => ord) = .lt at h
    cases hc : compareVec v w with
    | lt => exact Or.inl rfl
    | eq => exact Or.inr (Vec_eq_sound _ _ hc)
    | gt => simp [hc] at h
  · cases T_eq_sound _ _ h
    exact Or.inr rfl

theorem T.NF_tail_lt {lam : Nat} (ls : Vec (T lam) lam) (b : T lam) (h : T.isNF (T.P ls b)) :
    b < T.P ls b := by
  obtain ⟨-, hb, hh⟩ := T.isNF_P_inv ls b h
  clear h
  induction hb generalizing ls with
  | z => rfl
  | p v d _ _ _ hh' _ ih =>
      rcases T.vector_rel_of_P_le_P v ls T.Z T.Z hh with hv | rfl
      · exact T.P_lt_P_of_compareVec_lt _ _ _ _ hv
      · exact T.P_tail_lt _ _ _ (ih v hh')

theorem T.head_fund_le {lam : Nat} (s t : T lam) : T.head (T.fund s t) ≤ T.head s := by
  cases s with
  | Z => rw [T.fund]; exact T.le_refl _
  | P ls add => exact T.head_mono _ _ (T.fund_lt_self (T.P ls add) t (by intro h; cases h))

theorem T.rplc_NF_closed {lam : Nat} (ls : Vec (T lam) lam) (i : Fin lam) (a : T lam)
    (hs : T.isNF (T.P ls T.Z)) (ha : T.isNFComp i.val a) : T.isNF (T.P (ls.rplc i a) T.Z) := by
  have h (q : Fin lam) : T.isNFComp q.val ((ls.rplc i a).idx q) := by
    by_cases hqi : q.val = i.val
    · rw [Fin.eq_of_val_eq hqi, Vec.rplc_idx_same]; exact ha
    · rw [Vec.rplc_idx_of_ne _ _ _ _ hqi]; exact (T.isNF_P_inv ls T.Z hs).1 q
  exact .p _ T.Z (fun q => (h q).1) .z (fun q => (h q).2) (T.Z_le _)

/-! Domains of principal terms. -/

theorem T.dom_PZ_Omega_split {lam : Nat} (ls : Vec (T lam) lam) (i : Fin lam)
    (hd : T.dom (T.P ls T.Z) = .Omega i) :
    ∃ m : Fin lam, ∃ d : Dom lam, T.domVecMinIdx ls = some (m, d) ∧
      ((d = .one ∧ 0 < m.val ∧ i = m) ∨ ∃ j : Fin lam, d = .Omega j ∧ j ≤ m ∧ i = j) := by
  rw [T.dom, ite_eq_left rfl] at hd
  split at hd
  · cases hd
  · rename_i m d hmin
    refine ⟨m, d, hmin, ?_⟩
    split at hd <;> (try split at hd) <;> cases hd
    · exact Or.inl ⟨rfl, Nat.pos_of_ne_zero ‹_›, rfl⟩
    · exact Or.inr ⟨_, rfl, ‹_›, rfl⟩

theorem T.dom_PZ_omega_split {lam : Nat} (ls : Vec (T lam) lam)
    (hd : T.dom (T.P ls T.Z) = .omega) :
    ∃ m : Fin lam, ∃ d : Dom lam, T.domVecMinIdx ls = some (m, d) ∧
      ((d = .one ∧ m.val = 0) ∨ d = .omega ∨ ∃ j : Fin lam, d = .Omega j ∧ ¬ j ≤ m) := by
  rw [T.dom, ite_eq_left rfl] at hd
  split at hd
  · cases hd
  · rename_i m d hmin
    refine ⟨m, d, hmin, ?_⟩
    split at hd <;> (try split at hd) <;> (try cases hd)
    · exact Or.inl ⟨rfl, ‹_›⟩
    · exact Or.inr (Or.inr ⟨_, rfl, ‹_›⟩)
    · rename_i h1 h2
      cases d with
      | zero => exact absurd rfl (T.domVecMinIdx_some_spec ls m _ hmin).1
      | omega => exact Or.inr (Or.inl rfl)
      | one => exact absurd rfl h1
      | Omega j => exact absurd rfl (h2 j)

theorem T.fund_Omega_ne_Z {lam : Nat} (s t : T lam) (i : Fin lam) (hd : T.dom s = .Omega i) :
    T.fund s t ≠ T.Z := by
  cases s with
  | Z => cases hd
  | P ls add =>
      by_cases hadd : add = T.Z
      · subst add
        obtain ⟨m, d, hmin, hcase⟩ := T.dom_PZ_Omega_split ls i hd
        rw [T.fund, ite_eq_left rfl, hmin]
        rcases hcase with ⟨rfl, hm, rfl⟩ | ⟨j, rfl, hjm, rfl⟩
        · obtain ⟨_ | r, mh⟩ := i
          · exact absurd hm (Nat.lt_irrefl 0)
          · intro h; cases h
        · simp only [hjm, ite_true]; intro h; cases h
      · rw [T.fund_P_tail_eq ls add t hadd]; intro h; cases h

theorem T.fund_Omega_strict_mono {lam : Nat} (s x y : T lam) (i : Fin lam)
    (hd : T.dom s = .Omega i) (hxy : x < y) : T.fund s x < T.fund s y := by
  induction s using (measure T.size).wf.induction generalizing x y i with
  | h s ih =>
      cases s with
      | Z => cases hd
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            obtain ⟨m, d, hmin, hcase⟩ := T.dom_PZ_Omega_split ls i hd
            have hrep (j : Fin lam) {a b : T lam} (v : Vec (T lam) lam) (hab : a < b) :
                T.P (v.rplc j a) T.Z < T.P (v.rplc j b) T.Z :=
              T.P_lt_P_of_compareVec_lt _ _ _ _ (Vec.compare_lt_of_pivot _ _ j
                (fun q hq => by rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq),
                  Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq)])
                (by simpa only [Vec.rplc_idx_same] using hab))
            rw [T.fund, ite_eq_left rfl, hmin, T.fund, ite_eq_left rfl, hmin]
            rcases hcase with ⟨rfl, hm, rfl⟩ | ⟨j, rfl, hjm, rfl⟩
            · obtain ⟨_ | r, mh⟩ := i
              · exact absurd hm (Nat.lt_irrefl 0)
              · exact hrep ⟨r, Nat.lt_of_succ_lt mh⟩ _ hxy
            · simp only [hjm, ite_true]
              exact hrep m ls (ih (ls.idx m) (T.idx_size_lt_P ls T.Z m) x y i
                (T.domVecMinIdx_some_spec ls m _ hmin).2.1 hxy)
          · rw [T.fund_P_tail_eq ls add x hadd, T.fund_P_tail_eq ls add y hadd]
            exact T.P_tail_lt _ _ _ (ih add (T.add_size_lt_P ls add) x y i
              (by simpa [T.dom, hadd] using hd) hxy)

theorem T.iter_fund_lt_next {lam : Nat} (s t : T lam) (i : Fin lam) (hd : T.dom s = .Omega i) :
    T.iter (fun x => T.fund s x) t < T.fund s (T.iter (fun x => T.fund s x) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      rw [T.iter]
      cases he : T.fund s T.Z with
      | Z => exact False.elim (T.fund_Omega_ne_Z s T.Z i hd he)
      | P ls add => rfl
  | P us add _ ih => exact T.fund_Omega_strict_mono s _ _ i hd ih
  | nil | snoc => trivial

/-! Support domination on intervals. -/

theorem T.Gi_trans {lam : Nat} (u : Nat) (s : T lam) :
    ∀ x y, x ∈ T.Gi u s → y ∈ T.Gi u x → y ∈ T.Gi u s := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      intro x y hx hy
      cases s with
      | Z => cases hx
      | P v b =>
          apply (T.mem_Gi_P u v b y).mpr
          rcases (T.mem_Gi_P u v b x).mp hx with ⟨i, hui, rfl | hx⟩ | hx
          · exact Or.inl ⟨i, hui, Or.inr hy⟩
          · exact Or.inl ⟨i, hui, Or.inr (ih _ (T.idx_size_lt_P v b i) x y hx hy)⟩
          · exact Or.inr (ih b (T.add_size_lt_P v b) x y hx hy)

theorem T.find_violating_source {lam : Nat} (u : Nat) (b c₀ w : T lam)
    (hw : w ∈ T.Gi u c₀) (hbw : b ≤ w) :
    ∃ c, c ∈ T.Gi u c₀ ∧ b ≤ c ∧ ∀ x ∈ T.Gi u c, x < b := by
  induction w using (measure T.size).wf.induction with
  | h w ih =>
      by_cases h : ∃ x ∈ T.Gi u w, ¬ x < b
      · obtain ⟨x, hx, hn⟩ := h
        exact ih x (T.Gi_size_lt u w x hx) (T.Gi_trans u c₀ w x hw hx) (T.le_of_not_lt hn)
      · exact ⟨w, hw, hbw, fun x hx => Decidable.not_not.mp fun hn => h ⟨x, hx, hn⟩⟩

def T.GZ {lam : Nat} (u : Nat) (z : T lam) : List (T lam) :=
  [z] ++ T.Gi u z ++ [T.Z]

/-- Supports of `b` at level `u` are below `b` or dominated by supports of any `c ∈ [b, a]`
(or by `z`). -/
def T.IDom {lam : Nat} (u : Nat) (z b a : T lam) : Prop :=
  b < a ∧ ∀ c, b ≤ c → c ≤ a → ∀ x ∈ T.Gi u b,
    x < b ∨ ∃ y, y ∈ T.Gi u c ++ T.GZ u z ∧ x ≤ y

def T.WDom {lam : Nat} (z b a : T lam) : Prop := ∀ u, T.IDom u z b a

theorem T.NFComp_of_IDom {lam : Nat} (u : Nat) (z b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a) (hz : T.isNFComp u z)
    (hs : T.IDom u z b a) (hzb : z < b) : T.isNFComp u b := by
  have hZ : ∀ x ∈ T.GZ u z, x < b := by
    intro x hx
    simp only [T.GZ, List.mem_append, List.mem_singleton] at hx
    rcases hx with (rfl | hx) | rfl
    · exact hzb
    · exact T_trans _ _ _ (hz.2 x hx) hzb
    · exact T.lt_of_le_of_lt _ _ _ (T.Z_le z) hzb
  have hup : ∀ x ∈ T.Gi u b, x < a := by
    intro x hx
    rcases hs.2 a (Or.inl hs.1) (T.le_refl a) x hx with hx | ⟨y, hy, hxy⟩
    · exact T_trans _ _ _ hx hs.1
    · exact T.lt_of_le_of_lt _ _ _ hxy
        ((List.mem_append.mp hy).elim (ha.2 y) (fun hy => T_trans _ _ _ (hZ y hy) hs.1))
  refine ⟨hb, fun x hx => ?_⟩
  by_cases hxb : x < b
  · exact hxb
  · obtain ⟨c, hc, hbc, hcut⟩ := T.find_violating_source u b b x hx (T.le_of_not_lt hxb)
    rcases hs.2 c hbc (Or.inl (hup c hc)) c hc with hcc | ⟨y, hy, hcy⟩
    · exact False.elim (strict_partial_order.irrefl b (T.lt_of_le_of_lt _ _ _ hbc hcc))
    · have hyb : y < b := (List.mem_append.mp hy).elim (hcut y) (hZ y)
      exact False.elim (strict_partial_order.irrefl b
        (T.lt_of_le_of_lt _ _ _ hbc (T.lt_of_le_of_lt _ _ _ hcy hyb)))

theorem T.NFComp_of_IDom_zero {lam : Nat} (u : Nat) (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a) (hs : T.IDom u T.Z b a) : T.isNFComp u b := by
  cases b with
  | Z => exact T.isNFComp_Z u
  | P v c => exact T.NFComp_of_IDom u T.Z _ a hb ha (T.isNFComp_Z u) hs rfl

theorem T.IDom_eliminate {lam : Nat} (u : Nat) (z b a : T lam)
    (hb : T.IDom u z b a) (hz : T.IDom u T.Z z a) (hzb : z < b) : T.IDom u T.Z b a := by
  refine ⟨hb.1, fun c hbc hca x hx => ?_⟩
  rcases hb.2 c hbc hca x hx with hxc | ⟨y, hy, hxy⟩
  · exact Or.inl hxc
  · rcases List.mem_append.mp hy with hy | hy
    · exact Or.inr ⟨y, List.mem_append_left _ hy, hxy⟩
    · simp only [T.GZ, List.mem_append, List.mem_singleton] at hy
      rcases hy with (rfl | hy) | rfl
      · exact Or.inl (T.lt_of_le_of_lt _ _ _ hxy hzb)
      · rcases hz.2 c (Or.inl (T.lt_of_lt_of_le _ _ _ hzb hbc)) hca y hy with hyc | ⟨w, hw, hyw⟩
        · exact Or.inl (T.lt_of_le_of_lt _ _ _ hxy (T_trans _ _ _ hyc hzb))
        · exact Or.inr ⟨w, hw, T.le_trans _ _ _ hxy hyw⟩
      · exact Or.inr ⟨T.Z, List.mem_append_right _ (by simp [T.GZ]), hxy⟩

theorem T.IDom_tail {lam : Nat} (u : Nat) (z b a : T lam)
    (ls : Vec (T lam) lam) (hbtail : b < T.P ls b) (hs : T.IDom u z b a) :
    T.IDom u z (T.P ls b) (T.P ls a) := by
  refine ⟨T.P_tail_lt ls b a hs.1, fun c hl hh x hx => ?_⟩
  have hh' := T.le_antisymm _ _ (T.head_mono_le c (T.P ls a) hh) (T.head_mono_le (T.P ls b) c hl)
  cases c with
  | Z => cases hh'
  | P cs d =>
      change T.P cs T.Z = T.P ls T.Z at hh'
      cases hh'
      have hiff (x y : T lam) : T.P ls x ≤ T.P ls y ↔ x ≤ y := by
        simp only [LE.le, T.le, compareT, Vec_refl]
      have hmem (y) (h : y ∈ T.Gi u d ∨ y ∈ T.GZ u z) : y ∈ T.Gi u (T.P ls d) ++ T.GZ u z := by
        rcases h with h | h
        · exact List.mem_append_left _ ((T.mem_Gi_P u ls d y).mpr (Or.inr h))
        · exact List.mem_append_right _ h
      rcases (T.mem_Gi_P u ls b x).mp hx with hv | ht
      · exact Or.inr ⟨x, List.mem_append_left _ ((T.mem_Gi_P u ls d x).mpr (Or.inl hv)),
          T.le_refl _⟩
      · rcases hs.2 d ((hiff _ _).mp hl) ((hiff _ _).mp hh) x ht with hxd | ⟨y, hy, hxy⟩
        · exact Or.inl (T_trans _ _ _ hxd hbtail)
        · exact Or.inr ⟨y, hmem y (List.mem_append.mp hy), hxy⟩

theorem Vec.interval_pivot_properties {lam m : Nat} (low mid high : Vec (T lam) m) (i : Fin m)
    (heqAbove : ∀ j : Fin m, i.val < j.val → low.idx j = high.idx j)
    (hlm : compareVec low mid = Ordering.lt ∨ low = mid)
    (hmh : compareVec mid high = Ordering.lt ∨ mid = high) :
    (∀ j : Fin m, i.val < j.val → mid.idx j = high.idx j) ∧
      low.idx i ≤ mid.idx i ∧ mid.idx i ≤ high.idx i := by
  have irr (x : T lam) (h : x < x) : False := strict_partial_order.irrefl x h
  have key (v w : Vec (T lam) m) (h : compareVec v w = .lt ∨ v = w)
      (hab : ∀ j : Fin m, i.val < j.val → v.idx j = w.idx j) : v.idx i ≤ w.idx i := by
    rcases h with h | rfl
    · obtain ⟨p, hpEq, hpLt⟩ := Vec.compare_lt_has_pivot v w h
      rcases Nat.lt_trichotomy p.val i.val with hpi | hpi | hpi
      · rw [hpEq i hpi]; exact T.le_refl _
      · rw [Fin.eq_of_val_eq hpi] at hpLt; exact Or.inl hpLt
      · rw [hab p hpi] at hpLt; exact absurd hpLt (irr _)
    · exact T.le_refl _
  have hmid : ∀ j : Fin m, i.val < j.val → mid.idx j = high.idx j := by
    rcases hmh with h | rfl
    · obtain ⟨q, hqEq, hqLt⟩ := Vec.compare_lt_has_pivot mid high h
      have hqi : q.val ≤ i.val := by
        refine Nat.le_of_not_gt fun hiq => ?_
        rcases hlm with hl | rfl
        · obtain ⟨p, hpEq, hpLt⟩ := Vec.compare_lt_has_pivot low mid hl
          rcases Nat.lt_trichotomy q.val p.val with hqp | heq | hpq
          · rw [hqEq p hqp, ← heqAbove p (by omega)] at hpLt; exact irr _ hpLt
          · obtain rfl := Fin.eq_of_val_eq heq
            have hc := T_trans _ _ _ hpLt hqLt
            rw [← heqAbove q hiq] at hc
            exact irr _ hc
          · rw [← hpEq q hpq, heqAbove q hiq] at hqLt; exact irr _ hqLt
        · rw [heqAbove q hiq] at hqLt; exact irr _ hqLt
      exact fun j hj => hqEq j (by omega)
    · exact fun _ _ => rfl
  exact ⟨hmid, key low mid hlm fun j hj => (heqAbove j hj).trans (hmid j hj).symm,
    key mid high hmh hmid⟩

/-- Replacing the minimal coordinate `m` by a smaller `b`, and coordinates below `m` (at
visited levels) by `Z` or `z`, gives an interval-dominated principal term. -/
theorem T.IDom_low {lam : Nat} (u : Nat) (z b : T lam) (ls low : Vec (T lam) lam) (m : Fin lam)
    (hm : low.idx m = b) (hblt : b < ls.idx m)
    (habove : ∀ q : Fin lam, m.val < q.val → low.idx q = ls.idx q)
    (hbelow : ∀ q : Fin lam, u ≤ q.val → q.val < m.val → low.idx q = T.Z ∨ low.idx q = z)
    (hinner : u ≤ m.val → T.IDom u z b (ls.idx m)) :
    T.IDom u z (T.P low T.Z) (T.P ls T.Z) := by
  subst hm
  refine ⟨T.P_lt_P_of_compareVec_lt _ _ _ _ (Vec.compare_lt_of_pivot _ _ m habove hblt), ?_⟩
  intro c hlc hch x hx
  cases c with
  | Z => rcases hlc with h | h <;> cases h
  | P mid add =>
      obtain ⟨hmid, hlm, hmh⟩ := Vec.interval_pivot_properties low mid ls m habove
        (T.vector_rel_of_P_le_P _ _ _ _ hlc) (T.vector_rel_of_P_le_P _ _ _ _ hch)
      have hG (q : Fin lam) (hq : u ≤ q.val) (y) (hy : y = mid.idx q ∨ y ∈ T.Gi u (mid.idx q)) :
          y ∈ T.Gi u (T.P mid add) ++ T.GZ u z :=
        List.mem_append_left _ ((T.mem_Gi_P u mid add y).mpr (Or.inl ⟨q, hq, hy⟩))
      rcases (T.mem_Gi_P u low T.Z x).mp hx with ⟨q, huq, hq⟩ | ht
      · rcases Nat.lt_trichotomy q.val m.val with hqm | hqm | hmq
        · refine Or.inr ⟨x, List.mem_append_right _ ?_, T.le_refl _⟩
          rcases hbelow q huq hqm with h | h <;> rw [h] at hq
          · rcases hq with rfl | hq
            · simp [T.GZ]
            · cases hq
          · rcases hq with rfl | hq
            · simp [T.GZ]
            · simp [T.GZ, hq]
        · obtain rfl := Fin.eq_of_val_eq hqm
          rcases hq with rfl | hx
          · exact Or.inr ⟨_, hG q huq _ (Or.inl rfl), hlm⟩
          · rcases (hinner huq).2 (mid.idx q) hlm hmh x hx with hxb | ⟨y, hy, hxy⟩
            · exact Or.inr ⟨_, hG q huq _ (Or.inl rfl), Or.inl (T.lt_of_lt_of_le _ _ _ hxb hlm)⟩
            · refine Or.inr ⟨y, ?_, hxy⟩
              rcases List.mem_append.mp hy with hy | hy
              · exact hG q huq y (Or.inr hy)
              · exact List.mem_append_right _ hy
        · rw [habove q hmq, ← hmid q hmq] at hq
          exact Or.inr ⟨x, hG q huq x hq, T.le_refl _⟩
      · cases ht

theorem T.IDom_rplc_min {lam : Nat} (u : Nat) (z : T lam) (ls : Vec (T lam) lam)
    (m : Fin lam) (d : Dom lam) (b : T lam) (hmin : T.domVecMinIdx ls = some (m, d))
    (hblt : b < ls.idx m) (hinner : u ≤ m.val → T.IDom u z b (ls.idx m)) :
    T.IDom u z (T.P (ls.rplc m b) T.Z) (T.P ls T.Z) :=
  T.IDom_low u z b ls _ m (Vec.rplc_idx_same _ _ _) hblt
    (fun _ hq => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq))
    (fun q _ hq => Or.inl ((Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hq)).trans
      (T.dom_zero_eq_Z _ ((T.domVecMinIdx_some_spec ls m d hmin).2.2 q hq))))
    hinner

theorem T.fund_one_IDom {lam : Nat} (u : Nat) (z s : T lam) (hd : T.dom s = .one) :
    T.IDom u z (T.fund s T.Z) s := by
  have hne : s ≠ T.Z := by intro he; subst s; cases hd
  obtain ⟨-, h2, -, h4⟩ := T.fund_one_props s hd
  refine ⟨T.fund_lt_self s T.Z hne, fun c hl hu x hx =>
    Or.inr ⟨x, List.mem_append_left _ ?_, T.le_refl _⟩⟩
  rcases hu with hu | hu
  · rwa [← T.le_antisymm _ _ hl (h2 c hu)]
  · rw [T_eq_sound _ _ hu]
    exact h4 u x hx

theorem T.WDom_mul_PZ {lam : Nat} (u v : Vec (T lam) lam) (t : T lam)
    (hvec : compareVec u v = Ordering.lt) (hbase : T.WDom T.Z (T.P u T.Z) (T.P v T.Z)) :
    T.WDom T.Z (T.mul (T.P u T.Z) t) (T.P v T.Z) := by
  intro q
  cases t with
  | Z => exact ⟨rfl, fun _ _ _ x hx => by rw [T.mul] at hx; cases hx⟩
  | P ts add =>
      have hle : T.P u T.Z ≤ T.mul (T.P u T.Z) (T.P ts add) := T.P_le_P_same u T.Z _ (T.Z_le _)
      have hsub : ∀ t x : T lam, x ∈ T.Gi q (T.mul (T.P u T.Z) t) → x ∈ T.Gi q (T.P u T.Z) := by
        intro t
        induction t using T.rec (motive_2 := fun _ _ => True) with
        | Z => intro x hx; cases hx
        | P us add _ ih =>
            intro x hx
            rw [T.mul] at hx
            rcases (T.mem_Gi_P q u (T.mul (T.P u T.Z) add) x).mp hx with hv | ht
            · exact (T.mem_Gi_P q u T.Z x).mpr (Or.inl hv)
            · exact ih x ht
        | nil | snoc => trivial
      refine ⟨T.P_lt_P_of_compareVec_lt _ _ _ _ hvec, fun c hmc hcv x hx =>
        ((hbase q).2 c (T.le_trans _ _ _ hle hmc) hcv x (hsub _ x hx)).imp_left
          fun h => T.lt_of_lt_of_le _ _ _ h hle⟩

theorem T.mul_PZ_NF_closed {lam : Nat} (ls : Vec (T lam) lam) (hbase : T.isNF (T.P ls T.Z)) :
    ∀ t : T lam, T.isNF (T.mul (T.P ls T.Z) t) := by
  intro t
  obtain ⟨hcoords, _, _⟩ := T.isNF_P_inv ls T.Z hbase
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact T.isNF.z
  | P us add _ ih =>
      rw [T.mul]
      refine T.isNF.p ls _ (fun i => (hcoords i).1) ih (fun i => (hcoords i).2) ?_
      cases add with
      | Z => exact T.Z_le _
      | P => exact T.le_refl _
  | nil | snoc => trivial

/-! Fundamental sequences preserve normal forms. -/

theorem T.fund_PZ_one_pos_master {lam : Nat} (ls : Vec (T lam) lam) (m : Fin lam) (z : T lam)
    (hmin : T.domVecMinIdx ls = some (m, .one)) (hm : 0 < m.val)
    (hs : T.isNF (T.P ls T.Z)) (hz : T.isNFComp (m.val - 1) z) :
    T.isNF (T.fund (T.P ls T.Z) z) ∧ T.WDom z (T.fund (T.P ls T.Z) z) (T.P ls T.Z) ∧
      ∀ u, m.val ≤ u → T.IDom u T.Z (T.fund (T.P ls T.Z) z) (T.P ls T.Z) := by
  have hspec := T.domVecMinIdx_some_spec ls m .one hmin
  have hc := T.fund_one_NFComp m.val (ls.idx m) T.Z ((T.isNF_P_inv ls T.Z hs).1 m) hspec.2.1
  obtain ⟨_ | r, mh⟩ := m
  · exact absurd hm (Nat.lt_irrefl 0)
  have hrm : r ≠ r + 1 := Nat.ne_of_lt (Nat.lt_succ_self r)
  have hlow (z' : T lam) (u : Nat) (hb : ∀ q : Fin lam, u ≤ q.val → q.val < r + 1 →
      ((ls.rplc ⟨r + 1, mh⟩ (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z)).rplc ⟨r, Nat.lt_of_succ_lt mh⟩ z).idx q
        = T.Z ∨
      ((ls.rplc ⟨r + 1, mh⟩ (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z)).rplc ⟨r, Nat.lt_of_succ_lt mh⟩ z).idx q
        = z') :=
    T.IDom_low u z' _ ls _ ⟨r + 1, mh⟩
      (by rw [Vec.rplc_idx_of_ne _ _ _ _ hrm.symm, Vec.rplc_idx_same])
      (T.fund_one_IDom u z' _ hspec.2.1).1
      (fun q hq => by
        rw [Vec.rplc_idx_of_ne _ _ _ _ (by simp at hq ⊢; omega),
          Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq)])
      hb (fun _ => T.fund_one_IDom u z' _ hspec.2.1)
  rw [T.fund, ite_eq_left rfl, hmin]
  refine ⟨T.rplc_NF_closed _ _ z (T.rplc_NF_closed ls _ _ hs hc) hz,
    fun u => hlow z u fun q _ hq => ?_, fun u hu => hlow T.Z u fun _ hq hq' => ?_⟩
  · by_cases hqr : q.val = r
    · exact Or.inr (by rw [Fin.eq_of_val_eq (j := ⟨r, Nat.lt_of_succ_lt mh⟩) hqr, Vec.rplc_idx_same])
    · refine Or.inl ?_
      rw [Vec.rplc_idx_of_ne _ _ _ _ hqr, Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hq)]
      exact T.dom_zero_eq_Z _ (hspec.2.2 q hq)
  · exact absurd (Nat.lt_of_le_of_lt hq hq') (Nat.not_lt.mpr hu)

theorem T.fund_Omega_master {lam : Nat} (s : T lam) (hs : T.isNF s) :
    ∀ (i : Fin lam) (z : T lam), T.dom s = .Omega i → T.isNFComp (i.val - 1) z →
      T.isNF (T.fund s z) ∧ T.WDom z (T.fund s z) s ∧
      ∀ u, i.val ≤ u → T.IDom u T.Z (T.fund s z) s := by
  induction hs with
  | z => intro i z hd _; cases hd
  | p ls add hcoords haddNF hsupport hhead ihls ihadd =>
      intro i z hd hz
      by_cases hadd : add = T.Z
      · subst add
        have hparent := T.isNF.p ls T.Z hcoords haddNF hsupport hhead
        obtain ⟨m, d, hmin, hcase⟩ := T.dom_PZ_Omega_split ls i hd
        rcases hcase with ⟨rfl, hm, rfl⟩ | ⟨j, rfl, hjm, rfl⟩
        · exact T.fund_PZ_one_pos_master ls i z hmin hm hparent hz
        · obtain ⟨hnf, hwd, hhigh⟩ :=
            ihls m i z (T.domVecMinIdx_some_spec ls m (.Omega i) hmin).2.1 hz
          have hcomp := T.NFComp_of_IDom_zero m.val _ _ hnf
            ((T.isNF_P_inv ls T.Z hparent).1 m) (hhigh m.val hjm)
          simp only [T.fund, hmin, hjm, ite_true]
          exact ⟨T.rplc_NF_closed ls m _ hparent hcomp,
            fun u => T.IDom_rplc_min u z ls m (.Omega i) _ hmin (hwd u).1 (fun _ => hwd u),
            fun u hju => T.IDom_rplc_min u T.Z ls m (.Omega i) _ hmin (hwd u).1
              (fun _ => hhigh u hju)⟩
      · obtain ⟨hnf, hwd, hhigh⟩ := ihadd i z (by simpa [T.dom, hadd] using hd) hz
        have hf := T.isNF.p ls _ hcoords hnf hsupport
          (T.le_trans _ _ _ (T.head_fund_le add z) hhead)
        rw [T.fund_P_tail_eq ls add z hadd]
        exact ⟨hf, (fun u => T.IDom_tail u z _ add ls (T.NF_tail_lt _ _ hf) (hwd u)),
          fun u hu => T.IDom_tail u T.Z _ add ls (T.NF_tail_lt _ _ hf) (hhigh u hu)⟩

theorem T.fund_iter_NFComp {lam : Nat} (u : Nat) (s t : T lam) (i : Fin lam)
    (hui : u < i.val) (hs : T.isNFComp u s) (hd : T.dom s = .Omega i) :
    T.isNFComp u (T.fund s (T.iter (T.fund s) t)) ∧
      T.WDom T.Z (T.fund s (T.iter (T.fund s) t)) s := by
  have step (r : T lam) (hr : T.isNFComp u (T.iter (T.fund s) r))
      (hw : T.WDom T.Z (T.iter (T.fund s) r) s) :
      T.isNFComp u (T.fund s (T.iter (T.fund s) r)) ∧
        T.WDom T.Z (T.fund s (T.iter (T.fund s) r)) s := by
    obtain ⟨hnf, hwd, _⟩ := T.fund_Omega_master s hs.1 i _ hd
      (T.isNFComp_mono u (i.val - 1) (by omega) _ hr)
    have hlt := T.iter_fund_lt_next s r i hd
    exact ⟨T.NFComp_of_IDom u _ _ s hnf hs hr (hwd u) hlt,
      fun v => T.IDom_eliminate v _ _ s (hwd v) (hw v) hlt⟩
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      refine step T.Z (T.isNFComp_Z u) fun v => ⟨?_, fun _ _ _ _ hx => by cases hx⟩
      cases s with
      | Z => cases hd
      | P ls add => rfl
  | P ls add _ ih => exact step (T.P ls add) ih.1 ih.2
  | nil | snoc => trivial

theorem T.fund_omega_master {lam : Nat} (s : T lam) (hs : T.isNF s) :
    T.dom s = .omega → ∀ t : T lam, T.isNF (T.fund s t) ∧ T.WDom T.Z (T.fund s t) s := by
  induction hs with
  | z => intro hd; cases hd
  | p ls add hcoords haddNF hsupport hhead ihls ihadd =>
      intro hd t
      by_cases hadd : add = T.Z
      · subst add
        have hp := T.isNF.p ls T.Z hcoords haddNF hsupport hhead
        obtain ⟨m, d, hmin, hcase⟩ := T.dom_PZ_omega_split ls hd
        have hspec := T.domVecMinIdx_some_spec ls m d hmin
        have hc := (T.isNF_P_inv ls T.Z hp).1 m
        rcases hcase with ⟨rfl, hm0⟩ | rfl | ⟨j, rfl, hjm⟩
        · have hone := T.fund_one_IDom m.val T.Z _ hspec.2.1
          have hbNF := T.rplc_NF_closed ls m _ hp (T.fund_one_NFComp _ _ T.Z hc hspec.2.1)
          obtain ⟨mv, mh⟩ := m
          change mv = 0 at hm0
          subst mv
          rw [T.fund, ite_eq_left rfl, hmin]
          exact ⟨T.mul_PZ_NF_closed _ hbNF t, T.WDom_mul_PZ _ _ t (Vec.compare_rplc_lt _ _ _ hone.1)
            fun u => T.IDom_rplc_min u T.Z ls _ .one _ hmin hone.1
              fun _ => T.fund_one_IDom u T.Z _ hspec.2.1⟩
        · obtain ⟨hnf, hwd⟩ := ihls m hspec.2.1 t
          have hcomp := T.NFComp_of_IDom_zero m.val _ _ hnf hc (hwd m.val)
          rw [T.fund, ite_eq_left rfl, hmin]
          exact ⟨T.rplc_NF_closed ls m _ hp hcomp,
            fun u => T.IDom_rplc_min u T.Z ls m .omega _ hmin (hwd u).1 (fun _ => hwd u)⟩
        · obtain ⟨hcomp, hwd⟩ :=
            T.fund_iter_NFComp m.val (ls.idx m) t j (Nat.lt_of_not_ge hjm) hc hspec.2.1
          simp only [T.fund, hmin, hjm, ite_false, ite_true]
          exact ⟨T.rplc_NF_closed ls m _ hp hcomp,
            fun u => T.IDom_rplc_min u T.Z ls m (.Omega j) _ hmin (hwd u).1 (fun _ => hwd u)⟩
      · obtain ⟨hnf, hwd⟩ := ihadd (by simpa [T.dom, hadd] using hd) t
        have hf := T.isNF.p ls _ hcoords hnf hsupport
          (T.le_trans _ _ _ (T.head_fund_le add t) hhead)
        rw [T.fund_P_tail_eq ls add t hadd]
        exact ⟨hf, fun u => T.IDom_tail u T.Z _ add ls (T.NF_tail_lt _ _ hf) (hwd u)⟩

theorem T.fund_NF_closed {lam : Nat} (s t : T lam)
    (hs : T.isNF s) (ht : T.isNFComp 0 t) : T.isNF (T.fund s t) := by
  cases hd : T.dom s with
  | zero => rw [T.dom_zero_eq_Z s hd, T.fund]; exact .z
  | one => rw [(T.fund_one_props s hd).1 t]; exact (T.fund_one_props s hd).2.2.1 hs
  | omega => exact (T.fund_omega_master s hs hd t).1
  | Omega i => exact (T.fund_Omega_master s hs i t hd
      (T.isNFComp_mono 0 (i.val - 1) (Nat.zero_le _) t ht)).1

theorem T.isNFComp_above_dim {lam : Nat} (u : Nat) (hlu : lam ≤ u) (s : T lam)
    (hs : T.isNF s) : T.isNFComp u s := by
  have hv {k} (v : Vec (T lam) k) (hk : k ≤ u) : Vec.Gi u v = [] := by
    induction v with
    | nil => rfl
    | snoc k v a ih =>
        simp only [Vec.Gi, show ¬ u ≤ k by omega, ite_false, List.append_nil]
        exact ih (by omega)
  refine ⟨hs, fun x hx => ?_⟩
  suffices h : T.Gi u s = [] by rw [h] at hx; cases hx
  clear hx hs
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v b _ ih => rw [T.Gi, hv v hlu, ih]; rfl
  | nil | snoc => trivial

/-! Source-side bound of OT terms. -/

def T.otBound (lam : Nat) : T lam :=
  T.P (Vec.ofFn lam (fun x => if x.val = 1 then T.P (Vec.ofFn lam (fun _ => T.Z)) T.Z else T.Z))
    T.Z

theorem T.isOT_sound_bound (lam : Nat) (s : T lam) (hs : T.isOT lam s) :
    T.isNF s ∧ (1 < lam → s < T.otBound lam) := by
  induction hs with
  | base_0 n => exact ⟨T.LF_isNF 0 n, fun h => absurd h (Nat.not_lt_zero _)⟩
  | base_succ k n =>
      refine ⟨T.base_succ_isNF k n, fun hk => ?_⟩
      apply T.P_lt_P_of_compareVec_lt
      apply Vec.compare_lt_of_pivot _ _ ⟨1, hk⟩
      · intro j (hj : 1 < j.val)
        simp only [Vec.ofFn_idx, show j.val ≠ 0 by omega, show j.val ≠ 1 by omega, ite_false]
      · simp only [Vec.ofFn_idx, Nat.one_ne_zero, ite_false, ite_true]
        rfl
  | step lam a _ n ih =>
      refine ⟨T.fund_NF_closed a (T.ofNat n) ih.1 (T.ofNat_isNFComp 0 n), fun hlam => ?_⟩
      by_cases haz : a = T.Z
      · subst a; rw [T.fund]; rfl
      · exact strict_partial_order.trans _ _ _ (T.fund_lt_self a (T.ofNat n) haz) (ih.2 hlam)

theorem T.isOT_isNF {lam : Nat} (s : T lam) (hs : T.isOT lam s) : T.isNF s :=
  (T.isOT_sound_bound lam s hs).1

end new

import Subsp.old.stop_source_omega_nested

/-! Indexed support interpolation, allowing support terms already below the lower endpoint. -/

namespace new

def T.IDom {lam : Nat} (u : Nat) (z b a : T lam) : Prop :=
  b < a ∧ ∀ c, b ≤ c → c ≤ a → ∀ x ∈ T.Gi u b,
    x < b ∨ ∃ y, y ∈ T.Gi u c ++ T.GZ u z ∧ x ≤ y

def T.WDom {lam : Nat} (z b a : T lam) : Prop := ∀ u, T.IDom u z b a

theorem T.SDom_IDom {lam : Nat} (u : Nat) (z b a : T lam)
    (h : T.SDom z b a) : T.IDom u z b a :=
  ⟨h.1, fun c hl hh x hx => Or.inr (h.2 u c hl hh x hx)⟩

theorem T.IDom_Gi_lt_upper {lam : Nat} (u : Nat) (z b a : T lam)
    (hs : T.IDom u z b a) (ha : ∀ x ∈ T.Gi u a, x < a)
    (hz : ∀ x ∈ T.GZ u z, x < b) : ∀ x ∈ T.Gi u b, x < a := by
  intro x hx
  rcases hs.2 a (Or.inl hs.1) (T.le_refl a) x hx with hx | ⟨y, hy, hxy⟩
  · exact T_trans _ _ _ hx hs.1
  · apply T.lt_of_le_of_lt _ _ _ hxy
    exact (List.mem_append.mp hy).elim (ha y) (fun hy => T_trans _ _ _ (hz y hy) hs.1)

theorem T.IDom_Gi_closed {lam : Nat} (u : Nat) (z b a : T lam)
    (hs : T.IDom u z b a) (ha : ∀ x ∈ T.Gi u a, x < a)
    (hz : ∀ x ∈ T.GZ u z, x < b) : ∀ x ∈ T.Gi u b, x < b := by
  intro x hx
  by_cases hxb : T.lt x b
  · exact hxb
  · have hbx : b ≤ x := by
      rcases T_total x b with h | h | rfl
      · exact False.elim (hxb h)
      · exact Or.inl h
      · exact T.le_refl _
    obtain ⟨c, hc, hbc, hcut⟩ := T.find_violating_source u b b x hx hbx
    rcases hs.2 c hbc (Or.inl (T.IDom_Gi_lt_upper u z b a hs ha hz c hc)) c hc with
      hcc | ⟨y, hy, hcy⟩
    · exact False.elim (strict_partial_order.irrefl b (T.lt_of_le_of_lt _ _ _ hbc hcc))
    · have hyb : y < b := (List.mem_append.mp hy).elim (hcut y) (hz y)
      exact False.elim (strict_partial_order.irrefl b
        (T.lt_of_le_of_lt _ _ _ hbc (T.lt_of_le_of_lt _ _ _ hcy hyb)))

theorem T.NFComp_of_IDom {lam : Nat} (u : Nat) (z b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a) (hz : T.isNFComp u z)
    (hs : T.IDom u z b a) (hzb : z < b) : T.isNFComp u b :=
  ⟨hb, T.IDom_Gi_closed u z b a hs ha.2 (T.GZ_lt_of_NFComp u z b hz hzb)⟩

theorem T.NFComp_of_IDom_zero {lam : Nat} (u : Nat) (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a) (hs : T.IDom u T.Z b a) : T.isNFComp u b := by
  cases b with
  | Z => exact T.isNFComp_Z u
  | P v c => exact T.NFComp_of_IDom u T.Z _ a hb ha (T.isNFComp_Z u) hs rfl

theorem T.IDom_zero {lam : Nat} (u : Nat) (a : T lam) (h : T.Z < a) :
    T.IDom u T.Z T.Z a := ⟨h, fun _ _ _ _ hx => by cases hx⟩

theorem T.IDom_eliminate {lam : Nat} (u : Nat) (z b a : T lam)
    (hb : T.IDom u z b a) (hz : T.IDom u T.Z z a) (hzb : z < b) :
    T.IDom u T.Z b a := by
  refine ⟨hb.1, ?_⟩
  intro c hbc hca x hx
  rcases hb.2 c hbc hca x hx with hxc | ⟨y, hy, hxy⟩
  · exact Or.inl hxc
  · rcases List.mem_append.mp hy with hy | hy
    · exact Or.inr ⟨y, List.mem_append_left _ hy, hxy⟩
    · simp only [T.GZ, List.mem_append, List.mem_singleton] at hy
      rcases hy with (rfl | hy) | rfl
      · exact Or.inl (T.lt_of_le_of_lt _ _ _ hxy hzb)
      · rcases hz.2 c (Or.inl (T.lt_of_lt_of_le _ _ _ hzb hbc)) hca y hy with
          hyc | ⟨w, hw, hyw⟩
        · exact Or.inl (T.lt_of_le_of_lt _ _ _ hxy (T_trans _ _ _ hyc hzb))
        · exact Or.inr ⟨w, hw, T.le_trans _ _ _ hxy hyw⟩
      · exact Or.inr ⟨T.Z, List.mem_append_right _ (by simp [T.GZ]), hxy⟩

theorem T.IDom_tail {lam : Nat} (u : Nat) (z b a : T lam)
    (ls : Vec (T lam) lam) (hbtail : b < T.P ls b) (hs : T.IDom u z b a) :
    T.IDom u z (T.P ls b) (T.P ls a) := by
  refine ⟨T.P_tail_lt ls b a hs.1, ?_⟩
  intro c hl hh x hx
  obtain ⟨d, rfl, hbd, hda⟩ := T.sandwich_same_vector ls b a c hl hh
  rcases (T.mem_Gi_P u ls b x).mp hx with hv | ht
  · exact Or.inr ⟨x, List.mem_append_left _ ((T.mem_Gi_P u ls d x).mpr (Or.inl hv)), T.le_refl _⟩
  · rcases hs.2 d hbd hda x ht with hxd | ⟨y, hy, hxy⟩
    · exact Or.inl (T_trans _ _ _ hxd hbtail)
    · refine Or.inr ⟨y, ?_, hxy⟩
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ ((T.mem_Gi_P u ls d y).mpr (Or.inr hy))
      · exact List.mem_append_right _ hy

theorem T.tail_lt_of_NF {lam : Nat} (b : T lam) (hb : T.isNF b) :
    ∀ ls : Vec (T lam) lam, T.head b ≤ T.P ls T.Z → b < T.P ls b := by
  induction hb with
  | z => intro ls _; rfl
  | p v d _ _ _ hh _ ih =>
      intro ls hls
      rcases T.vector_rel_of_P_le_P v ls T.Z T.Z hls with hv | rfl
      · exact T.P_lt_P_of_compareVec_lt _ _ _ _ hv
      · exact T.P_tail_lt _ _ _ (ih v hh)

theorem T.NF_tail_lt {lam : Nat} (ls : Vec (T lam) lam) (b : T lam)
    (h : T.isNF (T.P ls b)) : b < T.P ls b :=
  T.tail_lt_of_NF b (T.isNF_P_inv ls b h).2.1 ls (T.isNF_P_inv ls b h).2.2

end new

import Subsp.old.stop_source_successor

/-! Constructive support transfer across intervals in the legacy source order. -/

namespace new

theorem T.le_antisymm {lam : Nat} (a b : T lam) (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases hab with h | h
  · rcases hba with h' | h'
    · exact False.elim (strict_partial_order.irrefl a (T_trans _ _ _ h h'))
    · exact (T_eq_sound _ _ h').symm
  · exact T_eq_sound _ _ h

theorem T.lt_of_le_of_lt {lam : Nat} (a b c : T lam) (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases hab with h | h
  · exact T_trans _ _ _ h hbc
  · rwa [T_eq_sound _ _ h]

theorem T.lt_of_lt_of_le {lam : Nat} (a b c : T lam) (hab : a < b) (hbc : b ≤ c) : a < c := by
  rcases hbc with h | h
  · exact T_trans _ _ _ hab h
  · rwa [← T_eq_sound _ _ h]

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

def T.decForallMem {lam : Nat} (l : List (T lam)) (P : T lam → Prop)
    (dP : ∀ x, Decidable (P x)) : Decidable (∀ x ∈ l, P x) :=
  match l with
  | [] => isTrue (fun _ hx => by cases hx)
  | a :: as =>
      match dP a with
      | isFalse h => isFalse (fun hall => h (hall a List.mem_cons_self))
      | isTrue h =>
          match T.decForallMem as P dP with
          | isFalse htail => isFalse (fun hall => htail (fun x hx => hall x (List.mem_cons_of_mem a hx)))
          | isTrue htail => isTrue (fun x hx => (List.mem_cons.mp hx).elim (fun he => he ▸ h) (htail x))

theorem T.exists_Gi_not_lt {lam : Nat} (u : Nat) (s b : T lam)
    (h : ¬ (∀ x ∈ T.Gi u s, x < b)) : ∃ x, x ∈ T.Gi u s ∧ ¬ x < b := by
  generalize T.Gi u s = l at h ⊢
  induction l with
  | nil => exact False.elim (h (fun x hx => by cases hx))
  | cons a as ih =>
      by_cases ha : T.lt a b
      · obtain ⟨x, hx, hn⟩ := ih (fun hall => h (fun x hx =>
          (List.mem_cons.mp hx).elim (fun he => he ▸ ha) (hall x)))
        exact ⟨x, List.mem_cons_of_mem a hx, hn⟩
      · exact ⟨a, List.mem_cons_self, ha⟩

theorem T.find_violating_source {lam : Nat} (u : Nat) (b c₀ w : T lam)
    (hw : w ∈ T.Gi u c₀) (hbw : b ≤ w) :
    ∃ c, c ∈ T.Gi u c₀ ∧ b ≤ c ∧ ∀ x ∈ T.Gi u c, x < b := by
  induction w using (measure T.size).wf.induction with
  | h w ih =>
      cases T.decForallMem (T.Gi u w) (fun x => x < b)
          (fun x => inferInstanceAs (Decidable (T.lt x b))) with
      | isTrue h => exact ⟨w, hw, hbw, h⟩
      | isFalse h =>
          obtain ⟨x, hx, hn⟩ := T.exists_Gi_not_lt u w b h
          apply ih x (T.Gi_size_lt u w x hx) (T.Gi_trans u c₀ w x hw hx)
          rcases T_total x b with h | h | rfl
          · exact False.elim (hn h)
          · exact Or.inl h
          · exact T.le_refl _

def T.GZ {lam : Nat} (u : Nat) (z : T lam) : List (T lam) :=
  [z] ++ T.Gi u z ++ [T.Z]

def T.listLe {lam : Nat} (xs ys : List (T lam)) : Prop :=
  ∀ x ∈ xs, ∃ y, y ∈ ys ∧ x ≤ y

def T.SDom {lam : Nat} (z b a : T lam) : Prop :=
  b < a ∧ ∀ (u : Nat) (c : T lam), b ≤ c → c ≤ a →
    T.listLe (T.Gi u b) (T.Gi u c ++ T.GZ u z)

theorem T.SDom_Gi_lt_upper {lam : Nat} (u : Nat) (z b a : T lam)
    (hs : T.SDom z b a) (ha : ∀ x ∈ T.Gi u a, x < a)
    (hz : ∀ x ∈ T.GZ u z, x < b) : ∀ x ∈ T.Gi u b, x < a := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hs.2 u a (Or.inl hs.1) (T.le_refl a) x hx
  apply T.lt_of_le_of_lt _ _ _ hxy
  rcases List.mem_append.mp hy with hy | hy
  · exact ha y hy
  · exact T_trans _ _ _ (hz y hy) hs.1

theorem T.SDom_Gi_closed {lam : Nat} (u : Nat) (z b a : T lam)
    (hs : T.SDom z b a) (ha : ∀ x ∈ T.Gi u a, x < a)
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
    obtain ⟨y, hy, hcy⟩ := hs.2 u c hbc
      (Or.inl (T.SDom_Gi_lt_upper u z b a hs ha hz c hc)) c hc
    have hyb : y < b := (List.mem_append.mp hy).elim (hcut y) (hz y)
    exact False.elim (strict_partial_order.irrefl b
      (T.lt_of_le_of_lt _ _ _ hbc (T.lt_of_le_of_lt _ _ _ hcy hyb)))

theorem T.GZ_lt_of_NFComp {lam : Nat} (u : Nat) (z b : T lam)
    (hz : T.isNFComp u z) (hzb : z < b) : ∀ x ∈ T.GZ u z, x < b := by
  intro x hx
  simp only [T.GZ, List.mem_append, List.mem_singleton] at hx
  rcases hx with (rfl | hx) | rfl
  · exact hzb
  · exact T_trans _ _ _ (hz.2 x hx) hzb
  · exact T.lt_of_le_of_lt _ _ _ (T.Z_le z) hzb

theorem T.NFComp_of_SDom {lam : Nat} (u : Nat) (z b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a) (hz : T.isNFComp u z)
    (hs : T.SDom z b a) (hzb : z < b) : T.isNFComp u b :=
  ⟨hb, T.SDom_Gi_closed u z b a hs ha.2 (T.GZ_lt_of_NFComp u z b hz hzb)⟩

theorem T.NFComp_of_SDom_zero {lam : Nat} (u : Nat) (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a) (hs : T.SDom T.Z b a) : T.isNFComp u b := by
  cases b with
  | Z => exact T.isNFComp_Z u
  | P v c => exact T.NFComp_of_SDom u T.Z _ a hb ha (T.isNFComp_Z u) hs rfl

theorem T.fund_one_SDom {lam : Nat} (s : T lam) (hd : T.dom s = .one) :
    T.SDom T.Z (T.fund s T.Z) s := by
  have hne : s ≠ T.Z := by intro he; subst s; cases hd
  refine ⟨T.fund_lt_self s T.Z hne, ?_⟩
  intro u c hl hu x hx
  refine ⟨x, List.mem_append_left _ ?_, T.le_refl _⟩
  rcases hu with hu | hu
  · have hc := T.le_antisymm _ _ hl (T.fund_one_upper s hd c hu)
    rwa [← hc]
  · rw [T_eq_sound _ _ hu]
    exact T.Gi_fund_one_subset u s hd x hx

end new

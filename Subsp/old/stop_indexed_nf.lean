import Subsp.old.stop_source_fund

/-! Indexed support conditions for legacy source normal forms.
The support at level `u` visits coordinates whose indices are at least `u`.
-/

namespace new

mutual
  def T.Gi {lam : Nat} (u : Nat) : T lam → List (T lam)
    | .Z => []
    | .P v b => Vec.Gi u v ++ T.Gi u b

  def Vec.Gi {lam k : Nat} (u : Nat) : Vec (T lam) k → List (T lam)
    | .nil => []
    | .snoc k v a => Vec.Gi u v ++ if u ≤ k then a :: T.Gi u a else []
end

theorem Vec.mem_Gi_iff {lam k : Nat} (u : Nat) (v : Vec (T lam) k) (x : T lam) :
    x ∈ Vec.Gi u v ↔
      ∃ i : Fin k, u ≤ i.val ∧ (x = v.idx i ∨ x ∈ T.Gi u (v.idx i)) := by
  induction v with
  | nil =>
      constructor
      · intro h; cases h
      · rintro ⟨i, _⟩; exact i.elim0
  | snoc k v a ih =>
      simp only [Vec.Gi, List.mem_append]
      constructor
      · rintro (hx | hx)
        · obtain ⟨i, hui, hi⟩ := ih.mp hx
          exact ⟨i.castSucc, hui, by simpa only [Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using hi⟩
        · by_cases huk : u ≤ k
          · simp only [huk, ite_true, List.mem_cons] at hx
            exact ⟨Fin.last k, huk, by simpa only [Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using hx⟩
          · simp [huk] at hx
      · rintro ⟨i, hui, hi⟩
        by_cases hik : i.val < k
        · exact Or.inl (ih.mpr ⟨⟨i.val, hik⟩, hui, by simpa only [Vec.idx, hik, dite_true] using hi⟩)
        · have hik' : i.val = k := by omega
          have huk : u ≤ k := hik' ▸ hui
          apply Or.inr
          simpa only [huk, ite_true, List.mem_cons, Vec.idx, hik, dite_false] using hi

theorem T.mem_Gi_P {lam : Nat} (u : Nat) (v : Vec (T lam) lam) (b x : T lam) :
    x ∈ T.Gi u (T.P v b) ↔
      (∃ i : Fin lam, u ≤ i.val ∧ (x = v.idx i ∨ x ∈ T.Gi u (v.idx i))) ∨
        x ∈ T.Gi u b := by
  simp only [T.Gi, List.mem_append, Vec.mem_Gi_iff]

theorem T.Gi_antitone {lam : Nat} (u v : Nat) (huv : u ≤ v) (s : T lam) :
    ∀ x ∈ T.Gi v s, x ∈ T.Gi u s := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      intro x hx
      cases s with
      | Z => cases hx
      | P ls b =>
          rw [T.mem_Gi_P] at hx ⊢
          rcases hx with ⟨i, hvi, rfl | hx⟩ | hx
          · exact Or.inl ⟨i, Nat.le_trans huv hvi, Or.inl rfl⟩
          · exact Or.inl ⟨i, Nat.le_trans huv hvi,
              Or.inr (ih _ (T.idx_size_lt_P ls b i) x hx)⟩
          · exact Or.inr (ih b (T.add_size_lt_P ls b) x hx)

inductive T.isNF {lam : Nat} : T lam → Prop where
  | z : isNF T.Z
  | p (ls : Vec (T lam) lam) (b : T lam)
      (hcoords : ∀ i : Fin lam, isNF (ls.idx i))
      (hadd : isNF b)
      (hsupport : ∀ i : Fin lam, ∀ x ∈ T.Gi i.val (ls.idx i), x < ls.idx i)
      (hhead : T.head b ≤ T.P ls T.Z) : isNF (T.P ls b)

def T.isNFComp {lam : Nat} (u : Nat) (s : T lam) : Prop :=
  T.isNF s ∧ ∀ x ∈ T.Gi u s, x < s

theorem T.isNF_isWNF {lam : Nat} (s : T lam) (hs : T.isNF s) : T.isWNF s := by
  induction hs with
  | z => exact .z
  | p ls b _ _ _ hh ihls ihb => exact .p ls b ihls ihb hh

theorem T.isNFComp_Z {lam : Nat} (u : Nat) : T.isNFComp u (T.Z : T lam) :=
  ⟨.z, fun _ hx => by cases hx⟩

theorem T.isNFComp_mono {lam : Nat} (u v : Nat) (huv : u ≤ v) (s : T lam)
    (hs : T.isNFComp u s) : T.isNFComp v s :=
  ⟨hs.1, fun x hx => hs.2 x (T.Gi_antitone u v huv s x hx)⟩

theorem T.isNF_P_inv {lam : Nat} (ls : Vec (T lam) lam) (b : T lam)
    (hs : T.isNF (T.P ls b)) :
    (∀ i : Fin lam, T.isNFComp i.val (ls.idx i)) ∧ T.isNF b ∧
      T.head b ≤ T.P ls T.Z := by
  cases hs with
  | p _ _ hc hb hg hh => exact ⟨fun i => ⟨hc i, hg i⟩, hb, hh⟩

theorem T.Gi_size_lt {lam : Nat} (u : Nat) (s : T lam) :
    ∀ x ∈ T.Gi u s, T.size x < T.size s := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      intro x hx
      cases s with
      | Z => cases hx
      | P v b =>
          rcases (T.mem_Gi_P u v b x).mp hx with ⟨i, _, rfl | hx⟩ | hx
          · exact T.idx_size_lt_P v b i
          · exact Nat.lt_trans (ih _ (T.idx_size_lt_P v b i) x hx) (T.idx_size_lt_P v b i)
          · exact Nat.lt_trans (ih b (T.add_size_lt_P v b) x hx) (T.add_size_lt_P v b)

theorem T.isNF_Gi {lam : Nat} (s : T lam) (hs : T.isNF s) (u : Nat) :
    ∀ x ∈ T.Gi u s, T.isNF x := by
  induction hs with
  | z => intro x hx; cases hx
  | p v b hc _ _ _ ihv ihb =>
      intro x hx
      rcases (T.mem_Gi_P u v b x).mp hx with ⟨i, _, rfl | hx⟩ | hx
      · exact hc i
      · exact ihv i x hx
      · exact ihb x hx

theorem T.P_tail_lt {lam : Nat} (v : Vec (T lam) lam) (a b : T lam) (h : a < b) :
    T.P v a < T.P v b := by
  simpa only [LT.lt, T.lt, compareT, Vec_refl] using h

theorem T.LF_step_lt (lam n : Nat) : T.LF lam n < T.LF lam (n + 1) := by
  induction n with
  | zero => cases lam <;> rfl
  | succ n ih =>
      cases lam with
      | zero => exact T.P_tail_lt _ _ _ ih
      | succ k =>
          apply T.P_lt_P_of_compareVec_lt
          apply Vec.compare_lt_of_pivot _ _ (Fin.last k)
          · intro j hj
            have := j.isLt
            simp only [Fin.val_last] at hj
            omega
          · simpa only [Vec.ofFn_idx, Fin.val_last, ite_true] using ih

theorem T.LF_support (lam n u : Nat) :
    ∀ x ∈ T.Gi u (T.LF lam n), x < T.LF lam n := by
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
      intro x hx
      cases lam with
      | zero =>
          exact strict_partial_order.trans _ _ _ (ih x hx) (T.LF_step_lt 0 n)
      | succ k =>
          rw [T.LF, T.mem_Gi_P] at hx
          rcases hx with ⟨i, _, hi⟩ | hx
          · simp only [Vec.ofFn_idx] at hi
            split at hi
            · rcases hi with rfl | hi
              · exact T.LF_step_lt (k + 1) n
              · exact strict_partial_order.trans _ _ _ (ih x hi) (T.LF_step_lt (k + 1) n)
            · rcases hi with rfl | hi
              · rfl
              · cases hi
          · cases hx

theorem T.LF_isNF (lam n : Nat) : T.isNF (T.LF lam n) := by
  induction n with
  | zero => exact .z
  | succ n ih =>
      cases lam with
      | zero =>
          refine .p Vec.nil _ (fun i => i.elim0) ih (fun i => i.elim0) ?_
          cases n with
          | zero => exact T.Z_le _
          | succ n => exact Or.inr (T_refl _)
      | succ k =>
          refine .p _ T.Z ?_ .z ?_ (T.Z_le _)
          · intro i
            rw [Vec.ofFn_idx]
            split
            · exact ih
            · exact .z
          · intro i
            rw [Vec.ofFn_idx]
            split
            · exact T.LF_support (k + 1) n i.val
            · intro x hx; cases hx

theorem T.base_succ_isNF (k n : Nat) :
    T.isNF (T.P (Vec.ofFn (k + 1)
      (fun i => if i.val = 0 then T.LF (k + 1) n else T.Z)) T.Z) := by
  refine .p _ T.Z ?_ .z ?_ (T.Z_le _)
  · intro i
    rw [Vec.ofFn_idx]
    split
    · exact T.LF_isNF (k + 1) n
    · exact .z
  · intro i
    rw [Vec.ofFn_idx]
    split
    · exact T.LF_support (k + 1) n i.val
    · intro x hx; cases hx

end new

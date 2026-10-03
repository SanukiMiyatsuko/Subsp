import Subsp.old.stop_basic

/-! Indexed support conditions for legacy source normal forms.
The support at level `u` visits coordinates whose indices are at least `u`.
-/

namespace new

theorem T.Z_le {lam : Nat} (s : T lam) : T.Z ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P ls add => exact Or.inl rfl

theorem T.le_refl {lam : Nat} (s : T lam) : s ≤ s := Or.inr (T_refl s)

theorem T.le_trans {lam : Nat} (a b c : T lam) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with h | h
  · rcases hbc with h' | h'
    · exact Or.inl (T_trans _ _ _ h h')
    · rw [← T_eq_sound _ _ h']; exact Or.inl h
  · rw [T_eq_sound _ _ h]; exact hbc

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

theorem T.lt_Z_false {lam : Nat} (s : T lam) : ¬ s < T.Z := by
  cases s <;> intro h <;> cases h

theorem T.P_le_P_same {lam : Nat} (v : Vec (T lam) lam) (a b : T lam) (h : a ≤ b) :
    T.P v a ≤ T.P v b := by
  simpa only [LE.le, T.le, compareT, Vec_refl] using h

theorem T.P_tail_lt {lam : Nat} (v : Vec (T lam) lam) (a b : T lam) (h : a < b) :
    T.P v a < T.P v b := by
  simpa only [LT.lt, T.lt, compareT, Vec_refl] using h

theorem T.head_mono {lam : Nat} (a b : T lam) (h : a < b) : T.head a ≤ T.head b := by
  cases a with
  | Z => exact T.Z_le _
  | P als aadd =>
      cases b with
      | Z => cases h
      | P bls badd =>
          change (match compareVec als bls with
            | .eq => compareT aadd badd | ord => ord) = .lt at h
          cases hc : compareVec als bls with
          | lt => exact Or.inl (T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
          | eq => rw [Vec_eq_sound _ _ hc]; exact T.le_refl _
          | gt => simp [hc] at h

theorem T.head_mono_le {lam : Nat} (a b : T lam) (h : a ≤ b) : T.head a ≤ T.head b := by
  rcases h with h | h
  · exact T.head_mono a b h
  · rw [T_eq_sound _ _ h]; exact T.le_refl _

mutual
  def T.Gi {lam : Nat} (u : Nat) : T lam → List (T lam)
    | .Z => []
    | .P v b => Vec.Gi u v ++ T.Gi u b

  def Vec.Gi {lam k : Nat} (u : Nat) : Vec (T lam) k → List (T lam)
    | .nil => []
    | .snoc k v a => Vec.Gi u v ++ if u ≤ k then a :: T.Gi u a else []
end

theorem T.mem_Gi_P {lam : Nat} (u : Nat) (v : Vec (T lam) lam) (b x : T lam) :
    x ∈ T.Gi u (T.P v b) ↔
      (∃ i : Fin lam, u ≤ i.val ∧ (x = v.idx i ∨ x ∈ T.Gi u (v.idx i))) ∨ x ∈ T.Gi u b := by
  suffices h : ∀ {k} (v : Vec (T lam) k), x ∈ Vec.Gi u v ↔
      ∃ i : Fin k, u ≤ i.val ∧ (x = v.idx i ∨ x ∈ T.Gi u (v.idx i)) by
    simp only [T.Gi, List.mem_append, h]
  intro k v
  induction v with
  | nil => exact ⟨fun h => (by cases h), fun ⟨i, _⟩ => i.elim0⟩
  | snoc k v a ih =>
      simp only [Vec.Gi, List.mem_append, ih]
      constructor
      · rintro (⟨i, hui, hi⟩ | hx)
        · exact ⟨i.castSucc, hui, by simpa only [Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using hi⟩
        · by_cases huk : u ≤ k
          · simp only [huk, ite_true, List.mem_cons] at hx
            exact ⟨Fin.last k, huk, by simpa only [Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using hx⟩
          · simp [huk] at hx
      · rintro ⟨i, hui, hi⟩
        by_cases hik : i.val < k
        · exact Or.inl ⟨⟨i.val, hik⟩, hui, by simpa only [Vec.idx, hik, dite_true] using hi⟩
        · have huk : u ≤ k := (show i.val = k by omega) ▸ hui
          exact Or.inr (by simpa only [huk, ite_true, List.mem_cons, Vec.idx, hik, dite_false] using hi)

inductive T.isNF {lam : Nat} : T lam → Prop where
  | z : isNF T.Z
  | p (ls : Vec (T lam) lam) (b : T lam)
      (hcoords : ∀ i : Fin lam, isNF (ls.idx i))
      (hadd : isNF b)
      (hsupport : ∀ i : Fin lam, ∀ x ∈ T.Gi i.val (ls.idx i), x < ls.idx i)
      (hhead : T.head b ≤ T.P ls T.Z) : isNF (T.P ls b)

def T.isNFComp {lam : Nat} (u : Nat) (s : T lam) : Prop :=
  T.isNF s ∧ ∀ x ∈ T.Gi u s, x < s

theorem T.isNFComp_Z {lam : Nat} (u : Nat) : T.isNFComp u (T.Z : T lam) :=
  ⟨.z, fun _ hx => by cases hx⟩

theorem T.isNFComp_mono {lam : Nat} (u v : Nat) (huv : u ≤ v) (s : T lam)
    (hs : T.isNFComp u s) : T.isNFComp v s := by
  refine ⟨hs.1, fun x hx => hs.2 x ?_⟩
  clear hs
  induction s using (measure T.size).wf.induction generalizing x with
  | h s ih =>
      cases s with
      | Z => cases hx
      | P ls b =>
          rw [T.mem_Gi_P] at hx ⊢
          rcases hx with ⟨i, hvi, rfl | hx⟩ | hx
          · exact Or.inl ⟨i, Nat.le_trans huv hvi, Or.inl rfl⟩
          · exact Or.inl ⟨i, Nat.le_trans huv hvi, Or.inr (ih _ (T.idx_size_lt_P ls b i) x hx)⟩
          · exact Or.inr (ih b (T.add_size_lt_P ls b) x hx)

theorem T.isNF_P_inv {lam : Nat} (ls : Vec (T lam) lam) (b : T lam) (hs : T.isNF (T.P ls b)) :
    (∀ i : Fin lam, T.isNFComp i.val (ls.idx i)) ∧ T.isNF b ∧ T.head b ≤ T.P ls T.Z := by
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

theorem T.LF_support (lam n u : Nat) :
    ∀ x ∈ T.Gi u (T.LF lam n), x < T.LF lam n := by
  have hstep (n) : T.LF lam n < T.LF lam (n + 1) := by
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
  induction n with
  | zero => intro x hx; cases hx
  | succ n ih =>
      intro x hx
      cases lam with
      | zero => exact strict_partial_order.trans _ _ _ (ih x hx) (hstep n)
      | succ k =>
          rw [T.LF, T.mem_Gi_P] at hx
          rcases hx with ⟨i, _, hi⟩ | hx
          · simp only [Vec.ofFn_idx] at hi
            split at hi
            · rcases hi with rfl | hi
              · exact hstep n
              · exact strict_partial_order.trans _ _ _ (ih x hi) (hstep n)
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
          | succ n => exact T.le_refl _
      | succ k =>
          refine .p _ T.Z (fun i => ?_) .z (fun i => ?_) (T.Z_le _) <;> rw [Vec.ofFn_idx] <;> split
          · exact ih
          · exact .z
          · exact T.LF_support (k + 1) n i.val
          · intro x hx; cases hx

theorem T.base_succ_isNF (k n : Nat) :
    T.isNF (T.P (Vec.ofFn (k + 1) (fun i => if i.val = 0 then T.LF (k + 1) n else T.Z)) T.Z) := by
  refine .p _ T.Z (fun i => ?_) .z (fun i => ?_) (T.Z_le _) <;> rw [Vec.ofFn_idx] <;> split
  · exact T.LF_isNF (k + 1) n
  · exact .z
  · exact T.LF_support (k + 1) n i.val
  · intro x hx; cases hx

/-! Finite terms and successor steps preserve indexed source normal forms. -/

theorem T.dom_PZ_one_iff {lam : Nat} (v : Vec (T lam) lam) :
    T.dom (T.P v T.Z) = .one ↔ T.domVecMinIdx v = none := by
  simp only [T.dom, ite_true]
  cases T.domVecMinIdx v with
  | none => simp
  | some md =>
      obtain ⟨m, d⟩ := md
      cases d with
      | zero | omega => simp
      | one => by_cases hm : m.val = 0 <;> simp [hm]
      | Omega i => by_cases hi : i ≤ m <;> simp [hi]

theorem T.fund_PZ_none {lam : Nat} (v : Vec (T lam) lam) (t : T lam)
    (h : T.domVecMinIdx v = none) : T.fund (T.P v T.Z) t = T.Z := by
  rw [T.fund, ite_eq_left rfl, h]

theorem T.fund_P_tail_eq {lam : Nat} (ls : Vec (T lam) lam) (add t : T lam) (hadd : add ≠ T.Z) :
    T.fund (T.P ls add) t = T.P ls (T.fund add t) := by
  rw [T.fund, ite_eq_right hadd]

theorem T.vector_lt_of_P_lt_PZ {lam : Nat} (v w : Vec (T lam) lam) (a : T lam)
    (h : T.P v a < T.P w T.Z) : compareVec v w = .lt := by
  change (match compareVec v w with | .eq => compareT a T.Z | ord => ord) = .lt at h
  cases hc : compareVec v w with
  | lt => rfl
  | eq => rw [hc] at h; exact False.elim (T.lt_Z_false a h)
  | gt => simp [hc] at h

/-- Successor-shaped terms: the argument is irrelevant, `fund s Z` is the predecessor,
normal forms are preserved and the support does not grow. -/
theorem T.fund_one_props {lam : Nat} (s : T lam) (hd : T.dom s = .one) :
    (∀ t, T.fund s t = T.fund s T.Z) ∧ (∀ b, b < s → b ≤ T.fund s T.Z) ∧
      (T.isNF s → T.isNF (T.fund s T.Z)) ∧ ∀ u, ∀ x ∈ T.Gi u (T.fund s T.Z), x ∈ T.Gi u s := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => cases hd
  | P v a _ ih =>
      by_cases haz : a = T.Z
      · subst a
        have hnone := (T.dom_PZ_one_iff v).mp hd
        have hall : ∀ i : Fin lam, T.dom (v.idx i) = .zero := by
          simpa only [hnone] using T.domVecMinIdx_spec v
        simp only [T.fund_PZ_none v _ hnone]
        refine ⟨fun _ => trivial, fun b hb => ?_, fun _ => .z, fun _ _ hx => by cases hx⟩
        cases b with
        | Z => exact T.le_refl _
        | P w c =>
            obtain ⟨i, _, hi⟩ := Vec.compare_lt_has_pivot w v (T.vector_lt_of_P_lt_PZ w v c hb)
            rw [T.dom_zero_eq_Z _ (hall i)] at hi
            exact False.elim (T.lt_Z_false _ hi)
      · obtain ⟨ih1, ih2, ih3, ih4⟩ := ih (by simpa only [T.dom, haz, ite_false] using hd)
        simp only [T.fund_P_tail_eq v a _ haz]
        refine ⟨fun t => by rw [ih1 t], fun b hb => ?_, fun hs => ?_, fun u x hx =>
          (T.mem_Gi_P u v a x).mpr (((T.mem_Gi_P u v _ x).mp hx).imp id (ih4 u x))⟩
        · cases b with
          | Z => exact T.Z_le _
          | P w c =>
              change (match compareVec w v with | .eq => compareT c a | ord => ord) = .lt at hb
              cases hc : compareVec w v with
              | lt => exact Or.inl (T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
              | eq =>
                  rw [hc] at hb
                  obtain rfl := Vec_eq_sound w v hc
                  exact T.P_le_P_same _ _ _ (ih2 c hb)
              | gt => simp [hc] at hb
        · cases hs with
          | p _ _ hv ha hg hh =>
              exact .p v _ hv (ih3 ha) hg
                (T.le_trans _ _ _ (T.head_mono _ _ (T.fund_lt_self a T.Z haz)) hh)
  | nil | snoc => trivial

theorem T.fund_one_NFComp {lam : Nat} (u : Nat) (s t : T lam)
    (hs : T.isNFComp u s) (hd : T.dom s = .one) : T.isNFComp u (T.fund s t) := by
  obtain ⟨h1, h2, h3, h4⟩ := T.fund_one_props s hd
  rw [h1 t]
  refine ⟨h3 hs.1, fun x hx => ?_⟩
  rcases h2 x (hs.2 x (h4 u x hx)) with h | h
  · exact h
  · have hsize := T.Gi_size_lt u _ x hx
    rw [T_eq_sound _ _ h] at hsize
    exact False.elim (Nat.lt_irrefl _ hsize)

theorem T.ofNat_isNFComp {lam : Nat} (u n : Nat) : T.isNFComp u (T.ofNat (lam := lam) n) := by
  have hG : ∀ n, ∀ x ∈ T.Gi u (T.ofNat (lam := lam) n), x = T.Z := by
    intro n
    induction n with
    | zero => intro x hx; cases hx
    | succ n ih =>
        intro x hx
        rcases (T.mem_Gi_P u _ _ x).mp hx with ⟨i, _, hx⟩ | hx
        · simp only [Vec.ofFn_idx] at hx
          rcases hx with rfl | hx
          · rfl
          · cases hx
        · exact ih x hx
  refine ⟨?_, fun x hx => ?_⟩
  · induction n with
    | zero => exact .z
    | succ n ih =>
        refine .p _ _ (fun i => by rw [Vec.ofFn_idx]; exact .z) ih
          (fun i => by rw [Vec.ofFn_idx]; intro x hx; cases hx) ?_
        cases n with
        | zero => exact T.Z_le _
        | succ n => exact T.le_refl _
  · rw [hG n x hx]
    cases n with
    | zero => cases hx
    | succ n => rfl

end new

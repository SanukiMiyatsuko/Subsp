import Subsp.Base

/-! Legacy source notation, normal forms, and fundamental-sequence infrastructure.
The declarations are grouped here to mirror the role of `Subsp.new.subsp`.
-/

-- Merged from Subsp/old/subsp.lean
namespace new

inductive Dom (lam : Nat) where
| zero
| one
| omega
| Omega (i : Fin lam)
deriving DecidableEq

mutual
  def T.dom {lam : Nat} : T lam → Dom lam
  | .Z => .zero
  | .P ls add =>
    if add = Z then
      match domVecMinIdx ls with
      | none => .one
      | some (m, domSm) =>
        match domSm with
        | .one =>
          if m.val = 0 then .omega
          else .Omega m
        | .Omega i =>
          if i ≤ m then
            .Omega i
          else .omega
        | _ => .omega
    else dom add

  def T.domVecMinIdx {lam m : Nat} : Vec (T lam) m → Option (Fin m × Dom lam)
  | .nil => none
  | .snoc k xs x =>
    match domVecMinIdx xs with
    | some (i, d) => some (i.castSucc, d)
    | none =>
      let dx := dom x
      if dx = .zero then none
      else some (Fin.last k, dx)
end

def T.fund {lam : Nat} (s t : T lam) : T lam :=
  match s with
  | Z => Z
  | P ls add =>
    if add = Z then
      match domVecMinIdx ls with
      | none => Z
      | some (m, d) =>
        match d with
        | .one =>
          match m with
          | ⟨0, _⟩ =>
            let updatedLs := ls.rplc m (T.fund ls[m] Z)
            mul (P updatedLs Z) t
          | ⟨m' + 1, h⟩ =>
            P ((ls.rplc m (fund ls[m] Z)).rplc ⟨m', Nat.lt_of_succ_lt h⟩ t) Z
        | .Omega i =>
          if i ≤ m then
            P (ls.rplc m (fund ls[m] t)) Z
          else
            let F := fun x => fund ls[m] x
            P (ls.rplc m (fund ls[m] (iter F t))) Z
        | _ =>
          P (ls.rplc m (fund ls[m] t)) Z
    else P ls (fund add t)
termination_by (T.size s, T.size t)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ (T.idx_size_lt_P ls _ m)
    | exact Prod.Lex.left _ _ (T.add_size_lt_P ls add)

def T.LF (lam : Nat) : Nat → T lam
| 0 => Z
| n + 1 =>
  match lam with
  | 0 => P Vec.nil (LF 0 n)
  | lam' + 1 =>
    P (Vec.ofFn (lam' + 1) (fun i => if i = lam' then LF (lam' + 1) n else Z)) Z

inductive T.isOT : (lam : Nat) → T lam → Prop where
| base_0 (n : Nat) : isOT 0 (LF 0 n)
| base_succ (lam : Nat) (n : Nat) : isOT (lam + 1) (P (Vec.ofFn (lam + 1) (fun i => if i.val = 0 then LF (lam + 1) n else Z)) Z)
| step (lam : Nat) (s : T lam) (hs : isOT lam s) (n : Nat) : isOT lam (fund s (ofNat n))

def T.OT (lam : Nat) := { s : T lam // T.isOT lam s }

end new

-- Merged from Subsp/old/stop_basic.lean
/-! Basic comparison and fundamental-sequence lemmas for the indexed legacy domain. -/

namespace new

theorem T.domVecMinIdx_spec {lam m : Nat} (v : Vec (T lam) m) :
    match T.domVecMinIdx v with
    | none => ∀ i : Fin m, T.dom (v.idx i) = .zero
    | some (i, d) => d ≠ .zero ∧ T.dom (v.idx i) = d ∧
        ∀ j : Fin m, j.val < i.val → T.dom (v.idx j) = .zero := by
  induction v with
  | nil => exact fun i => i.elim0
  | snoc k xs x ih =>
      rw [T.domVecMinIdx]
      cases hrec : T.domVecMinIdx xs with
      | some p =>
          obtain ⟨i, d⟩ := p
          rw [hrec] at ih
          refine ⟨ih.1, by simpa [Vec.idx, i.isLt] using ih.2.1, fun j hj => ?_⟩
          have hjk := Nat.lt_trans hj i.isLt
          simpa [Vec.idx, hjk] using ih.2.2 ⟨j.val, hjk⟩ hj
      | none =>
          rw [hrec] at ih
          by_cases hx : T.dom x = .zero
          · rw [ite_eq_left hx]
            intro i
            by_cases hi : i.val < k
            · simpa [Vec.idx, hi] using ih ⟨i.val, hi⟩
            · simpa [Vec.idx, hi] using hx
          · rw [ite_eq_right hx]
            exact ⟨hx, by simp [Vec.idx], fun j (hj : j.val < k) => by
              simpa [Vec.idx, hj] using ih ⟨j.val, hj⟩⟩

theorem T.domVecMinIdx_some_spec {lam m : Nat} (v : Vec (T lam) m) (i : Fin m) (d : Dom lam)
    (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero ∧ T.dom (v.idx i) = d ∧ ∀ j : Fin m, j.val < i.val → T.dom (v.idx j) = .zero := by
  simpa only [h] using T.domVecMinIdx_spec v

theorem Vec.rplc_idx_same {A : Type} {n : Nat} (v : Vec A n) (i : Fin n) (a : A) :
    (v.rplc i a).idx i = a := by
  simp [Vec.rplc, Vec.ofFn_idx]

theorem Vec.rplc_idx_of_ne {A : Type} {n : Nat} (v : Vec A n) (i j : Fin n) (a : A)
    (h : j.val ≠ i.val) : (v.rplc i a).idx j = v.idx j := by
  simp [Vec.rplc, Vec.ofFn_idx, h]
  rfl

theorem Vec.compare_lt_of_pivot {lam m : Nat} (v w : Vec (T lam) m) (i : Fin m)
    (heq : ∀ j : Fin m, i.val < j.val → v.idx j = w.idx j) (hlt : v.idx i < w.idx i) :
    compareVec v w = Ordering.lt := by
  induction m with
  | zero => exact i.elim0
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          by_cases hik : i.val = k
          · have hxy : x < y := by simpa [Fin.eq_of_val_eq (j := Fin.last k) hik, Vec.idx] using hlt
            simp [compareVec, show compareT x y = .lt from hxy]
          · have hiklt : i.val < k := by omega
            have hxy : x = y := by simpa [Vec.idx] using heq (Fin.last k) hiklt
            simpa [compareVec, hxy, T_refl] using ih xs ys ⟨i.val, hiklt⟩
              (fun j hj => by simpa [Vec.idx, j.isLt] using heq j.castSucc hj)
              (by simpa [Vec.idx, hiklt] using hlt)

theorem Vec.compare_lt_has_pivot {lam m : Nat} (v w : Vec (T lam) m)
    (h : compareVec v w = Ordering.lt) :
    ∃ i : Fin m, (∀ j : Fin m, i.val < j.val → v.idx j = w.idx j) ∧ v.idx i < w.idx i := by
  induction m with
  | zero => cases v; cases w; cases h
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          cases hc : compareT x y with
          | lt =>
              exact ⟨Fin.last k, fun j (hj : k < j.val) => by omega,
                by simpa [Vec.idx] using (show x < y from hc)⟩
          | eq =>
              obtain ⟨i, hiAbove, hiLt⟩ := ih xs ys (by simpa [compareVec, hc] using h)
              refine ⟨i.castSucc, fun j hij => ?_, by simpa [Vec.idx, i.isLt] using hiLt⟩
              by_cases hjk : j.val < k
              · simpa [Vec.idx, hjk] using hiAbove ⟨j.val, hjk⟩ hij
              · simpa [Vec.idx, hjk] using T_eq_sound x y hc
          | gt => simp [compareVec, hc] at h

theorem Vec.compare_rplc_lt {lam m : Nat} (v : Vec (T lam) m) (i : Fin m) (a : T lam)
    (h : a < v.idx i) : compareVec (v.rplc i a) v = Ordering.lt :=
  Vec.compare_lt_of_pivot _ _ i (fun j hj => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj))
    (by simpa only [Vec.rplc_idx_same] using h)

theorem Vec.compare_rplc_rplc_lt {lam m : Nat} (v : Vec (T lam) m) (i j : Fin m) (a b : T lam)
    (hji : j.val < i.val) (ha : a < v.idx i) : compareVec ((v.rplc i a).rplc j b) v = .lt :=
  Vec.compare_lt_of_pivot _ _ i (fun q hq => by
    rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega), Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq)])
    (by simpa only [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hji), Vec.rplc_idx_same] using ha)

theorem T.P_lt_P_of_compareVec_lt {lam : Nat} (v w : Vec (T lam) lam) (a b : T lam)
    (h : compareVec v w = Ordering.lt) : T.P v a < T.P w b := by
  simp only [LT.lt, T.lt, compareT, h]

theorem T.fund_lt_self {lam : Nat} (s t : T lam) (hne : s ≠ T.Z) : T.fund s t < s := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z => exact False.elim (hne rfl)
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none => rw [T.fund, ite_eq_left rfl, hmin]; rfl
            | some md =>
                obtain ⟨m, d⟩ := md
                have hspec := T.domVecMinIdx_some_spec ls m d hmin
                have hrec (u) : T.fund (ls.idx m) u < ls.idx m :=
                  ih _ (T.idx_size_lt_P ls T.Z m) u
                    fun hz => hspec.1 (hspec.2.1.symm.trans (congrArg T.dom hz))
                have key (u) (a b : T lam) := T.P_lt_P_of_compareVec_lt _ _ a b
                  (Vec.compare_rplc_lt _ _ _ (hrec u))
                rw [T.fund, ite_eq_left rfl, hmin]
                cases d with
                | one =>
                    obtain ⟨_ | r, mh⟩ := m
                    · cases t with
                      | Z => rfl
                      | P => exact key T.Z _ _
                    · exact T.P_lt_P_of_compareVec_lt _ _ _ _
                        (Vec.compare_rplc_rplc_lt _ _ _ _ _ (Nat.lt_succ_self r) (hrec T.Z))
                | _ => dsimp only; (try split) <;> exact key _ _ _
          · rw [T.fund, ite_eq_right hadd]
            change (match compareVec ls ls with
              | .eq => compareT (T.fund add t) add | ord => ord) = .lt
            rw [Vec_refl]
            exact ih _ (T.add_size_lt_P ls add) t hadd

theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam) (hdom : T.dom s = .zero) : s = T.Z := by
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      cases s with
      | Z => rfl
      | P v b =>
          by_cases hb : b = T.Z
          · subst b
            rw [T.dom, ite_eq_left rfl] at hdom
            split at hdom
            · cases hdom
            · split at hdom <;> (try split at hdom) <;> cases hdom
          · rw [T.dom, ite_eq_right hb] at hdom
            exact False.elim (hb (ih b (T.add_size_lt_P v b) hdom))

theorem T.dom_Omega_pos {lam : Nat} (s : T lam) (i : Fin lam) (hdom : T.dom s = .Omega i) :
    0 < i.val := by
  induction s using (measure T.size).wf.induction generalizing i with
  | h s ih =>
      cases s with
      | Z => cases hdom
      | P v b =>
          by_cases hb : b = T.Z
          · subst b
            rw [T.dom, ite_eq_left rfl] at hdom
            split at hdom
            · cases hdom
            · rename_i m d hm
              split at hdom <;> (try split at hdom) <;> cases hdom
              · exact Nat.pos_of_ne_zero ‹_›
              · exact ih _ (T.idx_size_lt_P v T.Z m) _ (T.domVecMinIdx_some_spec v m _ hm).2.1
          · rw [T.dom, ite_eq_right hb] at hdom
            exact ih b (T.add_size_lt_P v b) i hdom

/-! Countable head indices in the legacy OT fundamental-sequence closure. -/

inductive T.Countable {lam : Nat} : T lam → Prop where
  | z : Countable T.Z
  | p (v : Vec (T lam) lam) (b : T lam) (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
      (hb : Countable b) : Countable (T.P v b)

theorem T.Countable_min_zero {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z)
    (m : Fin lam) (d : Dom lam) (hm : T.domVecMinIdx v = some (m, d)) : m.val = 0 :=
  have hspec := T.domVecMinIdx_some_spec v m d hm
  Nat.eq_zero_of_not_pos fun hpos => hspec.1 (hspec.2.1.symm.trans (congrArg T.dom (hv m hpos)))

theorem T.Countable_mul {lam : Nat} (v : Vec (T lam) lam)
    (hv : ∀ i : Fin lam, 0 < i.val → v.idx i = T.Z) (t : T lam) :
    T.Countable (T.mul (T.P v T.Z) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact .z
  | P _ b _ ih => exact .p v _ hv ih
  | nil | snoc => trivial

theorem T.Countable_fund {lam : Nat} (s : T lam) (hs : T.Countable s) (t : T lam) :
    T.Countable (T.fund s t) := by
  induction hs with
  | z => rw [T.fund]; exact .z
  | p v b hv hb ih =>
      by_cases hbz : b = T.Z
      · subst b
        rw [T.fund, ite_eq_left rfl]
        cases hmin : T.domVecMinIdx v with
        | none => exact .z
        | some md =>
            obtain ⟨m, d⟩ := md
            have hm := T.Countable_min_zero v hv m d hmin
            have hrep (a) : ∀ i : Fin lam, 0 < i.val → (v.rplc m a).idx i = T.Z :=
              fun i hi => (Vec.rplc_idx_of_ne _ _ _ _ (by omega)).trans (hv i hi)
            cases d with
            | one =>
                obtain ⟨mv, mh⟩ := m
                change mv = 0 at hm
                subst mv
                exact T.Countable_mul _ (hrep _) t
            | _ => dsimp only; (try split) <;> exact .p _ _ (hrep _) .z
      · rw [T.fund, ite_eq_right hbz]
        exact .p v _ hv ih

theorem T.isOT_Countable (lam : Nat) (s : T lam) (hs : T.isOT lam s) : T.Countable s := by
  induction hs with
  | base_0 n =>
      induction n with
      | zero => exact .z
      | succ n ih => exact .p Vec.nil _ (fun i => i.elim0) ih
  | base_succ k n =>
      exact .p _ T.Z (fun i hi => by rw [Vec.ofFn_idx, ite_eq_right (Nat.ne_of_gt hi)]) .z
  | step lam a _ n ih => exact T.Countable_fund a ih _

theorem T.isOT_dom_not_Omega (lam : Nat) (s : T lam) (hs : T.isOT lam s) (i : Fin lam) :
    T.dom s ≠ .Omega i := by
  have hc := T.isOT_Countable lam s hs
  clear hs
  induction hc with
  | z => intro h; cases h
  | p v b hv hb ih =>
      intro hdom
      by_cases hbz : b = T.Z
      · subst b
        rw [T.dom, ite_eq_left rfl] at hdom
        split at hdom
        · cases hdom
        · rename_i m d hmin
          have hm := T.Countable_min_zero v hv m d hmin
          split at hdom <;> (try split at hdom) <;> cases hdom
          have hj := T.dom_Omega_pos _ _ (T.domVecMinIdx_some_spec v m _ hmin).2.1
          exact absurd (‹_ ≤ m› : _ ≤ m.val) (by omega)
      · rw [T.dom, ite_eq_right hbz] at hdom
        exact ih hdom

end new

-- Merged from Subsp/old/stop_indexed_nf.lean
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

-- Merged from Subsp/old/stop_source_fund_nf.lean
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

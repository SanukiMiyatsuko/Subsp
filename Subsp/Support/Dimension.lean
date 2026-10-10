import Subsp.Support.Quotient

/-! Dimension lifting of source terms, target arithmetic, and dimension cuts. -/

namespace Support.OTQuotient

open new

def padFull {lam : Nat} (xs : Vec (T lam) lam) : Vec (T (lam + 1)) (lam + 1) :=
  .snoc lam (padVec xs) .Z

def padDom {lam : Nat} : Dom lam → Dom (lam + 1)
  | .zero => .zero
  | .one => .one
  | .omega => .omega
  | .Omega xs => .Omega (padFull xs)

@[simp] theorem pad_eq_zero {lam : Nat} (s : T lam) : pad s = .Z ↔ s = .Z := by
  cases s <;> simp [pad]

@[simp] theorem padDom_eq_zero {lam : Nat} (d : Dom lam) :
    padDom d = .zero ↔ d = .zero := by
  cases d <;> simp [padDom]

theorem compareVec_padVec {lam m : Nat} (xs ys : Vec (T lam) m) :
    compareVec (padVec xs) (padVec ys) = compareVec xs ys := by
  rw [← compareArgs_codes, codes_padVec, codes_padVec, compareArgs_codes]

@[simp] theorem padFull_lt {lam : Nat} (xs ys : Vec (T lam) lam) :
    Vec.lt (padFull xs) (padFull ys) ↔ Vec.lt xs ys := by
  simp only [Vec.lt, padFull, compareVec, compareT, compareVec_padVec]

def padMin {lam m : Nat} : Option (Fin m × Dom lam) → Option (Fin m × Dom (lam + 1)) :=
  Option.map (fun (i, d) => (i, padDom d))

mutual
  theorem dom_pad {lam : Nat} (s : T lam) : T.dom (pad s) = padDom (T.dom s) := by
    cases s with
    | Z => rfl
    | P xs b =>
      simp only [pad, T.dom, pad_eq_zero]
      by_cases hb : b = .Z
      · simp only [hb, ↓reduceIte]
        simp only [T.domVecMinIdx, minIdx_padVec xs]
        cases h : T.domVecMinIdx xs with
        | none => simp [padMin, T.dom, padDom]
        | some p =>
          obtain ⟨i, d⟩ := p
          cases d <;> simp [padMin, padDom, padFull, Vec.lt, compareVec,
            compareT, compareVec_padVec]
          all_goals split <;> simp_all
      · simp only [hb, ↓reduceIte, dom_pad b]
  termination_by T.size s
  decreasing_by all_goals simp [T.size]; omega

  theorem minIdx_padVec {lam m : Nat} (xs : Vec (T lam) m) :
      T.domVecMinIdx (padVec xs) = padMin (T.domVecMinIdx xs) := by
    cases xs with
    | nil => rfl
    | snoc n xs x =>
      simp only [padVec, T.domVecMinIdx, minIdx_padVec xs, dom_pad x]
      cases h : T.domVecMinIdx xs with
      | none =>
        by_cases hx : T.dom x = .zero <;> simp [padMin, hx]
      | some p => obtain ⟨i, d⟩ := p; rfl
  termination_by Vec.size xs
  decreasing_by all_goals simp [Vec.size]; omega
end

theorem minIdx_padFull {lam : Nat} (xs : Vec (T lam) lam) :
      T.domVecMinIdx (padFull xs) =
        (T.domVecMinIdx xs).map (fun (i, d) => (i.castSucc, padDom d)) := by
    simp only [padFull, T.domVecMinIdx, minIdx_padVec]
    cases h : T.domVecMinIdx xs with
    | none => simp [padMin, T.dom]
    | some p => obtain ⟨i, d⟩ := p; rfl

theorem vec_snoc_idx_cast {A : Type} {m : Nat} (xs : Vec A m) (x : A) (i : Fin m) :
    (Vec.snoc m xs x).idx i.castSucc = xs.idx i := by
  simp [Vec.idx, i.isLt]

theorem vec_snoc_idx_last {A : Type} {m : Nat} (xs : Vec A m) (x : A) :
    (Vec.snoc m xs x).idx (Fin.last m) = x := by
  simp [Vec.idx]

theorem vec_ext {A : Type} {m : Nat} (xs ys : Vec A m)
    (h : ∀ i, xs.idx i = ys.idx i) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | snoc m xs x ih =>
    cases ys with
    | snoc _ ys y =>
      have hlast : x = y := by simpa only [vec_snoc_idx_last] using h (Fin.last m)
      have hprefix : xs = ys := ih ys (fun i => by
        simpa only [vec_snoc_idx_cast] using h i.castSucc)
      cases hlast
      cases hprefix
      rfl

theorem padVec_idx {lam m : Nat} (xs : Vec (T lam) m) (i : Fin m) :
    (padVec xs).idx i = pad (xs.idx i) := by
  induction xs with
  | nil => exact i.elim0
  | snoc m xs x ih =>
    simp only [padVec, Vec.idx]
    split
    · exact ih _
    · rfl

theorem padFull_idx_cast {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) :
    (padFull xs).idx i.castSucc = pad (xs.idx i) := by
  simp only [padFull, vec_snoc_idx_cast, padVec_idx]

theorem padFull_idx_last {lam : Nat} (xs : Vec (T lam) lam) :
    (padFull xs).idx (Fin.last lam) = .Z := by
  simp only [padFull, vec_snoc_idx_last]

theorem vec_rplc_idx {A : Type} {m : Nat} (xs : Vec A m) (i j : Fin m) (x : A) :
    (xs.rplc i x).idx j = if j.val = i.val then x else xs.idx j := by
  rw [Vec.rplc, Vec.ofFn_idx]
  rfl

theorem padFull_rplc {lam : Nat} (xs : Vec (T lam) lam) (i : Fin lam) (x : T lam) :
    padFull (xs.rplc i x) = (padFull xs).rplc i.castSucc (pad x) := by
  apply vec_ext
  intro j
  by_cases hj : j.val < lam
  · let k : Fin lam := ⟨j.val, hj⟩
    have he : j = k.castSucc := Fin.ext rfl
    rw [he, padFull_idx_cast, vec_rplc_idx, vec_rplc_idx, padFull_idx_cast]
    simp only [Fin.val_castSucc]
    split <;> rfl
  · have he : j = Fin.last lam := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [he, padFull_idx_last, vec_rplc_idx, padFull_idx_last]
    simp only [Fin.val_last, Fin.val_castSucc]
    have hi : ¬ lam = i.val := by have := i.isLt; omega
    simp [hi]

theorem pad_ofNat {lam : Nat} (n : Nat) : pad (T.ofNat (lam := lam) n) = T.ofNat n := by
  apply code_injective
  rw [code_pad, FiniteCorrespondence.code_ofNat, FiniteCorrespondence.code_ofNat]

theorem pad_oplus {lam : Nat} (s t : T lam) : pad (s + t) = pad s + pad t := by
  cases s with
  | Z => rfl
  | P xs b =>
    have ih := pad_oplus b t
    simp only [HAdd.hAdd, Add.add, T.oplus, pad] at *
    rw [ih]

theorem pad_mul {lam : Nat} (s t : T lam) : pad (T.mul s t) = T.mul (pad s) (pad t) := by
  cases t with
  | Z => rfl
  | P xs b => simp only [T.mul, pad_oplus, pad, pad_mul s b]

theorem pad_iter {lam : Nat} (F : T lam → T lam) (G : T (lam + 1) → T (lam + 1))
    (h : ∀ x, pad (F x) = G (pad x)) (s : T lam) :
    pad (T.iter F s) = T.iter G (pad s) := by
  cases s with
  | Z => rfl
  | P xs b => simp only [T.iter, pad, h, pad_iter F G h b]

theorem fund_pad {lam : Nat} (s t : T lam) :
    T.fund (pad s) (pad t) = pad (T.fund s t) := by
  cases s with
  | Z => simp [pad, T.fund]
  | P xs b =>
    change T.fund (.P (padFull xs) (pad b)) (pad t) = pad (T.fund (.P xs b) t)
    rw [T.fund]
    conv => rhs; rw [T.fund]
    simp only [pad_eq_zero]
    by_cases hb : b = .Z
    · simp only [hb, ↓reduceIte, minIdx_padFull]
      cases hm : T.domVecMinIdx xs with
      | none => rfl
      | some p =>
        obtain ⟨i, d⟩ := p
        cases d with
        | zero | omega =>
          simp only [Option.map, padDom, GetElem.getElem, Fin.eta, padFull_idx_cast]
          rw [fund_pad (xs.idx i) t, ← padFull_rplc]
          rfl
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero =>
            simp only [Option.map, padDom, Fin.castSucc_mk, GetElem.getElem]
            have hidx := padFull_idx_cast xs ⟨0, hj⟩
            simp only [Fin.castSucc_mk] at hidx
            rw [hidx]
            have hfund := fund_pad (xs.idx ⟨0, hj⟩) .Z
            simp only [pad] at hfund
            rw [hfund]
            have hr := padFull_rplc xs ⟨0, hj⟩ (T.fund (xs.idx ⟨0, hj⟩) .Z)
            simp only [Fin.castSucc_mk] at hr
            rw [← hr]
            simpa only [pad, padFull] using
              (pad_mul (.P (xs.rplc ⟨0, hj⟩ (T.fund (xs.idx ⟨0, hj⟩) .Z)) .Z) t).symm
          | succ j =>
            simp only [Option.map, padDom, Fin.castSucc_mk, GetElem.getElem]
            have hidx := padFull_idx_cast xs ⟨j + 1, hj⟩
            simp only [Fin.castSucc_mk] at hidx
            rw [hidx]
            have hfund := fund_pad (xs.idx ⟨j + 1, hj⟩) .Z
            simp only [pad] at hfund
            rw [hfund]
            have hr := padFull_rplc xs ⟨j + 1, hj⟩ (T.fund (xs.idx ⟨j + 1, hj⟩) .Z)
            simp only [Fin.castSucc_mk] at hr
            rw [← hr]
            have hr' := padFull_rplc (xs.rplc ⟨j + 1, hj⟩ (T.fund (xs.idx ⟨j + 1, hj⟩) .Z))
              ⟨j, Nat.lt_of_succ_lt hj⟩ t
            simp only [Fin.castSucc_mk] at hr'
            rw [← hr']
            rfl
        | Omega ys =>
          simp only [Option.map, padDom, padFull_lt, GetElem.getElem, Fin.eta, padFull_idx_cast]
          by_cases hxy : Vec.lt xs ys
          · simp only [hxy, ↓reduceIte]
            have hi : T.iter (T.fund (pad (xs.idx i))) (pad t) =
                pad (T.iter (T.fund (xs.idx i)) t) :=
              (pad_iter _ _ (fun x => (fund_pad (xs.idx i) x).symm) t).symm
            rw [hi, fund_pad, ← padFull_rplc]
            rfl
          · simp only [hxy, ↓reduceIte]
            rw [fund_pad, ← padFull_rplc]
            rfl
    · simp only [hb, ↓reduceIte, fund_pad b t]
      rfl
termination_by T.size s
decreasing_by
  all_goals
    first
    | apply Nat.lt_trans (Vec.idx_size_lt _ _)
      simp only [T.size]
      omega
    | exact T.add_size_lt_P _ _

end Support.OTQuotient

namespace Support.CountableSource

open new OTQuotient

def lowVec {lam : Nat} (k : Nat) (a : T lam) : Vec (T lam) (k + 1) :=
  Vec.ofFn (k + 1) (fun i => if i.val = 0 then a else .Z)

theorem lowVec_zero {lam : Nat} (a : T lam) : lowVec 0 a = .snoc 0 .nil a := by
  simp [lowVec, Vec.ofFn]

theorem lowVec_succ {lam : Nat} (k : Nat) (a : T lam) :
    lowVec (k + 1) a = .snoc (k + 1) (lowVec k a) .Z := by
  simp [lowVec, Vec.ofFn]

theorem lowVec_idx {lam : Nat} (k : Nat) (a : T lam) (i : Fin (k + 1)) :
    (lowVec k a).idx i = if i.val = 0 then a else .Z := by
  simp only [lowVec, Vec.ofFn_idx]

theorem lowVec_rplc_zero {lam : Nat} (k : Nat) (a b : T lam) :
    (lowVec k a).rplc ⟨0, Nat.zero_lt_succ k⟩ b = lowVec k b := by
  apply vec_ext
  intro i
  simp only [vec_rplc_idx, lowVec_idx]
  split <;> simp_all

theorem minIdx_lowVec {lam : Nat} (k : Nat) (a : T lam) :
    T.domVecMinIdx (lowVec k a) =
      if T.dom a = .zero then none else some (⟨0, Nat.zero_lt_succ k⟩, T.dom a) := by
  induction k with
  | zero => simp [lowVec_zero, T.domVecMinIdx]
  | succ k ih =>
    rw [lowVec_succ, T.domVecMinIdx, ih]
    by_cases h : T.dom a = .zero <;> simp [h, T.dom]

inductive Outer {k : Nat} : T (k + 1) → Prop
  | zero : Outer .Z
  | cons (a b : T (k + 1)) : Outer b → Outer (.P (lowVec k a) b)

theorem outer_oplus {k : Nat} {s t : T (k + 1)} (hs : Outer s) (ht : Outer t) :
    Outer (s + t) := by
  induction hs with
  | zero => exact ht
  | cons a b _ ih => exact Outer.cons a (b + t) ih

theorem outer_mul {k : Nat} {s : T (k + 1)} (hs : Outer s) (t : T (k + 1)) :
    Outer (T.mul s t) := by
  cases t with
  | Z => exact Outer.zero
  | P xs b => exact outer_oplus hs (outer_mul hs b)

theorem fund_outer {k : Nat} {s : T (k + 1)} (hs : Outer s) (t : T (k + 1)) :
    Outer (T.fund s t) := by
  induction hs with
  | zero => simpa [T.fund] using (Outer.zero (k := k))
  | cons a b hb ih =>
    rw [T.fund]
    by_cases hz : b = .Z
    · simp only [hz, ↓reduceIte, minIdx_lowVec]
      cases hd : T.dom a with
      | zero => simp only [↓reduceIte]; exact Outer.zero
      | one =>
        simp only [reduceCtorEq, ↓reduceIte, GetElem.getElem, lowVec_idx]
        simp only [lowVec_rplc_zero]
        exact outer_mul (Outer.cons _ _ Outer.zero) t
      | omega =>
        simp only [reduceCtorEq, ↓reduceIte, GetElem.getElem, lowVec_idx]
        simp only [lowVec_rplc_zero]
        exact Outer.cons _ _ Outer.zero
      | Omega ys =>
        simp only [reduceCtorEq, ↓reduceIte, GetElem.getElem, lowVec_idx]
        split <;> simp only [lowVec_rplc_zero] <;> exact Outer.cons _ _ Outer.zero
    · simp only [hz, ↓reduceIte]
      exact Outer.cons a _ ih

private theorem isOT_outer_cast {lam : Nat} {s : T lam} (h : T.isOT lam s) :
    ∀ k (e : lam = k + 1), Outer (e ▸ s) := by
  induction h with
  | base_0 n => intro k e; omega
  | base_succ lam n =>
    intro k e
    have he : lam = k := by omega
    subst lam
    cases e
    exact Outer.cons _ _ Outer.zero
  | step lam s hs n ih =>
    intro k e
    subst lam
    exact fund_outer (ih k rfl) _

theorem isOT_outer {k : Nat} {s : T (k + 1)} (h : T.isOT (k + 1) s) : Outer s :=
  isOT_outer_cast h k rfl

theorem trim_codes_lowVec {lam : Nat} (k : Nat) (a : T lam) :
    trim (codes (lowVec k a)) = trim [code a] := by
  induction k with
  | zero => simp [lowVec_zero, codes]
  | succ k ih =>
    simp only [lowVec_succ, codes, code, FiniteCorrespondence.trim_append_zero, ih]

def OuterForm : Code → Prop
  | .zero => True
  | .p args b => args.length ≤ 1 ∧ OuterForm b

theorem outer_code {k : Nat} {s : T (k + 1)} (hs : Outer s) : OuterForm (code s) := by
  induction hs with
  | zero => trivial
  | cons a b _ ih =>
    simp only [code, trim_codes_lowVec, OuterForm]
    refine ⟨?_, ih⟩
    cases hc : code a <;> simp [trim, Code.isZero]

theorem natCode_outer (n : Nat) : OuterForm (FiniteCorrespondence.natCode n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨by decide +kernel, ih⟩

theorem allOT_outer (s : AllOT) : OuterForm (key s) := by
  obtain ⟨lam, s, hs⟩ := s
  cases lam with
  | zero =>
    obtain ⟨n, rfl⟩ := FiniteCorrespondence.zero_dimension_exhaustive s
    change OuterForm (code (T.ofNat (lam := 0) n))
    rw [FiniteCorrespondence.code_ofNat]
    exact natCode_outer n
  | succ k => exact outer_code (isOT_outer hs)

theorem representative_outer (q : Classes) : OuterForm (representative q) := by
  induction q using Quotient.inductionOn with
  | h s => exact allOT_outer s

end Support.CountableSource

namespace Support.CountableTarget

open OCF.Jaeger

theorem lt_zero (t : Term) : Term.lt t .zero = false := by
  cases t <;> simp [Term.lt]

theorem inacc_not_below_omega (n : Nat) (a : Term) :
    Term.lt (.inacc n a) Term.bigOmega = false := by
  simp [Term.bigOmega, Term.lt, lt_zero]

theorem regular_not_below_omega {u : Term} (hu : Term.isRT u = true) :
    Term.lt u Term.bigOmega = false := by
  cases u with
  | zero | add | psi => cases hu
  | inacc n a => exact inacc_not_below_omega n a

theorem psi_below_omega_iff {u b : Term} (hu : Term.isRT u = true) :
    Term.lt (.psi u b) Term.bigOmega = true ↔ u = Term.bigOmega := by
  cases u with
  | zero | add | psi => cases hu
  | inacc n a => simp [Term.bigOmega, Term.lt, Term.fT, lt_zero]

theorem inacc_not_below_psiOmega (n : Nat) (a b : Term) :
    Term.lt (.inacc n a) (.psi Term.bigOmega b) = false := by
  simp only [Term.lt]
  simp [Term.bigOmega, Term.fT, Term.lt, lt_zero]

theorem psi_lt_psiOmega_subscript {u a b : Term} (hu : Term.isRT u = true)
    (h : Term.lt (.psi u a) (.psi Term.bigOmega b) = true) : u = Term.bigOmega := by
  rw [Term.lt] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · have hn := regular_not_below_omega hu
    rw [hn] at h
    cases h.1
  · exact h.1
  · exact (psi_below_omega_iff hu).mp h.2

theorem principal_below_omega {a : Term} (hp : Term.isPrin a = true)
    (hw : Term.wf a = true) (hlt : Term.lt a Term.bigOmega = true) :
    ∃ b, a = .psi Term.bigOmega b := by
  cases a with
  | zero | add => cases hp
  | inacc n b => rw [inacc_not_below_omega] at hlt; cases hlt
  | psi u b =>
    have hu := (Term.wf_psi_iff u b).mp hw
    exact ⟨b, congrArg (fun u => Term.psi u b) ((psi_below_omega_iff hu.1).mp hlt)⟩

theorem principal_le_psiOmega_below {a b : Term} (hp : Term.isPrin a = true)
    (hw : Term.wf a = true) (h : Term.le a (.psi Term.bigOmega b) = true) :
    Term.lt a Term.bigOmega = true := by
  simp only [Term.le, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | h
  · simp [Term.bigOmega, Term.lt, Term.fT]
  · cases a with
    | zero | add => cases hp
    | inacc n c => rw [inacc_not_below_psiOmega] at h; cases h
    | psi u c =>
      have hu := (Term.wf_psi_iff u c).mp hw
      exact (psi_below_omega_iff hu.1).mpr (psi_lt_psiOmega_subscript hu.1 h)

theorem head_properties {t : Term} (hw : Term.wf t = true) (hne : t ≠ .zero) :
    Term.isPrin (Term.head t) = true ∧ Term.wf (Term.head t) = true := by
  cases t with
  | zero => exact False.elim (hne rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    exact ⟨h.1, h.2.1⟩
  | inacc n a => exact ⟨rfl, hw⟩
  | psi u a => exact ⟨rfl, hw⟩

theorem head_below_omega (t : Term) :
    Term.lt (Term.head t) Term.bigOmega = Term.lt t Term.bigOmega := by
  cases t <;> simp [Term.head, Term.bigOmega, Term.lt]

inductive Outer : Term → Prop
  | zero : Outer .zero
  | atom (b : Term) : Outer (.psi Term.bigOmega b)
  | cons (a b : Term) : Outer b → Outer (.add (.psi Term.bigOmega a) b)

theorem wf_below_outer {t : Term} (hw : Term.wf t = true)
    (hlt : Term.lt t Term.bigOmega = true) : Outer t := by
  induction t with
  | zero => exact Outer.zero
  | inacc n a _ => rw [inacc_not_below_omega] at hlt; cases hlt
  | psi u a _ _ =>
    have hu := (Term.wf_psi_iff u a).mp hw
    have he := (psi_below_omega_iff hu.1).mp hlt
    rw [he]
    exact Outer.atom a
  | add a b _ ihb =>
    have h := (Term.wf_add_iff a b).mp hw
    have ha : Term.lt a Term.bigOmega = true := by simpa only [Term.bigOmega, Term.lt] using hlt
    obtain ⟨c, rfl⟩ := principal_below_omega h.1 h.2.1 ha
    have hb := head_properties h.2.2.1 h.2.2.2.1
    have hblt := principal_le_psiOmega_below hb.1 hb.2 h.2.2.2.2
    rw [head_below_omega] at hblt
    exact Outer.cons c b (ihb h.2.2.1 hblt)

theorem target_outer (t : Support.WFBelowOmega) : Outer t.val :=
  wf_below_outer t.property.1 t.property.2

end Support.CountableTarget

namespace Support.TargetArithmetic

open OCF.Jaeger BinaryTranslation

theorem lt_self (t : Term) : Term.lt t t = false := by
  induction t with
  | zero => simp [Term.lt]
  | add a b iha ihb => simp [Term.lt, ihb]
  | inacc n b ih => simp [Term.lt, ih]
  | psi u b ihu ihb => simp [Term.lt, ihu, ihb]

theorem zero_lt_iff (t : Term) : Term.lt .zero t = true ↔ t ≠ .zero := by
  cases t <;> simp [Term.lt]

theorem one_le_principal {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.le Term.one t = true := by
  cases t with
  | zero | add => cases hp
  | inacc n b =>
    cases n <;> cases b <;> simp [Term.le, Term.one, Term.bigOmega, Term.lt, Term.fT]
  | psi u b =>
    have hu := ((Term.wf_psi_iff u b).mp hw).1
    cases u with
    | zero | add | psi => cases hu
    | inacc n c =>
      cases n <;> cases c <;> cases b <;>
        simp [Term.le, Term.one, Term.bigOmega, Term.lt, Term.fT, CountableTarget.lt_zero]

theorem principal_not_lt_one {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.lt t Term.one = false := by
  cases t with
  | zero | add => cases hp
  | inacc n b => exact CountableTarget.inacc_not_below_psiOmega n b .zero
  | psi u b =>
    have hu := ((Term.wf_psi_iff u b).mp hw).1
    by_cases he : u = Term.bigOmega
    · rw [he, Term.one, Unary.psi_omega_lt, CountableTarget.lt_zero]
    · have hn : Term.lt (.psi u b) Term.bigOmega = false := by
        cases h : Term.lt (.psi u b) Term.bigOmega with
        | false => rfl
        | true => exact False.elim (he ((CountableTarget.psi_below_omega_iff hu).mp h))
      rw [Term.one, Term.lt]
      simp [CountableTarget.regular_not_below_omega hu, he, hn]

theorem principal_le_one_iff {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.le t Term.one = true ↔ t = Term.one := by
  simp only [Term.le, principal_not_lt_one hp hw, Bool.or_false, decide_eq_true_eq]

theorem one_lt_principal_iff {t : Term} (hp : Term.isPrin t = true) (hw : Term.wf t = true) :
    Term.lt Term.one t = true ↔ t ≠ Term.one := by
  constructor
  · intro h he
    rw [he, lt_self] at h
    cases h
  · intro he
    have h := one_le_principal hp hw
    simp only [Term.le, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact False.elim (he h.symm)
    · exact h

theorem dropOne_wf {t : Term} (hw : Term.wf t = true) : Term.wf (dropOne t) = true := by
  cases t with
  | zero => rfl
  | add a b =>
    simp only [dropOne]
    split
    · exact ((Term.wf_add_iff a b).mp hw).2.2.1
    · exact hw
  | inacc n b => exact hw
  | psi u b =>
    simp only [dropOne]
    split
    · rfl
    · exact hw

theorem succTerm_ne_zero (t : Term) : succTerm t ≠ .zero := by
  cases t <;> simp [succTerm, Term.one]

theorem head_succTerm {t : Term} (hne : t ≠ .zero) :
    Term.head (succTerm t) = Term.head t := by
  cases t with
  | zero => exact False.elim (hne rfl)
  | add | inacc | psi => rfl

theorem succTerm_wf {t : Term} (hw : Term.wf t = true) : Term.wf (succTerm t) = true := by
  induction t with
  | zero => exact Term.wf_one
  | add a b _ ihb =>
    have h := (Term.wf_add_iff a b).mp hw
    apply (Term.wf_add_iff _ _).mpr
    exact ⟨h.1, h.2.1, ihb h.2.2.1, succTerm_ne_zero b,
      by simpa only [head_succTerm h.2.2.2.1] using h.2.2.2.2⟩
  | inacc n b _ =>
    exact (Term.wf_add_iff _ _).mpr
      ⟨rfl, hw, Term.wf_one, by decide +kernel, one_le_principal rfl hw⟩
  | psi u b _ _ =>
    exact (Term.wf_add_iff _ _).mpr
      ⟨rfl, hw, Term.wf_one, by decide +kernel, one_le_principal rfl hw⟩

theorem succTerm_isSucc (t : Term) : Term.isSucc (succTerm t) = true := by
  induction t with
  | zero => decide +kernel
  | add a b _ ihb => exact ihb
  | inacc | psi => simp [succTerm, Term.isSucc, Term.one]

theorem succTerm_ne_one {t : Term} (hne : t ≠ .zero) : succTerm t ≠ Term.one := by
  cases t with
  | zero => exact False.elim (hne rfl)
  | add | inacc | psi => simp [succTerm, Term.one]

theorem predT_succTerm {t : Term} (hw : Term.wf t = true) : Term.predT (succTerm t) = t := by
  induction t with
  | zero => rfl
  | add a b _ ihb =>
    have h := (Term.wf_add_iff a b).mp hw
    simp only [succTerm, Term.predT, succTerm_ne_one h.2.2.2.1, ↓reduceIte, ihb h.2.2.1]
  | inacc | psi => simp [succTerm, Term.predT]

theorem succTerm_injective {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (h : succTerm s = succTerm t) : s = t := by
  have hp := congrArg Term.predT h
  simpa only [predT_succTerm hs, predT_succTerm ht] using hp

open FiniteCorrespondence

theorem head_one_nat {t : Term} (hw : Term.wf t = true) (hh : Term.head t = Term.one) :
    ∃ n, t = natTerm (n + 1) := by
  induction t with
  | zero => cases hh
  | add a b _ ihb =>
    have ha : a = Term.one := hh
    have h := (Term.wf_add_iff a b).mp hw
    have hb := CountableTarget.head_properties h.2.2.1 h.2.2.2.1
    have hhead := (principal_le_one_iff hb.1 hb.2).mp (ha ▸ h.2.2.2.2)
    obtain ⟨n, hn⟩ := ihb h.2.2.1 hhead
    exact ⟨n + 1, by simp only [natTerm, ha, hn]⟩
  | inacc => cases hh
  | psi u b _ _ => exact ⟨0, hh⟩

theorem dropOne_nat (n : Nat) : dropOne (natTerm (n + 1)) = natTerm n := by
  cases n <;> simp [natTerm, dropOne, Term.one]

theorem dropOne_of_head_ne {t : Term} (hh : Term.head t ≠ Term.one) : dropOne t = t := by
  cases t with
  | zero | inacc => rfl
  | add | psi => simp_all [Term.head, dropOne]

theorem nat_lt_of_head_ne {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero)
    (hh : Term.head t ≠ Term.one) (n : Nat) : Term.lt (natTerm n) t = true := by
  have hp := CountableTarget.head_properties hw hz
  have ho := (one_lt_principal_iff hp.1 hp.2).mpr hh
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have hae : Term.one ≠ a := fun h => hh h.symm
    change Term.lt Term.one a = true at ho
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n =>
      cases n with
      | zero =>
        have hae' : Term.psi Term.bigOmega .zero ≠ a := hae
        rw [natTerm, Term.one, Term.lt, ite_eq_right hae']; exact ho
      | succ n =>
        rw [natTerm, Term.lt, ite_eq_right hae]; exact ho
  | inacc k b =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simpa only [natTerm, Term.head, Term.lt] using ho
  | psi u b =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simpa only [natTerm, Term.head, Term.lt] using ho

theorem not_lt_nat_of_head_ne {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero)
    (hh : Term.head t ≠ Term.one) (n : Nat) : Term.lt t (natTerm n) = false := by
  have hp := CountableTarget.head_properties hw hz
  have ho := principal_not_lt_one hp.1 hp.2
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    change a ≠ Term.one at hh
    change Term.lt a Term.one = false at ho
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n =>
      cases n with
      | zero => rw [natTerm, Term.one, Term.lt]; exact ho
      | succ n =>
        rw [natTerm, Term.lt, ite_eq_right hh]; exact ho
  | inacc k b =>
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n => cases n <;> simpa [natTerm, Term.one, Term.head, Term.lt] using ho
  | psi u b =>
    change Term.psi u b ≠ Term.one at hh
    change Term.lt (.psi u b) Term.one = false at ho
    cases n with
    | zero => simp [natTerm, Term.lt]
    | succ n =>
      cases n with
      | zero => exact ho
      | succ n =>
        rw [natTerm, Term.lt, ite_eq_right hh]; exact ho

theorem dropOne_order {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (hsz : s ≠ .zero) (htz : t ≠ .zero) :
    Term.lt (dropOne s) (dropOne t) = Term.lt s t := by
  by_cases hsh : Term.head s = Term.one <;> by_cases hth : Term.head t = Term.one
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    obtain ⟨n, rfl⟩ := head_one_nat ht hth
    apply Bool.eq_iff_iff.mpr
    simp only [dropOne_nat, natTerm_lt, Nat.add_lt_add_iff_right]
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    rw [dropOne_nat, dropOne_of_head_ne hth,
      nat_lt_of_head_ne ht htz hth, nat_lt_of_head_ne ht htz hth]
  · obtain ⟨n, rfl⟩ := head_one_nat ht hth
    rw [dropOne_nat, dropOne_of_head_ne hsh,
      not_lt_nat_of_head_ne hs hsz hsh, not_lt_nat_of_head_ne hs hsz hsh]
  · rw [dropOne_of_head_ne hsh, dropOne_of_head_ne hth]

theorem dropOne_injective {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (hsz : s ≠ .zero) (htz : t ≠ .zero) (he : dropOne s = dropOne t) : s = t := by
  by_cases hsh : Term.head s = Term.one <;> by_cases hth : Term.head t = Term.one
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    obtain ⟨n, rfl⟩ := head_one_nat ht hth
    rw [dropOne_nat, dropOne_nat] at he
    exact congrArg (fun n => natTerm (n + 1)) (natTerm_injective he)
  · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
    rw [dropOne_nat, dropOne_of_head_ne hth] at he
    have hlt := nat_lt_of_head_ne ht htz hth m
    rw [he, lt_self] at hlt
    cases hlt
  · obtain ⟨n, rfl⟩ := head_one_nat ht hth
    rw [dropOne_nat, dropOne_of_head_ne hsh] at he
    have hlt := nat_lt_of_head_ne hs hsz hsh n
    rw [← he, lt_self] at hlt
    cases hlt
  · simpa only [dropOne_of_head_ne hsh, dropOne_of_head_ne hth] using he

theorem one_lt_add {a b : Term} (hp : Term.isPrin a = true) (hw : Term.wf a = true) :
    Term.lt Term.one (.add a b) = true := by
  have h := one_le_principal hp hw
  rw [Term.le] at h
  rw [Term.one, Term.lt]
  split
  · rfl
  · rename_i he
    have he' : Term.one ≠ a := he
    change Term.lt Term.one a = true
    simpa only [he', decide_false, Bool.false_or] using h

theorem one_lt_succTerm {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero) :
    Term.lt Term.one (succTerm t) = true := by
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    exact one_lt_add h.1 h.2.1
  | inacc | psi => exact one_lt_add rfl hw

theorem succTerm_not_lt_one {t : Term} (hw : Term.wf t = true) :
    Term.lt (succTerm t) Term.one = false := by
  cases t with
  | zero => exact lt_self Term.one
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    rw [succTerm, Term.one, Term.lt]
    exact principal_not_lt_one h.1 h.2.1
  | inacc | psi =>
    rw [succTerm, Term.one, Term.lt]
    exact principal_not_lt_one rfl hw

theorem add_one_order (s t : Term) :
    Term.lt (.add s Term.one) (.add t Term.one) = Term.lt s t := by
  rw [Term.lt]
  split
  · rename_i he
    subst t
    rw [lt_self, lt_self]
  · rfl

theorem succTerm_order {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true) :
    Term.lt (succTerm s) (succTerm t) = Term.lt s t := by
  induction s generalizing t with
  | zero =>
    cases t with
    | zero => simp only [succTerm, lt_self]
    | add | inacc | psi =>
      rw [show succTerm .zero = Term.one from rfl,
        one_lt_succTerm ht (by intro h; cases h)]
      simp [Term.lt]
  | add a b _ ihb =>
    have hsb := (Term.wf_add_iff a b).mp hs
    cases t with
    | zero => rw [succTerm, succTerm_not_lt_one hs, CountableTarget.lt_zero]
    | add c d =>
      have htd := (Term.wf_add_iff c d).mp ht
      simp only [succTerm, Term.lt]
      split
      · exact ihb hsb.2.2.1 htd.2.2.1
      · rfl
    | inacc n c =>
      rw [succTerm, succTerm, Term.lt, Term.lt]
      split
      · rename_i he
        rw [he, lt_self, succTerm_not_lt_one hsb.2.2.1]
      · rfl
    | psi u c =>
      rw [succTerm, succTerm, Term.lt, Term.lt]
      split
      · rename_i he
        rw [he, lt_self, succTerm_not_lt_one hsb.2.2.1]
      · rfl
  | inacc n a _ =>
    cases t with
    | zero => rw [succTerm, succTerm_not_lt_one hs, CountableTarget.lt_zero]
    | add c d =>
      have htd := (Term.wf_add_iff c d).mp ht
      simp only [succTerm, Term.lt]
      split
      · exact one_lt_succTerm htd.2.2.1 htd.2.2.2.1
      · rfl
    | inacc | psi => exact add_one_order _ _
  | psi u a _ _ =>
    cases t with
    | zero => rw [succTerm, succTerm_not_lt_one hs, CountableTarget.lt_zero]
    | add c d =>
      have htd := (Term.wf_add_iff c d).mp ht
      simp only [succTerm, Term.lt]
      split
      · exact one_lt_succTerm htd.2.2.1 htd.2.2.2.1
      · rfl
    | inacc | psi => exact add_one_order _ _

theorem one_le_of_ne_zero {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero) :
    Term.le Term.one t = true := by
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    rw [Term.le, one_lt_add h.1 h.2.1]
    simp
  | inacc | psi => exact one_le_principal rfl hw

theorem le_add_same (a b c : Term) :
    Term.le (.add a b) (.add a c) = Term.le b c := by
  simp [Term.le, Term.lt]

theorem not_lt_one {t : Term} (hw : Term.wf t = true) (hz : t ≠ .zero) :
    Term.lt t Term.one = false := by
  cases t with
  | zero => exact False.elim (hz rfl)
  | add a b =>
    have h := (Term.wf_add_iff a b).mp hw
    rw [Term.one, Term.lt]
    exact principal_not_lt_one h.1 h.2.1
  | inacc | psi => exact principal_not_lt_one rfl hw

theorem succTerm_le_eq_lt {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true) :
    Term.le (succTerm s) t = Term.lt s t := by
  induction s generalizing t with
  | zero =>
    cases t with
    | zero => decide +kernel
    | add | inacc | psi =>
      rw [show succTerm .zero = Term.one from rfl,
        one_le_of_ne_zero ht (by intro h; cases h)]
      simp [Term.lt]
  | add a b _ ihb =>
    have hb := (Term.wf_add_iff a b).mp hs
    cases t with
    | zero => simp [succTerm, Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : a = c
      · subst c
        rw [succTerm, le_add_same, Term.lt]
        simpa only [↓reduceIte] using ihb hb.2.2.1 hd.2.2.1
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]
  | inacc n a _ =>
    cases t with
    | zero => simp [succTerm, Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : Term.inacc n a = c
      · subst c
        rw [succTerm, le_add_same, Term.lt]
        simp only [↓reduceIte, one_le_of_ne_zero hd.2.2.1 hd.2.2.2.1]
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]
  | psi u a _ _ =>
    cases t with
    | zero => simp [succTerm, Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : Term.psi u a = c
      · subst c
        rw [succTerm, le_add_same, Term.lt]
        simp only [↓reduceIte, one_le_of_ne_zero hd.2.2.1 hd.2.2.2.1]
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]

theorem lt_succTerm_eq_le {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true) :
    Term.lt s (succTerm t) = Term.le s t := by
  induction s generalizing t with
  | zero =>
    cases t <;> simp [succTerm, Term.le, Term.lt, Term.one]
  | add a b _ ihb =>
    have hb := (Term.wf_add_iff a b).mp hs
    cases t with
    | zero =>
      rw [show succTerm .zero = Term.one from rfl, not_lt_one hs (by intro h; cases h)]
      simp [Term.le, Term.lt]
    | add c d =>
      have hd := (Term.wf_add_iff c d).mp ht
      by_cases he : a = c
      · subst c
        simp only [succTerm, Term.lt, ↓reduceIte, Term.le, Term.add.injEq, true_and]
        exact ihb hb.2.2.1 hd.2.2.1
      · simp [succTerm, Term.le, Term.lt, he]
    | inacc n c =>
      by_cases he : a = .inacc n c
      · subst a
        rw [succTerm, Term.lt]
        simp only [↓reduceIte, not_lt_one hb.2.2.1 hb.2.2.2.1, Term.le, reduceCtorEq,
          decide_false, Bool.false_or, Term.lt, lt_self]
      · simp [succTerm, Term.le, Term.lt, he]
    | psi u c =>
      by_cases he : a = .psi u c
      · subst a
        rw [succTerm, Term.lt]
        simp only [↓reduceIte, not_lt_one hb.2.2.1 hb.2.2.2.1, Term.le, reduceCtorEq,
          decide_false, Bool.false_or, Term.lt, lt_self]
      · simp [succTerm, Term.le, Term.lt, he]
  | inacc n a _ =>
    cases t with
    | zero =>
      rw [show succTerm .zero = Term.one from rfl, principal_not_lt_one rfl hs]
      simp [Term.le, Term.lt]
    | add c d => simp [succTerm, Term.le, Term.lt]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]

  | psi u a _ _ =>
    cases t with
    | zero =>
      rw [show succTerm .zero = Term.one from rfl, principal_not_lt_one rfl hs]
      simp [Term.le, Term.lt]
    | add c d => simp [succTerm, Term.le, Term.lt]
    | inacc | psi => simp [succTerm, Term.le, Term.lt]

theorem dropOne_lt_of_lt {s t : Term} (hs : Term.wf s = true) (ht : Term.wf t = true)
    (hlt : Term.lt s t = true) : Term.lt (dropOne s) t = true := by
  by_cases hs0 : s = .zero
  · simpa only [hs0, dropOne] using hlt
  · have ht0 : t ≠ .zero := by
      intro he
      rw [he, CountableTarget.lt_zero] at hlt
      cases hlt
    by_cases hsh : Term.head s = Term.one
    · obtain ⟨m, rfl⟩ := head_one_nat hs hsh
      rw [dropOne_nat]
      by_cases hth : Term.head t = Term.one
      · obtain ⟨n, rfl⟩ := head_one_nat ht hth
        have hn := (natTerm_lt (m + 1) (n + 1)).mp hlt
        exact (natTerm_lt m (n + 1)).mpr (by omega)
      · exact nat_lt_of_head_ne ht ht0 hth m
    · simpa only [dropOne_of_head_ne hsh] using hlt

end Support.TargetArithmetic

namespace Support.OT2

open OCF.Jaeger
open Support.BinaryTranslation (dropOne succTerm)
open Support.TargetArithmetic

def principal (a b : Term) : Term :=
  if b = .zero then .psi Term.bigOmega a
  else if a = .zero then .inacc 0 (dropOne b)
  else .psi (.inacc 0 (succTerm (dropOne b))) (dropOne a)

def assemble (p t : Term) : Term := if t = .zero then p else .add p t

theorem principal_isPrin (a b : Term) : Term.isPrin (principal a b) = true := by
  unfold principal
  split
  · rfl
  · split <;> rfl

theorem assemble_injective {p q t u : Term} (hp : Term.isPrin p = true)
    (hq : Term.isPrin q = true) (he : assemble p t = assemble q u) : p = q ∧ t = u := by
  unfold assemble at he
  by_cases ht : t = .zero <;> by_cases hu : u = .zero
  · simpa only [ht, hu, ↓reduceIte, and_true] using he
  · simp only [ht, hu, ↓reduceIte] at he
    cases p <;> simp_all [Term.isPrin]
  · simp only [ht, hu, ↓reduceIte] at he
    cases q <;> simp_all [Term.isPrin]
  · simpa only [ht, hu, ↓reduceIte, Term.add.injEq] using he

theorem assemble_lt {p q t u : Term} (hp : Term.isPrin p = true)
    (hq : Term.isPrin q = true) :
    Term.lt (assemble p t) (assemble q u) =
      if p = q then Term.lt t u else Term.lt p q := by
  by_cases he : p = q
  · subst q
    by_cases ht : t = .zero <;> by_cases hu : u = .zero
    · simp [assemble, ht, hu, lt_self]
    · cases p <;> simp_all [Term.isPrin, assemble, Term.lt, (zero_lt_iff u).mpr hu]
    · cases p <;> simp_all [Term.isPrin, assemble, Term.lt, lt_self, CountableTarget.lt_zero]
    · simp [assemble, ht, hu, Term.lt]
  · by_cases ht : t = .zero <;> by_cases hu : u = .zero
    · simp [assemble, ht, hu, he]
    · cases p <;> simp_all [Term.isPrin, assemble, Term.lt]
    · cases q <;> simp_all [Term.isPrin, assemble, Term.lt]
    · simp [assemble, ht, hu, he, Term.lt]

theorem zero_le (t : Term) : Term.le .zero t = true := by
  cases t <;> simp [Term.le, Term.lt]

end Support.OT2

namespace Support.OT2

open OCF.Jaeger
open Support.BinaryTranslation (dropOne succTerm)
open Support.TargetArithmetic

theorem mem_H_dropOne {u t z : Term} (hz : z ∈ Term.H u (dropOne t)) :
    z ∈ Term.H u t := by
  cases t with
  | zero => exact hz
  | inacc => exact hz
  | add a b =>
    simp only [dropOne] at hz
    split at hz
    · exact List.mem_append_right _ hz
    · exact hz
  | psi v a =>
    simp only [dropOne] at hz
    split at hz
    · cases hz
    · exact hz

theorem H_succTerm (u t : Term) :
    Term.H u (succTerm t) = Term.H u t ++ Term.H u Term.one := by
  induction t with
  | zero => rfl
  | add a b _ ihb => simp [succTerm, Term.H, ihb, List.append_assoc]
  | inacc | psi => rfl

end Support.OT2

namespace Support.OTQuotient

open new CountableSource

def zeros {lam : Nat} (m : Nat) : Vec (T lam) m := Vec.ofFn m (fun _ => .Z)

theorem zeros_succ {lam : Nat} (m : Nat) :
    zeros (lam := lam) (m + 1) = .snoc m (zeros m) .Z := rfl

theorem zeros_minIdx {lam : Nat} (m : Nat) : T.domVecMinIdx (zeros (lam := lam) m) = none := by
  induction m with
  | zero => rfl
  | succ m ih => simp [zeros_succ, T.domVecMinIdx, ih, T.dom]

def lastVec {lam : Nat} (k : Nat) (a : T lam) : Vec (T lam) (k + 1) := .snoc k (zeros k) a

theorem lastVec_idx {lam : Nat} (k : Nat) (a : T lam) (i : Fin (k + 1)) :
    (lastVec k a).idx i = if i.val = k then a else .Z := by
  simp only [lastVec, Vec.idx, zeros, Vec.ofFn_idx]
  split
  · rename_i h
    rw [ite_eq_right (by omega)]
  · rename_i h
    rw [ite_eq_left (by omega)]

theorem LF_step (k n : Nat) :
    T.LF (k + 1) (n + 1) = .P (lastVec k (T.LF (k + 1) n)) .Z := by
  rw [T.LF]
  congr 1
  apply vec_ext
  intro i
  rw [Vec.ofFn_idx, lastVec_idx]

theorem LF_one (k : Nat) : T.LF (k + 1) 1 = (T.ofNat 1 : T (k + 1)) := by
  rw [LF_step, T.LF, T.ofNat, T.ofNat]
  congr 1

theorem dom_one {lam : Nat} : T.dom (T.ofNat 1 : T lam) = .one := by
  simp only [T.ofNat, T.dom, ↓reduceIte]
  rw [show Vec.ofFn lam (fun _ => T.Z) = zeros lam from rfl, zeros_minIdx]

theorem fund_one {lam : Nat} (t : T lam) : T.fund (T.ofNat 1) t = .Z := by
  rw [T.ofNat, T.ofNat, T.fund]
  simp only [↓reduceIte]
  rw [show Vec.ofFn lam (fun _ => T.Z) = zeros lam from rfl, zeros_minIdx]

theorem minIdx_lastVec {lam : Nat} (k : Nat) (a : T lam) :
    T.domVecMinIdx (lastVec k a) =
      if T.dom a = .zero then none else some (Fin.last k, T.dom a) := by
  simp [lastVec, T.domVecMinIdx, zeros_minIdx]

theorem padVec_zeros {lam : Nat} (m : Nat) : padVec (zeros (lam := lam) m) = zeros m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [zeros_succ, padVec, ih, pad]

theorem padVec_lastVec {lam : Nat} (k : Nat) (a : T lam) :
    padVec (lastVec k a) = lastVec k (pad a) := by
  simp [lastVec, padVec, padVec_zeros]

theorem padVec_lowVec {lam : Nat} (k : Nat) (a : T lam) :
    padVec (lowVec k a) = lowVec k (pad a) := by
  apply vec_ext
  intro i
  rw [padVec_idx, lowVec_idx, lowVec_idx]
  split <;> rfl

theorem padFull_lowVec (k : Nat) (a : T (k + 1)) :
    padFull (lowVec k a) = lowVec (k + 1) (pad a) := by
  simp only [padFull, padVec_lowVec, lowVec_succ]

def dimensionTop (k : Nat) : T (k + 2) := .P (lastVec (k + 1) (T.ofNat 1)) .Z

theorem dimensionTop_LF (k : Nat) : dimensionTop k = T.LF (k + 2) 2 := by
  rw [LF_step, LF_one]
  rfl

theorem dimensionTop_dom (k : Nat) :
    T.dom (dimensionTop k) = .Omega (lastVec (k + 1) (T.ofNat 1)) := by
  rw [dimensionTop, T.dom]
  simp [minIdx_lastVec, dom_one, Fin.val_last]

theorem dimensionTop_fund (k : Nat) (x : T (k + 2)) :
    T.fund (dimensionTop k) x = .P (.snoc (k + 1) (lastVec k x) .Z) .Z := by
  rw [dimensionTop, T.fund]
  simp only [↓reduceIte, minIdx_lastVec, dom_one, reduceCtorEq, Fin.last]
  congr 1
  have hi : (lastVec (k + 1) (T.ofNat 1 : T (k + 2)))[(⟨k + 1, by omega⟩ : Fin (k + 2))] =
      T.ofNat 1 := by
    simp [GetElem.getElem, lastVec_idx]
  rw [hi, fund_one]
  apply vec_ext
  intro i
  simp only [vec_rplc_idx, lastVec_idx, Vec.idx]
  by_cases hk : i.val = k <;> by_cases hk1 : i.val = k + 1
  · omega
  · simp [hk]
  · simp [hk1]
  · have hil : i.val < k + 1 := by omega
    simp [hk, hk1, hil]

theorem dimensionTop_iter (k n : Nat) :
    T.iter (T.fund (dimensionTop k)) (T.ofNat n) = pad (T.LF (k + 1) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [T.ofNat, T.iter, ih, dimensionTop_fund, LF_step]
    simp only [pad, padVec_lastVec]

def lowerBase (k n : Nat) : T (k + 1) := .P (lowVec k (T.LF (k + 1) n)) .Z

def dimensionBound (k : Nat) : T (k + 2) := .P (lowVec (k + 1) (dimensionTop k)) .Z

theorem dimensionBound_isOT (k : Nat) : T.isOT (k + 2) (dimensionBound k) := by
  simpa only [dimensionBound, dimensionTop_LF, lowVec] using T.isOT.base_succ (k + 1) 2

theorem dimensionBound_fund (k n : Nat) :
    T.fund (dimensionBound k) (T.ofNat n) = pad (lowerBase k (n + 1)) := by
  rw [dimensionBound, T.fund]
  simp only [↓reduceIte, minIdx_lowVec, dimensionTop_dom, reduceCtorEq]
  have hlt : Vec.lt (lowVec (k + 1) (dimensionTop k))
      (lastVec (k + 1) (T.ofNat 1)) := by
    rw [lowVec_succ]
    rfl
  rw [ite_eq_left hlt]
  simp only [GetElem.getElem, lowVec_idx, ↓reduceIte]
  rw [dimensionTop_iter, dimensionTop_fund, lowVec_rplc_zero]
  rw [lowerBase, show pad (.P (lowVec k (T.LF (k + 1) (n + 1))) .Z) =
      .P (padFull (lowVec k (T.LF (k + 1) (n + 1)))) .Z from rfl,
    padFull_lowVec, LF_step]
  simp only [pad, padVec_lastVec]

theorem pad_lowerBase_isOT (k n : Nat) : T.isOT (k + 2) (pad (lowerBase k n)) := by
  cases n with
  | zero =>
    have he : pad (lowerBase k 0) = (T.ofNat 1 : T (k + 2)) := by
      rw [lowerBase, T.LF]
      have hv : lowVec k (T.Z : T (k + 1)) = zeros (k + 1) := by
        apply vec_ext
        intro i
        simp [lowVec_idx, zeros, Vec.ofFn_idx]
      rw [hv]
      change pad (T.ofNat 1 : T (k + 1)) = T.ofNat 1
      exact pad_ofNat 1
    rw [he]
    simpa [T.LF, T.ofNat, Vec.ofFn] using T.isOT.base_succ (k + 1) 0
  | succ n =>
    rw [← dimensionBound_fund k n]
    exact T.isOT.step _ _ (dimensionBound_isOT k) n

theorem isOT_pad {lam : Nat} {s : T lam} (hs : T.isOT lam s) :
    T.isOT (lam + 1) (pad s) := by
  induction hs with
  | base_0 n =>
    have he : T.LF 0 n = (T.ofNat n : T 0) := by
      induction n with
      | zero => rfl
      | succ n ih => simp [T.LF, T.ofNat, ih, Vec.ofFn]
    rw [he, pad_ofNat]
    exact FirstLimit.ofNat_isOT_one n
  | base_succ k n => exact pad_lowerBase_isOT k n
  | step lam s hs n ih =>
    rw [← fund_pad, pad_ofNat]
    exact T.isOT.step _ _ ih n

theorem isOT_liftBy {lam : Nat} (k : Nat) {s : T lam} (hs : T.isOT lam s) :
    T.isOT (lam + k) (liftBy k s) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact isOT_pad ih

theorem isOT_cast {lam m : Nat} (e : lam = m) {s : T lam} (hs : T.isOT lam s) :
    T.isOT m (e ▸ s) := by
  cases e
  exact hs

theorem isOT_promote {lam m : Nat} (h : lam ≤ m) {s : T lam} (hs : T.isOT lam s) :
    T.isOT m (promote h s) :=
  isOT_cast (Nat.add_sub_of_le h) (isOT_liftBy (m - lam) hs)

def promoteOT {lam m : Nat} (h : lam ≤ m) (s : T.OT lam) : T.OT m :=
  ⟨promote h s.val, isOT_promote h s.property⟩

theorem classOf_promoteOT {lam m : Nat} (h : lam ≤ m) (s : T.OT lam) :
    classOf ⟨m, promoteOT h s⟩ = classOf ⟨lam, s⟩ :=
  (class_eq_iff _ _).mpr (code_promote h s.val)

theorem isOT_ofNat (lam n : Nat) : T.isOT lam (T.ofNat n) := by
  have h := isOT_promote (Nat.zero_le lam) (FiniteCorrespondence.ofNat_isOT_zero n)
  have he : promote (Nat.zero_le lam) (T.ofNat n : T 0) = (T.ofNat n : T lam) := by
    apply code_injective
    rw [code_promote, FiniteCorrespondence.code_ofNat, FiniteCorrespondence.code_ofNat]
  rwa [he] at h

def HasDimensionWitness (lam : Nat) (q : Classes) : Prop :=
  ∃ s : T.OT lam, classOf ⟨lam, s⟩ = q

theorem hasDimensionWitness_mono {lam m : Nat} (h : lam ≤ m) {q : Classes}
    (hq : HasDimensionWitness lam q) : HasDimensionWitness m q := by
  obtain ⟨s, hs⟩ := hq
  exact ⟨promoteOT h s, (classOf_promoteOT h s).trans hs⟩

theorem hasDimensionWitness_iff (q : Classes) (lam : Nat) :
    HasDimensionWitness lam q ↔ minDimension q ≤ lam := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h
    exact dimensionWitness_minimal q ⟨lam, s⟩ hs
  · intro h
    exact hasDimensionWitness_mono h (minDimension_spec q)

end Support.OTQuotient

namespace Support.HigherBoundary

open new OCF.Jaeger OTQuotient CountableSource BinaryTranslation

theorem compare_lowVec {lam : Nat} (k : Nat) (a b : T lam) :
    compareVec (lowVec k a) (lowVec k b) = compareT a b := by
  induction k with
  | zero => simp only [lowVec_zero, compareVec]; cases compareT a b <;> rfl
  | succ k ih => simp only [lowVec_succ, compareVec, compareT]; exact ih

end Support.HigherBoundary

namespace Support.DimensionCut

open new Support.OTQuotient Support.CountableSource

theorem dom_eq_zero_iff (s : T lam) : T.dom s = .zero ↔ s = .Z := by
  cases s with
  | Z => simp [T.dom]
  | P xs b =>
    constructor
    · intro h
      rw [T.dom] at h
      by_cases hb : b = .Z
      · simp only [hb, ↓reduceIte] at h
        cases hm : T.domVecMinIdx xs with
        | none => simp [hm] at h
        | some p =>
          obtain ⟨m, d⟩ := p
          cases d <;> simp only [hm] at h
          all_goals first | cases h | (split at h <;> cases h)
      · simp only [hb, ↓reduceIte] at h
        exact False.elim (hb ((dom_eq_zero_iff b).mp h))
    · intro h; cases h
termination_by T.size s
decreasing_by simp only [T.size]; omega

theorem minIdx_none_iff {lam m : Nat} (xs : Vec (T lam) m) :
    T.domVecMinIdx xs = none ↔ xs = zeros m := by
  constructor
  · intro h
    induction xs with
    | nil => rfl
    | snoc m xs x ih =>
      rw [T.domVecMinIdx] at h
      cases he : T.domVecMinIdx xs with
      | some p => simp [he] at h
      | none =>
        simp only [he] at h
        have hx : T.dom x = .zero := by
          by_cases hx : T.dom x = .zero
          · exact hx
          · simp [hx] at h
        rw [(dom_eq_zero_iff x).mp hx, ih he, zeros_succ]
  · rintro rfl
    exact zeros_minIdx m

theorem minIdx_spec {lam m : Nat} (xs : Vec (T lam) m) {i : Fin m} {d : Dom lam}
    (h : T.domVecMinIdx xs = some (i, d)) :
    d = T.dom (xs.idx i) ∧ d ≠ .zero ∧ ∀ j : Fin m, j.val < i.val → xs.idx j = .Z := by
  induction xs with
  | nil => cases h
  | snoc m xs x ih =>
    rw [T.domVecMinIdx] at h
    cases he : T.domVecMinIdx xs with
    | none =>
      simp only [he] at h
      by_cases hx : T.dom x = .zero
      · simp [hx] at h
      · simp only [hx, ↓reduceIte] at h
        cases h
        refine ⟨by simp [Vec.idx], hx, ?_⟩
        intro j hj
        change j.val < m at hj
        have hz := (minIdx_none_iff xs).mp he
        simp [Vec.idx, hj, hz, zeros, Vec.ofFn_idx]
    | some p =>
      obtain ⟨k, e⟩ := p
      simp only [he] at h
      cases h
      have hs := ih he
      refine ⟨by simpa only [vec_snoc_idx_cast] using hs.1, hs.2.1, ?_⟩
      intro j hj
      have hjm : j.val < m := by have := k.isLt; omega
      simpa only [Vec.idx, hjm, ↓reduceDIte] using hs.2.2 ⟨j.val, hjm⟩ hj

theorem dom_one_principal {lam : Nat} (xs : Vec (T lam) lam)
    (h : T.dom (.P xs .Z) = .one) : xs = zeros lam := by
  apply (minIdx_none_iff xs).mp
  rw [T.dom] at h
  simp only [↓reduceIte] at h
  cases hm : T.domVecMinIdx xs with
  | none => rfl
  | some p =>
    obtain ⟨i, d⟩ := p
    cases d <;> simp only [hm] at h
    all_goals first | cases h | (split at h <;> cases h)

theorem fund_zero_of_dom_one {lam : Nat} {s : T lam}
    (hd : T.dom s = .one) (hf : T.fund s .Z = .Z) : s = T.ofNat 1 := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      rw [dom_one_principal xs hd]
      rfl
    · rw [T.fund, ite_eq_right hb] at hf
      cases hf

theorem compareVec_zero_not_lt {lam m : Nat} (xs : Vec (T lam) m) :
    compareVec xs (zeros m) ≠ .lt := by
  induction xs with
  | nil => intro h; cases h
  | snoc m xs x ih =>
    cases x with
    | Z => simpa only [zeros_succ, compareVec, compareT] using ih
    | P ys b => intro h; cases h

theorem nonzero_not_below_one {lam : Nat} {s : T lam} (hs : s ≠ .Z) :
    compareT s (T.ofNat 1) ≠ .lt := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P xs b =>
    change (match compareVec xs (zeros lam) with
      | .eq => compareT b .Z
      | o => o) ≠ .lt
    cases he : compareVec xs (zeros lam) with
    | lt => exact False.elim (compareVec_zero_not_lt xs he)
    | gt => intro h; cases h
    | eq => cases b <;> intro h <;> cases h

def RootLow (s : T (k + 2)) : Prop :=
  match s with
  | .Z => True
  | .P (.snoc _ _ x) _ => x = .Z

theorem rootLow_principal {k : Nat} (xs : Vec (T (k + 2)) (k + 2)) (b : T (k + 2)) :
    RootLow (.P xs b) ↔ xs.idx (Fin.last (k + 1)) = .Z := by
  cases xs with
  | snoc m xs x => simp [RootLow, vec_snoc_idx_last]

theorem below_dimensionTop_iff_rootLow {k : Nat} (s : T (k + 2)) :
    compareT s (dimensionTop k) = .lt ↔ RootLow s := by
  cases s with
  | Z => exact ⟨fun _ => trivial, fun _ => rfl⟩
  | P xs b =>
    cases xs with
    | snoc m xs x =>
      by_cases hx : x = .Z
      · subst x
        simp [dimensionTop, lastVec, compareT, compareVec, T.ofNat, RootLow]
      · have hn : ¬ RootLow (.P (.snoc (k + 1) xs x) b) := hx
        refine ⟨?_, fun h => False.elim (hn h)⟩
        intro h
        change (match (match compareT x (T.ofNat 1) with
          | .eq => compareVec xs (zeros (k + 1))
          | o => o) with
          | .eq => compareT b .Z
          | o => o) = .lt at h
        cases he : compareT x (T.ofNat 1) with
        | lt => exact False.elim (nonzero_not_below_one hx he)
        | gt => simp [he] at h
        | eq =>
          cases hp : compareVec xs (zeros (k + 1)) with
          | lt => exact False.elim (compareVec_zero_not_lt xs hp)
          | gt => simp [he, hp] at h
          | eq => cases b <;> simp [he, hp, compareT] at h

theorem minIdx_last_repr {k : Nat} (xs : Vec (T (k + 2)) (k + 2))
    {i : Fin (k + 2)} {d : Dom (k + 2)} (hm : T.domVecMinIdx xs = some (i, d))
    (hi : i.val = k + 1) : xs = lastVec (k + 1) (xs.idx i) := by
  have hs := minIdx_spec xs hm
  apply vec_ext
  intro j
  rw [lastVec_idx]
  by_cases hj : j.val = k + 1
  · have he : j = i := Fin.ext (hj.trans hi.symm)
    simp [he, hi]
  · have hji : j.val < i.val := by have := j.isLt; omega
    simp [hj, hs.2.2 j hji]

theorem update_cross_spec {k : Nat} (xs : Vec (T (k + 2)) (k + 2))
    {i : Fin (k + 2)} {d : Dom (k + 2)} (hm : T.domVecMinIdx xs = some (i, d))
    (hx : xs.idx (Fin.last (k + 1)) ≠ .Z) (y : T (k + 2))
    (hl : compareT (.P (xs.rplc i y) .Z) (dimensionTop k) = .lt) :
    i.val = k + 1 ∧ y = .Z ∧ xs = lastVec (k + 1) (xs.idx i) := by
  have hz := (rootLow_principal (xs.rplc i y) .Z).mp
    ((below_dimensionTop_iff_rootLow _).mp hl)
  rw [vec_rplc_idx] at hz
  have hi : i.val = k + 1 := by
    by_cases hi : i.val = k + 1
    · exact hi
    · have hn : (Fin.last (k + 1)).val ≠ i.val := by simp only [Fin.val_last]; omega
      rw [ite_eq_right hn] at hz
      exact False.elim (hx hz)
  have hy : y = .Z := by simpa only [Fin.val_last, hi, ↓reduceIte] using hz
  exact ⟨hi, hy, minIdx_last_repr xs hm hi⟩

theorem update_cross_eq_one {k : Nat} (xs : Vec (T (k + 2)) (k + 2))
    {i : Fin (k + 2)} {d : Dom (k + 2)} (hm : T.domVecMinIdx xs = some (i, d))
    (hx : xs.idx (Fin.last (k + 1)) ≠ .Z) (y : T (k + 2))
    (hl : compareT (.P (xs.rplc i y) .Z) (dimensionTop k) = .lt) :
    .P (xs.rplc i y) .Z = T.ofNat 1 := by
  obtain ⟨hi, rfl, _⟩ := update_cross_spec xs hm hx y hl
  have hs := minIdx_spec xs hm
  have he : xs.rplc i .Z = zeros (k + 2) := by
    apply vec_ext
    intro j
    rw [vec_rplc_idx]
    have hz : (zeros (lam := k + 2) (k + 2)).idx j = .Z := by simp [zeros, Vec.ofFn_idx]
    rw [hz]
    split
    · rfl
    · rename_i hji
      have hjlt : j.val < i.val := by have := j.isLt; omega
      exact hs.2.2 j hjlt
  rw [he]
  rfl

theorem mul_principal_node {lam : Nat} (xs ys : Vec (T lam) lam) (b : T lam) :
    T.mul (.P xs .Z) (.P ys b) = .P xs (T.mul (.P xs .Z) b) := rfl

theorem fund_cross_dimensionTop {k : Nat} (s t : T (k + 2))
    (hs : compareT s (dimensionTop k) ≠ .lt)
    (hl : compareT (T.fund s t) (dimensionTop k) = .lt) :
    T.fund s t = .Z ∨ T.fund s t = T.ofNat 1 ∨ s = dimensionTop k := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P xs b =>
    have hx : xs.idx (Fin.last (k + 1)) ≠ .Z := by
      intro hz
      exact hs ((below_dimensionTop_iff_rootLow _).mpr ((rootLow_principal xs b).mpr hz))
    by_cases hb : b = .Z
    · subst b
      rw [T.fund] at hl ⊢
      simp only [↓reduceIte] at hl ⊢
      cases hm : T.domVecMinIdx xs with
      | none =>
        have hz := (minIdx_none_iff xs).mp hm
        exact False.elim (hx (by simp [hz, zeros, Vec.ofFn_idx]))
      | some p =>
        obtain ⟨i, d⟩ := p
        simp only [hm] at hl ⊢
        cases d with
        | zero | omega =>
          exact Or.inr (Or.inl (update_cross_eq_one xs hm hx _ hl))
        | Omega ys =>
          by_cases hv : Vec.lt xs ys
          · simp only [hv, ↓reduceIte] at hl ⊢
            exact Or.inr (Or.inl (update_cross_eq_one xs hm hx _ hl))
          · simp only [hv, ↓reduceIte] at hl ⊢
            exact Or.inr (Or.inl (update_cross_eq_one xs hm hx _ hl))
        | one =>
          obtain ⟨j, hj⟩ := i
          cases j with
          | zero =>
            cases t with
            | Z => exact Or.inl rfl
            | P ys c =>
              rw [mul_principal_node] at hl
              have hz := (rootLow_principal _ _).mp ((below_dimensionTop_iff_rootLow _).mp hl)
              rw [vec_rplc_idx] at hz
              have hn : (Fin.last (k + 1)).val ≠ (⟨0, hj⟩ : Fin (k + 2)).val := by
                simp only [Fin.val_last]; omega
              rw [ite_eq_right hn] at hz
              exact False.elim (hx hz)
          | succ j =>
            let i : Fin (k + 2) := ⟨j + 1, hj⟩
            let p : Fin (k + 2) := ⟨j, Nat.lt_of_succ_lt hj⟩
            have hsmall : compareT (.P (xs.rplc i (T.fund (xs.idx i) .Z)) .Z)
                (dimensionTop k) = .lt := by
              apply (below_dimensionTop_iff_rootLow _).mpr
              apply (rootLow_principal _ _).mpr
              have hz := (rootLow_principal _ _).mp ((below_dimensionTop_iff_rootLow _).mp hl)
              rw [vec_rplc_idx] at hz
              have hn : (Fin.last (k + 1)).val ≠ p.val := by
                simp only [Fin.val_last, p]; omega
              rwa [ite_eq_right hn] at hz
            obtain ⟨hi, hf, he⟩ := update_cross_spec xs hm hx _ hsmall
            have hd : T.dom (xs.idx i) = .one := (minIdx_spec xs hm).1.symm
            have hxone := fund_zero_of_dom_one hd hf
            exact Or.inr (Or.inr (by rw [he, hxone]; rfl))
    · rw [T.fund, ite_eq_right hb] at hl
      have hz := (rootLow_principal xs _).mp ((below_dimensionTop_iff_rootLow _).mp hl)
      exact False.elim (hx hz)

theorem outer_below_dimensionBound_iff {k : Nat} (a b : T (k + 2)) :
    compareT (.P (lowVec (k + 1) a) b) (dimensionBound k) = .lt ↔
      compareT a (dimensionTop k) = .lt := by
  simp only [dimensionBound, compareT, HigherBoundary.compare_lowVec]
  cases he : compareT a (dimensionTop k) with
  | lt => simp
  | gt => simp
  | eq => cases b <;> simp [compareT]

theorem dom_one_fund_not_cross {k : Nat} (s : T (k + 2))
    (hd : T.dom s = .one) (hs : compareT s (dimensionTop k) ≠ .lt) :
    compareT (T.fund s .Z) (dimensionTop k) ≠ .lt := by
  cases s with
  | Z => cases hd
  | P xs b =>
    by_cases hb : b = .Z
    · subst b
      have he := dom_one_principal xs hd
      exact False.elim (hs ((below_dimensionTop_iff_rootLow _).mpr
        ((rootLow_principal xs .Z).mpr (by simp [he, zeros, Vec.ofFn_idx]))))
    · intro hl
      rw [T.fund, ite_eq_right hb] at hl
      have hz := (rootLow_principal xs _).mp ((below_dimensionTop_iff_rootLow _).mp hl)
      exact hs ((below_dimensionTop_iff_rootLow _).mpr ((rootLow_principal xs b).mpr hz))

theorem padded_small_argument {k : Nat} {a : T (k + 2)} (ha : a = .Z ∨ a = T.ofNat 1) :
    ∃ s : T (k + 1), T.isOT (k + 1) s ∧ pad s = .P (lowVec (k + 1) a) .Z := by
  rcases ha with rfl | rfl
  · refine ⟨T.ofNat 1, isOT_ofNat _ _, ?_⟩
    rw [pad_ofNat]
    change T.P (zeros (lam := k + 2) (k + 2)) T.Z = T.P (lowVec (k + 1) T.Z) T.Z
    congr 1
    apply vec_ext
    intro i
    simp [zeros, lowVec_idx, Vec.ofFn_idx]
  · refine ⟨lowerBase k 1, T.isOT.base_succ k 1, ?_⟩
    rw [lowerBase, LF_one]
    change T.P (padFull (lowVec k (T.ofNat (lam := k + 1) 1))) T.Z = _
    rw [padFull_lowVec, pad_ofNat]

theorem collapsed_argument_cross_padded {k : Nat} (a x : T (k + 2)) (n : Nat)
    (ha : compareT a (dimensionTop k) ≠ .lt)
    (he : T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) =
      .P (lowVec (k + 1) (T.fund a x)) .Z)
    (hl : compareT (T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n))
      (dimensionBound k) = .lt) :
    ∃ s : T (k + 1), T.isOT (k + 1) s ∧
      pad s = T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) := by
  have hx : compareT (T.fund a x) (dimensionTop k) = .lt :=
    (outer_below_dimensionBound_iff _ _).mp (he ▸ hl)
  rcases fund_cross_dimensionTop a x ha hx with hf | hf | rfl
  · rw [he]
    exact padded_small_argument (Or.inl hf)
  · rw [he]
    exact padded_small_argument (Or.inr hf)
  · refine ⟨lowerBase k (n + 1), T.isOT.base_succ k (n + 1), ?_⟩
    exact (dimensionBound_fund k n).symm

theorem outer_step_cross_padded {k : Nat} {s : T (k + 2)} (ho : Outer s) (n : Nat)
    (hs : compareT s (dimensionBound k) ≠ .lt)
    (hl : compareT (T.fund s (T.ofNat n)) (dimensionBound k) = .lt) :
    ∃ u : T (k + 1), T.isOT (k + 1) u ∧ pad u = T.fund s (T.ofNat n) := by
  cases ho with
  | zero => exact False.elim (hs rfl)
  | cons a b hb =>
    have ha : compareT a (dimensionTop k) ≠ .lt :=
      fun h => hs ((outer_below_dimensionBound_iff a b).mpr h)
    by_cases hb0 : b = .Z
    · subst b
      cases hd : T.dom a with
      | zero =>
        have he : T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) = .Z := by
          simp [T.fund, minIdx_lowVec, hd]
        exact ⟨T.ofNat 0, isOT_ofNat _ _, by rw [he]; rfl⟩
      | one =>
        have he : T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) =
            T.mul (.P (lowVec (k + 1) (T.fund a .Z)) .Z) (T.ofNat n) := by
          simp only [T.fund, ↓reduceIte, minIdx_lowVec, hd, reduceCtorEq,
            ↓reduceIte, GetElem.getElem, lowVec_idx, lowVec_rplc_zero]
        cases n with
        | zero => exact ⟨T.ofNat 0, isOT_ofNat _ _, by rw [he]; rfl⟩
        | succ n =>
          rw [he, T.ofNat, mul_principal_node] at hl
          have hf := (outer_below_dimensionBound_iff _ _).mp hl
          exact False.elim (dom_one_fund_not_cross a hd ha hf)
      | omega =>
        have he : T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) =
            .P (lowVec (k + 1) (T.fund a (T.ofNat n))) .Z := by
          simp only [T.fund, ↓reduceIte, minIdx_lowVec, hd, reduceCtorEq,
            ↓reduceIte, GetElem.getElem, lowVec_idx, lowVec_rplc_zero]
        exact collapsed_argument_cross_padded a _ n ha he hl
      | Omega ys =>
        by_cases hv : Vec.lt (lowVec (k + 1) a) ys
        · have he : T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) =
              .P (lowVec (k + 1) (T.fund a (T.iter (T.fund a) (T.ofNat n)))) .Z := by
            simp only [T.fund, ↓reduceIte, minIdx_lowVec, hd, reduceCtorEq,
              ↓reduceIte, hv, GetElem.getElem, lowVec_idx, lowVec_rplc_zero]
          exact collapsed_argument_cross_padded a _ n ha he hl
        · have he : T.fund (.P (lowVec (k + 1) a) .Z) (T.ofNat n) =
              .P (lowVec (k + 1) (T.fund a (T.ofNat n))) .Z := by
            simp only [T.fund, ↓reduceIte, minIdx_lowVec, hd, reduceCtorEq,
              ↓reduceIte, hv, GetElem.getElem, lowVec_idx, lowVec_rplc_zero]
          exact collapsed_argument_cross_padded a _ n ha he hl
    · rw [T.fund, ite_eq_right hb0] at hl
      have h := (outer_below_dimensionBound_iff _ _).mp hl
      exact False.elim (ha h)

theorem LF_positive (k n : Nat) : T.LF (k + 1) (n + 1) ≠ .Z := by
  rw [LF_step]
  intro h; cases h

private theorem generated_small_cast {lam : Nat} {s : T lam} (h : T.isOT lam s) :
    ∀ k (e : lam = k + 2), compareT (e ▸ s) (dimensionBound k) = .lt →
      ∃ u : T (k + 1), T.isOT (k + 1) u ∧ pad u = e ▸ s := by
  induction h with
  | base_0 n => intro k e; omega
  | base_succ lam n =>
    intro k e hl
    have he : lam = k + 1 := by omega
    subst lam
    cases e
    cases n with
    | zero => exact padded_small_argument (Or.inl rfl)
    | succ n =>
      cases n with
      | zero =>
        exact padded_small_argument (Or.inr (LF_one (k + 1)))
      | succ n =>
        have ha := (outer_below_dimensionBound_iff _ _).mp hl
        have hr := (below_dimensionTop_iff_rootLow _).mp ha
        rw [LF_step] at hr
        have hz := (rootLow_principal _ _).mp hr
        simp only [lastVec, vec_snoc_idx_last] at hz
        exact False.elim (LF_positive (k + 1) n hz)
  | step lam s hs n ih =>
    intro k e hl
    subst lam
    change compareT (T.fund s (T.ofNat n)) (dimensionBound k) = .lt at hl
    change ∃ u : T (k + 1), T.isOT (k + 1) u ∧ pad u = T.fund s (T.ofNat n)
    by_cases hsmall : compareT s (dimensionBound k) = .lt
    · obtain ⟨u, hu, he⟩ := ih k rfl hsmall
      refine ⟨T.fund u (T.ofNat n), T.isOT.step _ _ hu n, ?_⟩
      rw [← fund_pad, pad_ofNat, he]
    · exact outer_step_cross_padded (CountableSource.isOT_outer hs) n hsmall hl

theorem isOT_below_dimensionBound {k : Nat} {s : T (k + 2)}
    (hs : T.isOT (k + 2) s) (hl : compareT s (dimensionBound k) = .lt) :
    ∃ u : T.OT (k + 1), pad u.val = s := by
  obtain ⟨u, hu, he⟩ := generated_small_cast hs k rfl hl
  exact ⟨⟨u, hu⟩, he⟩

def boundaryElement (k : Nat) : AllOT :=
  ⟨k + 2, dimensionBound k, dimensionBound_isOT k⟩

def boundaryClass (k : Nat) : Classes := classOf (boundaryElement k)

theorem pad_below_dimensionTop (s : T (k + 1)) :
    compareT (pad s) (dimensionTop k) = .lt := by
  apply (below_dimensionTop_iff_rootLow _).mpr
  cases s <;> simp [pad, RootLow]

theorem pad_outer_below_dimensionBound {k : Nat} {s : T (k + 1)} (hs : Outer s) :
    compareT (pad s) (dimensionBound k) = .lt := by
  cases hs with
  | zero => rfl
  | cons a b hb =>
    change compareT (.P (padFull (lowVec k a)) (pad b)) (dimensionBound k) = .lt
    rw [padFull_lowVec]
    exact (outer_below_dimensionBound_iff _ _).mpr (pad_below_dimensionTop a)

theorem dimension_witness_below_boundary {k : Nat} {q : Classes}
    (hq : HasDimensionWitness (k + 1) q) : ClassLT q (boundaryClass k) := by
  obtain ⟨s, rfl⟩ := hq
  change compareCode (code s.val) (code (dimensionBound k)) = .lt
  rw [← code_pad s.val, compareCode_code]
  exact pad_outer_below_dimensionBound (CountableSource.isOT_outer s.property)

theorem dimension_witness_iff_below_boundary (k : Nat) (q : Classes) :
    HasDimensionWitness (k + 1) q ↔ ClassLT q (boundaryClass k) := by
  constructor
  · exact dimension_witness_below_boundary
  · intro hq
    apply (hasDimensionWitness_iff q (k + 1)).mpr
    apply Nat.le_of_not_gt
    intro hn
    obtain ⟨s, hs⟩ := minDimension_spec q
    generalize hd : minDimension q = d at s hs
    cases d with
    | zero => omega
    | succ d =>
      cases d with
      | zero => omega
      | succ m =>
        have hkm : k ≤ m := by omega
        have hm : ClassLT q (boundaryClass m) := by
          by_cases he : k = m
          · simpa only [he] using hq
          · have hkdim : k + 2 ≤ m + 1 := by omega
            have hkw : HasDimensionWitness (m + 1) (boundaryClass k) :=
              hasDimensionWitness_mono hkdim ⟨(boundaryElement k).2, rfl⟩
            exact classLT_trans hq (dimension_witness_below_boundary hkw)
        rw [← hs] at hm
        change compareCode (code s.val) (code (dimensionBound m)) = .lt at hm
        rw [compareCode_code] at hm
        obtain ⟨u, hu⟩ := isOT_below_dimensionBound s.property hm
        have he : classOf ⟨m + 1, u⟩ = q := by
          rw [← hs]
          apply (class_eq_iff _ _).mpr
          rw [← hu, code_pad]
        have hmin := dimensionWitness_minimal q ⟨m + 1, u⟩ he
        change minDimension q ≤ m + 1 at hmin
        omega

end Support.DimensionCut

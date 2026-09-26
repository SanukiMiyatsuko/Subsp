import SubspRepo.stop_surj_general

open T

/-
WIP for the general surjectivity proof.

This file intentionally records the stable higher-coordinate infrastructure reached
during the 2026-09-26 exploration.  The unfinished decoder experiments live in
DecodeGen.lean / Probe*.lean and are not imported by Subsp/.
-/

def surj_vcons {A : Type} {k : Nat} (a : A) : new.Vec A k → new.Vec A (k + 1)
| .nil => .snoc 0 .nil a
| .snoc n xs x => .snoc (n + 1) (surj_vcons a xs) x

def surj_hsum {lam : Nat} : {k : Nat} → new.Vec (new.T lam) k → T
| 0, .nil => T.Z
| _ + 1, .snoc m xs x =>
    T.add (T.card_times m (T.early_collapse (trans x))) (surj_hsum xs)

def surj_hfound {lam : Nat} : {k : Nat} → new.Vec (new.T lam) k → Bool
| 0, .nil => false
| _ + 1, .snoc _ xs x =>
    match x with
    | new.T.Z => surj_hfound xs
    | new.T.P _ _ => true

theorem surj_transAux_vcons {lam k : Nat}
    (a0 : new.T lam) (v : new.Vec (new.T lam) k) :
    transAux (surj_vcons a0 v) =
      (surj_hfound v, surj_hsum v, trans a0) := by
  induction v with
  | nil =>
      rw [surj_vcons, transAux.eq_2, surj_hfound, surj_hsum]
  | snoc n xs x ih =>
      rw [surj_vcons, transAux.eq_3, ih, surj_hsum]
      cases x with
      | Z =>
          rw [surj_hfound]
      | P ls add =>
          rw [surj_hfound]

#print axioms surj_transAux_vcons

theorem surj_vcons_toList {A : Type} {k : Nat}
    (a : A) (v : new.Vec A k) :
    new.Vec.toList (surj_vcons a v) = a :: new.Vec.toList v := by
  induction v with
  | nil => rfl
  | snoc n xs x ih =>
      rw [surj_vcons, new.Vec.toList, ih]
      rfl

theorem surj_vcons_all_comp {lam k : Nat}
    (a : new.T lam) (v : new.Vec (new.T lam) k)
    (ha : new.T.isNFComp a)
    (hv : ∀ x : new.T lam, x ∈ new.Vec.toList v → new.T.isNFComp x) :
    ∀ x : new.T lam, x ∈ new.Vec.toList (surj_vcons a v) →
      new.T.isNFComp x := by
  intro x hx
  rw [surj_vcons_toList] at hx
  cases List.mem_cons.mp hx with
  | inl hxa =>
      rw [hxa]
      exact ha
  | inr hxv =>
      exact hv x hxv

#print axioms surj_vcons_toList
#print axioms surj_vcons_all_comp

def T.unone : T → T
| T.Z => T.P 0 T.Z T.Z
| T.P 0 T.Z b => T.P 0 T.Z (T.P 0 T.Z b)
| t => t

theorem surj_one_del_unone (s : T) :
    T.one_del (T.unone s) = s := by
  cases s with
  | Z => rfl
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z => rfl
          | P q c d => rfl
      | succ p => rfl

#print axioms surj_one_del_unone

/-
Next target:
  reconstruct a vector of higher coordinates whose transAux sum is a prescribed
  coefficient component, using T.part, T.uncard1, and surj_unec_good0.

The tempting canonical rule "use only coordinates 0 and 1" passed shallow tests
but failed at depth 4, so it must not be promoted to a theorem without an
additional normalization step.
-/

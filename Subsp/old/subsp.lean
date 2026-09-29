import Subsp.Base

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

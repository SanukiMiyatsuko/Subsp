import Subsp.multi.Base

open multi
open T

namespace emp

inductive Dom where
| zero
| one
| omega

def T.dom (s : T) : Dom :=
  match s with
  | Z => .zero
  | P li add =>
    if add = Z then
      match V.fnz li with
      | none => .one
      | some _ => .omega
    else dom add
termination_by s.size
decreasing_by
  simp only [T.size]
  omega

def T.fund (s t : T) : T :=
  match s with
  | Z => Z
  | P li add =>
    if add = Z then
      match V.fnz li with
      | none => Z
      | some i =>
        match dom (li.get0 i) with
        | .one =>
          let updatedLs := li.set i (fund (li.get0 i) Z)
          match i with
          | 0 => mul (P updatedLs Z) t
          | i' + 1 =>
            let F := fun x => P (updatedLs.set i' x) Z
            iter F t
        | _ => P (li.set i (fund (li.get0 i) t)) Z
    else P li (fund add t)
termination_by s.size
decreasing_by
  all_goals
    simp only [T.size]
    first
    | omega
    | have := V.size_get0_le li i; omega

def T.LF (n : Nat) : V T :=
  match n with
  | 0 => .snoc (ofNat 1) .emp
  | n' + 1 => V.append (LF n') (.snoc Z .emp)

end emp

import Subsp.Buchholz.Base
import Subsp.Base

open T

def T.stand : T → T
| Z => Z
| P s0 s1 s2 =>
  let sts2 := stand s2
  if head sts2 ≤ P s0 s1 Z then
    P s0 s1 sts2
  else sts2

def T.part (n : Nat) : T → T × T
| Z => (Z, Z)
| P s0 s1 s2 =>
  let ps2 := part n s2
  if s0 ≤ n then
    (ps2.1, P s0 s1 ps2.2)
  else
    (P s0 s1 ps2.1, ps2.2)

def T.early_collapse (n : Nat) (s : T) : T :=
  let ps := part n s
  if ps.1 = Z then
    ps.2
  else stand (P n ps.1 ps.2)

def T.one_del : T → T
| P 0 Z s2 => s2
| s => s

def T.card_times (n : Nat) : T → T
| Z => Z
| P s0 s1 s2 =>
  let head : T :=
    if s0 < n then
      if s0 = 0 then
        P n (early_collapse s0 s1) Z
      else P n (stand (P s0 Z (early_collapse s0 s1))) Z
    else if s0 = n then
      if s1 < P n (P 0 Z Z) Z then
        P n (stand (P n Z s1)) Z
      else P s0 s1 Z
    else P s0 s1 Z
  head + card_times n s2

mutual

def trans {lam : Nat} : new.T lam → T
| new.T.Z => T.Z
| new.T.P ls add =>
  let (head, _) := transAux ls
  head + trans add

def transAux {lam k : Nat} : new.Vec (new.T lam) k → T × T
| .nil => (T.P 0 T.Z T.Z, T.Z)
| .snoc 0 .nil a0 =>
  let ta0 := trans a0
  let lower := T.early_collapse 0 ta0
  match a0 with
  | new.T.Z => (T.P 0 T.Z T.Z, lower)
  | _ => (T.P 0 ta0 T.Z, lower)
| .snoc (m + 1) v a =>
  let (headRest, lowerRest) := transAux v
  let ta := trans a
  let idx := m + 1
  let lower := T.card_times idx (T.early_collapse idx ta) + lowerRest
  match a with
  | new.T.Z => (headRest, lower)
  | _ =>
    (T.P idx (T.card_times idx (T.one_del ta) + lowerRest) T.Z, lower)

end

import Subsp.Buchholz.Base
import Subsp.new.Base

open T

def T.stand : T → T
| Z => Z
| P s0 s1 s2 =>
  let sts2 := stand s2
  if head sts2 ≤ P s0 s1 Z then
    P s0 s1 sts2
  else sts2

def T.part : T → T × T
| Z => (Z, Z)
| P s0 s1 s2 =>
  if s0 = 0 then
    (Z, P s0 s1 s2)
  else
    let ps2 := part s2
    (P s0 s1 ps2.1, ps2.2)

def T.early_collapse (s : T) : T :=
  let ps := part s
  if ps.1 = Z then
    s
  else stand (P 0 ps.1 ps.2)

def T.one_del : T → T
| P 0 Z s2 => s2
| s => s

def T.card_times (n : Nat) : T → T
| Z => Z
| P s0 s1 s2 =>
  match n with
  | 0 => P s0 s1 s2
  | n' + 1 =>
    let head : T :=
      if s0 = 0 then
        P 1 (mul (P 1 Z Z) (ofNat n') + early_collapse s1) Z
      else P 1 (mul (P 1 Z Z) (ofNat n) + s1) Z
    head + card_times n s2

mutual

def trans {lam : Nat} : new.T lam → T
| new.T.Z => T.Z
| new.T.P ls add =>
  let (foundAbove0, sumAbove0, transA0) := transAux ls
  if foundAbove0 then
    T.P 1 (T.card_times 1 (T.one_del sumAbove0) + T.early_collapse transA0) (trans add)
  else if transA0 = T.Z then
    T.P 0 T.Z (trans add)
  else
    T.P 0 transA0 (trans add)

def transAux {lam k : Nat} : new.Vec (new.T lam) k → Bool × T × T
| .nil => (false, T.Z, T.Z)
| .snoc 0 .nil a0 => (false, T.Z, trans a0)
| .snoc (m + 1) v a =>
  let (foundRest, sumRest, transA0) := transAux v
  let found : Bool :=
    match a with
    | new.T.Z => foundRest
    | _ => true
  (found, T.card_times m (T.early_collapse (trans a)) + sumRest, transA0)

end

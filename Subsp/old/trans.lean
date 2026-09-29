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
  if s0 ≤ n then
    (Z, P s0 s1 s2)
  else
    let ps2 := part n s2
    (P s0 s1 ps2.1, ps2.2)

def T.early_collapse (n : Nat) (s : T) : T :=
  let ps := part n s
  if ps.1 = Z then
    s
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

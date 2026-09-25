import Subsp.Buchholz.Rank1
open T

def gen : Nat → List T
  | 0 => [Z]
  | n + 1 =>
    let xs := gen n
    [Z] ++ [0, 1].flatMap (fun i => xs.flatMap (fun a => xs.map (fun b => P i a b)))

def ltB (a b : T) : Bool :=
  match T.decLt a b with
  | isTrue _ => true
  | isFalse _ => false

def nfB (a : T) : Bool :=
  match T.decIsNF a with
  | isTrue _ => true
  | isFalse _ => false

def le1B (p : Nat) : Bool :=
  if p ≤ 1 then true else false

def idx1 : T → Bool
  | Z => true
  | P p _ b => le1B p && idx1 b

def good1 (x : T) : Bool :=
  nfB x && idx1 x && (T.G1 1 x).all (fun y => ltB y x)

def xs := (gen 3).filter good1

#eval xs.length
#eval xs.all (fun a => xs.all (fun b => !(ltB b a) || good1 (T.add a b)))
#eval (xs.find? (fun a => xs.any (fun b => ltB b a && !good1 (T.add a b)))).map reprStr

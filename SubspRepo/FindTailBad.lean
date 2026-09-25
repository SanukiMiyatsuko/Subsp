import Subsp.Buchholz.Rank1
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 =>
  let p := gen n
  [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))

def good (u : Nat) (x : T) : Bool :=
  decide (T.isNF1 x) && (T.G1 u x).all (fun y => decide (y < x))

def bad := (gen 3).filter (fun x =>
  match x with
  | P (i+1) _ t => good 0 x && !(good 0 t)
  | _ => false)

#eval bad.length
#eval bad.take 10 |>.map reprStr

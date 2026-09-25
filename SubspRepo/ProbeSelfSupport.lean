import Subsp.Buchholz.Rank1
open T

def genSS : Nat → List T
| 0 => [Z]
| n + 1 =>
  let p := genSS n
  [Z] ++ [0, 1, 2].flatMap (fun i =>
    p.flatMap (fun a => p.map (fun b => P i a b)))

def idx1SS : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1SS b

def good1SS (s : T) : Bool :=
  (T.G1 1 s).all (fun x => decide (x < s))

def top1SS : T → Bool
| P 1 _ _ => true
| _ => false

def propSS (s : T) : Bool :=
  if top1SS s && decide (T.isNF1 s) && idx1SS s && good1SS s && decide (s < P 1 s Z) then
    (T.G1 0 s).all (fun x => decide (x < P 1 s Z))
  else true

def xsSS := genSS 3
#eval xsSS.length
#eval xsSS.all propSS
#eval (xsSS.find? (fun s => !(propSS s))).map
  (fun s => (reprStr s, (T.G1 0 s).map reprStr))

import Subsp.new.stop
open T

def terms : Nat → List T
| 0 => [Z]
| n+1 =>
  let xs := terms n
  [Z] ++ (List.range 3).flatMap (fun k => xs.flatMap (fun a => xs.map (fun b => P k a b)))

def good (u:Nat) (s:T) : Bool :=
  decide (T.isNF1 s ∧ ∀ y ∈ T.G1 u s, y < s)

def firstECBad (n:Nat) : Option (T×T) :=
  let xs := (terms n).filter (fun x => good 0 x)
  xs.findSome? (fun x => xs.findSome? (fun y => if decide (x<y) && !decide (T.early_collapse x < T.early_collapse y) then some (x,y) else none))

def firstCardBad (n m:Nat) : Option (T×T) :=
  let xs := (terms n).filter (fun x => good 0 x)
  xs.findSome? (fun x => xs.findSome? (fun y => if decide (x<y) && !decide (T.card_times m (T.early_collapse x) < T.card_times m (T.early_collapse y)) then some (x,y) else none))

#eval firstECBad 2
#eval firstCardBad 2 0
#eval firstCardBad 2 1
#eval firstCardBad 2 2

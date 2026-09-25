import Subsp.new.stop
open T

def terms : Nat → List T
| 0 => [Z]
| n+1 => let xs:=terms n; [Z] ++ (List.range 3).flatMap (fun k => xs.flatMap (fun a => xs.map (fun b=>P k a b)))
def good (u:Nat) (s:T):Bool := decide (T.isNF1 s ∧ ∀y∈T.G1 u s, y<s)
def badECGood1 (n:Nat) := (terms n).find? (fun x => good 0 x && !good 1 (T.early_collapse x))
def badCardGood1 (n m:Nat) := (terms n).find? (fun x => good 0 x && !good 1 (T.card_times m (T.early_collapse x)))
#eval badECGood1 2
#eval badCardGood1 2 0
#eval badCardGood1 2 1
#eval badCardGood1 2 2

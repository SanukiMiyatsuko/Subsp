import Subsp.new.stop
open T

def terms : Nat → List T
| 0 => [Z]
| n+1 => let xs:=terms n; [Z] ++ (List.range 3).flatMap (fun k => xs.flatMap (fun a => xs.map (fun b=>P k a b)))
def good (u:Nat) (s:T):Bool := decide (T.isNF1 s ∧ ∀y∈T.G1 u s, y<s)
def badTail (n:Nat) := (terms n).find? (fun s => match s with | Z=>false | P p a b => p>0 && good 0 s && !good 0 b)
#eval badTail 2
#eval badTail 3

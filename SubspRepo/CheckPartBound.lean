import Subsp.new.stop
open T

def terms : Nat → List T | 0=>[Z] | n+1=>let xs:=terms n; [Z] ++ (List.range 3).flatMap (fun k => xs.flatMap (fun a => xs.map (fun b=>P k a b)))
def good0 (s:T):Bool := decide (T.isNF1 s ∧ ∀y∈T.G1 0 s,y<s)
def bad (n:Nat) := (terms n).find? (fun s => if good0 s then let ps:=T.part s; match ps.1,ps.2 with | P _ _ _, P 0 e _ => !decide (e≤ps.1) | _,_=>false else false)
#eval bad 3

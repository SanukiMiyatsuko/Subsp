import Subsp.new.stop
open T

def showT : T → String | Z=>"Z" | P n a b=>"P("++toString n++","++showT a++","++showT b++")"
def terms : Nat → List T | 0=>[Z] | n+1=>let xs:=terms n; [Z] ++ (List.range 3).flatMap (fun k => xs.flatMap (fun a => xs.map (fun b=>P k a b)))
def good (u:Nat) (s:T):Bool := decide (T.isNF1 s ∧ ∀y∈T.G1 u s, y<s)
def badTail (n:Nat) := (terms n).find? (fun s => match s with | Z=>false | P p _ b => p>0 && (match b with | P q _ _ => q>0 | Z => false) && good 0 s && !good 0 b)
#eval match badTail 3 with | none=>"none" | some s => showT s ++ " tail=" ++ (match s with | Z=>"" | P _ _ b=>showT b)

import Subsp.Buchholz.Rank1
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def xs := gen 3
def good1 (x:T) : Bool := (decide (T.isNF1 x)) && (decide (T.index_Prop1 1 x)) && (T.G1 1 x).all (fun y => decide (y<x))
def idx0nf (x:T) : Bool := (decide (T.isNF1 x)) && (decide (T.index_Prop1 0 x))
def bad := xs.findSome? (fun u => if good1 u then xs.findSome? (fun e => if idx0nf e && !(decide (T.isNF1 (T.add u e))) then some (u,e) else none) else none)
#eval match bad with | none => "none" | some (u,e) => reprStr u ++ " / " ++ reprStr e ++ " => " ++ reprStr (T.add u e)

import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def showT : T → String
| Z => "Z"
| P n a b => "P(" ++ toString n ++ "," ++ showT a ++ "," ++ showT b ++ ")"

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0 (x:T):Bool := decide (T.isNF1 x) && (T.G1 0 x).all (fun y=>decide (y < x))
def xs := (gen 2).filter good0
def pairs := xs.flatMap (fun a => xs.map (fun b => (a,b)))
def bad := pairs.find? (fun p => decide (p.1 < p.2) && !(decide (p.1 < T.early_collapse p.2)))
#eval match bad with | none => "none" | some p => showT p.1 ++ " < " ++ showT p.2 ++ " but not < ec=" ++ showT (T.early_collapse p.2)

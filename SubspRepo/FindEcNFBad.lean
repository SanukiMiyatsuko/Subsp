import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def showT : T → String
| Z => "Z"
| P n a b => "P(" ++ toString n ++ "," ++ showT a ++ "," ++ showT b ++ ")"

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def bad := (gen 3).find? (fun x => decide (T.isNF1 x) && !(decide (T.isNF1 (T.early_collapse x))))
#eval match bad with | none => "none" | some x => showT x ++ " -> " ++ showT (T.early_collapse x)

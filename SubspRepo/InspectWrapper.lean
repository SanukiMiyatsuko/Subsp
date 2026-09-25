import Subsp.Buchholz.Rank1
open T

def showT : T → String
| Z => "Z"
| P p a b => "P(" ++ toString p ++ "," ++ showT a ++ "," ++ showT b ++ ")"

def m : T := T.P 0 (T.P 1 (T.P 1 T.Z T.Z) T.Z) T.Z
#eval showT m
#eval (T.G1 0 m).map showT
#eval (T.G1 1 m).map showT
#eval (T.G1 0 m).map (fun x => (showT x, decide (x < T.P 1 m T.Z)))

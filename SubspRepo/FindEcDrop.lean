import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def showT : T → String
| Z => "Z"
| P n a b => "P(" ++ toString n ++ "," ++ showT a ++ "," ++ showT b ++ ")"

def gen : Nat → List T
| 0 => [Z]
| n+1 =>
  let p := gen n
  [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))

def good0 (x:T) : Bool :=
  decide (T.isNF1 x) && (T.G1 0 x).all (fun y => decide (y < x))

def dropped (s:T) : Bool :=
  if good0 s then
    let ps := T.part s
    if decide (ps.1 = Z) then false
    else decide (T.early_collapse s = ps.2)
  else false

def bad := (gen 3).find? dropped

#eval match bad with
| none => "none"
| some s => showT s ++ " part=" ++ showT (T.part s).1 ++ "/" ++ showT (T.part s).2 ++ " ec=" ++ showT (T.early_collapse s)

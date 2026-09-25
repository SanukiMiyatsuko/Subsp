import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1 : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1 b
def deep1 (s:T):Bool := idx1 s && (T.G1 0 s).all idx1
def prop (a:T):Bool := let e:=T.early_collapse a; (T.G1 0 e).all (fun x=>decide (x < T.P 1 e T.Z))
def xs := (gen 3).filter deep1
#eval xs.length
#eval xs.all prop
#eval (xs.find? (fun x=>!(prop x))).map reprStr

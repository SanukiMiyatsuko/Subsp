import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1 : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1 b
def nf (x:T):Bool := decide (T.isNF1 x)
def deep1 (s:T):Bool := idx1 s && (T.G1 0 s).all idx1
def good1 (s:T):Bool := (T.G1 1 s).all (fun x=>decide (x < s))
def prop (d:T):Bool := let C:=T.card_times 1 d; (T.G1 0 C).all (fun x=>decide (x < T.P 1 C T.Z))
def xs := (gen 3).filter (fun x => nf x && deep1 x && good1 x)
#eval xs.length
#eval xs.all prop
#eval (xs.find? (fun x => !(prop x))).map reprStr

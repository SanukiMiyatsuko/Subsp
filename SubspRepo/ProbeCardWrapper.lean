import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx0 : T → Bool
| Z => true
| P p _ b => decide (p=0) && idx0 b
def nf (x:T):Bool := decide (T.isNF1 x)
def prop (c:T):Bool := let C:=T.card_times 1 c; (T.G1 0 C).all (fun x => decide (x < T.P 1 C T.Z))
def xs := (gen 3).filter (fun x => idx0 x && nf x)
#eval xs.length
#eval xs.all prop
#eval (xs.find? (fun c => !(prop c))).map reprStr

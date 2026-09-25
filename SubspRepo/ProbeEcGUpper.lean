import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good0 (x:T) : Bool := decide (T.isNF1 x ∧ ∀ y:T, y ∈ T.G1 0 x → y < x)
def leB (a b:T):Bool := decide (a < b) || decide (a = b)
def prop (s:T):Bool := (T.G1 0 (T.early_collapse s)).all (fun y => leB y s)
def gs := (gen 3).filter good0
#eval gs.length
#eval gs.all prop
#eval (gs.find? (fun s => !(prop s))).map reprStr

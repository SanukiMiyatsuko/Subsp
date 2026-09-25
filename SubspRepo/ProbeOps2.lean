import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def good (u:Nat) (x:T):Bool := decide (T.isNF1 x) && (T.G1 u x).all (fun y=>decide (y < x))
def idxb (u:Nat) : T → Bool | Z=>true | P p _ t => decide (p≤u) && idxb u t
def xs0 := (gen 2).filter (fun x => good 1 x && idxb 0 x)
def xs1 := (gen 2).filter (fun x => good 1 x && idxb 1 x)
def mono (f:T→T) (xs:List T):Bool := xs.all (fun a => xs.all (fun b => !(decide (a < b)) || decide (f a < f b)))
def refl (f:T→T) (xs:List T):Bool := xs.all (fun a => xs.all (fun b => !(decide (f a < f b)) || decide (a < b)))
#eval xs0.length
#eval mono T.one_del xs0
#eval refl T.one_del xs0
#eval mono (T.card_times 1) xs0
#eval refl (T.card_times 1) xs0
#eval mono (T.card_times 2) xs0
#eval refl (T.card_times 2) xs0
#eval xs1.length
#eval mono T.one_del xs1
#eval refl T.one_del xs1

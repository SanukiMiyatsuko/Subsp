import Subsp.Buchholz.Rank1
open T

def genD : Nat → List T
| 0 => [Z]
| n+1 => let p:=genD n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1B : T → Bool
| Z => true
| P p a b => decide (p ≤ 1) && idx1B b
def nfB (a:T):Bool := match T.decIsNF a with | isTrue _ => true | isFalse _ => false
def deep (m:T):Bool := (T.G1 0 m).all idx1B
def prop (m:T):Bool := (T.G1 0 m).all (fun x => decide (x < T.P 1 m T.Z))
def outer1 : T → Bool | P 1 _ _ => true | _ => false
def good1B (m:T):Bool := (T.G1 1 m).all (fun x => decide (x<m))
def xs := (genD 3).filter (fun m => nfB m && outer1 m && idx1B m && deep m && good1B m)
#eval xs.length
#eval xs.all prop
#eval (xs.filter (fun m => !prop m)).take 20 |>.map (fun m => (reprStr m, (T.G1 0 m).filter (fun x => !(decide (x<T.P 1 m T.Z))) |>.map reprStr))

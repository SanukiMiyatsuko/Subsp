import Subsp.Buchholz.Rank1
open T

def genGSu : Nat → List T
| 0 => [Z]
| n+1 => let p := genGSu n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1GSu : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1GSu b
def good1GSu (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def top1GSu : T → Bool | P 1 _ _ => true | _ => false
def propGSu (s:T) : Bool := if top1GSu s && idx1GSu s && good1GSu s then (T.G1 0 s).all (fun x => decide (x < P 1 s Z)) else true
def xsGSu := genGSu 3
#eval xsGSu.length
#eval xsGSu.all propGSu
#eval (xsGSu.find? (fun s => !(propGSu s))).map (fun s => (reprStr s,(T.G1 0 s).map reprStr))

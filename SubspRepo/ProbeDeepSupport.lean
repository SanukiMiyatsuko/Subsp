import Subsp.Buchholz.Rank1
open T

def genDSp : Nat → List T
| 0 => [Z]
| n+1 => let p := genDSp n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1DSp : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1DSp b
def deep1DSp (s:T) : Bool := idx1DSp s && (T.G1 0 s).all idx1DSp
def propDSp (s:T) : Bool := if deep1DSp s then (T.G1 0 s).all (fun x => decide (x < P 1 s Z)) else true
def xsDSp := genDSp 3
#eval xsDSp.length
#eval xsDSp.all propDSp
#eval (xsDSp.find? (fun s => !(propDSp s))).map (fun s => (reprStr s,(T.G1 0 s).map reprStr))

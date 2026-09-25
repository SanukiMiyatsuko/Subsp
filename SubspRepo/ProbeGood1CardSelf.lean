import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genGC : Nat → List T
| 0 => [Z]
| n+1 => let p := genGC n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1GC : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1GC b
def good1GC (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def propGC (s:T) : Bool := if s != Z && decide (T.isNF1 s) && idx1GC s && good1GC s then decide (s < T.card_times 1 s) else true
def xsGC := genGC 3
#eval xsGC.length
#eval xsGC.all propGC
#eval (xsGC.find? (fun s => !(propGC s))).map (fun s => (reprStr s, reprStr (T.card_times 1 s)))

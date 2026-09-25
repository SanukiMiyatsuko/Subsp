import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genCWc : Nat → List T
| 0 => [Z]
| n+1 => let p := genCWc n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1CWc : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1CWc b
def good1CWc (s:T) : Bool := (T.G1 1 s).all (fun x => decide (x < s))
def propCWc (s:T) : Bool := if decide (T.isNF1 s) && idx1CWc s && good1CWc s then decide (s < T.P 1 (T.card_times 1 s) T.Z) else true
def xsCWc := genCWc 3
#eval xsCWc.length
#eval xsCWc.all propCWc
#eval (xsCWc.find? (fun s => !(propCWc s))).map (fun s => (reprStr s, reprStr (T.card_times 1 s)))

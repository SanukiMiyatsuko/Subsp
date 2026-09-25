import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genEL : Nat → List T
| 0 => [Z]
| n+1 => let p := genEL n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def leEL (a b:T) : Bool := decide (a < b) || decide (a = b)
def goodEL (s:T) : Bool := decide (T.isNF1 s) && (T.G1 0 s).all (fun x => decide (x < s))
def xsEL := genEL 3
#eval xsEL.all (fun s => if goodEL s then leEL (T.early_collapse s) s else true)
#eval (xsEL.find? (fun s => goodEL s && !(leEL (T.early_collapse s) s))).map (fun s => (reprStr s, reprStr (T.early_collapse s)))

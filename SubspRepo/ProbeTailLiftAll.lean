import Subsp.Buchholz.Rank1
open T

def genTL : Nat → List T
| 0 => [Z]
| n+1 => let p := genTL n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def leTL (a b:T) : Bool := decide (a < b) || decide (a = b)
def propTL (p b:T) : Bool :=
  if decide (T.isNF1 b) && leTL (T.head b) p then
    xsTL.all (fun x => if decide (x < b) then decide (x < T.add p b) else true)
  else true
def xsTL := genTL 2
#eval (xsTL.flatMap (fun p => xsTL.map (fun b => (p,b)))).all (fun q => propTL q.1 q.2)
#eval (xsTL.flatMap (fun p => xsTL.map (fun b => (p,b)))).find? (fun q => !(propTL q.1 q.2)) |>.map (fun q => (reprStr q.1, reprStr q.2, reprStr (T.add q.1 q.2)))

import Subsp.Buchholz.Rank1
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def idx1b (s:T): Bool := decide (T.index_Prop1 1 s)
def prop (m:T): Bool := (T.G1 0 m).all (fun y => decide (y < T.P 1 m T.Z))
#eval (gen 3).filter idx1b |>.all prop
#eval (gen 3).filter idx1b |>.filter (fun x => !prop x) |>.take 10 |>.map reprStr

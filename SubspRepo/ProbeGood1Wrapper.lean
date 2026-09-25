import Subsp.Buchholz.Rank1
open T

def genW : Nat → List T
  | 0 => [Z]
  | n + 1 =>
    let xs := genW n
    [Z] ++ ([0,1].flatMap (fun i => xs.flatMap (fun a => xs.map (fun b => P i a b))))

def idx1W : T → Bool
  | Z => true
  | P p _ b => (decide (p ≤ 1)) && idx1W b

def good1W (x:T):Bool :=
  (decide (T.isNF1 x)) && (idx1W x) && ((T.G1 1 x).all (fun y => decide (y < x)))

def propW (m:T):Bool := (T.G1 0 m).all (fun x => decide (x < T.P 1 m T.Z))
def xsW := (genW 3).filter good1W
#eval xsW.length
#eval xsW.all propW
#eval (xsW.find? (fun m => !(propW m))).map reprStr

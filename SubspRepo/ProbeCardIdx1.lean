import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n + 1 =>
  let xs := gen n
  [Z] ++ [0,1,2].flatMap (fun i => xs.flatMap (fun a => xs.map (fun b => P i a b)))

def ltB (a b : T) : Bool := match T.decLt a b with | isTrue _ => true | isFalse _ => false
def nfB (a : T) : Bool := match T.decIsNF a with | isTrue _ => true | isFalse _ => false
def good1 (x : T) : Bool := nfB x && (T.G1 1 x).all (fun y => ltB y x)
def idx1 : T → Bool
| Z => true
| P p _ b => decide (p ≤ 1) && idx1 b

def xs := (gen 3).filter (fun x => good1 x && idx1 x)
#eval xs.length
#eval xs.all (fun x => good1 (T.card_times 1 x))
#eval (xs.find? (fun x => !good1 (T.card_times 1 x))).map reprStr

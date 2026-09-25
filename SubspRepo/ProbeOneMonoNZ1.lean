import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
  | 0 => [Z]
  | n + 1 =>
    let xs := gen n
    [Z] ++ [0, 1].flatMap (fun i => xs.flatMap (fun a => xs.map (fun b => P i a b)))
def ltB (a b : T) : Bool := match T.decLt a b with | isTrue _ => true | isFalse _ => false
def nfB (a : T) : Bool := match T.decIsNF a with | isTrue _ => true | isFalse _ => false
def idx1 : T → Bool | Z => true | P p _ b => (if p ≤ 1 then true else false) && idx1 b
def good1 (x : T) : Bool := nfB x && idx1 x && (T.G1 1 x).all (fun y => ltB y x)
def xs := (gen 3).filter (fun x => good1 x && !decide (x = Z))
#eval xs.length
#eval xs.all (fun a => xs.all (fun b => !ltB a b || ltB (T.one_del a) (T.one_del b)))
#eval (xs.findSome? (fun a => match xs.find? (fun b => ltB a b && !ltB (T.one_del a) (T.one_del b)) with | none => none | some b => some (a,b))).map (fun p => reprStr p.1 ++ " / " ++ reprStr p.2)

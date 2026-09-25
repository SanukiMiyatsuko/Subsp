import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen01 : Nat → List T
| 0 => [Z]
| n+1 =>
  let p := gen01 n
  [Z] ++ [0,1].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))

def chkMap (f : T → T) (xs : List T) : Bool :=
  xs.all (fun a => xs.all (fun b => (decide (a < b)) == (decide (f a < f b))))
#eval (gen01 2).length
#eval chkMap T.early_collapse (gen01 2)
#eval chkMap (fun x => T.card_times 1 (T.early_collapse x)) (gen01 2)

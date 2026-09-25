import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 =>
  let p := gen n
  [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))

def chkMap (f : T → T) (xs : List T) : Bool :=
  xs.all (fun a => xs.all (fun b =>
    let lhs := decide (a < b)
    let rhs := decide (f a < f b)
    lhs == rhs))

#eval (gen 2).length
#eval chkMap T.early_collapse (gen 2)
#eval chkMap (T.card_times 0) (gen 2)
#eval chkMap (T.card_times 1) (gen 2)
#eval chkMap (T.card_times 2) (gen 2)
#eval chkMap T.one_del (gen 2)

import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genEG : Nat → List T
| 0 => [Z]
| n+1 =>
  let p := genEG n
  [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))

def good0EG (s : T) : Bool :=
  decide (T.isNF1 s) && (T.G1 0 s).all (fun x => decide (x < s))

def xsEG := (genEG 3).filter good0EG
#eval xsEG.length
#eval xsEG.all (fun s => good0EG (T.early_collapse s))
#eval (xsEG.find? (fun s => !(good0EG (T.early_collapse s)))).map reprStr

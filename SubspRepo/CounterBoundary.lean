import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def e2 := P 0 Z Z
def e := P 1 Z e2
def b := P 0 e Z
def s := P 1 Z b
#eval decide (T.isNF1 s)
#eval decide (∀x:T, x∈T.G1 0 s → x<s)
#eval reprStr (T.part s).1
#eval reprStr (T.part s).2
#eval decide (T.head (T.part s).2 ≤ P 0 (T.part s).1 Z)
#eval reprStr (T.early_collapse s)
#eval decide (T.isNF1 (T.early_collapse s))
#eval decide (T.isNF1 b)
#eval decide (∀x:T, x∈T.G1 0 b → x<b)
#eval reprStr (T.early_collapse b)
#eval decide (b<s)

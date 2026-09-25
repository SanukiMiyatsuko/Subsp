import Subsp.new.stop
open T

def u := P 1 Z Z
def e := P 1 Z (P 0 Z Z)
def d := P 0 e Z
def s := P 1 Z d
#eval decide (T.isNF1 s)
#eval decide (∀y∈T.G1 0 s,y<s)
#eval decide (u<e)
#eval decide (e<s)
#eval T.part s
#eval decide (T.isNF1 (P 0 (T.part s).1 (T.part s).2))
#eval T.early_collapse s
#eval decide (T.isNF1 (T.early_collapse s))

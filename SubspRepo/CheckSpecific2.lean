import SubspRepo.DecodeGen
open T
def aX2 : T := P 1 Z (P 0 Z Z)
def lX2 : T := P 0 aX2 Z
def cX2 : T := P 1 Z lX2
def tX2 : T := P 1 cX2 Z
#eval (good0 tX2, decide (tX2 < C 2))
#eval (rawT (trans (decC 2 30 tX2)), compB (decC 2 30 tX2))
#eval rawT (trans (decC 2 30 (T.unec lX2)))

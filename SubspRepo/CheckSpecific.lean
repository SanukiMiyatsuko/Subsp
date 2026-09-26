import SubspRepo.DecodeGen
open T
def aX : T := P 1 Z (P 0 Z Z)
def lX : T := P 0 aX Z
def cX : T := P 1 Z lX
#eval (good0 aX, good0 lX, good0 cX, good0 (T.unec lX))
#eval (rawT (T.unec lX), rawT (T.part cX).1, rawT (T.part cX).2)

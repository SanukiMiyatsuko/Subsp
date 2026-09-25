import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def x : T := P 0 (P 1 Z Z) Z
#eval decide (T.isNF1 x)
#eval decide (∀ y : T, y ∈ T.G1 0 x → y < x)
#eval reprStr (early_collapse x)
#eval decide (∀ y : T, y ∈ T.G1 0 (early_collapse x) → y < early_collapse x)

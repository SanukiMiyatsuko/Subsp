import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T
def x := P 0 (P 1 Z Z) Z
#eval decide (T.isNF1 x)
#eval decide (T.isNF1 (T.card_times 1 x))
#eval reprStr (T.card_times 1 x)

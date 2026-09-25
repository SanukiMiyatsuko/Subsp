import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def a := P 0 (P 1 Z Z) Z
def b := P 1 (P 0 Z Z) (P 0 Z Z)
def c := P 2 Z (P 0 (P 1 Z Z) Z)
#eval reprStr (early_collapse a)
#eval reprStr (early_collapse b)
#eval reprStr (early_collapse c)
#eval reprStr (card_times 0 a)
#eval reprStr (card_times 1 a)
#eval reprStr (card_times 2 a)
#eval reprStr (card_times 0 b)
#eval reprStr (card_times 1 b)
#eval reprStr (card_times 2 b)
#eval reprStr (one_del (P 0 Z (P 0 Z Z)))

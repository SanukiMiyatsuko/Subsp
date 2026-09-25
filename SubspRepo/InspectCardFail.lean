import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T
def c : T := P 0 (P 2 Z Z) Z
#eval reprStr c
#eval reprStr (T.card_times 1 c)
#eval (T.G1 0 (T.card_times 1 c)).map reprStr
#eval (T.G1 0 (T.card_times 1 c)).map (fun x => (reprStr x, decide (x < T.P 1 (T.card_times 1 c) Z)))

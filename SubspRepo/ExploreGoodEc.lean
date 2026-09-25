import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T
#eval decide (T.isNF1 (P 1 Z Z) ∧ ∀y:T, y∈T.G1 0 (P 1 Z Z) → y < P 1 Z Z)
#eval reprStr (T.early_collapse (P 1 Z Z))
#eval reprStr (T.early_collapse (P 1 (P 0 Z Z) Z))

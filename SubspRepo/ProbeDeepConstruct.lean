import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def one := P 1 Z Z
def twoDeep := P 1 one Z
def threeDeep := P 1 twoDeep Z
def d1 := P 0 one Z
def d2 := P 0 twoDeep Z
def d3 := P 0 threeDeep Z
def chk (d:T) := let C:=T.card_times 1 d; (reprStr C, (T.G1 0 C).map reprStr, (T.G1 0 C).all (fun x=>decide (x<T.P 1 C Z)))
#eval chk d1
#eval chk d2
#eval chk d3

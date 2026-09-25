import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genCM : Nat → List T
| 0 => [Z]
| n+1 => let p := genCM n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def leCM (a b:T) : Bool := decide (a < b) || decide (a = b)
def propCM (n:Nat) (c:T) : Bool :=
  let C := T.card_times n c
  (T.G1 0 C).all (fun x => decide (x < P 1 C Z) || (T.G1 0 c).any (fun z => leCM x z) || leCM x c)
def xsCM := genCM 3
#eval xsCM.all (fun c => propCM 1 c)
#eval (xsCM.find? (fun c => !(propCM 1 c))).map (fun c => (reprStr c, reprStr (T.card_times 1 c), (T.G1 0 (T.card_times 1 c)).map reprStr))

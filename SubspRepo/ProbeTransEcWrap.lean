import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def og (s:T):Bool := decide (T.isNF1 s) && (T.G1 0 s).all (fun x=>decide (x<s))
def prop (a:new.T 2):Bool := if og (trans a) then let E:=T.early_collapse (trans a); let C:=T.card_times 1 (T.one_del E); (T.G1 0 C).all (fun x=>decide (x<T.P 1 C Z)) else true
def xs:=gen2 3
#eval xs.length
#eval xs.all prop
#eval xs.find? (fun a=>!(prop a)) |>.map (fun a=>reprStr (trans a))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2MS (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2MS : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2MS n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2MS a b) c)))
def leMS (a b : T):Bool := decide (a < b)||decide (a = b)
def propMS (s : new.T 2):Bool := (T.G1 0 (trans s)).all (fun x => (new.T.G s).any (fun z => leMS x (trans z)))
def xsMS:=gen2MS 3
#eval xsMS.length
#eval xsMS.all propMS
#eval (xsMS.find? (fun s => !(propMS s))).map (fun s=>(reprStr (trans s),(T.G1 0 (trans s)).map reprStr,(new.T.G s).map (fun z => reprStr (trans z))))

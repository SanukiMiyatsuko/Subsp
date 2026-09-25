import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2FM (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2FM : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2FM n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2FM a b) c)))
def ogFM(s:T):Bool:=decide (T.isNF1 s)&&(T.G1 0 s).all (fun x=>decide (x < s))
def propFM(a b:new.T 2):Bool:=if ogFM (trans a)&&ogFM (trans b) then let r:=transAux (v2FM a b); if r.1 then let M:=T.card_times 1 (T.one_del r.2.1)+T.early_collapse r.2.2; decide (M<T.P 1 M Z) else true else true
def xsFM:=gen2FM 2
#eval xsFM.all (fun a=>xsFM.all (fun b=>propFM a b))
#eval xsFM.find? (fun a=>xsFM.any (fun b=>!(propFM a b))) |>.map (fun a=>reprStr (trans a))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2AS (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2AS : Nat → List (new.T 2) | 0=>[new.T.Z] | n+1=>let p:=gen2AS n; [new.T.Z]++p.flatMap (fun a=>p.flatMap (fun b=>p.map (fun c=>new.T.P (v2AS a b) c)))
def ogAS(s:T):Bool:=decide (T.isNF1 s)&&(T.G1 0 s).all (fun x=>decide (x < s))
def propAS(a b:new.T 2):Bool:=if ogAS (trans a)&&ogAS (trans b) then let r:=transAux (v2AS a b); if r.1 then let c:=T.one_del r.2.1; decide (c < T.card_times 1 c) else true else true
def xsAS:=gen2AS 2
#eval xsAS.all (fun a=>xsAS.all (fun b=>propAS a b))
#eval (xsAS.flatMap (fun a => xsAS.map (fun b => (a,b)))).find? (fun q => !(propAS q.1 q.2)) |>.map (fun q => let r:=transAux (v2AS q.1 q.2); (reprStr (trans q.1), reprStr (trans q.2), reprStr r.2.1, reprStr (T.one_del r.2.1), reprStr (T.card_times 1 (T.one_del r.2.1))))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2AU (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2AU : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2AU n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2AU a b) c)))
def ogAU (s:T):Bool := decide (T.isNF1 s) && (T.G1 0 s).all (fun x=>decide (x < s))
def propAU (a b:new.T 2):Bool :=
  if ogAU (trans a) && ogAU (trans b) then
    let r:=transAux (v2AU a b)
    if r.1 then
      let A:=T.card_times 1 (T.one_del r.2.1)
      (T.G1 0 A).all (fun x=>decide (x < T.P 1 A T.Z))
    else true
  else true
def xsAU:=gen2AU 2
#eval xsAU.length
#eval xsAU.all (fun a=>xsAU.all (fun b=>propAU a b))
#eval xsAU.find? (fun a=>xsAU.any (fun b=>!(propAU a b))) |>.map (fun a=>reprStr (trans a))

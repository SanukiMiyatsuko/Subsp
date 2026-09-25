import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2ASW (a b : new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2ASW : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n + 1 =>
  let p := gen2ASW n
  [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2ASW a b) c)))
def ogASW (s:T):Bool := decide (T.isNF1 s) && (T.G1 0 s).all (fun x => decide (x<s))
def propASW (a b:new.T 2):Bool :=
  if ogASW (trans a) && ogASW (trans b) then
    let r:=transAux (v2ASW a b)
    if r.1 then
      let A:=T.card_times 1 (T.one_del r.2.1)
      decide (A < T.P 1 A T.Z)
    else true
  else true
def xsASW:=gen2ASW 2
#eval xsASW.all (fun a=>xsASW.all(fun b=>propASW a b))
#eval (xsASW.find? (fun a=>xsASW.any(fun b=>!(propASW a b)))).map (fun a=>reprStr(trans a))

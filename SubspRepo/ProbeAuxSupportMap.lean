import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2ASM (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2ASM : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2ASM n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2ASM a b) c)))
def leASM (a b:T):Bool := decide (a < b) || decide (a = b)
def propASM (a b:new.T 2):Bool :=
  let v:=v2ASM a b
  let r:=transAux v
  (T.G1 0 (T.one_del r.2.1)).all (fun x => (new.Vec.toList v).any (fun z=>leASM x (trans z)))
def xsASM:=gen2ASM 2
#eval xsASM.length
#eval xsASM.all (fun a=>xsASM.all (fun b => propASM a b))
#eval (xsASM.flatMap (fun a => xsASM.map (fun b => (a,b)))).find? (fun q=>!(propASM q.1 q.2)) |>.map (fun q=> let r:=transAux(v2ASM q.1 q.2); (reprStr r.2.1, reprStr(T.one_del r.2.1),(T.G1 0(T.one_del r.2.1)).map reprStr))

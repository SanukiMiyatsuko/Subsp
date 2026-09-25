import Subsp.new.subsp

def v2s (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def z2s : new.T 2 := new.T.Z
def one2s : new.T 2 := new.T.P (v2s z2s z2s) z2s
def us : new.T 2 := new.T.P (v2s z2s one2s) z2s
def badts : new.T 2 := new.T.P (v2s us z2s) z2s

def gens : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gens n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2s a b) c)))

def nfcb (s:new.T 2) : Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
def cand := (gens 2).findSome? (fun a => (gens 2).find? (fun b => nfcb (new.T.P (v2s a b) badts)))
#eval (gens 2).length
#eval cand.isSome

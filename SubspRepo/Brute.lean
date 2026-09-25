import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans

open T

-- finite test families, not used in proofs
def gen1 : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 =>
  let p := gen1 n
  [new.T.Z] ++ p.flatMap (fun a => p.map (fun b => new.T.P (new.Vec.snoc 0 new.Vec.nil a) b))

def vec2 (a b : new.T 2) : new.Vec (new.T 2) 2 :=
  new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 =>
  let p := gen2 n
  [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (vec2 a b) c)))

def chkOrd1 (xs : List (new.T 1)) : Bool :=
  xs.all (fun a => xs.all (fun b =>
    let lhs := new.compareT a b == Ordering.lt
    let rhs := decide (trans a < trans b)
    lhs == rhs))

def chkOrd2 (xs : List (new.T 2)) : Bool :=
  xs.all (fun a => xs.all (fun b =>
    let lhs := new.compareT a b == Ordering.lt
    let rhs := decide (trans a < trans b)
    lhs == rhs))

def chkNF {lam : Nat} (xs : List (new.T lam)) : Bool :=
  xs.all (fun a => if h : new.T.isNF a then decide (T.isNF1 (trans a)) else true)

#eval (gen1 2).length
#eval chkOrd1 (gen1 3)
#eval chkNF (gen1 2)
#eval (gen2 2).length
#eval chkOrd2 (gen2 2)
#eval chkNF (gen2 2)

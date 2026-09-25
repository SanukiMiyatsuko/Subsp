import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def gen1 : Nat → List (new.T 1)
| 0 => [new.T.Z]
| n+1 =>
  let p := gen1 n
  [new.T.Z] ++ p.flatMap (fun a => p.map (fun b => new.T.P (new.Vec.snoc 0 new.Vec.nil a) b))

def vec2 (a b : new.T 2) : new.Vec (new.T 2) 2 := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 =>
  let p := gen2 n
  [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (vec2 a b) c)))

def chkMap (f : T → T) (xs : List T) : Bool :=
  xs.all (fun a => xs.all (fun b => (decide (a < b)) == (decide (f a < f b))))

def imgs1 := (gen1 3).map trans
def imgs2 := (gen2 2).map trans
#eval chkMap T.early_collapse imgs1
#eval chkMap T.early_collapse imgs2
#eval chkMap (fun x => T.card_times 0 (T.early_collapse x)) imgs2
#eval chkMap (fun x => T.card_times 1 (T.early_collapse x)) imgs2
#eval chkMap (fun x => T.card_times 2 (T.early_collapse x)) imgs2

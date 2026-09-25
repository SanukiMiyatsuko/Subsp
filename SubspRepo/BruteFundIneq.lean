import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def bound : new.T 2 := new.T.P (new.Vec.ofFn 2 (fun x => if x.val=1 then new.T.P (new.Vec.ofFn 2 (fun _=>new.T.Z)) new.T.Z else new.T.Z)) new.T.Z
def ots := (gen2 3).filter (fun s => (decide (new.T.isNF s)) && (decide (new.compareT s bound = Ordering.lt)))
def ole (x y:T):Bool := decide (x<y) || decide (x=y)
def chkSame := ots.all (fun s => (List.range 5).all (fun n => ole (T.fund1 (trans s) (T.ofNat n)) (trans (new.T.fund s (new.T.ofNat n)))))
def chkShift := ots.all (fun s => (List.range 5).all (fun n => ole (T.fund1 (trans s) (T.ofNat n)) (trans (new.T.fund s (new.T.ofNat (n+1))))))
#eval ots.length
#eval chkSame
#eval chkShift

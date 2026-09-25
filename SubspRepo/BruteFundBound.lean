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
def chkOfNat := ots.all (fun s => (List.range 5).all (fun n => decide (trans (new.T.fund s (new.T.ofNat n)) = T.fund1 (trans s) (T.ofNat n))))
def bad := ots.find? (fun s => !(List.range 5).all (fun n => decide (trans (new.T.fund s (new.T.ofNat n)) = T.fund1 (trans s) (T.ofNat n))))
#eval ots.length
#eval chkOfNat
#eval bad.isSome

def showN {l} : new.T l → String
| new.T.Z => "Z"
| new.T.P ls a => "P[" ++ showV ls ++ ";" ++ showN a ++ "]"
where showV {l k} : new.Vec (new.T l) k → String
| new.Vec.nil => ""
| new.Vec.snoc _ xs x => showV xs ++ "," ++ showN x
#eval match bad with | none => "none" | some s => showN s
#eval match bad with | none => [] | some s => (List.range 5).map (fun n => decide (trans (new.T.fund s (new.T.ofNat n)) = T.fund1 (trans s) (T.ofNat n)))

import Subsp.new.stop_ot_downward

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def bound : new.T 2 := ot_bound 2
def ots := (gen2 3).filter (fun s => (decide (new.T.isNF s)) && (decide (new.compareT s bound = Ordering.lt)))
def base2 (n:Nat) : new.T 2 := new.T.P (new.Vec.ofFn 2 (fun i => if i.val=0 then new.T.LF 2 n else new.T.Z)) new.T.Z
#eval ots.length
#eval (List.range 12).map (fun N => (ots.filter (fun s => !((List.range (N+1)).any (fun n => decide (new.compareT s (base2 n) ≠ Ordering.gt))))).length)

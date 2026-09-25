import Subsp.new.stop_ot_base

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def bound : new.T 2 := new.T.P (new.Vec.ofFn 2 (fun x => if x.val=1 then new.T.P (new.Vec.ofFn 2 (fun _=>new.T.Z)) new.T.Z else new.T.Z)) new.T.Z
def ots := (gen2 3).filter (fun s => (decide (new.T.isNF s)) && (decide (new.compareT s bound = Ordering.lt)))

def base2s : List (new.T 2) :=
  (List.range 4).map (fun n =>
    new.T.P (new.Vec.ofFn 2 (fun i => if i.val = 0 then new.T.LF 2 n else new.T.Z)) new.T.Z)

def eqN (a b : new.T 2) : Bool := decide (a = b)
def memN (a : new.T 2) (xs : List (new.T 2)) : Bool := xs.any (fun b => eqN a b)

def nubN : List (new.T 2) → List (new.T 2)
| [] => []
| a::as => if memN a as then nubN as else a :: nubN as

def stepClose (xs : List (new.T 2)) : List (new.T 2) :=
  nubN (xs ++ xs.flatMap (fun s => (List.range 4).map (fun n => new.T.fund s (new.T.ofNat n))))

def clos : Nat → List (new.T 2)
| 0 => base2s
| n+1 => stepClose (clos n)

#eval (List.range 5).map (fun k => (clos k).length)
#eval (List.range 5).map (fun k => ots.all (fun s => memN s (clos k)))
#eval (List.range 5).map (fun k => (ots.filter (fun s => !(memN s (clos k)))).length)

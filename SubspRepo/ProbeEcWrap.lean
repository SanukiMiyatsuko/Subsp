import Subsp.Buchholz.Rank1
import Subsp.new.trans
open T

def genE : Nat → List T
  | 0 => [Z]
  | n + 1 =>
    let p := genE n
    [Z] ++ ([0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b))))

def good0E (x : T) : Bool :=
  (decide (T.isNF1 x)) && ((T.G1 0 x).all (fun y => decide (y < x)))

def propE (s : T) : Bool :=
  (T.G1 0 (T.early_collapse s)).all
    (fun x => decide (x < T.P 1 (T.early_collapse s) T.Z))

def gsE := (genE 3).filter good0E
#eval gsE.length
#eval gsE.all propE
#eval (gsE.find? (fun s => !(propE s))).map reprStr

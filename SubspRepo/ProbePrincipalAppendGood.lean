import Subsp.new.stop_nf_core
open T

def genP : Nat → List T
| 0 => [Z]
| n+1 =>
  let p := genP n
  [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))

def good0 (s:T) : Bool := (T.G1 0 s).all (fun x => decide (x < s))

def prop (p b:T) : Bool :=
  if hp : T.isNF1 p then
    if hb : T.isNF1 b then
      if good0 p then
        if decide (T.head b ≤ p) then good0 (T.add p b) else true
      else true
    else true
  else true

def ps := (genP 2).filter (fun s => match s with | P _ _ Z => true | _ => false)
def bs := genP 2
#eval ps.length
#eval bs.length
#eval (ps.flatMap (fun p => bs.map (fun b => (p,b)))).find? (fun q => !(prop q.1 q.2)) |>.map (fun q => (reprStr q.1, reprStr q.2, reprStr (T.add q.1 q.2), (T.G1 0 (T.add q.1 q.2)).map reprStr))

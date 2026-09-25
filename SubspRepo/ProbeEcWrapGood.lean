import Subsp.new.stop_ec
open T

def gen : Nat → List T
| 0 => [Z]
| n+1 => let p:=gen n; [Z] ++ [0,1,2].flatMap (fun i => p.flatMap (fun a => p.map (fun b => P i a b)))
def nf (x:T):Bool := decide (T.isNF1 x)
def good0 (s:T):Bool := (T.G1 0 s).all (fun x=>decide (x < s))
def prop (s:T):Bool := let e:=T.early_collapse s; let C:=T.card_times 1 (T.one_del e); (T.G1 0 C).all (fun x=>decide (x < T.P 1 C Z))
def xs := (gen 3).filter (fun x => nf x && good0 x)
#eval xs.length
#eval xs.all prop
#eval (xs.find? (fun x => !(prop x))).map (fun x => (reprStr x, reprStr (T.early_collapse x), reprStr (T.card_times 1 (T.one_del (T.early_collapse x)))))

import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def gen2S : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2S n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def ngoodS (s:new.T 2):Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y=>decide (new.compareT y s = Ordering.lt))
def leoldS (a b:T):Bool := decide (a<b) || decide (a=b)
def badXS (s:new.T 2) := (T.G1 0 (_root_.trans s)).find? (fun x => !(new.T.G s).any (fun y => leoldS x (_root_.trans y)))
def xsS := (gen2S 3).filter ngoodS
def badS := xsS.find? (fun s=>(badXS s).isSome)

def showT2 : Nat → new.T 2 → String
| 0, _ => "…"
| _+1, new.T.Z => "Z"
| n+1, new.T.P v a => "P[" ++ showT2 n (v.idx ⟨0, by decide⟩) ++ "," ++ showT2 n (v.idx ⟨1, by decide⟩) ++ "](" ++ showT2 n a ++ ")"

#eval match badS with | none=>"none" | some s=>"src=" ++ showT2 6 s ++ " -> " ++ reprStr (_root_.trans s)++" oldG="++toString ((T.G1 0 (_root_.trans s)).map reprStr)++" newGtrans="++toString ((new.T.G s).map (fun y=>reprStr (_root_.trans y)))++" bad="++match badXS s with | none=>"?" | some x=>reprStr x

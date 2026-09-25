import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def v2 (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def gen2 : Nat → List (new.T 2)
| 0 => [new.T.Z]
| n+1 => let p:=gen2 n; [new.T.Z] ++ p.flatMap (fun a => p.flatMap (fun b => p.map (fun c => new.T.P (v2 a b) c)))
def xs := gen2 2
def badPair := xs.findSome? (fun s => match xs.find? (fun t => !(decide (_root_.trans (new.T.fund s t) = T.fund1 (_root_.trans s) (_root_.trans t)))) with | none => none | some t => some (s,t))
#eval match badPair with | none=>"none" | some (s,t)=> reprStr s++" / "++reprStr t++" => "++reprStr (_root_.trans (new.T.fund s t))++" vs "++reprStr (T.fund1 (_root_.trans s) (_root_.trans t))

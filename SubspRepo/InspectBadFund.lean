import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

def showN {l} : new.T l → String
| new.T.Z => "Z"
| new.T.P ls a => "P[" ++ showV ls ++ ";" ++ showN a ++ "]"
where showV {l k} : new.Vec (new.T l) k → String
| new.Vec.nil => ""
| new.Vec.snoc _ xs x => showV xs ++ "," ++ showN x

def v2 (a b:new.T 2) := new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def z2 : new.T 2 := new.T.Z
def one2 : new.T 2 := new.T.P (v2 z2 z2) z2
-- from bad print P[,P[,Z,P[,Z,Z;Z];Z],Z;Z]
-- top a0 = P vector [Z, P vector [Z,Z] Z] Z ?
def c : new.T 2 := new.T.P (v2 z2 one2) z2
def s : new.T 2 := new.T.P (v2 c z2) z2
#eval showN s
#eval decide (new.T.isNF s)
#eval reprStr (trans c)
#eval reprStr (trans s)
#eval new.T.dom c
#eval T.dom1 (trans c)
#eval new.T.dom s
#eval T.dom1 (trans s)
#eval showN (new.T.fund s (new.T.ofNat 0))
#eval reprStr (trans (new.T.fund s (new.T.ofNat 0)))
#eval reprStr (T.fund1 (trans s) (T.ofNat 0))

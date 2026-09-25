import Subsp.new.subsp

def z2 : new.T 2 := new.T.Z
def v2c (a b:new.T 2) := new.Vec.ofFn 2 (fun i => if i.val=0 then a else b)
def one2 : new.T 2 := new.T.P (v2c z2 z2) z2
-- bad NF from brute: P(P(Z,one;Z),Z;Z)
def u : new.T 2 := new.T.P (v2c z2 one2) z2
def badt : new.T 2 := new.T.P (v2c u z2) z2
-- choose outer head with coord1 = u / maybe big
def big : new.T 2 := new.T.P (v2c z2 u) z2
def par : new.T 2 := new.T.P (v2c big z2) badt

def nfcb (s:new.T 2) : Bool := decide (new.T.isNF s) && (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))
#eval decide (new.T.isNF badt)
#eval nfcb badt
#eval decide (new.T.isNF par)
#eval nfcb par

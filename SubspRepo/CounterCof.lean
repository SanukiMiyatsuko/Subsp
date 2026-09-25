import Subsp.new.subsp

def v2c (a b : new.T 2) : new.Vec (new.T 2) 2 :=
  new.Vec.snoc 1 (new.Vec.snoc 0 new.Vec.nil a) b

def N : new.T 2 := new.T.P (v2c new.T.Z new.T.Z) new.T.Z
def C : new.T 2 := new.T.P (v2c new.T.Z N) new.T.Z
def X : new.T 2 := new.T.P (v2c C new.T.Z) new.T.Z
def A : new.T 2 := new.T.P (v2c C new.T.Z) new.T.Z
def B : new.T 2 := new.T.P (v2c X new.T.Z) new.T.Z
def Bd : new.T 2 := new.T.P (new.Vec.ofFn 2 (fun x => if x.val = 1 then N else new.T.Z)) new.T.Z

#eval decide (new.T.isNF N)
#eval decide (new.T.isNFComp N)
#eval decide (new.T.isNF C)
#eval decide (new.T.isNFComp C)
#eval decide (new.T.isNF X)
#eval decide (new.T.isNFComp X)
#eval decide (new.T.isNF A)
#eval decide (new.T.isNF B)
#eval decide (B < A)
#eval decide (A < Bd)
#eval (List.range 8).map (fun n => decide (B < new.T.fund A (new.T.ofNat n) || B = new.T.fund A (new.T.ofNat n)))
#eval new.T.dom C
#eval new.T.dom A

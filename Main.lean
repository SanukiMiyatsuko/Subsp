import Subsp
import Subsp.new.subsp

def testDecLt {lam : Nat} (a b : new.T lam) : Decidable (a < b) :=
  inferInstance

def testDecEq {lam : Nat} (a b : new.T lam) : Decidable (a = b) :=
  inferInstance

#print axioms testDecLt
#print axioms testDecEq
#print axioms new.T_total
#print axioms new.T.exists_G_not_lt
#print axioms new.T.decForallMem
#print axioms new.T.NFComp_of_ZeroDom
#print axioms new.T.SDom_G_closed

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

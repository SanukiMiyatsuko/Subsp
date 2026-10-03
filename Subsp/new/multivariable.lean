import Subsp.Multivariable
import Subsp.new.subsp

namespace new
namespace Multi
namespace Current

/--
The current fundamental-sequence operation on genuine multivariable terms.
Both arguments are compiled at the common canonical support before invoking the
fixed-arity implementation.
-/
def fund (s t : Term) : Term :=
  let n := Nat.max s.support t.support
  let s' : T n := UTerm.compile n s.code
  let t' : T n := UTerm.compile n t.code
  Term.ofFixed (T.fund s' t')

end Current
end Multi
end new

import Subsp.new.stop
open T
open new

#eval repr (trans (new.T.P (new.Vec.ofFn 3 (fun i => if i.val=2 then new.T.ofNat 1 else new.T.Z)) new.T.Z))
#eval repr (trans (new.T.P (new.Vec.ofFn 3 (fun i => if i.val=1 then new.T.ofNat 1 else new.T.Z)) new.T.Z))
#eval repr (trans (new.T.P (new.Vec.ofFn 3 (fun i => if i.val=0 then new.T.ofNat 1 else new.T.Z)) new.T.Z))
#eval repr (trans (new.T.P (new.Vec.ofFn 3 (fun i => if i.val=2 then new.T.ofNat 2 else if i.val=1 then new.T.ofNat 3 else new.T.ofNat 4)) new.T.Z))

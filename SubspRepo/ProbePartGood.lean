import SubspRepo.DecodeGen
open T
def partSndGood2 (s:T):Bool :=
  if good0 s then good0 (T.part s).2 else true
def partFstGood2 (s:T):Bool :=
  if good0 s then good0 (T.part s).1 else true
#eval (terms 3).find? (fun s => !partSndGood2 s) |>.map rawT
#eval (terms 3).find? (fun s => !partFstGood2 s) |>.map rawT

import ProbePrincipalTransGood
open T
#eval ((gen1P 4).find? (fun a => reprStr (trans a) == "1^1")).map (fun a => reprStr (trans (new.T.P (v1P a) new.T.Z)))

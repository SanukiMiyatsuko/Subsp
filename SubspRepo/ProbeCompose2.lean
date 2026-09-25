import Bridge
open T

def xs : List T := [T.Z, T.P 0 T.Z T.Z, T.P 1 T.Z T.Z, T.P 2 T.Z T.Z, T.P 1 (T.P 3 T.Z T.Z) (T.P 0 T.Z T.Z)]
#eval xs.map (fun c => (c, (List.range 4).map (fun m => T.card_times 1 (T.card_times m c) == T.card_times (m+1) c)))

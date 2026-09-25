import Subsp.new.trans
open T

def terms : Nat → List T
  | 0 => [Z]
  | n + 1 =>
    let xs := terms n
    [Z] ++ [0, 1].flatMap (fun i => xs.flatMap (fun a => xs.map (fun b => P i a b)))

#eval (terms 2).all (fun a => (terms 2).all (fun b => decide (T.card_times 1 (T.add a b) = T.add (T.card_times 1 a) (T.card_times 1 b))))
#eval (terms 2).all (fun c => decide (T.card_times 1 (T.card_times 1 c) = T.card_times 2 c))
#eval (terms 2).all (fun c => decide (T.card_times 1 (T.card_times 2 c) = T.card_times 3 c))

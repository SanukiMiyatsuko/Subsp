import Subsp.new.stop
import SubspRepo.stop_surj_decode

open T

def vzero {A : Type} (z : A) : (k : Nat) → new.Vec A k
| 0 => new.Vec.nil
| k+1 => new.Vec.snoc k (vzero z k) z

def vcons {A : Type} {k : Nat} (a : A) : new.Vec A k → new.Vec A (k+1)
| .nil => .snoc 0 .nil a
| .snoc n xs x => .snoc (n+1) (vcons a xs) x

def only0 {lam : Nat} (a : new.T lam) : new.Vec (new.T lam) lam :=
  new.Vec.ofFn lam (fun i => if i.val = 0 then a else new.T.Z)

def T.unone : T → T
| Z => P 0 Z Z
| P 0 Z b => P 0 Z (P 0 Z b)
| t => t

mutual

def decN : (lam : Nat) → Nat → T → new.T lam
| lam, 0, _ => new.T.Z
| 0, fuel+1, t =>
  match t with
  | T.Z => new.T.Z
  | T.P 0 c d => new.T.P new.Vec.nil (decN 0 fuel d)
  | T.P _ _ _ => new.T.Z
| k+1, fuel+1, t =>
  match t with
  | T.Z => new.T.Z
  | T.P 0 c d => new.T.P (only0 (decC (k+1) fuel c)) (decN (k+1) fuel d)
  | T.P 1 c d =>
      let H := (T.part c).1
      let L := (T.part c).2
      let sum := T.unone (T.uncard1 H)
      let hs := decS (k+1) fuel k sum
      let a0 := decC (k+1) fuel (T.unec L)
      new.T.P (vcons a0 hs) (decN (k+1) fuel d)
  | T.P _ _ _ => new.T.Z

def decC : (lam : Nat) → Nat → T → new.T lam
| 0, _, _ => new.T.Z
| k+1, 0, _ => new.T.Z
| k+1, fuel+1, t =>
  match t with
  | T.Z => new.T.Z
  | T.P 0 c d => new.T.P (only0 (decC (k+1) fuel c)) (decN (k+1) fuel d)
  | T.P 1 c d =>
      let H := (T.part c).1
      let L := (T.part c).2
      let sum := T.unone (T.uncard1 H)
      let hs := decS (k+1) fuel k sum
      let a0 := decC (k+1) fuel (T.unec L)
      new.T.P (vcons a0 hs) (decN (k+1) fuel d)
  | T.P _ _ _ => new.T.Z

def decS : (lam : Nat) → Nat → (k : Nat) → T → new.Vec (new.T lam) k
| lam, 0, k, _ => vzero new.T.Z k
| lam, fuel+1, 0, _ => new.Vec.nil
| lam, fuel+1, k+1, s =>
    let H := (T.part s).1
    let L := (T.part s).2
    let hi := decS lam fuel k (T.uncard1 H)
    let lo := decC lam fuel (T.unec L)
    vcons lo hi

end

def B : Nat → T
| 0 => P 0 (P 0 Z Z) Z
| 1 => P 0 (P 1 Z Z) Z
| n'+2 => P 0 (P 1 (P 1 (mul (P 1 Z Z) (ofNat (n'+1))) Z) Z) Z

def C : Nat → T
| 0 => P 0 Z Z
| 1 => P 1 Z Z
| n'+2 => P 1 (P 1 (mul (P 1 Z Z) (ofNat (n'+1))) Z) Z

def terms : Nat → List T
| 0 => [Z]
| n+1 =>
    let xs := terms n
    [Z] ++ (List.range 3).flatMap
      (fun k => xs.flatMap (fun a => xs.map (fun b => P k a b)))

def good0 (x:T) : Bool :=
  decide (T.isNF1 x) && (T.G1 0 x).all (fun y => decide (y < x))

def nf1b (x:T):Bool := decide (T.isNF1 x)

def chkN (lam depth fuel:Nat) : Bool :=
  (terms depth).all (fun t =>
    if nf1b t && decide (t < B lam) then
      decide (trans (decN lam fuel t) = t) &&
        decide (new.T.isNF (decN lam fuel t))
    else true)

def compB {lam : Nat} (s : new.T lam) : Bool :=
  decide (new.T.isNF s) &&
    (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))

def chkC (lam depth fuel:Nat) : Bool :=
  (terms depth).all (fun t =>
    if good0 t && decide (t < C lam) then
      decide (trans (decC lam fuel t) = t) && compB (decC lam fuel t)
    else true)

#eval (chkN 0 3 20, chkC 0 3 20)
#eval (chkN 1 3 20, chkC 1 3 20)
#eval (chkN 2 3 20, chkC 2 3 20)
#eval (chkN 3 3 20, chkC 3 3 20)
#eval (chkN 4 3 20, chkC 4 3 20)

def badN (lam depth fuel:Nat) := (terms depth).find? (fun t =>
  nf1b t && decide (t < B lam) &&
    !(decide (trans (decN lam fuel t) = t) &&
      decide (new.T.isNF (decN lam fuel t))))

def badC (lam depth fuel:Nat) := (terms depth).find? (fun t =>
  good0 t && decide (t < C lam) &&
    !(decide (trans (decC lam fuel t) = t) && compB (decC lam fuel t)))

#eval (badN 2 3 20).map (fun t => (reprStr t, reprStr (trans (decN 2 20 t))))
#eval (badC 2 3 20).map (fun t => (reprStr t, reprStr (trans (decC 2 20 t))))

def rawT : T → String
| Z => "Z"
| P n a b => "P(" ++ toString n ++ "," ++ rawT a ++ "," ++ rawT b ++ ")"

def dbgC (t:T) :=
  match t with
  | P 1 c d =>
      let H := (T.part c).1
      let L := (T.part c).2
      let u := T.uncard1 H
      let s := T.unone u
      (rawT c, rawT H, rawT L, rawT u, rawT s,
        rawT (T.unec L), rawT (trans (decC 2 20 t)))
  | _ => ("","","","","","","")

#eval match badC 2 3 20 with
  | none => ("","","","","","","")
  | some t => dbgC t

def chkNC (lam depth fuel:Nat) : Bool :=
  (terms depth).all (fun t =>
    if nf1b t && decide (t < C lam) then
      decide (trans (decN lam fuel t) = t) &&
        decide (new.T.isNF (decN lam fuel t))
    else true)

#eval (chkNC 0 3 20, chkNC 1 3 20, chkNC 2 3 20,
  chkNC 3 3 20, chkNC 4 3 20, chkNC 5 3 20)
#eval (chkC 5 3 20, chkN 5 3 20)

def badNC (lam depth fuel:Nat) := (terms depth).find? (fun t =>
  nf1b t && decide (t < C lam) &&
    !(decide (trans (decN lam fuel t) = t) &&
      decide (new.T.isNF (decN lam fuel t))))

#eval (badNC 1 3 20).map (fun t => (rawT t, rawT (trans (decN 1 20 t))))
#eval (badNC 2 3 20).map (fun t => (rawT t, rawT (trans (decN 2 20 t))))
#eval (badNC 3 3 20).map (fun t => (rawT t, rawT (trans (decN 3 20 t))))

def propLow (x:T) : Bool :=
  if good0 x then
    match x with
    | T.P 1 c d =>
      let L := (T.part c).2
      good0 (T.unec L)
    | _ => true
  else true

def badLow (depth:Nat) := (terms depth).find? (fun x => !propLow x)
#eval (badLow 3).map rawT

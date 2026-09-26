import Subsp.new.stop
import SubspRepo.stop_surj_decode
open T

def vzero2 {A : Type} (z : A) : (k : Nat) → new.Vec A k
| 0 => new.Vec.nil
| k+1 => new.Vec.snoc k (vzero2 z k) z

def vcons2 {A : Type} {k : Nat} (a : A) : new.Vec A k → new.Vec A (k+1)
| .nil => .snoc 0 .nil a
| .snoc n xs x => .snoc (n+1) (vcons2 a xs) x

def only02 {lam : Nat} (a : new.T lam) : new.Vec (new.T lam) lam :=
  new.Vec.ofFn lam (fun i => if i.val = 0 then a else new.T.Z)

def T.unone2 : T → T
| Z => P 0 Z Z
| P 0 Z b => P 0 Z (P 0 Z b)
| t => t

mutual
  def decN2 : (lam : Nat) → Nat → T → new.T lam
  | lam, 0, _ => new.T.Z
  | 0, fuel+1, t =>
      match t with
      | T.Z => new.T.Z
      | T.P 0 c d => new.T.P new.Vec.nil (decN2 0 fuel d)
      | _ => new.T.Z
  | k+1, fuel+1, t =>
      match t with
      | T.Z => new.T.Z
      | T.P 0 c d =>
          new.T.P (only02 (decC2 (k+1) fuel c)) (decN2 (k+1) fuel d)
      | T.P 1 c d =>
          let H := (T.part c).1
          let L := (T.part c).2
          let sum := T.unone2 (T.uncard1 H)
          let hs := decS2 (k+1) fuel k sum
          let a0 := decC2 (k+1) fuel (T.unec L)
          new.T.P (vcons2 a0 hs) (decN2 (k+1) fuel d)
      | _ => new.T.Z
  def decC2 : (lam : Nat) → Nat → T → new.T lam
  | 0, _, _ => new.T.Z
  | k+1, 0, _ => new.T.Z
  | k+1, fuel+1, t =>
      match t with
      | T.Z => new.T.Z
      | T.P 0 c d =>
          new.T.P (only02 (decC2 (k+1) fuel c)) (decN2 (k+1) fuel d)
      | T.P 1 c d =>
          let H := (T.part c).1
          let L := (T.part c).2
          let sum := T.unone2 (T.uncard1 H)
          let hs := decS2 (k+1) fuel k sum
          let a0 := decC2 (k+1) fuel (T.unec L)
          new.T.P (vcons2 a0 hs) (decN2 (k+1) fuel d)
      | _ => new.T.Z
  def decS2 : (lam : Nat) → Nat → (k : Nat) → T →
      new.Vec (new.T lam) k
  | lam, 0, k, _ => vzero2 new.T.Z k
  | lam, fuel+1, 0, _ => new.Vec.nil
  | lam, fuel+1, k+1, s =>
      let H := (T.part s).1
      let L := (T.part s).2
      let hi := decS2 lam fuel k (T.uncard1 H)
      let lo := decC2 lam fuel (T.unec L)
      vcons2 lo hi
end

def terms2 : Nat → List T
| 0 => [Z]
| n+1 =>
    let xs := terms2 n
    [Z] ++ (List.range 3).flatMap
      (fun k => xs.flatMap (fun a => xs.map (fun b => P k a b)))

def good02 (x:T):Bool :=
  decide (T.isNF1 x) && (T.G1 0 x).all (fun y => decide (y < x))

def compB2 {lam} (s:new.T lam):Bool :=
  decide (new.T.isNF s) &&
    (new.T.G s).all (fun y => decide (new.compareT y s = Ordering.lt))

def raw2 : T → String
| Z => "Z"
| P n a b => "P(" ++ toString n ++ "," ++ raw2 a ++ "," ++ raw2 b ++ ")"

def auxS2 (lam k fuel:Nat) (s:T) :=
  transAux (vcons2 (new.T.Z : new.T lam) (decS2 lam fuel k s))

def okS2 (lam k fuel:Nat) (s:T):Bool :=
  match auxS2 lam k fuel s with
  | (f,sum,a0) =>
      f && decide (sum=s) && decide (a0=Z) &&
        (new.Vec.toList (decS2 lam fuel k s)).all compB2

def badS2 (lam k depth fuel:Nat) :=
  (terms2 depth).find? (fun s =>
    good02 s &&
    decide (s < T.mul (P 1 Z Z) (T.ofNat k)) &&
    !(okS2 lam k fuel s))

#eval (badS2 3 2 3 20).map (fun s =>
  (raw2 s,
    match auxS2 3 2 20 s with
    | (f,u,a) => (f,raw2 u,raw2 a),
    (new.Vec.toList (decS2 3 20 2 s)).map (fun x => raw2 (trans x))))

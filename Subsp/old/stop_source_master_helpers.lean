import Subsp.old.stop_source_support_lift

/-! Small source-side helpers used by the indexed fundamental-sequence closure proof. -/

namespace new

theorem T.isNF_P_coord_NFComp {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNF (T.P ls add)) (i : Fin lam) :
    T.isNFComp i.val (ls.idx i) :=
  (T.isNF_P_inv ls add hs).1 i

theorem T.head_fund_le {lam : Nat}
    (s t : T lam) :
    T.head (T.fund s t) ≤ T.head s := by
  cases s with
  | Z => exact T.le_refl _
  | P ls add =>
      exact T.head_mono _ _
        (T.fund_lt_self (T.P ls add) t (by intro h; cases h))

theorem T.fund_one_master {lam : Nat}
    (s : T lam) (hs : T.isNF s) (hd : T.dom s = .one) :
    T.isNF (T.fund s T.Z) ∧
      T.SDom T.Z (T.fund s T.Z) s :=
  ⟨T.fund_one_NF s hs hd, T.fund_one_SDom s hd⟩

theorem T.fund_one_NFComp_closed {lam : Nat}
    (u : Nat) (s : T lam)
    (hs : T.isNFComp u s) (hd : T.dom s = .one) :
    T.isNFComp u (T.fund s T.Z) :=
  T.fund_one_NFComp u s T.Z hs hd

theorem T.NFComp_of_SDom_Z {lam : Nat}
    (u : Nat) (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp u a)
    (hs : T.SDom T.Z b a) :
    T.isNFComp u b :=
  T.NFComp_of_SDom_zero u b a hb ha hs

end new

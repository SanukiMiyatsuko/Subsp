import Subsp.old.stop_source_comp0

/-! Component extraction lemmas for indexed source normal forms. -/

namespace new

theorem T.isNFComp_coord_at_index {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNF (T.P ls add)) (i : Fin lam) :
    T.isNFComp i.val (ls.idx i) :=
  (T.isNF_P_inv ls add hs).1 i

theorem T.isNFComp_coord_mono {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNF (T.P ls add)) (i : Fin lam)
    (v : Nat) (hiv : i.val ≤ v) :
    T.isNFComp v (ls.idx i) :=
  T.isNFComp_mono i.val v hiv _ (T.isNFComp_coord_at_index ls add hs i)

end new

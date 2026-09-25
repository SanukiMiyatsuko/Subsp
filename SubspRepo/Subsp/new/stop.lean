import Subsp.order
import Subsp.Buchholz.Base
import Subsp.Buchholz.Rank1
import Subsp.new.Base
import Subsp.new.subsp
import Subsp.new.trans
import Subsp.new.stop_nf_order_c

theorem new.T.OT_iff_NF (lam : Nat) (s : T lam) :
  isOT lam s ↔ isNF s ∧
    (1 < lam → s < P (Vec.ofFn lam (fun x => if x.val = 1 then P (Vec.ofFn lam (fun y => Z)) Z else Z)) Z) := by
  sorry

theorem NF_is_NF1 (lam : Nat) (s : new.T lam) :
  new.T.isNF s → T.isNF1 (trans s) := by
  exact gnf_NF_is_NF1 s

theorem order_embeding (lam : Nat) (s t : new.T lam) (hs : new.T.isNF s) (ht : new.T.isNF t) :
  s < t ↔ trans s < trans t := by
  exact gnf_order_embedding s t hs ht

def new.T.NF (lam : Nat) := { s : T lam // isNF s }

theorem wellfounded_NF (lam : Nat) : WellFounded (fun s t : new.T.NF lam => s.val < t.val) := by
  let R1 := fun x y : T.NF1 => x.1 < y.1
  let RN := fun x y : new.T.NF lam => x.1 < y.1
  have hacc :
      ∀ a : T.NF1, ∀ s : new.T.NF lam,
        trans s.1 = a.1 → Acc RN s := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
      intro s heq
      constructor
      intro t hts
      have htrans : trans t.1 < trans s.1 :=
        (order_embeding lam t.1 s.1 t.2 s.2).mp hts
      have htrans' : trans t.1 < a.1 := by
        rw [← heq]
        exact htrans
      let ta : T.NF1 := ⟨trans t.1, NF_is_NF1 lam t.1 t.2⟩
      exact ih ta htrans' t rfl
  constructor
  intro s
  let a : T.NF1 := ⟨trans s.1, NF_is_NF1 lam s.1 s.2⟩
  exact hacc a s rfl

def T.isSubNF (n : Nat) (s : T) :=
  isNF1 s ∧
    match n with
    | 0 => s < P 0 (P 0 Z Z) Z
    | 1 => s < P 0 (P 1 Z Z) Z
    | n' + 1 => s < P 0 (P 1 (P 1 (mul (P 1 Z Z) (ofNat n')) Z) Z) Z

theorem OT_iff_NF1 (lam : Nat) (s : new.T lam) : new.T.isOT lam s ↔ T.isSubNF lam (trans s) := by
  sorry

def new.T.OT (lam : Nat) := { s : T lam // isOT lam s }

theorem wellfounded_OT (lam : Nat) : WellFounded (fun s t : new.T.OT lam => s.val < t.val) := by
  let RN := fun x y : new.T.NF lam => x.1 < y.1
  let RO := fun x y : new.T.OT lam => x.1 < y.1
  have hacc :
      ∀ s : new.T.NF lam, ∀ hs : new.T.isOT lam s.1,
        Acc RO ⟨s.1, hs⟩ := by
    intro s
    induction s using (wellfounded_NF lam).induction with
    | h s ih =>
      intro hs
      constructor
      intro t hts
      have htnf : new.T.isNF t.1 :=
        ((new.T.OT_iff_NF lam t.1).mp t.2).1
      exact ih ⟨t.1, htnf⟩ hts t.2
  constructor
  intro s
  have hsnf : new.T.isNF s.1 :=
    ((new.T.OT_iff_NF lam s.1).mp s.2).1
  exact hacc ⟨s.1, hsnf⟩ s.2

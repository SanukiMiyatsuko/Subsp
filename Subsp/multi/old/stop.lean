import Subsp.Buchholz.Rank1
import Subsp.multi.old.nt
import Subsp.multi.Assembly
import Subsp.multi.old.surj

def T.SubNF := { s : T // T.isNF1 s ∧ s < P 1 Z Z }

theorem NOT_SubNF_order_iso :
    ∃ f : old.sys.NOT → T.SubNF,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  exact MultiAssembly.order_iso old.sys (fun s => old.NF s ∧ s < old.otb) old.tr (T.P 1 T.Z T.Z)
    old.Inv_base (fun s hs n => old.Inv_fund s hs n) (fun s hs => old.Inv_norm s hs) old.tr_norm
    (fun _ hs => ⟨old.NF_good hs.1, old.tr_lt_bound hs.1 hs.2⟩)
    (fun _ _ hs ht h => old.tr_mono hs.1 ht.1 h)
    (fun s _ hs => old.fund_lt_self s hs _) (fun a b ha hb h => old.cofinal a b ha hb h)
    old.surj (fun s hs => old.le_base s hs.2)

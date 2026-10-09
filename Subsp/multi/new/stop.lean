import Subsp.Buchholz.Rank1
import Subsp.multi.new.nt
import Subsp.multi.Assembly
import Subsp.multi.new.surj

def T.SubNF := { s : T // T.isNF1 s ∧ s < P 0 (P 1 (P 1 (P 1 (P 0 Z Z) Z) Z) Z) Z }

theorem NOT_SubNF_order_iso :
    ∃ f : new.sys.NOT → T.SubNF,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  exact MultiAssembly.order_iso new.sys (fun s => new.NF s ∧ s < new.otb) new.tr new.bound
    new.Inv_base (fun s hs n => new.Inv_fund s hs n) (fun s hs => new.Inv_norm s hs) new.tr_norm
    (fun _ hs => ⟨new.NF_good hs.1, new.tr_lt_bound hs.1 hs.2⟩)
    (fun _ _ hs ht h => new.tr_mono hs.1 ht.1 h)
    (fun s _ hs => new.fund_lt_self s hs _) (fun a b ha hb h => new.cofinal a b ha hb h)
    new.surj (fun s hs => new.le_base s hs.2)

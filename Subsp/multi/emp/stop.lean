import Subsp.Buchholz.Rank1
import Subsp.multi.emp.nt
import Subsp.multi.Assembly
import Subsp.multi.emp.surj

def T.SubNF := { s : T // T.isNF1 s ∧ s < P 0 (P 1 (P 1 (P 0 Z Z) Z) Z) Z }

theorem NOT_SubNF_order_iso :
    ∃ f : emp.sys.NOT → T.SubNF,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) := by
  exact MultiAssembly.order_iso emp.sys emp.NF emp.tr emp.bound
    emp.NF_base (fun s hs n => emp.NF_fund s hs n) (fun _ hs => emp.NF_norm hs) emp.tr_norm
    (fun _ hs => ⟨emp.NF_good hs, emp.tr_lt_bound hs⟩) (fun _ _ hs ht h => emp.tr_mono hs ht h)
    (fun s _ hs => emp.fund_lt_self s hs _) (fun a b ha hb h => emp.cofinal a b ha hb h)
    emp.surj (fun s _ => emp.le_base s)

theorem emp.NOTFundLt_iff_lt (a b : emp.sys.NOT) : emp.sys.NOTFundLt a b ↔ a.val < b.val :=
  MultiAssembly.fundLt_iff_lt emp.sys emp.NF emp.tr
    emp.NF_base (fun s hs n => emp.NF_fund s hs n) (fun _ hs => emp.NF_norm hs)
    (fun _ hs => emp.NF_good hs) (fun _ _ hs ht h => emp.tr_mono hs ht h)
    (fun s _ hs => emp.fund_lt_self s hs _) (fun a b ha hb h => emp.cofinal a b ha hb h) a b

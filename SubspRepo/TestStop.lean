import Subsp.order
import Subsp.Buchholz.Base
import Subsp.Buchholz.Rank1
import Subsp.new.Base
import Subsp.new.subsp
import Subsp.new.trans

open T

 theorem test_new_ofNat_step_lt {lam : Nat} (n : Nat) :
    new.T.ofNat (lam := lam) n < new.T.ofNat (lam := lam) (n + 1) := by
  induction n with
  | zero =>
      change new.T.Z < new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z
      rfl
  | succ n ih =>
      rw [new.T.ofNat, new.T.ofNat]
      exact new.T.P_tail_lt (new.Vec.ofFn lam (fun _ => new.T.Z))
        (new.T.ofNat n) (new.T.ofNat (n + 1)) ih

 theorem test_new_ofNat_NFComp {lam : Nat} (n : Nat) :
    new.T.isNFComp (new.T.ofNat (lam := lam) n) := by
  induction n with
  | zero =>
      exact new.T.isNFComp_Z
  | succ n ih =>
      let zs : new.Vec (new.T lam) lam :=
        new.Vec.ofFn lam (fun _ => new.T.Z)
      have hnf : new.T.isNF (new.T.P zs (new.T.ofNat n)) := by
        apply new.T.isNF.p zs (new.T.ofNat n)
        · intro x hx
          obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx zs x hx
          have hz : zs.idx i = new.T.Z := by
            unfold zs
            rw [new.Vec.ofFn_idx]
          rw [← hi, hz]
          exact new.T.isNF.z
        · exact ih.1
        · intro x hx y hy
          obtain ⟨i, hi⟩ := new.Vec.mem_toList_exists_idx zs x hx
          have hz : zs.idx i = new.T.Z := by
            unfold zs
            rw [new.Vec.ofFn_idx]
          rw [← hi, hz] at hy
          change y ∈ ([] : List (new.T lam)) at hy
          cases hy
        · cases n with
          | zero =>
              change new.T.Z ≤ new.T.P zs new.T.Z
              exact new.T.Z_le (new.T.P zs new.T.Z)
          | succ k =>
              change new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z ≤
                new.T.P zs new.T.Z
              unfold zs
              exact new.T.le_refl (new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z)
      constructor
      · change new.T.isNF (new.T.P zs (new.T.ofNat n))
        exact hnf
      · intro y hy
        change y ∈ new.T.G (new.T.P zs (new.T.ofNat n)) at hy
        cases (new.T.mem_G_P zs (new.T.ofNat n) y).mp hy with
        | inl hv =>
            obtain ⟨i, hcase⟩ := hv
            have hz : zs.idx i = new.T.Z := by
              unfold zs
              rw [new.Vec.ofFn_idx]
            cases hcase with
            | inl heq =>
                rw [heq, hz]
                rfl
            | inr hG =>
                rw [hz] at hG
                change y ∈ ([] : List (new.T lam)) at hG
                cases hG
        | inr hadd =>
            have hylt : y < new.T.ofNat n := ih.2 y hadd
            have hstep : new.T.ofNat (lam := lam) n < new.T.ofNat (lam := lam) (n + 1) :=
              test_new_ofNat_step_lt (lam := lam) n
            change y < new.T.P zs (new.T.ofNat n)
            have htrans : y < new.T.ofNat (lam := lam) (n + 1) :=
              strict_partial_order.trans y (new.T.ofNat (lam := lam) n) (new.T.ofNat (lam := lam) (n + 1)) hylt hstep
            change y < new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) (new.T.ofNat n) at htrans
            exact htrans

#print axioms test_new_ofNat_NFComp

theorem test_new_LF_step_lt (lam n : Nat) :
    new.T.LF lam n < new.T.LF lam (n + 1) := by
  induction n with
  | zero =>
      cases lam with
      | zero =>
          change new.T.Z < new.T.P new.Vec.nil new.T.Z
          rfl
      | succ k =>
          change new.T.Z < new.T.P
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.Z else new.T.Z)) new.T.Z
          rfl
  | succ n ih =>
      cases lam with
      | zero =>
          rw [new.T.LF, new.T.LF]
          exact new.T.P_tail_lt new.Vec.nil (new.T.LF 0 n) (new.T.LF 0 (n + 1)) ih
      | succ k =>
          rw [new.T.LF, new.T.LF]
          apply new.T.P_lt_P_of_compareVec_lt
          apply new.Vec.compare_lt_of_pivot
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.LF (k + 1) n else new.T.Z))
            (new.Vec.ofFn (k + 1) (fun i => if i = k then new.T.LF (k + 1) (n + 1) else new.T.Z))
            (Fin.last k)
          · intro j hj
            have hjle : j.val ≤ k := Nat.lt_succ_iff.mp j.isLt
            have hnot : ¬ k < j.val := Nat.not_lt_of_ge hjle
            exact False.elim (hnot hj)
          · rw [new.Vec.ofFn_idx, new.Vec.ofFn_idx]
            have heq : (Fin.last k : Fin (k + 1)) = k := rfl
            rw [if_pos heq, if_pos heq]
            exact ih

#print axioms test_new_LF_step_lt

theorem test_new_LF_NFComp (lam n : Nat) :
    new.T.isNFComp (new.T.LF lam n) := by
  induction n with
  | zero =>
      exact new.T.isNFComp_Z
  | succ n ih =>
      cases lam with
      | zero =>
          have hnf : new.T.isNF (new.T.P new.Vec.nil (new.T.LF 0 n)) := by
            apply new.T.isNF.p new.Vec.nil (new.T.LF 0 n)
            · intro x hx
              cases hx
            · exact ih.1
            · intro x hx
              cases hx
            · cases n with
              | zero =>
                  change new.T.Z ≤ new.T.P new.Vec.nil new.T.Z
                  exact new.T.Z_le (new.T.P new.Vec.nil new.T.Z)
              | succ m =>
                  change new.T.P new.Vec.nil new.T.Z ≤ new.T.P new.Vec.nil new.T.Z
                  exact new.T.le_refl (new.T.P new.Vec.nil new.T.Z)
          constructor
          · change new.T.isNF (new.T.P new.Vec.nil (new.T.LF 0 n))
            exact hnf
          · intro y hy
            change y ∈ new.T.G (new.T.P new.Vec.nil (new.T.LF 0 n)) at hy
            cases (new.T.mem_G_P new.Vec.nil (new.T.LF 0 n) y).mp hy with
            | inl hv =>
                obtain ⟨i, _⟩ := hv
                exact i.elim0
            | inr hadd =>
                have hylt : y < new.T.LF 0 n := ih.2 y hadd
                have hstep : new.T.LF 0 n < new.T.LF 0 (n + 1) :=
                  test_new_LF_step_lt 0 n
                have htrans : y < new.T.LF 0 (n + 1) :=
                  strict_partial_order.trans y (new.T.LF 0 n) (new.T.LF 0 (n + 1)) hylt hstep
                change y < new.T.P new.Vec.nil (new.T.LF 0 n) at htrans
                exact htrans
      | succ k =>
          let v : new.Vec (new.T (k + 1)) (k + 1) :=
            new.Vec.ofFn (k + 1)
              (fun i => if i = k then new.T.LF (k + 1) n else new.T.Z)
          have hcoord : ∀ i : Fin (k + 1), new.T.isNFComp (v.idx i) := by
            intro i
            unfold v
            rw [new.Vec.ofFn_idx]
            by_cases hi : i.val = k
            · rw [ite_eq_left hi]
              exact ih
            · rw [ite_eq_right hi]
              exact new.T.isNFComp_Z
          have hnf : new.T.isNF (new.T.P v new.T.Z) :=
            new.T.isNF_PZ_of_coords v hcoord
          constructor
          · change new.T.isNF (new.T.P v new.T.Z)
            exact hnf
          · intro y hy
            change y ∈ new.T.G (new.T.P v new.T.Z) at hy
            cases (new.T.mem_G_P v new.T.Z y).mp hy with
            | inl hv =>
                obtain ⟨i, hcase⟩ := hv
                by_cases hi : i.val = k
                · have hvi : v.idx i = new.T.LF (k + 1) n := by
                    unfold v
                    rw [new.Vec.ofFn_idx, ite_eq_left hi]
                  cases hcase with
                  | inl heq =>
                      rw [heq, hvi]
                      have hstep : new.T.LF (k + 1) n < new.T.LF (k + 1) (n + 1) :=
                        test_new_LF_step_lt (k + 1) n
                      change new.T.LF (k + 1) n < new.T.P v new.T.Z
                      change new.T.LF (k + 1) n <
                        new.T.P
                          (new.Vec.ofFn (k + 1)
                            (fun j => if j = k then new.T.LF (k + 1) n else new.T.Z))
                          new.T.Z
                      exact hstep
                  | inr hG =>
                      rw [hvi] at hG
                      have hylt : y < new.T.LF (k + 1) n := ih.2 y hG
                      have hstep : new.T.LF (k + 1) n < new.T.LF (k + 1) (n + 1) :=
                        test_new_LF_step_lt (k + 1) n
                      have htrans : y < new.T.LF (k + 1) (n + 1) :=
                        strict_partial_order.trans y (new.T.LF (k + 1) n)
                          (new.T.LF (k + 1) (n + 1)) hylt hstep
                      change y < new.T.P v new.T.Z
                      change y <
                        new.T.P
                          (new.Vec.ofFn (k + 1)
                            (fun j => if j = k then new.T.LF (k + 1) n else new.T.Z))
                          new.T.Z
                      exact htrans
                · have hvi : v.idx i = new.T.Z := by
                    unfold v
                    rw [new.Vec.ofFn_idx, ite_eq_right hi]
                  cases hcase with
                  | inl heq =>
                      rw [heq, hvi]
                      rfl
                  | inr hG =>
                      rw [hvi] at hG
                      change y ∈ ([] : List (new.T (k + 1))) at hG
                      cases hG
            | inr hz =>
                change y ∈ ([] : List (new.T (k + 1))) at hz
                cases hz

#print axioms test_new_LF_NFComp

theorem test_new_base_succ_NF (k n : Nat) :
    new.T.isNF
      (new.T.P
        (new.Vec.ofFn (k + 1)
          (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
        new.T.Z) := by
  apply new.T.isNF_PZ_of_coords
  intro i
  rw [new.Vec.ofFn_idx]
  by_cases hi : i.val = 0
  · rw [ite_eq_left hi]
    exact (test_new_LF_NFComp (k + 1) n)
  · rw [ite_eq_right hi]
    exact new.T.isNFComp_Z

 theorem test_new_base_succ_bound (k n : Nat) (hk : 1 < k + 1) :
    new.T.P
      (new.Vec.ofFn (k + 1)
        (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
      new.T.Z <
    new.T.P
      (new.Vec.ofFn (k + 1)
        (fun i => if i.val = 1 then
          new.T.P (new.Vec.ofFn (k + 1) (fun _ => new.T.Z)) new.T.Z
        else new.T.Z))
      new.T.Z := by
  apply new.T.P_lt_P_of_compareVec_lt
  let q : Fin (k + 1) := ⟨1, hk⟩
  apply new.Vec.compare_lt_of_pivot
    (new.Vec.ofFn (k + 1)
      (fun i => if i.val = 0 then new.T.LF (k + 1) n else new.T.Z))
    (new.Vec.ofFn (k + 1)
      (fun i => if i.val = 1 then
        new.T.P (new.Vec.ofFn (k + 1) (fun _ => new.T.Z)) new.T.Z
      else new.T.Z)) q
  · intro j hj
    rw [new.Vec.ofFn_idx, new.Vec.ofFn_idx]
    have hj0 : j.val ≠ 0 := by
      intro heq
      rw [heq] at hj
      exact Nat.not_lt_zero 1 hj
    have hj1 : j.val ≠ 1 := by
      intro heq
      rw [heq] at hj
      exact Nat.lt_irrefl 1 hj
    rw [ite_eq_right hj0, ite_eq_right hj1]
  · rw [new.Vec.ofFn_idx, new.Vec.ofFn_idx]
    have hq0 : q.val ≠ 0 := by
      intro h
      change (1 : Nat) = 0 at h
      cases h
    have hq1 : q.val = 1 := rfl
    rw [ite_eq_right hq0, ite_eq_left hq1]
    rfl

 theorem test_new_isOT_sound (lam : Nat) (s : new.T lam)
    (hs : new.T.isOT lam s) :
    new.T.isNF s ∧
      (1 < lam →
        s < new.T.P
          (new.Vec.ofFn lam
            (fun x => if x.val = 1 then
              new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z
            else new.T.Z))
          new.T.Z) := by
  induction hs with
  | base_0 n =>
      constructor
      · exact (test_new_LF_NFComp 0 n).1
      · intro h
        exact False.elim (Nat.not_lt_zero 1 h)
  | base_succ k n =>
      constructor
      · exact test_new_base_succ_NF k n
      · intro hk
        exact test_new_base_succ_bound k n hk
  | step lam a ha n ih =>
      constructor
      · apply new.T.fund_NF_closed a (new.T.ofNat n) ih.1
        intro hd
        exact test_new_ofNat_NFComp n
      · intro hlam
        by_cases haz : a = new.T.Z
        · rw [haz, new.T.fund]
          rfl
        · have hfall : new.T.fund a (new.T.ofNat n) < a :=
            new.T.fund_lt_self a (new.T.ofNat n) haz
          exact strict_partial_order.trans
            (new.T.fund a (new.T.ofNat n)) a
            (new.T.P
              (new.Vec.ofFn lam
                (fun x => if x.val = 1 then
                  new.T.P (new.Vec.ofFn lam (fun _ => new.T.Z)) new.T.Z
                else new.T.Z))
              new.T.Z)
            hfall (ih.2 hlam)

#print axioms test_new_isOT_sound

theorem test_new_LF_cofinal (lam : Nat) (s : new.T lam)
    (hs : new.T.isNF s) : ∃ n : Nat, s < new.T.LF lam n := by
  let motive : Nat → Prop :=
    fun m => ∀ (k : Nat) (a : new.T k), new.T.size a = m →
      new.T.isNF a → ∃ n : Nat, a < new.T.LF k n
  have main : ∀ m : Nat, motive m := by
    intro m
    exact Nat.strongRecOn m (motive := motive) (fun m ih => by
      intro k a hsize ha
      cases a with
      | Z =>
          exact ⟨1, test_new_LF_step_lt k 0⟩
      | P ls add =>
          cases k with
          | zero =>
              cases ls with
              | nil =>
                  have hadd : new.T.isNF add := by
                    cases ha with
                    | p _ _ _ h1 _ _ => exact h1
                  have hsz : new.T.size add < m := by
                    have hh := new.T.add_size_lt_P new.Vec.nil add
                    rw [hsize] at hh
                    exact hh
                  obtain ⟨n, hn⟩ := ih (new.T.size add) hsz 0 add rfl hadd
                  refine ⟨n + 1, ?_⟩
                  rw [new.T.LF]
                  exact new.T.P_tail_lt new.Vec.nil add (new.T.LF 0 n) hn
          | succ k =>
              let q : Fin (k + 1) := Fin.last k
              have hqnf : new.T.isNF (ls.idx q) := by
                have hc := new.T.isNF_P_coord_NFComp ls add ha q
                exact hc.1
              have hqsz : new.T.size (ls.idx q) < m := by
                have hh : new.T.size (ls[q]) < new.T.size (new.T.P ls add) :=
                  new.T.idx_size_lt_P ls add q
                rw [new.Vec.getElem_eq_idx] at hh
                rw [hsize] at hh
                exact hh
              obtain ⟨n, hn⟩ := ih (new.T.size (ls.idx q)) hqsz
                (k + 1) (ls.idx q) rfl hqnf
              refine ⟨n + 1, ?_⟩
              rw [new.T.LF]
              apply new.T.P_lt_P_of_compareVec_lt
              apply new.Vec.compare_lt_of_pivot ls
                (new.Vec.ofFn (k + 1)
                  (fun i => if i.val = k then new.T.LF (k + 1) n else new.T.Z)) q
              · intro j hj
                have hjle : j.val ≤ k := Nat.lt_succ_iff.mp j.isLt
                have hnot : ¬ k < j.val := Nat.not_lt_of_ge hjle
                exact False.elim (hnot hj)
              · rw [new.Vec.ofFn_idx]
                have hq : q.val = k := rfl
                rw [ite_eq_left hq]
                exact hn)
  exact main (new.T.size s) lam s rfl hs

#print axioms test_new_LF_cofinal

theorem test_stand_eq_self_of_NF1 (s : T) (hs : T.isNF1 s) :
    T.stand s = s := by
  induction hs with
  | z => rfl
  | p s0 s1 s2 hs1 hs2 hg hh ih1 ih2 =>
      rw [T.stand]
      rw [ih2]
      rw [ite_eq_left hh]

#print axioms test_stand_eq_self_of_NF1

theorem test_NF1_index_self_all (s : T) (hs : T.isNF1 s) :
    match s with
    | T.Z => True
    | T.P p a b => T.index_Prop1 p (T.P p a b) := by
  induction hs with
  | z => exact True.intro
  | p p a b ha hb hg hh iha ihb =>
      apply T.index_Prop1.p p a b (Nat.le_refl p)
      cases b with
      | Z => exact T.index_Prop1.z
      | P q c d =>
          have hhead : T.P q c T.Z ≤ T.P p a T.Z := hh
          have hqp : q ≤ p := head_le_index q p c a hhead
          have hq : T.index_Prop1 q (T.P q c d) := ihb
          exact Rank1Termination.index_mono hqp (T.P q c d) hq

theorem test_NF1_index_self (p : Nat) (a b : T)
    (hs : T.isNF1 (T.P p a b)) :
    T.index_Prop1 p (T.P p a b) :=
  test_NF1_index_self_all (T.P p a b) hs

theorem test_part_add (s : T) :
    T.add (T.part s).1 (T.part s).2 = s := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
      rw [T.part]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        rfl
      · rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            have ih : T.add c d = b := by
              have h := ihb
              rw [hpart] at h
              exact h
            change T.add (T.P p a c) d = T.P p a b
            rw [T.P_add_eq, ih]

theorem test_part_fst_head_le (s : T) :
    T.head (T.part s).1 ≤ T.head s := by
  cases s with
  | Z =>
      change T.Z ≤ T.Z
      exact Or.inr rfl
  | P p a b =>
      rw [T.part]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact T.Z_le (T.head (T.P p a b))
      · rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            change T.P p a T.Z ≤ T.P p a T.Z
            exact Or.inr rfl

theorem test_part_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part s).1 ∧ T.isNF1 (T.part s).2 := by
  induction hs with
  | z => exact ⟨T.isNF1.z, T.isNF1.z⟩
  | p p a b ha hb hg hh iha ihb =>
      rw [T.part]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact ⟨T.isNF1.z, T.isNF1.p p a b ha hb hg hh⟩
      · rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            have hcnf : T.isNF1 c := by
              have h := ihb.1
              rw [hpart] at h
              exact h
            have hdnf : T.isNF1 d := by
              have h := ihb.2
              rw [hpart] at h
              exact h
            have hcle : T.head c ≤ T.head b := by
              have h := test_part_fst_head_le b
              rw [hpart] at h
              exact h
            have hhead : T.head c ≤ T.P p a T.Z :=
              partial_order.trans (T.head c) (T.head b) (T.P p a T.Z) hcle hh
            exact ⟨T.isNF1.p p a c ha hcnf hg hhead, hdnf⟩

theorem test_lt_P_change_tail_of_size_le (x : T) (p : Nat) (a b c : T)
    (h : x < T.P p a b) (hsz : x.size ≤ a.size) :
    x < T.P p a c := by
  cases x with
  | Z => exact T.Lt.Z_lt_P p a c
  | P q d e =>
      cases lt_inv q d e p a b h with
      | inl hh => exact T.Lt.p_head q p d a e c hh
      | inr hor =>
          cases hor with
          | inl hm =>
              cases hm.1
              exact T.Lt.p_mid p d a e c hm.2
          | inr ht =>
              cases ht.1
              cases ht.2.1
              have hgt : a.size < (T.P p a e).size :=
                T.size_lt_size_P_left p a e
              exact False.elim ((Nat.not_lt_of_ge hsz) hgt)

theorem test_G1_add (u : Nat) (a b : T) :
    T.G1 u (T.add a b) = T.G1 u a ++ T.G1 u b := by
  induction a with
  | Z =>
      rw [T.add]
      rw [T.G1.eq_1]
      rw [List.nil_append]
  | P p x y ihx ihy =>
      cases b with
      | Z =>
          rw [T.add_Z]
          rw [T.G1.eq_1]
          rw [List.append_nil]
      | P q c d =>
          rw [T.P_add_eq]
          rw [T.G1.eq_2, T.G1.eq_2]
          by_cases hup : u ≤ p
          · rw [ite_eq_left hup, ite_eq_left hup]
            rw [ihy]
            rw [← List.append_assoc]
          · rw [ite_eq_right hup, ite_eq_right hup]
            exact ihy

theorem test_add_interval_size_le (a b x : T)
    (hax : a ≤ x) (hxu : x < T.add a b) :
    a.size ≤ x.size := by
  induction a generalizing x with
  | Z => exact Nat.zero_le x.size
  | P p c d ihc ihd =>
      cases hax with
      | inr heq =>
          rw [heq]
          exact Nat.le_refl x.size
      | inl hlt =>
          have hu : T.add (T.P p c d) b = T.P p c (T.add d b) :=
            T.P_add_eq p c d b
          rw [hu] at hxu
          obtain ⟨e, hex, hde, heu⟩ :=
            sandwich_tail p c d x (T.add d b) hlt hxu
          rw [hex]
          have hsz : d.size ≤ e.size :=
            ihd e (Or.inl hde) heu
          change c.size + d.size + 1 ≤ c.size + e.size + 1
          exact Nat.add_le_add_right (Nat.add_le_add_left hsz c.size) 1

theorem test_good0_part_fst (s : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 0 s, x < s) :
    ∀ x ∈ T.G1 0 (T.part s).1, x < (T.part s).1 := by
  intro x hx
  let a := (T.part s).1
  let b := (T.part s).2
  have hadd : T.add a b = s := by
    unfold a b
    exact test_part_add s
  have hxadd : x ∈ T.G1 0 (T.add a b) := by
    rw [test_G1_add]
    exact List.mem_append_left (T.G1 0 b) hx
  have hxsin : x ∈ T.G1 0 s := by
    rw [← hadd]
    exact hxadd
  have hxs : x < s := hg x hxsin
  have hxsz : x.size < a.size := G1_size_lt 0 a x hx
  cases lt_total_thm x a with
  | inl hxa => exact hxa
  | inr hor =>
      cases hor with
      | inl hax =>
          have hsz : a.size ≤ x.size := by
            apply test_add_interval_size_le a b x (Or.inl hax)
            rw [hadd]
            exact hxs
          exact False.elim ((Nat.not_lt_of_ge hsz) hxsz)
      | inr heq =>
          rw [heq] at hxsz
          exact False.elim (Nat.lt_irrefl a.size hxsz)

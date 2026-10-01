import Subsp.old.stop_vector_order

/-! Conditional order and normal-form preservation from smaller indexed components. -/

namespace LegacyTranslation

def GoodAt {lam : Nat} (u : Nat) (s : new.T lam) : Prop :=
  T.isNF1 (trans s) ∧ ∀ x ∈ T.G1 u (trans s), x < trans s

theorem good_index_lt_wrap (k : Nat) (a b : T)
    (hi : T.index_Prop1 k a)
    (hg : ∀ x : T, x ∈ T.G1 k a → x < a) :
    a < T.P k a b := by
  cases hi with
  | z => exact T.Lt.Z_lt_P _ _ _
  | p p c d hp _ =>
      rcases Nat.eq_or_lt_of_le hp with rfl | hp
      · exact T.Lt.p_mid _ _ _ _ _ (hg c (by simp [T.G1]))
      · exact T.Lt.p_head _ _ _ _ _ _ hp

theorem good_wrap_support (u k : Nat) (a : T)
    (huk : u ≤ k) (hi : T.index_Prop1 k a)
    (hgk : ∀ x : T, x ∈ T.G1 k a → x < a)
    (hgu : ∀ x : T, x ∈ T.G1 u a → x < a) :
    ∀ x : T, x ∈ T.G1 u (T.P k a T.Z) → x < T.P k a T.Z := by
  intro x hx
  have ha : a < T.P k a T.Z := good_index_lt_wrap k a T.Z hi hgk
  simp only [T.G1, huk, ite_true, List.append_nil, List.mem_append,
    List.mem_singleton] at hx
  rcases hx with rfl | hx
  · exact ha
  · exact lt_trans_thm _ _ _ (hgu x hx) ha


theorem order_preserve_bounded {lam : Nat} (N : Nat)
    (hgood : ∀ (s : new.T lam), new.T.size s < N →
      ∀ u, new.T.isNFComp u s → GoodAt u s)
    (s t : new.T lam) (hsz : new.T.size s ≤ N) (htz : new.T.size t ≤ N)
    (hs : new.T.isNF s) (ht : new.T.isNF t) (hlt : s < t) : trans s < trans t := by
  induction s using (measure new.T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z =>
          cases t with
          | Z => cases hlt
          | P w b =>
              obtain ⟨p, a, he, _⟩ := aux_principal w
              rw [trans_as_add, he, p_zero_add]
              exact .Z_lt_P _ _ _
      | P v a =>
          cases t with
          | Z => cases hlt
          | P w b =>
              obtain ⟨hv, ha, _⟩ := new.T.isNF_P_inv v a hs
              obtain ⟨hw, hb, _⟩ := new.T.isNF_P_inv w b ht
              change (match new.compareVec v w with
                | .eq => new.compareT a b | ord => ord) = .lt at hlt
              cases hc : new.compareVec v w with
              | lt =>
                  apply trans_lt_of_vec_lt v w a b
                  · intro i
                    exact hgood _ (Nat.lt_of_lt_of_le (new.T.idx_size_lt_P v a i) hsz) i.val (hv i)
                  · intro i
                    exact hgood _ (Nat.lt_of_lt_of_le (new.T.idx_size_lt_P w b i) htz) i.val (hw i)
                  · intro i hi
                    exact ih _ (new.T.idx_size_lt_P v a i) _
                      (Nat.le_trans (Nat.le_of_lt (new.T.idx_size_lt_P v a i)) hsz)
                      (Nat.le_trans (Nat.le_of_lt (new.T.idx_size_lt_P w b i)) htz)
                      (hv i).1 (hw i).1 hi
                  · exact hc
              | eq =>
                  obtain rfl := new.Vec_eq_sound v w hc
                  rw [new.Vec_refl] at hlt
                  rw [trans_as_add, trans_as_add]
                  exact add_left_lt _ _ _ (ih a (new.T.add_size_lt_P v a) b
                    (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P v a)) hsz)
                    (Nat.le_trans (Nat.le_of_lt (new.T.add_size_lt_P v b)) htz) ha hb hlt)
              | gt => simp [hc] at hlt

theorem NF_step {lam : Nat} (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (hs : new.T.isNF (new.T.P v a))
    (hnf : ∀ s : new.T lam, new.T.size s < new.T.size (new.T.P v a) →
      new.T.isNF s → T.isNF1 (trans s))
    (hgood : ∀ s : new.T lam, new.T.size s < new.T.size (new.T.P v a) →
      ∀ u, new.T.isNFComp u s → GoodAt u s) :
    T.isNF1 (trans (new.T.P v a)) := by
  obtain ⟨hv, ha, hh⟩ := new.T.isNF_P_inv v a hs
  have hvg : VecGood v := fun i => hgood _ (new.T.idx_size_lt_P v a i) i.val (hv i)
  have hhead : T.head (trans a) ≤ (transAux v).1 := by
    cases a with
    | Z => exact T.Z_le _
    | P w b =>
        rw [trans_P_head]
        obtain ⟨hw, _, _⟩ := new.T.isNF_P_inv w b ha
        have hwg : VecGood w := fun i => hgood _
          (Nat.lt_trans (new.T.idx_size_lt_P w b i) (new.T.add_size_lt_P v _)) i.val (hw i)
        rcases hh with hh | hh
        · have hcmp : new.compareVec w v = .lt := by
            change (match new.compareVec w v with | .eq => Ordering.eq | ord => ord) = .lt at hh
            cases he : new.compareVec w v <;> simp_all
          apply Or.inl
          apply aux_head_lt w v hwg hvg
          · intro i hi
            exact order_preserve_bounded (new.T.size (new.T.P v (new.T.P w b))) hgood _ _
              (Nat.le_of_lt (Nat.lt_trans (new.T.idx_size_lt_P w b i) (new.T.add_size_lt_P v _)))
              (Nat.le_of_lt (new.T.idx_size_lt_P v _ i)) (hw i).1 (hv i).1 hi
          · exact hcmp
        · have he : new.T.P w new.T.Z = new.T.P v new.T.Z := new.T_eq_sound _ _ hh
          cases he
          exact Or.inr rfl
  have htail := hnf a (new.T.add_size_lt_P v a) ha
  have hprincipal := aux_head_closed v hvg
  obtain ⟨p, b, he, _⟩ := aux_principal v
  rw [he] at hprincipal hhead
  rw [trans_as_add, he, p_zero_add]
  obtain ⟨hb, _, hg, _⟩ := T.isNF1_P_inv _ _ _ hprincipal
  exact .p p b (trans a) hb htail hg hhead

end LegacyTranslation

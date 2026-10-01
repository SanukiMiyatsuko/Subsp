import Subsp.old.stop_types
import Subsp.old.stop_basic

/-! Constructive order isomorphisms in dimensions zero and one. -/

namespace LegacyZero

def length : new.T 0 → Nat
  | .Z => 0
  | .P _ a => length a + 1

theorem eq_ofNat (s : new.T 0) : s = new.T.ofNat (length s) := by
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v a _ ih => cases v; exact congrArg (new.T.P new.Vec.nil) ih
  | nil => trivial
  | snoc => trivial

theorem length_ofNat (n : Nat) : length (new.T.ofNat (lam := 0) n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

theorem LF_ofNat (n : Nat) : new.T.LF 0 n = new.T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (new.T.P new.Vec.nil) ih

theorem isOT (s : new.T 0) : new.T.isOT 0 s :=
  eq_ofNat s ▸ (LF_ofNat (length s) ▸ new.T.isOT.base_0 (length s))

theorem lt_ofNat (n m : Nat) :
    new.T.ofNat (lam := 0) n < new.T.ofNat m ↔ n < m := by
  change (new.compareT (new.T.ofNat n) (new.T.ofNat m) = .lt) ↔ n < m
  induction m generalizing n with
  | zero => cases n <;> simp [new.T.ofNat, new.compareT]
  | succ m ih =>
      cases n with
      | zero => simp [new.T.ofNat, new.compareT]
      | succ n =>
          simpa only [new.T.ofNat, new.Vec.ofFn,
            new.compareT, new.compareVec, Nat.succ_lt_succ_iff] using ih n

theorem lt_one_eq_zero (s : T) (h : s < T.P 0 T.Z T.Z) : s = T.Z := by
  cases h with
  | Z_lt_P => rfl
  | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
  | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h

theorem IsN_of_head_le_one (s : T) (hs : T.isNF1 s)
    (hh : T.head s ≤ T.P 0 T.Z T.Z) : T.IsN s := by
  induction hs with
  | z => exact .zero
  | p p a b ha hb hg hhead _ ih =>
      rcases hh with hh | hh
      · cases hh with
        | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
        | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
      · cases hh
        exact .succ b (ih hhead)

theorem IsN_of_SubNF (s : T) (hs : T.isSubNF 0 s) : T.IsN s := by
  cases hs.2 with
  | Z_lt_P => exact .zero
  | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
  | p_mid _ a _ _ _ h =>
      have ha := lt_one_eq_zero a h
      subst a
      exact IsN_of_head_le_one _ hs.1 (Or.inr rfl)
  | p_tail _ _ _ _ h => cases h

theorem ofNat_SubNF (n : Nat) : T.isSubNF 0 (T.ofNat n) := by
  refine ⟨IsN_isNF1 _ (ofNat_IsN n), ?_⟩
  cases n with
  | zero => exact .Z_lt_P _ _ _
  | succ n => exact .p_mid _ _ _ _ _ (.Z_lt_P _ _ _)

def map (s : new.T.OT 0) : T.SubNF 0 :=
  ⟨T.ofNat (length s.val), ofNat_SubNF (length s.val)⟩

theorem map_injective (s t : new.T.OT 0) (h : map s = map t) : s = t := by
  have hn : length s.val = length t.val := by
    have he : T.ofNat (length s.val) = T.ofNat (length t.val) := congrArg Subtype.val h
    rcases Nat.lt_trichotomy (length s.val) (length t.val) with hn | hn | hn
    · exact False.elim (lt_irrefl_thm _ (he ▸ ofNat_strict_mono hn))
    · exact hn
    · exact False.elim (lt_irrefl_thm _ (he ▸ ofNat_strict_mono hn))
  exact Subtype.ext ((eq_ofNat s.val).trans ((congrArg new.T.ofNat hn).trans (eq_ofNat t.val).symm))

theorem map_surjective (t : T.SubNF 0) : ∃ s : new.T.OT 0, map s = t := by
  obtain ⟨n, hn⟩ := IsN_exists_ofNat (IsN_of_SubNF t.val t.property)
  refine ⟨⟨new.T.ofNat n, isOT _⟩, Subtype.ext ?_⟩
  exact (congrArg T.ofNat (length_ofNat n)).trans hn.symm

theorem map_lt_iff (s t : new.T.OT 0) :
    s.val < t.val ↔ (map s).val < (map t).val := by
  rw [eq_ofNat s.val, eq_ofNat t.val, lt_ofNat]
  exact ⟨ofNat_strict_mono, ofNat_reflect_lt⟩

end LegacyZero

theorem OT_SubNF_order_iso_zero :
    ∃ f : new.T.OT 0 → T.SubNF 0,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) :=
  ⟨LegacyZero.map, LegacyZero.map_injective,
    LegacyZero.map_surjective, LegacyZero.map_lt_iff⟩

namespace LegacyOne

def vec (a : new.T 1) : new.Vec (new.T 1) 1 := .snoc 0 .nil a

mutual
  def encode : new.T 1 → T
    | .Z => .Z
    | .P v b => .P 0 (encodeVec v) (encode b)
  def encodeVec : {n : Nat} → new.Vec (new.T 1) n → T
    | _, .nil => .Z
    | _, .snoc _ _ a => encode a
end

def decode : T → new.T 1
  | .Z => .Z
  | .P _ a b => .P (vec (decode a)) (decode b)

theorem encode_P (a b : new.T 1) :
    encode (.P (vec a) b) = T.P 0 (encode a) (encode b) := rfl

theorem decode_encode (s : new.T 1) : decode (encode s) = s := by
  induction s using new.T.rec
      (motive_2 := fun _ v => ∀ x ∈ new.Vec.toList v, decode (encode x) = x) with
  | Z => rfl
  | P v b hv hb =>
      cases v with
      | snoc _ vs a =>
          cases vs
          change new.T.P (vec (decode (encode a))) (decode (encode b)) = _
          rw [hv a (by simp [new.Vec.toList]), hb]
          rfl
  | nil x hx => cases hx
  | snoc _ xs a ihxs iha x hx =>
      rcases List.mem_append.mp hx with hx | hx
      · exact ihxs x hx
      · obtain rfl := List.mem_singleton.mp hx; exact iha

theorem encode_injective {s t : new.T 1} (h : encode s = encode t) : s = t :=
  (decode_encode s).symm.trans ((congrArg decode h).trans (decode_encode t))

theorem encode_ne_zero {s : new.T 1} (h : s ≠ new.T.Z) : encode s ≠ T.Z :=
  fun hs => h (encode_injective hs)

theorem compare_vec (a b : new.T 1) : new.compareVec (vec a) (vec b) = new.compareT a b := by
  cases h : new.compareT a b <;> simp [vec, new.compareVec, h]

theorem encode_lt_iff (s t : new.T 1) : s < t ↔ encode s < encode t := by
  induction s using new.T.rec
      (motive_2 := fun _ v => ∀ x ∈ new.Vec.toList v, ∀ t, x < t ↔ encode x < encode t) generalizing t with
  | Z =>
      cases t with
      | Z =>
          constructor
          · intro h; cases h
          · intro h; cases h
      | P v b => exact ⟨fun _ => .Z_lt_P _ _ _, fun _ => rfl⟩
  | P v b hv hb =>
      cases v with
      | snoc _ vs a =>
          cases vs
          have ha := hv a (by simp [new.Vec.toList])
          cases t with
          | Z =>
              constructor
              · intro h; cases h
              · intro h; cases h
          | P w d =>
              cases w with
              | snoc _ ws c =>
                  cases ws
                  change new.T.P (vec a) b < new.T.P (vec c) d ↔
                    T.P 0 (encode a) (encode b) < T.P 0 (encode c) (encode d)
                  constructor
                  · intro h
                    change (match new.compareVec (vec a) (vec c) with
                      | .eq => new.compareT b d | ord => ord) = .lt at h
                    rw [compare_vec] at h
                    cases hc : new.compareT a c with
                    | lt => exact .p_mid _ _ _ _ _ ((ha c).mp hc)
                    | eq =>
                        obtain rfl := new.T_eq_sound a c hc
                        rw [new.T_refl] at h
                        exact .p_tail _ _ _ _ ((hb d).mp h)
                    | gt => simp [hc] at h
                  · intro h
                    change (match new.compareVec (vec a) (vec c) with
                      | .eq => new.compareT b d | ord => ord) = .lt
                    rw [compare_vec]
                    rcases lt_inv 0 (encode a) (encode b) 0 (encode c) (encode d) h with hhead | ⟨_, hmid⟩ | ⟨_, he, htail⟩
                    · exact False.elim (Nat.not_lt_zero _ hhead)
                    · have hc := (ha c).mpr hmid
                      change new.compareT a c = .lt at hc
                      rw [hc]
                    · obtain rfl := encode_injective he
                      rw [new.T_refl]
                      exact (hb d).mpr htail
  | nil x hx => cases hx
  | snoc _ xs a ihxs iha x hx t =>
      rcases List.mem_append.mp hx with hx | hx
      · exact ihxs x hx t
      · obtain rfl := List.mem_singleton.mp hx; exact iha t

def liftDom : Dom1 → new.Dom 1
  | .Zero => .zero
  | .One => .one
  | .ω => .omega
  | .Ω _ => .omega

theorem dom_encode (s : new.T 1) : new.T.dom s = liftDom (T.dom1 (encode s)) := by
  induction s using new.T.rec
      (motive_2 := fun _ v => ∀ x ∈ new.Vec.toList v, new.T.dom x = liftDom (T.dom1 (encode x))) with
  | Z => rfl
  | P v b hv hb =>
      cases v with
      | snoc _ vs a =>
          cases vs
          have ha := hv a (by simp [new.Vec.toList])
          by_cases hz : b = new.T.Z
          · subst b
            cases hd : T.dom1 (encode a) <;>
              simp [encode, encodeVec, new.T.dom, new.T.domVecMinIdx, ha,
                hd, liftDom, T.dom1]
          · simpa [encode, encodeVec, new.T.dom, T.dom1, hz, encode_ne_zero hz] using hb
  | nil x hx => cases hx
  | snoc _ xs a ihxs iha x hx =>
      rcases List.mem_append.mp hx with hx | hx
      · exact ihxs x hx
      · obtain rfl := List.mem_singleton.mp hx; exact iha

theorem dom_not_Omega (s : new.T 1) (l : Nat) : T.dom1 (encode s) ≠ .Ω l := by
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => intro h; cases h
  | P v b _ hb =>
      by_cases hz : b = new.T.Z
      · subst b
        cases hd : T.dom1 (encodeVec v) <;> simp [encode, T.dom1, hd]
      · simpa [encode, T.dom1, encode_ne_zero hz] using hb
  | nil => trivial
  | snoc => trivial

theorem encode_oplus (s t : new.T 1) : encode (s + t) = T.add (encode s) (encode t) := by
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v b _ ih =>
      change T.P 0 (encodeVec v) (encode (b + t)) = T.add (T.P 0 (encodeVec v) (encode b)) (encode t)
      rw [ih, T.P_add_eq]
  | nil => trivial
  | snoc => trivial

theorem add_mul_comm (s t : T) : T.add s (T.mul s t) = T.add (T.mul s t) s := by
  induction t with
  | Z => cases s <;> rfl
  | P _ _ b _ ih =>
      change T.add s (T.add (T.mul s b) s) = T.add (T.add (T.mul s b) s) s
      rw [← Rank1Termination.add_assoc, ih]

theorem encode_mul (s t : new.T 1) : encode (new.T.mul s t) = T.mul (encode s) (encode t) := by
  induction t using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v b _ ih =>
      rw [new.T.mul, encode_oplus, ih]
      change T.add (encode s) (T.mul (encode s) (encode b)) = T.add (T.mul (encode s) (encode b)) (encode s)
      exact add_mul_comm _ _
  | nil => trivial
  | snoc => trivial

theorem encode_ofNat (n : Nat) : encode (new.T.ofNat n) = T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (T.P 0 T.Z) ih

theorem vec_rplc (a b : new.T 1) (i : Fin 1) : (vec a).rplc i b = vec b := by
  have hi : i = ⟨0, by decide⟩ := Fin.eq_of_val_eq (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
  subst i
  rfl

theorem dom_min_vec (a : new.T 1) :
    new.T.domVecMinIdx (vec a) =
      if new.T.dom a = .zero then none else some (⟨0, by decide⟩, new.T.dom a) := rfl

theorem encode_fund (s t : new.T 1) : encode (new.T.fund s t) = T.fund1 (encode s) (encode t) := by
  induction s using (measure new.T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z => rw [new.T.fund]; rfl
      | P v b =>
          cases v with
          | snoc _ vs a =>
              cases vs
              have ha (u) := ih a (new.T.idx_size_lt_P (vec a) b ⟨0, by decide⟩) u
              have hb (u) := ih b (new.T.add_size_lt_P (vec a) b) u
              change encode (new.T.fund (new.T.P (vec a) b) t) = T.fund1 (T.P 0 (encode a) (encode b)) (encode t)
              by_cases hz : b = new.T.Z
              · subst b
                change encode (new.T.fund (new.T.P (vec a) new.T.Z) t) = T.fund1 (T.P 0 (encode a) T.Z) (encode t)
                cases hd : T.dom1 (encode a) with
                | Zero =>
                    have haz : a = new.T.Z := encode_injective (dom1_Zero_imp_eq_Z _ hd)
                    subst a
                    rw [new.T.fund, fund1_P0_of_Zero _ _ hd]
                    simp [vec, new.T.domVecMinIdx, new.T.dom, encode]
                | One =>
                    rw [new.T.fund, ite_eq_left rfl, fund1_P0_of_One _ _ hd]
                    simp only [dom_min_vec, dom_encode a, hd, liftDom, reduceCtorEq, ite_false]
                    simp only [vec_rplc]
                    rw [encode_mul, encode_P]
                    change T.mul (T.P 0 (encode (new.T.fund a new.T.Z)) T.Z) (encode t) = _
                    rw [ha]
                    rfl
                | ω =>
                    rw [new.T.fund, ite_eq_left rfl, fund1_P0_of_ω _ _ hd]
                    simp only [dom_min_vec, dom_encode a, hd, liftDom, reduceCtorEq, ite_false]
                    simp only [vec_rplc]
                    rw [encode_P]
                    change T.P 0 (encode (new.T.fund a t)) T.Z = _
                    rw [ha]
                | Ω l => exact False.elim (dom_not_Omega a l hd)
              · rw [new.T.fund, ite_eq_right hz]
                change T.P 0 (encode a) (encode (new.T.fund b t)) = _
                rw [hb]
                rw [T.fund1, ite_eq_right (encode_ne_zero hz)]

inductive ZeroIndices : T → Prop where
  | z : ZeroIndices .Z
  | p (a b : T) : ZeroIndices a → ZeroIndices b → ZeroIndices (.P 0 a b)

theorem encode_decode (s : T) (h : ZeroIndices s) : encode (decode s) = s := by
  induction h with
  | z => rfl
  | p a b _ _ ha hb =>
      change T.P 0 (encode (decode a)) (encode (decode b)) = _
      rw [ha, hb]

def tower : Nat → T
  | 0 => .Z
  | n + 1 => .P 0 (tower n) .Z

theorem tower_lt_next (n : Nat) : tower n < tower (n + 1) := by
  induction n with
  | zero => exact .Z_lt_P _ _ _
  | succ n ih => exact .p_mid _ _ _ _ _ ih

theorem tower_nf (n : Nat) :
    T.isNF1 (tower n) ∧ ∀ x ∈ T.G1 0 (tower n), x < tower n := by
  induction n with
  | zero => exact ⟨.z, fun _ h => by cases h⟩
  | succ n ih =>
      refine ⟨.p 0 _ T.Z ih.1 .z ih.2 (T.Z_le _), ?_⟩
      intro x hx
      change x ∈ [tower n] ++ T.G1 0 (tower n) ++ [] at hx
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx
      · exact tower_lt_next n
      · exact lt_trans_thm _ _ _ (ih.2 x hx) (tower_lt_next n)

theorem tower_below_Omega (n : Nat) : tower n < T.P 1 T.Z T.Z := by
  cases n with
  | zero => exact .Z_lt_P _ _ _
  | succ n => exact .p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0)

theorem encode_LF (n : Nat) : encode (new.T.LF 1 n) = tower n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [new.T.LF, new.Vec.ofFn, encode, encodeVec, tower] using congrArg (T.P 0 · T.Z) ih

theorem encode_base (n : Nat) :
    encode (new.T.P (new.Vec.ofFn 1 (fun i => if i.val = 0 then new.T.LF 1 n else new.T.Z)) new.T.Z) =
      tower (n + 1) := by
  simpa [new.Vec.ofFn, encode, encodeVec, tower] using congrArg (T.P 0 · T.Z) (encode_LF n)

theorem sound_aux (lam : Nat) (s : new.T lam) (hs : new.T.isOT lam s) :
    ∀ h : lam = 1, T.isSubNF 1 (encode (h ▸ s)) := by
  induction hs with
  | base_0 n => intro h; cases h
  | base_succ k n =>
      intro h
      have hk : k = 0 := Nat.succ.inj h
      subst k
      rw [encode_base]
      exact ⟨(tower_nf (n + 1)).1, .p_mid _ _ _ _ _ (tower_below_Omega n)⟩
  | step lam a _ n ih =>
      intro h
      subst lam
      have hi := ih rfl
      rw [encode_fund, encode_ofNat]
      have step (z : T) (hz : T.isNF1 z) (hv : T.ValidArg1 (encode a) z) :
          T.isSubNF 1 (T.fund1 (encode a) z) :=
        ⟨T.fund1_NF1_closed _ _ hi.1 hz hv,
          lt_trans_thm _ _ _ (T.fund1_fall _ _ hv) hi.2⟩
      cases hd : T.dom1 (encode a) with
      | Zero =>
          rw [dom1_Zero_imp_eq_Z _ hd, T.fund1.eq_1]
          exact ⟨.z, .Z_lt_P _ _ _⟩
      | One =>
          rw [fund1_One_const _ hd]
          exact step T.Z .z ((ValidArg1_One_iff _ _ hd).mpr rfl)
      | ω => exact step _ (IsN_isNF1 _ (ofNat_IsN n)) ((ValidArg1_ω_iff _ _ hd).mpr (ofNat_IsN n))
      | Ω l => exact False.elim (dom_not_Omega a l hd)

theorem sound (s : new.T 1) (hs : new.T.isOT 1 s) : T.isSubNF 1 (encode s) :=
  sound_aux 1 s hs rfl

theorem strong_below_Omega (s : T) (hc : s < T.P 1 T.Z T.Z)
    (hg : ∀ x ∈ T.G1 0 s, x < s) : s < T.P 0 (T.P 1 T.Z T.Z) T.Z := by
  cases hc with
  | Z_lt_P => exact .Z_lt_P _ _ _
  | p_head p _ a _ b _ h =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
      subst p
      exact .p_mid _ _ _ _ _ (lt_trans_thm _ _ _ (hg a (by simp [T.G1])) (.p_head _ _ _ _ _ _ h))
  | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h

theorem SubNF_zeroIndices (s : T) (hs : T.isSubNF 1 s) : ZeroIndices s := by
  have main : ∀ s, T.isNF1 s → s < T.P 0 (T.P 1 T.Z T.Z) T.Z → ZeroIndices s := by
    intro s hnf
    induction hnf with
    | z => intro _; exact .z
    | p p a b ha hb hg hh iha ihb =>
        intro hc
        cases hc with
        | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
        | p_mid _ _ _ _ _ h =>
            have hac := strong_below_Omega a h hg
            have hbc : b < T.P 0 (T.P 1 T.Z T.Z) T.Z := lt_of_le_of_lt_thm T _ _ _
              (T.isNF1_tail_le _ (.p 0 a b ha hb hg hh) _ _ _ rfl)
              (.p_mid _ _ _ _ _ h)
            exact .p a b (iha hac) (ihb hbc)
        | p_tail _ _ _ _ h => cases h
  exact main s hs.1 hs.2

def Image (a : T) : Prop := ∃ s : new.T.OT 1, encode s.val = a

theorem image_sound (a : T) (h : Image a) : T.isSubNF 1 a := by
  obtain ⟨s, rfl⟩ := h
  exact sound s.val s.property

theorem image_step (a : T) (h : Image a) (n : Nat) : Image (T.fund1 a (T.ofNat n)) := by
  obtain ⟨s, rfl⟩ := h
  refine ⟨⟨new.T.fund s.val (new.T.ofNat n), new.T.isOT.step 1 _ s.property n⟩, ?_⟩
  rw [encode_fund, encode_ofNat]

theorem image_downward (a b : T) (ha : Image a) (hb : T.isNF1 b) (hba : b ≤ a) : Image b := by
  have main : ∀ a : T.NF1, Image a.val → ∀ b, T.isNF1 b → b ≤ a.val → Image b := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
        intro ha b hb hba
        rcases hba with hba | rfl
        · have hac : a.val < T.P 1 T.Z T.Z := lt_trans_thm _ _ _ (image_sound a.val ha).2
            (T.Lt.p_head _ _ _ _ _ _ (Nat.zero_lt_succ 0))
          obtain ⟨n, hfall, hupper⟩ := fund1_countable_cofinal a.val b a.property hb hac hba
          have him := image_step a.val ha n
          exact ih ⟨_, (image_sound _ him).1⟩ hfall him b hb hupper
        · exact ha
  exact main ⟨a, (image_sound a ha).1⟩ ha b hb hba

theorem image_tower (n : Nat) : Image (tower n) := by
  cases n with
  | zero =>
      let s : new.T 1 := new.T.P (vec new.T.Z) new.T.Z
      have hs : new.T.isOT 1 s := new.T.isOT.base_succ 0 0
      have hz : new.T.fund s (new.T.ofNat 0) = new.T.Z := by
        rw [new.T.fund]
        rfl
      exact ⟨⟨new.T.Z, hz ▸ new.T.isOT.step 1 s hs 0⟩, rfl⟩
  | succ n => exact ⟨⟨_, new.T.isOT.base_succ 0 n⟩, encode_base n⟩

theorem tower_cofinal (s : T) (hs : ZeroIndices s) : ∃ n, s < tower n := by
  induction hs with
  | z => exact ⟨1, .Z_lt_P _ _ _⟩
  | p a b _ _ ih _ =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, .p_mid _ _ _ _ _ hn⟩

theorem exists_preimage (s : T) (hs : T.isSubNF 1 s) : Image s := by
  obtain ⟨n, hn⟩ := tower_cofinal s (SubNF_zeroIndices s hs)
  exact image_downward _ s (image_tower n) hs.1 (Or.inl hn)

def map (s : new.T.OT 1) : T.SubNF 1 := ⟨encode s.val, sound s.val s.property⟩

theorem map_injective (s t : new.T.OT 1) (h : map s = map t) : s = t :=
  Subtype.ext (encode_injective (congrArg Subtype.val h))

theorem map_surjective (t : T.SubNF 1) : ∃ s : new.T.OT 1, map s = t := by
  obtain ⟨s, hs⟩ := exists_preimage t.val t.property
  exact ⟨s, Subtype.ext hs⟩

theorem map_lt_iff (s t : new.T.OT 1) :
    s.val < t.val ↔ (map s).val < (map t).val := encode_lt_iff s.val t.val

end LegacyOne

theorem OT_SubNF_order_iso_one :
    ∃ f : new.T.OT 1 → T.SubNF 1,
      (∀ s t, f s = f t → s = t) ∧
      (∀ t, ∃ s, f s = t) ∧
      (∀ s t, s.val < t.val ↔ (f s).val < (f t).val) :=
  ⟨LegacyOne.map, LegacyOne.map_injective,
    LegacyOne.map_surjective, LegacyOne.map_lt_iff⟩

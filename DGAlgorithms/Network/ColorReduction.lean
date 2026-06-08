import Mathlib

-- variable (n : Nat)
-- #check n.pow

def optimalSizes : ℕ → ℕ
| 0 => 4
| k+1 =>
  let r := optimalSizes k
  (r).choose (r / 2)

lemma optimalSizes.even : ∀ n, Even (optimalSizes n) := by
  intro n
  induction n
  case zero => unfold optimalSizes; exact Nat.even_iff.mpr rfl
  case succ n ih =>
    unfold optimalSizes
    extract_lets r
    -- apply?
    sorry


-- lemma optimalSizes.monotone : StrictMono optimalSizes := by
--   apply strictMono_nat_of_lt_succ
--   intro n
--   nth_rw 1 [optimalSizes]


#eval (List.range 4).map optimalSizes
-- #eval (20 : Nat).choose 10

section PickMin

variable [DecidableEq α]

variable {a b : Finset α}
variable (hab : a ≠ b) (hab_card : a.card = b.card)

include hab hab_card
lemma finset_eq_card_sdiff_nonempty : (a \ b).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro h
  apply hab $ Finset.eq_of_subset_of_card_le h (ge_of_eq hab_card)

variable [LinearOrder α]
def pick_min := (a \ b).min' (finset_eq_card_sdiff_nonempty hab hab_card)

lemma pick_min_left : pick_min hab hab_card ∈ a := by
  have := Finset.mem_sdiff.mp $ Finset.min'_mem (a \ b) (finset_eq_card_sdiff_nonempty hab hab_card)
  exact this.left

lemma pick_min_right : pick_min hab hab_card ∉ b := by
  have := Finset.mem_sdiff.mp $ Finset.min'_mem (a \ b) (finset_eq_card_sdiff_nonempty hab hab_card)
  exact this.right

lemma pick_min_ne {c : Finset α} (hbc: b ≠ c) (hbc_card : b.card = c.card) :
    pick_min hab hab_card ≠ pick_min hbc hbc_card := by
  intro h_contra
  have := pick_min_right hab hab_card
  have := h_contra ▸ pick_min_left hbc hbc_card
  contradiction

end PickMin

section ConstructAllSubsets

def construct_all_subsetsAux (c n k : ℕ) (h : n ≤ c) : List (List (Fin c)) :=
  match n, k with
  | _, 0 => [∅]
  -- | 1, c => [{c}]
  | 0, k+1 => []
  -- | 1, 0 => [{0}]
  | n+1, k+1 =>
    construct_all_subsetsAux c n (k+1) (by omega) ++
      (construct_all_subsetsAux c n k (by omega)).map (List.cons ⟨n, by omega⟩)

variable (c n k : ℕ) (h : n ≤ c)

lemma construct_all_subsetsAux_lt : ∀ l ∈ (construct_all_subsetsAux c n k h), ∀ x ∈ l, x < n := by
  fun_induction construct_all_subsetsAux
  · simp
  · simp
  rename_i n k ih₁ ih₂
  rw [List.forall_mem_append]
  constructor
  · tauto
  · grind


@[simp]
lemma construct_all_subsetsAux_length : (construct_all_subsetsAux c n k h).length = n.choose k := by
  fun_induction construct_all_subsetsAux
  all_goals simp_all [Nat.choose_succ_left, add_comm]

lemma construct_all_subsetsAux_sortedLT : (construct_all_subsetsAux c n k h).SortedLT := by
  fun_induction construct_all_subsetsAux
  case case1 _ => grind
  case case2 _ => grind
  case case3 n k h h1 h2 =>
    apply List.sortedLT_iff_isChain.mpr
    apply List.isChain_append.mpr
    constructor; grind
    constructor
    · apply (List.isChain_map _).mpr
      have : ∀ a b : List (Fin c), a < b → ⟨n, by omega⟩ :: a < ⟨n, by omega⟩ :: b := by
        intro _ _ h
        exact List.cons_lt_cons_self.mpr h
      exact List.IsChain.imp this $ List.sortedLT_iff_isChain.mp h2
  -- TODO: Clean this up
    intro x hx y hy
    apply List.mem_of_mem_getLast? at hx
    apply List.mem_of_mem_head? at hy
    simp at hy
    obtain ⟨a, b⟩ := hy
    rw [←b.right]
    cases x with
    | nil => simp
    | cons x xs =>
      apply List.cons_lt_cons_iff.mpr; left
      apply Fin.val_fin_lt.mp
      simp [construct_all_subsetsAux_lt _ _ _ _ _ hx]


@[simp]
lemma construct_all_subsetsAux_gt_eq_nil (hkn : k > n) : construct_all_subsetsAux c n k h = [] := by
  rw [←List.length_eq_zero_iff]
  have := Nat.choose_eq_zero_iff.mpr hkn
  simp_all

@[simp]
lemma construct_all_subsetsAux_elem_length_gt (hkn : k > n) : ∀ l ∈ construct_all_subsetsAux c n k h, l.length = 0 := by
  rw [construct_all_subsetsAux_gt_eq_nil]
  intro l hl
  contradiction; exact hkn

lemma construct_all_subsetsAux_elem_length_le (hkn : k ≤ n) : ∀ l ∈ construct_all_subsetsAux c n k h, l.length = k := by
  fun_induction construct_all_subsetsAux
  · simp
  · tauto
  rename_i n k h ih₁ ih₂
  intro l hl
  rw [List.mem_append] at hl
  cases' hl with hl hl
  · cases' lt_or_eq_of_le hkn
    · apply ih₁ (by omega) l hl
    · rw [construct_all_subsetsAux_gt_eq_nil c n (k+1) (by omega) (by omega)] at hl
      contradiction
  · rw [List.mem_map] at hl
    obtain ⟨x, hx⟩ := hl
    specialize ih₂ (Nat.le_of_succ_le_succ hkn) x hx.left
    rw [←hx.right, List.length_cons, ih₂]


lemma construct_all_subsetsAux_elem_nodup : ∀ l ∈ construct_all_subsetsAux c n k h, l.Nodup := by
  fun_induction construct_all_subsetsAux
  case case1 _ => simp
  case case2 _ => simp
  case case3 n k h h1 h2  =>
    intro l hl
    rw [List.mem_append] at hl
    cases' hl with hl hl
    · simp_all
    · rw [List.mem_map] at hl
      obtain ⟨x, hx, hxl⟩ := hl
      subst hxl
      rw [List.nodup_cons]
      constructor
      · intro hcontra
        rw [List.mem_iff_get] at hcontra
        obtain ⟨i, hi⟩ := hcontra
        have := construct_all_subsetsAux_lt c n k _ x hx (x.get i) (by simp)
        rw [hi] at this
        simp_all
      · exact List.nodup_iff_pairwise_ne.mpr (h2 x hx)


-- lemma construct_all_subsetsAux_toFinset_length (n k : ℕ) : ∀ l ∈ (construct_all_subsetsAux n k).map List.toFinset, l.card = n.min k := by

-- #loogle List.toFinset, List.cons

lemma construct_all_subsetsAux_nodup : (construct_all_subsetsAux c n k h).Nodup := by
  fun_induction construct_all_subsetsAux
  case case1 _ => simp
  case case2 _ => simp
  case case3 n k h h1 h2  =>
    apply List.nodup_append.mpr
    constructor; exact h1
    constructor; rw [List.nodup_map_iff List.cons_injective]; exact h2

    intro a ha b hb hab
    have ha := construct_all_subsetsAux_lt _ _ _ _ _ ha
    have hb : ∃ x ∈ b, x = n := by
      rw [List.mem_map] at hb
      obtain ⟨x, hx⟩ := hb
      simp [←hx.right]

    obtain ⟨x, hxb, hxn⟩ := hb
    subst hab hxn
    specialize ha x hxb
    exact (lt_self_iff_false x).mp ha


lemma construct_all_subsetsAux_toFinset_nodup : ((construct_all_subsetsAux c n k h).map List.toFinset).Nodup := by
  fun_induction construct_all_subsetsAux
  case case1 _ => simp
  case case2 _ => simp
  case case3 n k h h1 h2 =>
    rw [List.map_append, List.nodup_append]
    constructor; assumption
    constructor
    · rw [List.map_map, Function.comp_def, List.nodup_map_iff_inj_on (construct_all_subsetsAux_nodup c n k (by omega))]
      intro x hx y hy h

      apply (List.nodup_map_iff_inj_on (construct_all_subsetsAux_nodup _ _ _ _)).mp h2 _ hx _ hy

      ext a
      apply Finset.ext_iff.mp at h
      specialize h a
      by_cases han : a = ⟨n, by omega⟩
      · symm at han
        subst han
        have hx : ⟨n, by omega⟩ ∉ x.toFinset := by
          intro hcontra
          have := construct_all_subsetsAux_lt c n k _ x hx ⟨n, by omega⟩ (List.mem_toFinset.mp hcontra)
          exact (lt_self_iff_false n).mp this
        have hy : ⟨n, by omega⟩ ∉ y.toFinset := by
          intro hcontra
          have := construct_all_subsetsAux_lt c n k _ y hy ⟨n, by omega⟩ (List.mem_toFinset.mp hcontra)
          exact (lt_self_iff_false n).mp this
        simp_all
      · simp_all

    intro x hx y hy
    have hx : ∀ a ∈ x, a < n := by
      have := construct_all_subsetsAux_lt c n (k+1) (by omega)
      aesop
    have hy : ∃ a ∈ y, a = n := by aesop
    intro h_contra
    subst h_contra
    obtain ⟨a, ha⟩ := hy
    have := hx a ha.left
    exact Nat.ne_of_lt this ha.right



-- lemma foo (n k : ℕ) : ((construct_all_subsetsAux n k).map (List.toFinset)).toFinset = (List.range n).toFinset.powersetCard k := by

--   -- ext x
--   -- constructor

--   sorry

-- def construct_all_subsets (n k : ℕ) : Finset (Finset ℕ) := ((construct_all_subsetsAux n k).map List.toFinset).toFinset

-- #eval (construct_all_subsets 10 6).Pairwise LT.lt
end ConstructAllSubsets

def pick_ith_subset (n k : ℕ) (i : Fin (n.choose k)) : Finset (Fin n) :=
  ((construct_all_subsetsAux n n k (by omega)).map List.toFinset).get ⟨i, by simp⟩

lemma pick_ith_subset_injective (n k : ℕ) : Function.Injective (pick_ith_subset n k) := by
  unfold pick_ith_subset
  suffices Function.Injective ((construct_all_subsetsAux n n k (by omega)).map List.toFinset).get by
    rw [←Function.comp_def, Function.Injective.of_comp_iff this]
    intro a b h
    ext
    simp_all
  apply List.nodup_iff_injective_get.mp
  exact construct_all_subsetsAux_toFinset_nodup _ _ _ _



lemma pick_ith_subset_card (n k : ℕ) (i : Fin (n.choose k)) : (pick_ith_subset n k i).card = k := by
  unfold pick_ith_subset
  have : k ≤ n := by
    by_contra
    rw [Nat.choose_eq_zero_of_lt (not_le.mp this)] at i
    apply Fin.elim0 i

  simp
  rw [List.toFinset_card_of_nodup]
  · simp_all [construct_all_subsetsAux_elem_length_le n n k]
  · simp [construct_all_subsetsAux_elem_nodup n n k]


/- A single color-reduction step

  This function assumes that the color space is “nice”, that is, (2*k).choose k.

  See [crStep] for the variant without this assumption.
-/
def crStep' (k : ℕ) (a b : Fin ((2*k).choose k)) (h : a ≠ b) : Fin (2 * k) :=
  let targetSet := (List.finRange (2*k)).toFinset
  let sourceSet := targetSet.powersetCard k
  have : sourceSet.card = (2*k).choose k := by
    rw [Finset.card_powersetCard]
    unfold targetSet
    simp [List.toFinset_finRange]

  let e := pick_ith_subset (2 * k) k

  let a := e a
  let b := e b
  have hab : a ≠ b := (pick_ith_subset_injective (2 * k) k).ne h

  have hab_card : Finset.card a = Finset.card b := by
    trans k
    exact pick_ith_subset_card _ _ _
    exact Eq.symm $ pick_ith_subset_card _ _ _

  have hab : a ≠ b := by simp_all

  pick_min hab hab_card

lemma crStep'_ne (k : ℕ) (a b c : Fin ((2*k).choose k)) (hab : a ≠ b) (hbc : b ≠ c) : crStep' k a b hab ≠ crStep' k b c hbc := by
  unfold crStep'
  simp [pick_min_ne]

lemma choose_half_strictMono : StrictMono fun k => (2*k).choose k := by
  apply strictMono_nat_of_lt_succ
  intro n
  induction n
  case hf.zero => simp
  case hf.succ k ih =>
    have : (2 * (k + 1)).choose (k + 1) > 0 := by exact Nat.zero_lt_of_lt ih
    calc (2 * (k + 1 + 1)).choose (k + 1 + 1)
      _ = (2 * (k + 1) + 1).choose (k + 1) + (2 * (k + 1) + 1).choose (k + 2) := by aesop
      _ = (2 * (k + 1) + 1).choose (k + 1) + (2 * (k + 1) + 1).choose (k + 1) := by simp [Nat.choose_symm_half]
      _ = 2 * ((2 * (k + 1) + 1).choose (k + 1)) := by omega
      _ = 2 * ((2 * (k + 1)).choose (k + 1 - 1) + (2 * (k + 1)).choose (k + 1)) := by simp [Nat.choose_succ_left]
      _ = 2 * ((2 * (k + 1)).choose k + (2 * (k + 1)).choose (k + 1)) := by simp
      _ ≥ 2 * (2 * (k + 1)).choose (k + 1) := by simp
      _ > (2 * (k + 1)).choose (k + 1) := by simp_all

-- lemma choose_half_super_id : sorry := by
  -- have a := StrictMono.id_le

-- TODO: Rename these
def IsSuitable (n k : ℕ) : Prop := n ≤ (2*k).choose k

instance (n : ℕ) : DecidablePred (IsSuitable n) := fun k =>
  if h : n ≤ (2*k).choose k then
    isTrue h
  else
    isFalse h

lemma IsSuitable.exists (n : ℕ) : ∃ k : ℕ, IsSuitable n k :=
  (Filter.tendsto_atTop_atTop_iff_of_monotone choose_half_strictMono.monotone).mp
    choose_half_strictMono.tendsto_atTop n

def findLarger (n : ℕ) : ℕ :=
  Nat.find (IsSuitable.exists n)

-- #eval (List.range 50).map (fun x => 2 * findLarger x)

lemma findLarger_le {k : ℕ} (h : k ≥ 4) : 2 * findLarger k ≤ k := by
  cases h
  case refl =>
    native_decide
  case step k hk =>
    induction k
    case zero => native_decide
    case succ k ih =>
      -- have := Nat.find_min' (IsSuitable.exists k)
      sorry

def crStep (k : ℕ) (a b : Fin k) (h : a ≠ b) : Fin (2 * findLarger k) :=
  have : k ≤ (2 * (findLarger k)).choose (findLarger k) := by exact Nat.find_spec (IsSuitable.exists k)
  let a : Fin ((2 * findLarger k).choose (findLarger k)) := a.castLE this
  let b : Fin ((2 * findLarger k).choose (findLarger k)) := b.castLE this
  crStep' (findLarger k) a b (Fin.castLE_inj.ne.mpr h)

lemma crStep_ne (k : ℕ) (a b c : Fin k) (hab : a ≠ b) (hbc : b ≠ c) : crStep k a b hab ≠ crStep k b c hbc := by
  unfold crStep
  simp [crStep'_ne]

-- #eval findLarger 1000000000000000000000000000000

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

/- A single color-reduction step

  This function assumes that the color space is “nice”, that is, (2*k).choose k.

  See [crStep] for the variant without this assumption.

  # Note
  This function is `noncomputable`. This is becuase it internally uses `Finset.equivFin` which is
  `noncomputable`. That could in principle be replaced with a computable counterpart, but that is
  a job for another day.
-/
noncomputable
def crStep' (k : ℕ) (a b : Fin ((2*k).choose k)) (h : a ≠ b) : Fin (2 * k) :=
  let targetSet := (List.finRange (2*k)).toFinset
  let sourceSet := targetSet.powersetCard k
  have : sourceSet.card = (2*k).choose k := by
    rw [Finset.card_powersetCard]
    unfold targetSet
    simp [List.toFinset_finRange]

  let e := (this ▸ Finset.equivFin sourceSet).symm

  let a := e a
  let b := e b
  have hab : a ≠ b := e.injective.ne h

  let ⟨a, ha⟩ := a
  let ⟨b, hb⟩ := b

  have hab_card : Finset.card a = Finset.card b := by
    trans k
    exact (Finset.mem_powersetCard.mp ha).right
    exact (Finset.mem_powersetCard.mp hb).right.symm

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

noncomputable
def crStep (k : ℕ) (a b : Fin k) (h : a ≠ b) : Fin (2 * findLarger k) :=
  have : k ≤ (2 * (findLarger k)).choose (findLarger k) := by exact Nat.find_spec (IsSuitable.exists k)
  let a : Fin ((2 * findLarger k).choose (findLarger k)) := a.castLE this
  let b : Fin ((2 * findLarger k).choose (findLarger k)) := b.castLE this
  crStep' (findLarger k) a b (Fin.castLE_inj.ne.mpr h)

lemma crStep_ne (k : ℕ) (a b c : Fin k) (hab : a ≠ b) (hbc : b ≠ c) : crStep k a b hab ≠ crStep k b c hbc := by
  unfold crStep
  simp [crStep'_ne]

-- #eval findLarger 1000000000000000000000000000000

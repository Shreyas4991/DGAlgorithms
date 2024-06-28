import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Basic

set_option autoImplicit false

def powerTower (n : ℕ) : ℕ → ℕ
| 0 => 1
| (m + 1) => n ^ powerTower n m

notation x " ^^ " y:90 => powerTower x y

lemma powerTower_eq_iterate (n m : ℕ) : n ^^ m = (n ^ ·)^[m] 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [powerTower, Function.iterate_succ_apply', ih]

@[simp] lemma powerTower_zero (n : ℕ) : n ^^ 0 = 1 := rfl
@[simp] lemma powerTower_succ {n m : ℕ} : n ^^ (m + 1) = n ^ (n ^^ m) := rfl

lemma powerTower_pos {n m : ℕ} (hn : 0 < n) : 0 < n ^^ m := by
  cases m with
  | zero => exact Nat.one_pos
  | succ m => exact pow_pos hn _

lemma zero_powerTower {m : ℕ} : 0 ^^ m = if Even m then 1 else 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih, Nat.even_add_one]

lemma one_powerTower {m : ℕ} : 1 ^^ m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

lemma powerTower_strictMono : StrictMono (2 ^^ ·) :=
    strictMono_nat_of_lt_succ fun _ => Nat.lt_pow_self (by norm_num) _

lemma Real.logb_lt_self {b x : ℝ} (hb : exp (-1) < log b) (hx : 0 < x) : logb b x < x := by
  rw [logb]
  have : 0 < b.log := hb.trans' (exp_pos _)
  rw [div_lt_iff this]
  suffices log x ≤ x / exp 1 by
    refine this.trans_lt ?_
    rw [div_eq_mul_inv, ←Real.exp_neg]
    gcongr
  have' := @log_le_sub_one_of_pos (x / exp 1) (by positivity)
  rwa [log_div hx.ne' (exp_pos _).ne', log_exp, tsub_le_iff_right, sub_add_cancel] at this

lemma Real.logb_le_self {b x : ℝ} (hb : exp (-1) ≤ log b) (hx : 0 ≤ x) : logb b x ≤ x := by
  rw [logb]
  have : 0 < b.log := hb.trans_lt' (exp_pos _)
  rw [div_le_iff this]
  suffices log x ≤ x / exp 1 by
    refine this.trans ?_
    rw [div_eq_mul_inv, ←Real.exp_neg]
    gcongr
  rcases lt_or_eq_of_le hx with hx | rfl
  case inr => simp
  case inl =>
    have' := @log_le_sub_one_of_pos (x / exp 1) (by positivity)
    rwa [log_div hx.ne' (exp_pos _).ne', log_exp, tsub_le_iff_right, sub_add_cancel] at this

lemma Real.logb_two_lt_self {x : ℝ} (hx : 0 < x) : logb 2 x < x :=
  (Real.logb_lt_self · hx) <| exp_neg_one_lt_d9.trans_le <| log_two_gt_d9.le.trans' <| by norm_num

lemma Real.logb_two_le_self {x : ℝ} (hx : 0 ≤ x) : logb 2 x ≤ x :=
  (Real.logb_le_self · hx) <| exp_neg_one_lt_d9.le.trans <| log_two_gt_d9.le.trans' <| by norm_num

lemma Nat.floor_log_two_lt_self {x : ℕ} (hx : 1 ≤ x) : Nat.log 2 x < x := by
  rw [←lt_pow_iff_log_lt one_lt_two (by omega)]
  exact lt_two_pow x

lemma Real.floor_logb_two_lt_self {x : ℝ} (hx : 1 ≤ x) : ⌊logb 2 x⌋₊ < ⌊x⌋₊ := by
  have : ⌊logb 2 x⌋₊ = Nat.log 2 ⌊x⌋₊ := by
    have : _ = Int.log 2 x := Real.floor_logb_natCast one_lt_two (by linarith)
    rwa [Nat.cast_ofNat, ←Int.ofNat_floor_eq_floor, Int.log_of_one_le_right _ hx,
      Nat.cast_inj] at this
    exact logb_nonneg one_lt_two hx
  rw [this]
  refine Nat.floor_log_two_lt_self ?_
  simpa only [Nat.one_le_floor_iff]

noncomputable def logStar (x : ℝ) : ℕ := if x ≤ 1 then 0 else logStar (Real.logb 2 x) + 1
  termination_by ⌊x⌋₊
  decreasing_by exact Real.floor_logb_two_lt_self (by linarith)

lemma logStar_of_le_one {x : ℝ} (hx : x ≤ 1) : logStar x = 0 := by rw [logStar, if_pos hx]

lemma logStar_of_ge_one {x : ℝ} (hx : 1 < x) : logStar x = logStar (Real.logb 2 x) + 1 := by
  rw [logStar, if_neg hx.not_le]

@[simp] lemma logStar_one : logStar 1 = 0 := logStar_of_le_one le_rfl
@[simp] lemma logStar_two : logStar 2 = 1 := by simp [logStar_of_ge_one]

lemma logStar_eq_zero_iff {x : ℝ} : logStar x = 0 ↔ x ≤ 1 := by
  refine ⟨fun h => ?_, logStar_of_le_one⟩
  by_contra!
  simp [logStar_of_ge_one this] at h

lemma logStar_pos_iff {x : ℝ} : 0 < logStar x ↔ 1 < x := by
  rw [pos_iff_ne_zero, ne_eq, logStar_eq_zero_iff, not_le]

lemma logStar_two_powerTower {i : ℕ} : logStar (2 ^^ i) = i := by
  induction i with
  | zero => simp
  | succ n ih =>
      rw [powerTower_succ, Nat.cast_pow, Nat.cast_ofNat, logStar_of_ge_one, Real.logb_pow two_pos,
        Real.logb_self_eq_one one_lt_two, mul_one, ih]
      exact one_lt_pow one_lt_two (powerTower_pos two_pos).ne'

lemma iterate_logb_logStar_le (x : ℝ) : (Real.logb 2)^[logStar x] x ≤ 1 := by
  induction x using logStar.induct with
  | case1 x h => rwa [logStar_of_le_one h]
  | case2 x hx ih => rwa [logStar, if_neg hx]

lemma iterate_logb_of_lt_logStar {x : ℝ} {n : ℕ} (hn : n < logStar x) :
    1 < (Real.logb 2)^[n] x := by
  induction n generalizing x with
  | zero =>
      rw [logStar_pos_iff] at hn
      simp only [Function.iterate_zero, id_eq]
      linarith
  | succ n ih =>
      refine ih ?_
      rwa [logStar_of_ge_one (by rw [←logStar_pos_iff]; omega), add_lt_add_iff_right] at hn

lemma iterate_mono_on {x y : ℝ} {n : ℕ} (hn : n ≤ logStar x) (hxy : x ≤ y) :
    (Real.logb 2)^[n] x ≤ (Real.logb 2)^[n] y := by
  induction n generalizing x y with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      refine ih ?g1 ?g2
      case g1 =>
        rwa [logStar_of_ge_one (by rw [←logStar_pos_iff]; omega), add_le_add_iff_right] at hn
      refine Real.logb_le_logb_of_le (by linarith) ?_ hxy
      have : 0 < logStar x := by omega
      rw [logStar_pos_iff] at this
      linarith

example : 10 ^ 19728 < 2 ^^ 5 := by decide

-- note this set is *not* upwards closed because of the way log is defined
lemma logStar_isLeast {x : ℝ} :
    IsLeast {n | (Real.logb 2)^[n] x ≤ 1} (logStar x) :=
  And.intro (iterate_logb_logStar_le x) fun _ hn =>
    le_of_not_lt fun h => not_lt_of_le (Set.mem_setOf.1 hn) (iterate_logb_of_lt_logStar h)

lemma logStar_mono : Monotone logStar := fun _ _ hxy =>
  le_of_not_lt fun hxy' =>
    ((iterate_logb_of_lt_logStar hxy').trans_le (iterate_mono_on hxy'.le hxy)).not_le
      (iterate_logb_logStar_le _)

noncomputable def gi : GaloisInsertion logStar (2 ^^ ·) := by
  refine GaloisInsertion.monotoneIntro ?g3 logStar_mono ?g2 ?g1
  case g3 =>
    intro x y h
    dsimp
    exact mod_cast powerTower_strictMono.monotone h
  case g1 =>
    intro x
    rw [logStar_two_powerTower]
  case g2 =>
    intro x
    induction x using logStar.induct with
    | case1 x hx => simpa [logStar_of_le_one hx]
    | case2 x hx ih =>
        rw [logStar, if_neg hx, powerTower_succ]
        rw [Real.logb_le_iff_le_rpow (by linarith) (by linarith)] at ih
        exact mod_cast ih

lemma logStar_eq_add_one_iff {x : ℝ} {n : ℕ} :
    logStar x = n + 1 ↔ x ≤ 2 ^^ (n + 1) ∧ 2 ^^ n < x := by
  rw [le_antisymm_iff, Nat.add_one_le_iff, gi.gc, gi.gc.lt_iff_lt]

example : logStar (10 ^ 19728) = 5 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 2 = 1 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 3 = 2 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 4 = 2 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 5 = 3 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 16 = 3 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 17 = 4 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 65536 = 4 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar 65537 = 5 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar (10 ^ 10) = 5 := by rw [logStar_eq_add_one_iff]; norm_cast
example : logStar (10 ^ 19728) = 5 := by rw [logStar_eq_add_one_iff]; norm_cast

-- the smallest number `x` for which logStar x > 5 is 2 ^ (2 ^ 65536), which has over 10 ^ 19727
-- digits

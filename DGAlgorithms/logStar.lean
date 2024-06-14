import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Basic

def powerTower (n : ℕ) : ℕ → ℕ
| 0 => 1
| (m + 1) => n ^ powerTower n m

notation x " ^^ " y:90 => powerTower x y

lemma powerTower_eq_iterate (n m : ℕ) : n ^^ m = (n ^ ·)^[m] 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [powerTower, Function.iterate_succ_apply', ih]

@[simp] lemma powerTower_zero (n : ℕ) : n ^^ 0 = 1 := rfl
@[simp] lemma powerTower_succ (n : ℕ) : n ^^ (m + 1) = n ^ (n ^^ m) := rfl

lemma powerTower_pos (hn : 0 < n) : 0 < n ^^ m := by
  cases m with
  | zero => exact Nat.one_pos
  | succ m => exact pow_pos hn _

lemma zero_powerTower : 0 ^^ m = if Even m then 1 else 0 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih, Nat.even_add_one]

lemma one_powerTower : 1 ^^ m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp [ih]

lemma Real.logb_lt_self {b x : ℝ} (hb : exp (-1) < log b) (hx : 0 < x) : logb b x < x := by
  rw [logb]
  have : 0 < b.log := hb.trans' (exp_pos _)
  rw [div_lt_iff this]
  suffices log x ≤ x / exp 1 by
    refine this.trans_lt ?_
    rw [div_eq_mul_inv, ←Real.exp_neg]
    gcongr
  have' := @log_le_sub_one_of_pos (x / exp 1) (by positivity)
  rw [log_div hx.ne' (exp_pos _).ne', log_exp, tsub_le_iff_right, sub_add_cancel] at this
  exact this

lemma Real.logb_two_lt_self {x : ℝ} (hx : 0 < x) : logb 2 x < x :=
  (Real.logb_lt_self · hx) <| exp_neg_one_lt_d9.trans_le <| log_two_gt_d9.le.trans' <| by norm_num

lemma Nat.floor_log_two_lt_self (hx : 1 ≤ x) : Nat.log 2 x < x := by
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

lemma logStar_of_le_one (hx : x ≤ 1) : logStar x = 0 := by rw [logStar, if_pos hx]

lemma logStar_of_ge_one (hx : 1 < x) : logStar x = logStar (Real.logb 2 x) + 1 := by
  rw [logStar, if_neg hx.not_le]

@[simp] lemma logStar_one : logStar 1 = 0 := logStar_of_le_one le_rfl
@[simp] lemma logStar_two : logStar 2 = 1 := by simp [logStar_of_ge_one]

lemma logStar_two_powerTower : logStar (2 ^^ i) = i := by
  induction i with
  | zero => simp
  | succ n ih =>
      rw [powerTower_succ, Nat.cast_pow, Nat.cast_ofNat, logStar_of_ge_one, Real.logb_pow two_pos,
        Real.logb_self_eq_one one_lt_two, mul_one, ih]
      exact one_lt_pow one_lt_two (powerTower_pos two_pos).ne'

-- lemma logStar_eq_aux (x : ℝ) : ∃ n, (Real.logb 2)^[n] x ≤ 1 := sorry

-- lemma logStar_floor : logStar x = logStar ⌊x⌋₊ := sorry

-- lemma logStar_mono : Monotone logStar := by sorry

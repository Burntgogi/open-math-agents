import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace OnePercent

open Real

/-- The discrete binomial count used for choosing R and S, in logarithmic form. -/
theorem log_choose_cost {n u : ℕ} (hu : 0 < u) (hun : u ≤ n) :
    log (n.choose u : ℝ) ≤ u * (1 + log ((n : ℝ) / u)) := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hn' : (0 : ℝ) < n := by exact_mod_cast hu.trans_le hun
  have hc : (0 : ℝ) < n.choose u := by exact_mod_cast Nat.choose_pos hun
  have hpow := Real.pow_div_factorial_le_exp (u : ℝ) (Nat.cast_nonneg u) u
  have h : (n.choose u : ℝ) ≤ (((n : ℝ) / u)^u) * exp u := by
    calc
      (n.choose u : ℝ) ≤ (n : ℝ)^u / u.factorial := Nat.choose_le_pow_div u n
      _ = (((n : ℝ)/u)^u) * ((u : ℝ)^u / u.factorial) := by
        rw [div_pow]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hl := log_le_log hc h
  rw [log_mul (by positivity) (exp_pos _).ne', log_exp, log_pow] at hl
  linarith

/-- Replacing a floored binomial exponent by its real cap increases its log cost. -/
theorem choice_cost_mono {u a N : ℝ} (hu : 0 < u) (hua : u ≤ a) (haN : a ≤ N) :
    u * (1 + log (N / u)) ≤ a * (1 + log (N / a)) := by
  have ha := hu.trans_le hua
  have hN := ha.trans_le haN
  have h := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos ha hu)) hu.le
  have hdiv : u * (a / u) = a := by field_simp
  have hl : 0 ≤ log (N / a) := log_nonneg ((one_le_div ha).2 haN)
  have hd : log (N / u) = log (N / a) + log (a / u) := by
    rw [log_div hN.ne' hu.ne', log_div hN.ne' ha.ne', log_div ha.ne' hu.ne']
    ring
  rw [hd]
  nlinarith [mul_nonneg (sub_nonneg.2 hua) hl]

private theorem log_le_dyadic {y : ℝ} (hy : 0 < y) (n : ℕ) (h : y ≤ 2 ^ n) :
    log y ≤ n * (0.7 : ℝ) := by
  calc
    log y ≤ log (2 ^ n) := log_le_log hy h
    _ = n * log 2 := log_pow 2 n
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [log_two_lt_d9]) (Nat.cast_nonneg _)

/-- The full exponent before collecting the constant and the slope. -/
theorem entropy_margin (x : ℝ) :
    0.101*x + 0.1*log (10*exp 1) + 0.001*log (1000*exp 1) + log 2 +
      0.24*(log (2*71000^2) - 2*(1000 + 0.22*x)) < -470 - 0.0046*x := by
  have h₁ := log_le_dyadic (y := 10) (by norm_num) 4 (by norm_num)
  have h₂ := log_le_dyadic (y := 1000) (by norm_num) 10 (by norm_num)
  have h₃ := log_le_dyadic (y := 2*71000^2) (by norm_num) 34 (by norm_num)
  rw [log_mul (by norm_num : (10:ℝ) ≠ 0) (exp_pos 1).ne',
      log_mul (by norm_num : (1000:ℝ) ≠ 0) (exp_pos 1).ne', log_exp]
  norm_num at h₁ h₂ h₃
  linarith [log_two_lt_d9]

/-- A uniform container bound; all logarithms are natural. -/
theorem container_shrink {x : ℝ} (hx : 5000 ≤ x) :
    log (10^24) + 1000 + 0.22*x + log (5 + 2*log (2*x^2)) + 300 < x/2 := by
  have hpos : 0 < x := by linarith
  have h₁ := log_le_dyadic (y := 10) (by norm_num) 4 (by norm_num)
  have h₂ := log_le_dyadic (y := 100) (by norm_num) 7 (by norm_num)
  have h₃ := log_le_sub_one_of_pos (div_pos hpos (by norm_num : (0:ℝ) < 100))
  rw [log_div hpos.ne' (by norm_num)] at h₃
  have h₄ : 0 ≤ log (2*x^2) := log_nonneg (by nlinarith [sq_nonneg (x-1)])
  have h₅ := log_le_sub_one_of_pos (div_pos (by linarith : 0 < 5+2*log (2*x^2))
                                               (by norm_num : (0:ℝ) < 100))
  rw [log_div (by linarith) (by norm_num)] at h₅
  rw [log_mul (by norm_num) (pow_ne_zero 2 hpos.ne'), log_pow] at h₅
  rw [log_mul (by norm_num) (pow_ne_zero 2 hpos.ne'), log_pow, log_pow]
  norm_num at h₁ h₂
  linarith [log_two_lt_d9]

/-- The KL change bound for one successful test is strictly better than the budget. -/
theorem entropy_decrement {η : ℝ} (h : 0 < η) :
    η^2/16 < (η/4)*(η/2) - (η/4)^2/2 := by nlinarith [sq_pos_of_pos h]

theorem minimum_hit_fraction {f : ℝ}
    (h : 0.244 ≤ 0.115 + 0.001 + 0.001 + 0.51*f) : 0.24 < f := by linarith

theorem retained_fraction : (0.11:ℝ) < 1/9 - 4/(3*5000^2) := by norm_num

/-- A deliberately loose bound p/k ≤ 2k already closes the terminal contradiction. -/
theorem terminal_contradiction {k v t : ℝ} (hk : 0 < k) (hv : v ≤ 2*k)
    (ht : 0.98*v + 0.11*k ≤ t) : 1.01*v < t := by linarith

end OnePercent

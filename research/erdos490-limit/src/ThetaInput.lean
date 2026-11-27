import Mathlib

open Asymptotics Real Filter
open scoped Topology Chebyshev

namespace Erdos490PrimeCells

theorem theta_log_error_of_psi
    (hψ : ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun (x : ℝ) ↦ x * exp (-c * (log x) ^ ((1 : ℝ) / 2))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |θ x - x| ≤ K*x / log x ^ 3 := by
  obtain ⟨c,hc,hψ⟩ := hψ
  obtain ⟨C,hC,hψ⟩ := hψ.exists_pos
  obtain ⟨B,hB,hBnd⟩ := Chebyshev.isBigO_psi_sub_theta_sqrt.exists_pos
  refine ⟨C+B,by positivity,?_⟩
  have hdec := (isLittleO_pow_exp_pos_mul_atTop 6 hc).bound (by norm_num : (0:ℝ)<1)
  have hroot := (isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ)<1/2)).bound
    (by norm_num : (0:ℝ)<1)
  have hcomp : Tendsto (fun x : ℝ => √(log x)) atTop atTop :=
    tendsto_sqrt_atTop.comp tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,hψ.bound,hBnd.bound,hcomp.eventually hdec,hroot]
    with x hx hxψ hxθ hex hr
  have hx0 : 0 < x := by linarith
  have hl := log_pos hx
  have hsq := sq_sqrt hl.le
  have hsx := sq_sqrt hx0.le
  have hl6 : √(log x) ^ 6 = log x ^ 3 := by rw [show 6=2*3 by decide, pow_mul,hsq]
  change ‖√(log x)^6‖ ≤ 1*‖exp (c * √(log x))‖ at hex
  rw [hl6,Real.norm_eq_abs,abs_of_pos (by positivity),one_mul,Real.norm_eq_abs,abs_of_pos (exp_pos _)] at hex
  change ‖log x ^ (3:ℝ)‖ ≤ 1 * ‖x ^ (1/2:ℝ)‖ at hr
  rw [← Real.sqrt_eq_rpow,show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast,one_mul,
    Real.norm_eq_abs,abs_of_pos (by positivity),Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] at hr
  have hsmall : √x ≤ x / log x ^ 3 := by
    rw [le_div_iff₀ (by positivity)]
    calc
      _ ≤ √x * √x := by gcongr
      _ = x := mul_self_sqrt hx0.le
  change |ψ x - x| ≤ C * |x * exp (-c * log x ^ ((1:ℝ)/2))| at hxψ
  rw [abs_of_pos (mul_pos hx0 (exp_pos _)), ← sqrt_eq_rpow, neg_mul, exp_neg] at hxψ
  change |ψ x - θ x| ≤ B * |√x| at hxθ
  rw [abs_of_nonneg (sqrt_nonneg _)] at hxθ
  have hrec := one_div_le_one_div_of_le (pow_pos hl 3) hex
  rw [one_div (exp _)] at hrec
  calc
    |θ x - x| ≤ |θ x - ψ x| + |ψ x - x| := abs_sub_le _ _ _
    _ = |ψ x - θ x| + |ψ x - x| := by rw [abs_sub_comm (θ x)]
    _ ≤ B * (x / log x ^ 3) + C * (x * (1 / log x ^ 3)) := by
      apply add_le_add (hxθ.trans (mul_le_mul_of_nonneg_left hsmall hB.le))
      exact hxψ.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrec hx0.le) hC.le)
    _ = _ := by ring

end Erdos490PrimeCells

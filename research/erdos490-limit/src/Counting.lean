import PrimeCells

open Filter Real
open scoped Topology Chebyshev

namespace Erdos490PrimeCells

noncomputable def piReal (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

theorem counting_pnt : Tendsto (fun x : ℝ => piReal x * log x / x) atTop (𝓝 1) := by
  obtain ⟨K,hK,hθ⟩ := theta_log_error_of_psi StrongPNT
  obtain ⟨B,hB,hπ⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.exists_pos
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun x : ℝ => (B+K)/log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := B+K) (f := atTop)).mul (tendsto_inv_atTop_zero.comp tendsto_log_atTop)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_gt_atTop 1,tendsto_log_atTop.eventually_ge_atTop 1,hθ,hπ.bound]
    with x hx hlog ht hp
  have hx0 : 0 < x := by linarith
  have hl := log_pos hx
  change |piReal x - θ x/log x| ≤ B*|x/log x^2| at hp
  rw [abs_of_pos (div_pos hx0 (pow_pos hl 2))] at hp
  have hrep : piReal x*log x/x-1 =
      (piReal x-θ x/log x)*(log x/x)+(θ x-x)/x := by field_simp; ring
  rw [Real.norm_eq_abs,hrep]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_div,abs_of_pos hx0,abs_of_pos hl]
  calc
    _ ≤ (B*(x/log x^2))*(log x/x)+(K*x/log x^3)/x := by gcongr
    _ = B/log x+K/log x^3 := by field_simp
    _ ≤ B/log x+K/log x := by
      gcongr
      simpa only [pow_one] using pow_le_pow_right₀ hlog (by decide : 1 ≤ 3)
    _ = _ := by ring

/-- The scaled prime count at a moving interior point. The fixed log shift
allows separate old cofactor fibers. -/
theorem counting_at_moving_scale {y : ℝ → ℝ} {w : ℝ} (hw : 0 < w)
    (hy : Tendsto y atTop (𝓝 w)) (c : ℝ) :
    Tendsto (fun t : ℝ => t * piReal (exp (t*y t-c)) / exp (t*y t-c))
      atTop (𝓝 w⁻¹) := by
  have hlin : Tendsto (fun t : ℝ => t * y t - c) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-c) (Filter.Tendsto.atTop_mul_pos hw tendsto_id hy)
  have hp := counting_pnt.comp (tendsto_exp_atTop.comp hlin)
  have hdiv : Tendsto (fun t : ℝ => c/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := c) (f := atTop)).mul tendsto_inv_atTop_zero
  have hi := (hy.sub hdiv).inv₀ (by simpa using hw.ne' : w-0 ≠ 0)
  have h := hp.mul hi
  simp only [sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0,hlin.eventually_gt_atTop 0] with t ht hu
  dsimp only [Function.comp_apply]
  rw [log_exp]
  have hy0 : y t-c/t ≠ 0 := by
    rw [sub_ne_zero,ne_eq,eq_div_iff ht.ne']
    linarith [mul_comm (y t) t]
  field_simp

#print axioms counting_at_moving_scale
end Erdos490PrimeCells

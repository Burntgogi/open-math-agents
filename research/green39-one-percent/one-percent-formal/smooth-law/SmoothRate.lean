import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

open Filter Asymptotics
open scoped Topology

namespace Green39.Smooth
noncomputable section

/-- Scalar upper bound for the joint failure event with the manuscript's constants. -/
def paperRate (N p k : ℝ) := N*(2*Real.exp (-k/320000000000000000) +
    p*Real.exp (10^24 - (10^24/2)*Real.sqrt k) +
    p*Real.exp (-(9:ℝ)/10000*Real.sqrt k))

theorem paperRate_le {N p k : ℝ} (hN : 0 ≤ N) (hp : 1 ≤ p)
    (hk : 10^16 ≤ Real.sqrt k) (hcost : N*p ≤ Real.exp (Real.sqrt k/10000)) :
    paperRate N p k ≤ 4*Real.exp (-(8:ℝ)/10000*Real.sqrt k) := by
  let r := Real.sqrt k
  have hr : (10:ℝ)^16 ≤ r := hk
  have hk0 : 0 ≤ k := by
    by_contra! h
    rw [Real.sqrt_eq_zero_of_nonpos h.le] at hk
    norm_num at hk
  have hr2 : r^2 = k := Real.sq_sqrt hk0
  have hr0 : 0 ≤ r := Real.sqrt_nonneg k
  have h₁ : -k/320000000000000000 ≤ -(9:ℝ)/10000*r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hr0]
  have h₂ : (10:ℝ)^24 - (10^24/2)*r ≤ -(9:ℝ)/10000*r := by linarith
  let e := Real.exp (-(9:ℝ)/10000*r)
  have he : 0 ≤ e := Real.exp_nonneg _
  calc
    paperRate N p k ≤ N*(2*e + p*e + p*e) := by
      unfold paperRate
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₁) (by norm_num : (0:ℝ) ≤ 2))
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h₂) (zero_le_one.trans hp))) le_rfl) hN
    _ ≤ 4*(N*p)*e := by
      have hpe := mul_le_mul_of_nonneg_right hp he
      nlinarith [mul_nonneg hN (sub_nonneg.mpr hpe)]
    _ ≤ 4*Real.exp (r/10000)*e := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- If the logarithmic family-and-shift cost is o(√k), the explicit finite error tends to zero. -/
theorem paperRate_tendsto {N p k : ℕ → ℝ} (hN : ∀ n, 0 ≤ N n) (hp : ∀ n, 1 ≤ p n)
    (hk : Tendsto k atTop atTop)
    (hcost : (fun n ↦ Real.log (1+N n*p n)) =o[atTop] (fun n ↦ Real.sqrt (k n))) :
    Tendsto (fun n ↦ paperRate (N n) (p n) (k n)) atTop (𝓝 0) := by
  have hr := Real.tendsto_sqrt_atTop.comp hk
  have hu : Tendsto (fun n ↦ 4*Real.exp (-(8:ℝ)/10000*Real.sqrt (k n))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp
      (hr.const_mul_atTop_of_neg (show -(8:ℝ)/10000 < 0 by norm_num))).const_mul 4
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall fun n ↦ by
      dsimp [paperRate]
      have hp0 := (zero_le_one.trans (hp n))
      have hN0 := hN n
      positivity
  · filter_upwards [hr.eventually_ge_atTop (10^16), hcost.bound (show 0 < (1:ℝ)/10000 by norm_num)]
      with n hn hc
    apply paperRate_le (hN n) (hp n) hn
    have hpos : 0 < 1+N n*p n := by
      have hh := mul_nonneg (hN n) (zero_le_one.trans (hp n))
      linarith
    have hlog : Real.log (1+N n*p n) ≤ Real.sqrt (k n)/10000 := by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hc
      linarith [le_abs_self (Real.log (1+N n*p n))]
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hpos] at h
    linarith

end
end Green39.Smooth

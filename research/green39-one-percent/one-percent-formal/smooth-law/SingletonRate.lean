import SmoothRate
import Mathlib

open Filter Real
namespace Green39.Smooth

theorem singleton_paperRate : ∀ᶠ p : ℕ in atTop,
    paperRate 1 p p.sqrt ≤ exp (-((p.sqrt : ℝ)^(0.48:ℝ))) := by
  have hs : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop.mpr fun k => (eventually_ge_atTop (k^2)).mono ?_
    exact fun _ hp => Nat.le_sqrt'.mpr hp
  have hk : Tendsto (fun p : ℕ => (p.sqrt : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hs
  have hr := Real.tendsto_sqrt_atTop.comp hk
  have hl := hk.eventually ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).bound
    (by norm_num : (0:ℝ) < 1/30000))
  have hm := hk.eventually ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2-0.48)).eventually_ge_atTop 2500)
  filter_upwards [hs.eventually_ge_atTop 4, hr.eventually_ge_atTop ((10:ℝ)^16), hl, hm] with p h4 hbig hlog hmargin
  let k : ℝ := p.sqrt
  have hk4 : 4 ≤ k := by dsimp [k]; exact_mod_cast h4
  have hk0 : 0 < k := by linarith
  have hp1 : 1 ≤ p := by have := Nat.sqrt_le_self p; omega
  have hp3 : p ≤ p.sqrt^3 := by
    have h := Nat.lt_succ_sqrt' p
    have hm₁ := Nat.mul_le_mul_left p.sqrt h4
    have hm₂ := Nat.mul_le_mul_left (p.sqrt^2) h4
    rw [Nat.succ_eq_add_one] at h
    nlinarith
  have hcost : (p:ℝ) ≤ exp (sqrt k/10000) := by
    change ‖log k‖ ≤ (1/30000:ℝ)*‖k^(1/2:ℝ)‖ at hlog
    rw [← Real.sqrt_eq_rpow, Real.norm_of_nonneg (sqrt_nonneg _),
      Real.norm_of_nonneg (log_nonneg (by linarith))] at hlog
    rw [← Real.exp_log (show 0 < (p:ℝ) by exact_mod_cast (show 0 < p by omega))]
    apply Real.exp_le_exp.mpr
    have hl' := Real.log_le_log (by exact_mod_cast (show 0 < p by omega) : (0:ℝ)<p)
      (show (p:ℝ) ≤ k^(3:ℕ) by dsimp [k]; exact_mod_cast hp3)
    rw [log_pow] at hl'
    norm_num at hl'
    linarith only [hl', hlog]
  have h := paperRate_le (N:=1) (p:=(p:ℝ)) (k:=k) (by norm_num) (by exact_mod_cast hp1) hbig (by simpa using hcost)
  have hz : (2500:ℝ)*k^(0.48:ℝ) ≤ sqrt k := by
    rw [sqrt_eq_rpow, show (1/2:ℝ) = (1/2-0.48)+0.48 by norm_num, rpow_add hk0]
    exact mul_le_mul_of_nonneg_right hmargin (rpow_nonneg hk0.le _)
  have hlog4 : log (4:ℝ) ≤ 4 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : 0 < (4:ℝ))]
  change (10:ℝ)^16 ≤ sqrt k at hbig
  apply h.trans
  conv_lhs => lhs; rw [← Real.exp_log (by norm_num : 0 < (4:ℝ))]
  rw [← exp_add]
  apply exp_le_exp.mpr
  linarith

end Green39.Smooth
#print axioms Green39.Smooth.singleton_paperRate

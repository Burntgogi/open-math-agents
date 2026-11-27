import BlueKernel
import KernelRange
import Transfer

open Real Filter MeasureTheory Set
open scoped Topology
namespace Erdos490Smooth
open Shift490 Erdos490PrimeCells

/-- A single translated cofactor shift, uniform over a full unit strip. -/
theorem blue_strip_minorant (k : ℕ) {w j c : ℝ} (hw : 0 < w) (hj : 0 < j) (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ r ∈ Icc j (j+1),
      smoothKernel k w hw (j+1) - ε ≤ F (smoothLabels k (exp (t*w))) (t*r-c) := by
  have hd : Tendsto (fun t : ℝ => c/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [hd.eventually_lt_const (half_pos hj),eventually_gt_atTop 0,
    smoothKernel_uniform k hw (half_pos hj) (b := j+1) hε] with t hcut ht hh
  intro r hr
  have hnon : 0 ≤ c/t := div_nonneg hc ht.le
  have hlow : j/2 ≤ r-c/t := by linarith [hr.1]
  have hhigh : r-c/t ≤ j+1 := by linarith [hr.2]
  have hh' := (abs_lt.mp (hh _ ⟨hlow,hhigh⟩)).1
  have hm := smoothKernel_antitone k hw (a := r-c/t) (b := j+1) (lt_of_lt_of_le (half_pos hj) hlow)
    (by change 0 < j+1; linarith) hhigh
  rw [show t*(r-c/t) = t*r-c by field_simp] at hh'
  linarith

/-- Quantitative lower transfer for one strip of the actual new-label law. -/
theorem moving_blue_strip (k : ℕ) {w j c : ℝ} (hw : 0 < w) (hj : 0 < j) (hc : 0 ≤ c)
    (i : Label) (l : List Label) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    let A := Ioc (x-j-1) (x-j)
    let ν := (labelSum limitFactor (i::l) : Measure ℝ)
    ∀ᶠ t : ℝ in atTop, ν.real A * smoothKernel k w hw (j+1) - ε ≤
      ∫ y in A, F (smoothLabels k (exp (t*w))) (t*(x-y)-c) ∂(labelSum (primeFactor t) (i::l) : Measure ℝ) := by
  let A := Ioc (x-j-1) (x-j)
  let mt (t : ℝ) := (labelSum (primeFactor t) (i::l) : Measure ℝ)
  let ν := (labelSum limitFactor (i::l) : Measure ℝ)
  let d := smoothKernel k w hw (j+1)
  have hA : MeasurableSet A := measurableSet_Ioc
  have hmass : Tendsto (fun t => (mt t).real A) atTop (𝓝 (ν.real A)) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (labelStrip_tendsto i l (by linarith : x-j-1 < x-j))
  have hh := (hmass.mul_const d).eventually_const_lt (by linarith : ν.real A*d-ε/2 < ν.real A*d)
  filter_upwards [hh,blue_strip_minorant k hw hj hc (half_pos hε)] with t ht hbound
  let f (y : ℝ) := F (smoothLabels k (exp (t*w))) (t*(x-y)-c)
  have hfm : Measurable f := (measurable_F _).comp (by fun_prop)
  have hfi : Integrable f (mt t) :=
    Integrable.mono' (integrable_const (μ := mt t) (1:ℝ)) hfm.aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (F_nonneg _ _)]; exact F_le_one _ _)
  have lower : (mt t).real A * (d-ε/2) ≤ ∫ y in A, f y ∂mt t := by
    rw [← smul_eq_mul, ← setIntegral_const]
    apply setIntegral_mono_on (integrable_const _) hfi.integrableOn hA
    intro y hy
    apply hbound (x-y)
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hprob : (mt t).real A ≤ 1 := measureReal_le_one
  change ν.real A * d - ε ≤ ∫ y in A, f y ∂mt t
  exact le_trans (by nlinarith [mul_le_mul_of_nonneg_right hprob (half_pos hε).le]) lower

#print axioms moving_blue_strip
end Erdos490Smooth



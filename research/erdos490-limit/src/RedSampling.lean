import LabelDensity

open MeasureTheory Real Set
open scoped Interval

namespace Erdos490PrimeCells

/-- The Lebesgue mass of the exponential weight in the red sampling window. -/
theorem redSampling_weight_integral {z B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ) :
    (∫ x in Icc (z - B - δ) (z + δ), exp (x - z - δ)) =
      1 - exp (-B - 2 * δ) := by
  have hab : z - B - δ ≤ z + δ := by linarith
  have hcont : Continuous (fun x : ℝ => exp (x - z - δ)) := by fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ => exp (t - z - δ)) (exp (x - z - δ)) x := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id x).sub_const z).sub_const δ).exp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hcont.intervalIntegrable _ _)]
  rw [show z + δ - z - δ = 0 by ring, exp_zero,
    show z - B - δ - z - δ = -B - 2 * δ by ring]

/-- Transport the weighted mass of a finite family of old centers to the closed sampling
window. The density identity is tested using its indicator, so an endpoint of the window is
included on the probability side. -/
theorem redSampling_integral_lower {ι : Type*} (S : Finset ι) (y c : ι → ℝ)
    (μ : ι → ProbabilityMeasure ℝ) (d : ι → ℝ → ℝ) {z B δ : ℝ}
    (hy : ∀ s ∈ S, y s ∈ Icc (z - B) z) (hc : ∀ s ∈ S, 0 ≤ c s)
    (hidentity : ∀ s ∈ S, ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x, φ x * d s x) = ∫ x, φ x ∂(μ s : Measure ℝ))
    (hsupport : ∀ s ∈ S, ∀ᵐ x ∂(μ s : Measure ℝ), x ∈ Icc (y s - δ) (y s + δ)) :
    IntegrableOn (fun x => exp (x - z - δ) * ∑ s ∈ S, c s * d s x)
      (Icc (z - B - δ) (z + δ)) ∧
    exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z)) ≤
      ∫ x in Icc (z - B - δ) (z + δ), exp (x - z - δ) * ∑ s ∈ S, c s * d s x := by
  let W := Icc (z - B - δ) (z + δ)
  let w (x : ℝ) := exp (x - z - δ)
  let φ := W.indicator w
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hφ : Measurable φ := hw.indicator measurableSet_Icc
  have hw_bound : ∀ x ∈ W, ‖w x‖ ≤ 1 := by
    intro x hx
    rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
    have hupper : x ≤ z + δ := hx.2
    linarith
  have hφ_bound (x : ℝ) : ‖φ x‖ ≤ 1 := by
    change ‖W.indicator w x‖ ≤ 1
    by_cases hx : x ∈ W
    · rw [indicator_of_mem hx]
      exact hw_bound x hx
    · rw [indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  have hterm (s : ι) (hs : s ∈ S) :
      IntegrableOn (fun x => w x * (c s * d s x)) W := by
    have hm : (∫ x, d s x) = 1 := by
      simpa only [one_mul, integral_const, probReal_univ, one_smul] using
        hidentity s hs (fun _ => 1) measurable_const (fun _ => by simp)
    have hdi : Integrable (d s) := by
      by_contra h
      rw [integral_undef h] at hm
      exact zero_ne_one hm
    have hw_bound_ae : ∀ᵐ x ∂(volume.restrict W : Measure ℝ), ‖w x‖ ≤ 1 :=
      (ae_restrict_mem measurableSet_Icc).mono hw_bound
    simpa only [IntegrableOn, mul_comm] using
      ((hdi.integrableOn (s := W)).const_mul (c s)).mul_bdd
        hw.aestronglyMeasurable hw_bound_ae
  have hpoint (s : ι) (hs : s ∈ S) :
      exp (-2 * δ) * exp (y s - z) ≤ ∫ x in W, w x * d s x := by
    have htest : (∫ x in W, w x * d s x) = ∫ x, φ x ∂(μ s : Measure ℝ) := by
      rw [← integral_indicator (s := W) measurableSet_Icc, ← hidentity s hs φ hφ hφ_bound]
      congr 1
      funext x
      change W.indicator (fun x => w x * d s x) x = W.indicator w x * d s x
      by_cases hx : x ∈ W
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    have hφi : Integrable φ (μ s : Measure ℝ) :=
      (integrable_const (1 : ℝ)).mono' hφ.aestronglyMeasurable (ae_of_all _ hφ_bound)
    rw [htest, ← exp_add]
    calc
      exp (-2 * δ + (y s - z)) =
          ∫ _ : ℝ, exp (-2 * δ + (y s - z)) ∂(μ s : Measure ℝ) := by
        rw [integral_const, probReal_univ, one_smul]
      _ ≤ ∫ x, φ x ∂(μ s : Measure ℝ) := by
        apply integral_mono_ae (integrable_const _) hφi
        filter_upwards [hsupport s hs] with x hx
        have hxW : x ∈ W := by
          exact ⟨by linarith [hx.1, (hy s hs).1], by linarith [hx.2, (hy s hs).2]⟩
        change exp _ ≤ W.indicator w x
        rw [indicator_of_mem hxW]
        change exp _ ≤ exp (x - z - δ)
        rw [exp_le_exp]
        linarith [hx.1]
  change IntegrableOn (fun x => w x * ∑ s ∈ S, c s * d s x) W ∧
    _ ≤ ∫ x in W, w x * ∑ s ∈ S, c s * d s x
  simp_rw [Finset.mul_sum]
  refine ⟨integrable_finsetSum S hterm, ?_⟩
  rw [integral_finsetSum S hterm]
  apply Finset.sum_le_sum
  intro s hs
  rw [mul_left_comm (exp (-2 * δ)) (c s)]
  simp_rw [mul_left_comm (w _) (c s), integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hpoint s hs) (hc s hs)

/-- The sampling step (13) for a finite family of good old centers.
The sampled point can avoid any finite set of exceptional endpoints. -/
theorem exists_redSampling_ge {ι : Type*} (S : Finset ι) (y c : ι → ℝ)
    (μ : ι → ProbabilityMeasure ℝ) (d : ι → ℝ → ℝ) {z B δ : ℝ}
    (hB : 0 < B) (hδ : 0 ≤ δ)
    (hy : ∀ s ∈ S, y s ∈ Icc (z - B) z) (hc : ∀ s ∈ S, 0 ≤ c s)
    (hidentity : ∀ s ∈ S, ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x, φ x * d s x) = ∫ x, φ x ∂(μ s : Measure ℝ))
    (hsupport : ∀ s ∈ S, ∀ᵐ x ∂(μ s : Measure ℝ), x ∈ Icc (y s - δ) (y s + δ))
    (hne : (∑ s ∈ S, c s * exp (y s - z)) ≠ 0) {E : Set ℝ} (hE : E.Finite) :
    ∃ x ∈ Icc (z - B - δ) (z + δ), x ∉ E ∧
      exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z)) ≤ ∑ s ∈ S, c s * d s x := by
  let W := Icc (z - B - δ) (z + δ)
  let m := exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z))
  let w (x : ℝ) := exp (x - z - δ)
  change ∃ x ∈ W, x ∉ E ∧ m ≤ ∑ s ∈ S, c s * d s x
  have hsum : 0 ≤ ∑ s ∈ S, c s * exp (y s - z) :=
    Finset.sum_nonneg fun s hs => mul_nonneg (hc s hs) (exp_pos _).le
  have hm : 0 < m := mul_pos (exp_pos _) (lt_of_le_of_ne hsum hne.symm)
  have hw : IntegrableOn w W := by
    have hcont : Continuous w := by dsimp [w]; fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨hi, hlower⟩ := redSampling_integral_lower S y c μ d hy hc hidentity hsupport
  by_contra! h
  have hle : (∫ x in W, w x * ∑ s ∈ S, c s * d s x) ≤ ∫ x in W, w x * m := by
    apply integral_mono_ae hi (hw.mul_const m)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := W) measurableSet_Icc,
      ae_restrict_of_ae (s := W) (hE.countable.ae_notMem (volume : Measure ℝ))] with x hx hxE
    exact mul_le_mul_of_nonneg_left (h x hx hxE).le (exp_pos _).le
  have hmass : (∫ x in W, w x) < 1 := by
    change (∫ x in Icc (z - B - δ) (z + δ), exp (x - z - δ)) < 1
    rw [redSampling_weight_integral hB hδ]
    exact sub_lt_self _ (exp_pos _)
  exact (not_lt_of_ge (hlower.trans hle)) (by
    rw [integral_mul_const]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hmass hm)

/-- Specialization to the normalized densities of nonempty lists of old labels. -/
theorem exists_redSampling_labelDensity_ge {ι : Type*} (S : Finset ι) (y c : ι → ℝ)
    (i : ι → Label) (L : ι → List Label) {z B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hy : ∀ s ∈ S, y s ∈ Icc (z - B) z) (hc : ∀ s ∈ S, 0 ≤ c s)
    (hsupport : ∀ s ∈ S, ∀ᵐ x ∂(labelSum limitFactor (i s :: L s) : Measure ℝ),
      x ∈ Icc (y s - δ) (y s + δ))
    (hne : (∑ s ∈ S, c s * exp (y s - z)) ≠ 0) {E : Set ℝ} (hE : E.Finite) :
    ∃ x ∈ Icc (z - B - δ) (z + δ), x ∉ E ∧
      exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z)) ≤
        ∑ s ∈ S, c s * (labelDensity (i s) (L s) x / log ((i s).hi / (i s).lo)) := by
  refine exists_redSampling_ge S y c (fun s => labelSum limitFactor (i s :: L s))
    (fun s x => labelDensity (i s) (L s) x / log ((i s).hi / (i s).lo))
    hB hδ hy hc ?_ hsupport hne hE
  intro s _ φ _ _
  have hm := (log_pos ((one_lt_div (i s).positive).mpr (i s).nonempty)).ne'
  simp_rw [← mul_div_assoc]
  rw [integral_div, integral_mul_labelDensity, mul_div_cancel_left₀ _ hm]

/-- The empty product gives an atom at zero, outside the sampling window when its lower
endpoint is positive. -/
theorem redSampling_empty_restrict {z B δ : ℝ} (h : 0 < z - B - δ) :
    (labelSum limitFactor [] : Measure ℝ).restrict (Icc (z - B - δ) (z + δ)) = 0 := by
  change (Measure.dirac (0 : ℝ)).restrict (Icc (z - B - δ) (z + δ)) = 0
  rw [Measure.restrict_eq_zero, Measure.dirac_apply' _ measurableSet_Icc]
  simp [h.not_ge]

#print axioms redSampling_weight_integral
#print axioms redSampling_integral_lower
#print axioms exists_redSampling_ge
#print axioms exists_redSampling_labelDensity_ge
#print axioms redSampling_empty_restrict

end Erdos490PrimeCells

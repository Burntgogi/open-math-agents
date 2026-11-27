import AbelCells

open Filter Finset Real MeasureTheory Set
open scoped Topology Interval Chebyshev

namespace Erdos490PrimeCells

private lemma logEnvelope {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    (∫ t in x..y, 1 / (t * log t ^ 4)) =
      (1 / log x ^ 3 - 1 / log y ^ 3) / 3 := by
  have hpt {t : ℝ} (ht : t ∈ Set.uIcc x y) : 1 < t := by
    rw [Set.uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(log t ^ 3)⁻¹ / 3)
    (f' := fun t => 1 / (t * log t ^ 4)) (a := x) (b := y) (fun t ht => ?_) ?_
  · rw [h]; ring
  · have ht1 := hpt ht
    have ht0 : 0 < t := by linarith
    have hl := log_pos ht1
    apply (((((Real.hasDerivAt_log ht0.ne').pow 3).inv (pow_ne_zero 3 hl.ne')).neg).div_const 3).congr_deriv
    simp only [Pi.pow_apply]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 := hpt ht
    have ht0 : 0 < t := by linarith
    have hl := log_pos ht1
    exact (continuousAt_const.div (continuousAt_id.mul ((continuousAt_log ht0.ne').pow 4))
      (mul_ne_zero ht0.ne' (pow_ne_zero _ hl.ne'))).continuousWithinAt

private theorem pointwise {x K : ℝ} (hx : 1 < x) (hl : 1 ≤ log x)
    (h : |θ x - x| ≤ K*x / log x ^ 3) :
    |slope x * (θ x - x)| ≤ (2*K) * (1 / (x * log x ^ 4)) := by
  have hx0 : 0 < x := by linarith
  have hl0 := log_pos hx
  have hK : 0 ≤ K := by
    have hpos := (abs_nonneg _).trans h
    by_contra! hn
    exact (not_lt_of_ge hpos) (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hn hx0) (by positivity))
  have hsl : |slope x| = (log x + 1) / (x ^ 2 * log x ^ 2) := by
    unfold slope
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [abs_mul, hsl]
  calc
    _ ≤ ((2 * log x) / (x ^ 2 * log x ^ 2)) * (K*x / log x ^ 3) := by
      gcongr
      linarith
    _ = _ := by field_simp

theorem reciprocal_remainder {x y K : ℝ} (hx : 1 < x) (hxy : x ≤ y) (hl : 1 ≤ log x)
    (hK : 0 ≤ K) (hθ : ∀ t ∈ Set.Icc x y, |θ t - t| ≤ K*t / log t ^ 3) :
    |reciprocalInterval x y - (log (log y) - log (log x))| ≤ 3*K / log x ^ 3 := by
  have hpos {t : ℝ} (ht : x ≤ t) : 0 < t := by linarith
  have hlog {t : ℝ} (ht : x ≤ t) : 1 ≤ log t := hl.trans (log_le_log (hpos le_rfl) ht)
  have hlogpos {t : ℝ} (ht : x ≤ t) : 0 < log t := log_pos (hx.trans_le ht)
  have hs : ContinuousOn slope (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy]
    exact fun t ht => (slope_cont (hx.trans_le ht.1)).continuousWithinAt
  have hi : IntervalIntegrable (fun t => slope t * θ t) volume x y :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hs
  have hj : IntervalIntegrable (fun t => slope t * t) volume x y :=
    (hs.mul continuousOn_id).intervalIntegrable
  have hk {t : ℝ} (ht : t ∈ Set.Icc x y) :
      |kernel t * (θ t - t)| ≤ K / log x ^ 3 := by
    have ht0 := hpos ht.1
    have hl0 := hlogpos ht.1
    rw [abs_mul, kernel, abs_of_pos (inv_pos.mpr (mul_pos ht0 hl0))]
    calc
      _ ≤ (t * log t)⁻¹ * (K*t / log t ^ 3) := by gcongr; exact hθ t ht
      _ = K / log t ^ 4 := by field_simp
      _ ≤ K / log x ^ 3 := by
        gcongr
        calc
          log x ^ 3 ≤ log t ^ 3 := by gcongr; exact ht.1
          _ ≤ log t ^ 4 := pow_le_pow_right₀ (hlog ht.1) (by decide)
  have herr : IntervalIntegrable (fun t => slope t * (θ t - t)) volume x y := by
    simpa only [mul_sub] using hi.sub hj
  have he : |∫ t in x..y, slope t * (θ t - t)| ≤ K / log x ^ 3 := by
    apply (intervalIntegral.abs_integral_le_integral_abs hxy).trans
    calc
      _ ≤ ∫ t in x..y, (2*K) * (1 / (t * log t ^ 4)) := by
        apply intervalIntegral.integral_mono_on hxy herr.abs
        · apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hxy]
          intro t ht
          have ht0 := hpos ht.1
          have hl0 := hlogpos ht.1
          fun_prop (disch := positivity)
        · intro t ht
          exact pointwise (hx.trans_le ht.1) (hlog ht.1) (hθ t ht)
      _ = (2*K) * ((1 / log x ^ 3 - 1 / log y ^ 3) / 3) := by
        rw [intervalIntegral.integral_const_mul, logEnvelope hx hxy]
      _ ≤ _ := by
        have h1 : 0 ≤ K * (1 / log y ^ 3) := by have := hlogpos hxy; positivity
        have h2 : 0 ≤ K * (1 / log x ^ 3) := by have := hlogpos (le_rfl (a := x)); positivity
        rw [div_eq_mul_one_div K]
        linarith only [h1,h2]
  rw [abel_reciprocal hx hxy, ← abel_main_term hx hxy, show
    kernel y * θ y - kernel x * θ x - (∫ t in x..y, slope t * θ t) -
    (kernel y * y - kernel x * x - (∫ t in x..y, slope t * t)) =
    kernel y * (θ y-y) - kernel x * (θ x-x) -
    ((∫ t in x..y, slope t * θ t) - ∫ t in x..y, slope t * t) by ring,
    ← intervalIntegral.integral_sub hi hj]
  simp only [← mul_sub]
  have h1 := abs_sub (kernel y * (θ y - y) - kernel x * (θ x - x)) (∫ t in x..y, slope t * (θ t-t))
  have h2 := abs_sub (kernel y * (θ y-y)) (kernel x * (θ x-x))
  rw [mul_div_assoc]
  linarith [hk (t := y) ⟨hxy,le_rfl⟩, hk (t := x) ⟨le_rfl,hxy⟩]

end Erdos490PrimeCells

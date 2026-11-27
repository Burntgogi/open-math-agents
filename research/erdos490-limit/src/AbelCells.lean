import PrimeNumberTheoremAnd.IEANTN.Mertens

open Filter Finset Real MeasureTheory Set
open scoped Topology Interval Chebyshev

namespace Erdos490PrimeCells

noncomputable def kernel (x : ℝ) := (x * log x)⁻¹
noncomputable def slope (x : ℝ) := -(log x + 1) / (x ^ 2 * log x ^ 2)

private theorem kernel_hasDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt kernel (slope x) x := by
  have hx' := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')).inv (mul_ne_zero hx0.ne' hx'.ne')
  apply h.congr_deriv
  dsimp [slope]
  field_simp

theorem slope_cont {x : ℝ} (hx : 1 < x) : ContinuousAt slope x := by
  have := (Real.log_pos hx).ne'
  unfold slope
  fun_prop (disch := positivity)

noncomputable def reciprocalInterval (x y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (n : ℝ)⁻¹

theorem abel_reciprocal {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    reciprocalInterval x y =
      kernel y * θ y - kernel x * θ x - ∫ t in x..y, slope t * θ t := by
  let c (n : ℕ) : ℝ := if n.Prime then log n else 0
  have hc (z : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, c n) = θ z := by
    simp [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, c]
  have hk : IntegrableOn (deriv kernel) (Set.Icc x y) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr (f := slope)
    · exact fun t ht => (slope_cont (hx.trans_le ht.1)).continuousWithinAt
    · exact fun t ht => (kernel_hasDeriv (hx.trans_le ht.1)).deriv
  have ha := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ x) hxy
    (fun t ht => (kernel_hasDeriv (hx.trans_le ht.1)).differentiableAt) hk
  simp only [hc, ← intervalIntegral.integral_of_le hxy] at ha
  convert ha using 1
  · unfold reciprocalInterval
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime
    · have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      simp [c,hp,kernel,field]
      exact (div_self (log_pos h).ne').symm
    · simp [c,hp]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    change slope t * θ t = deriv kernel t * θ t
    rw [(kernel_hasDeriv (hx.trans_le ht.1)).deriv]

private theorem primitive_hasDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => (log t)⁻¹ - log (log t)) (slope x * x) x := by
  have hx0 : 0 < x := by linarith
  have hl := log_pos hx
  have logDer := Real.hasDerivAt_log hx0.ne'
  apply ((logDer.inv hl.ne').sub (logDer.log hl.ne')).congr_deriv
  unfold slope
  field_simp
  ring

theorem abel_main_term {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    kernel y * y - kernel x * x - (∫ t in x..y, slope t * t) =
      log (log y) - log (log x) := by
  have hpt {t : ℝ} (ht : t ∈ Set.uIcc x y) : 1 < t := by
    rw [Set.uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => primitive_hasDeriv (hpt ht))
    (ContinuousOn.intervalIntegrable (fun t ht =>
      ((slope_cont (hpt ht)).mul continuousAt_id).continuousWithinAt))]
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  simp [kernel, mul_inv_rev, hx0, hy0]
  ring

end Erdos490PrimeCells

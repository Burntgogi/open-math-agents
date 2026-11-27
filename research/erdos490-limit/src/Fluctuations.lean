import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

noncomputable section
namespace Shift490
open Finset MeasureTheory ProbabilityTheory

/-- The second-moment estimate uses only pairwise independence. The variables can be the
success indicators on a product of arbitrary (including countably infinite) cell spaces. -/
theorem few_successes {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (s : Finset ι) (X : ι → Ω → ℝ)
    (hL : ∀ i ∈ s, MemLp (X i) 2 μ)
    (h01 : ∀ i ∈ s, ∀ ω, X i ω = 0 ∨ X i ω = 1)
    (hi : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ)
    {m : ℝ} (hm : 0 < m) (hmean : 4*m ≤ ∑ i ∈ s, ∫ ω, X i ω ∂μ) :
    μ {ω | (∑ i ∈ s, X i ω) < m} ≤ ENNReal.ofReal (1/m) := by
  let T := ∑ i ∈ s, X i
  let M := ∑ i ∈ s, ∫ ω, X i ω ∂μ
  have hM : 4*m ≤ M := hmean
  have hpos : 0 < M := by linarith
  have hT : MemLp T 2 μ := memLp_finsetSum' s hL
  have hE : ∫ ω, T ω ∂μ = M := by
    simp only [T, M, Finset.sum_apply]
    exact integral_finsetSum s fun i hi' => (hL i hi').integrable (by norm_num)
  have hv : variance T μ ≤ M := by
    rw [show T = ∑ i ∈ s, X i from rfl, IndepFun.variance_sum hL hi]
    apply sum_le_sum
    intro i h
    rw [variance_eq_sub (hL i h)]
    have he : X i ^ 2 = X i := by
      funext ω
      rcases h01 i h ω with h' | h' <;> simp [Pi.pow_apply, h']
    rw [he]
    linarith [sq_nonneg (∫ ω, X i ω ∂μ)]
  calc
    _ ≤ μ {ω | M/2 ≤ |T ω - ∫ z, T z ∂μ|} := by
      apply measure_mono
      intro ω h
      change M/2 ≤ |T ω - ∫ z, T z ∂μ|
      have hh : T ω < m := by simpa [T] using h
      rw [hE, abs_of_nonpos (by linarith)]
      linarith
    _ ≤ ENNReal.ofReal (variance T μ / (M/2)^2) :=
      meas_ge_le_variance_div_sq hT (by positivity)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_div_iff₀ (by positivity) hm).mpr
      nlinarith [mul_le_mul_of_nonneg_right hv hm.le, mul_nonneg hpos.le (sub_nonneg.mpr hM)]

/-- In the product geometric exponent law the all-zero atom has weight ∏(1-q).
Changing a single exponent from zero to one multiplies its weight by q. -/
theorem single_success_weight {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℝ) :
    (∑ i ∈ s, ∏ j ∈ s, ((1-q j) * q j ^ (if j = i then 1 else 0 : ℕ))) =
      (∏ j ∈ s, (1-q j)) * ∑ i ∈ s, q i := by
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [prod_mul_distrib]
  congr 1
  rw [prod_eq_single_of_mem i hi] <;> simp_all

/-- Lower bound for the probability of success using only reciprocal mass. -/
theorem success_probability_lower {ι : Type*} (s : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i ∧ q i ≤ 1)
    (hsmall : ∑ i ∈ s, q i ≤ 1/2) :
    (∑ i ∈ s, q i)/2 ≤ (∏ i ∈ s, (1-q i)) * ∑ i ∈ s, q i := by
  classical
  have bound (u : Finset ι) (hu : u ⊆ s) :
      1 - ∑ i ∈ u, q i ≤ ∏ i ∈ u, (1-q i) := by
    induction u using Finset.induction with
    | empty => simp
    | insert a u ha ih =>
      have hsub : u ⊆ s := fun i hi => hu (mem_insert_of_mem hi)
      obtain ⟨h0,h1⟩ := hq a (hu (mem_insert_self ..))
      have hs : 0 ≤ ∑ i ∈ u, q i := sum_nonneg fun i hi => (hq i (hsub hi)).1
      rw [sum_insert ha, prod_insert ha]
      exact le_trans (by nlinarith [mul_nonneg h0 hs]) (mul_le_mul_of_nonneg_left
        (ih hsub) (sub_nonneg.mpr h1))
  have hh := bound s (fun _ h => h)
  have hn := sum_nonneg (s := s) fun i hi => (hq i hi).1
  nlinarith [mul_nonneg hn (show 0 ≤ (∏ i ∈ s, (1-q i)) - 1/2 by linarith)]

#print axioms few_successes
#print axioms single_success_weight
#print axioms success_probability_lower
end Shift490

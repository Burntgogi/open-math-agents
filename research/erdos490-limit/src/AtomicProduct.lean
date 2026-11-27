import LabelSum
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

open Real MeasureTheory Set Finset
open scoped ENNReal NNReal
namespace Erdos490PrimeCells

/-- The discrete finite product law, before normalizing each factor. -/
theorem atomic_product {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : κ → ℝ≥0) (v : κ → ℝ) :
    Measure.pi (fun _ : ι => ∑ k, w k • Measure.dirac (v k)) =
      ∑ f : ι → κ, (∏ i, w (f i)) • Measure.dirac (fun i => v (f i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hset := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,Measure.dirac_apply' _ hset]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro f _
  simp only [Set.indicator_apply,Pi.one_apply,Set.mem_univ_pi]
  by_cases h : ∀ i, v (f i) ∈ s i
  · simp [h]
  · push Not at h
    obtain ⟨i,hi⟩ := h
    rw [if_neg (fun hh => hi (hh i)),mul_zero]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

/-- Restore the masses after a product of normalized laws.  This includes zero
factors, for which Mathlib chooses an arbitrary normalization. -/
theorem pi_restore_mass {ι : Type*} [Fintype ι] (μ : FiniteMeasure ℝ) :
    Measure.pi (fun _ : ι => (μ : Measure ℝ)) =
      (μ.mass ^ Fintype.card ι) • (ProbabilityMeasure.pi (fun _ : ι => μ.normalize) : Measure (ι → ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ProbabilityMeasure.toMeasure_pi,Measure.pi_pi]
  have h (i : ι) : (μ : Measure ℝ) (s i) = (μ.mass:ℝ≥0∞) * (μ.normalize : Measure ℝ) (s i) := by
    simpa only [ENNReal.coe_mul,FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun a : ℝ≥0 => (a:ℝ≥0∞)) (μ.self_eq_mass_mul_normalize (s i))
  simp_rw [h]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,ENNReal.coe_pow]

end Erdos490PrimeCells




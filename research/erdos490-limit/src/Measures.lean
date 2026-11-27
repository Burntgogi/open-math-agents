import Weak
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open Filter Real MeasureTheory
open scoped Topology Interval ENNReal NNReal

namespace Erdos490PrimeCells

noncomputable def primeLaw (s a b : ℝ) : FiniteMeasure ℝ :=
  ⟨∑ p ∈ primeBand s a b, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/s), inferInstance⟩

private lemma integral_primeLaw (s a b : ℝ) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ v, f v ∂(primeLaw s a b : Measure ℝ)) = weighted s a b f := by
  change (∫ v, f v ∂(∑ p ∈ primeBand s a b, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/s))) = _
  unfold weighted
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [← Measure.coe_nnreal_smul,integral_smul_measure,integral_dirac]
    simp [div_eq_mul_inv, mul_comm]
  · intro p _
    exact f.integrable (μ := ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/s))

private noncomputable def density (x : ℝ) : ℝ≥0 := Real.toNNReal x⁻¹

noncomputable def cellLaw (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Set.Ioc a b)).withDensity (fun t => (density t : ℝ≥0∞)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,MeasureTheory.setLIntegral_univ]
    have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')
    apply lt_of_le_of_lt (lintegral_mono (g := fun t : ℝ => ‖t⁻¹‖ₑ) (fun t => ?_))
      (hi.1.hasFiniteIntegral)
    exact Real.ofReal_le_enorm _⟩

private theorem integral_cellLaw {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ v, f v ∂(cellLaw a b ha hab : Measure ℝ)) = ∫ v in a..b, f v/v := by
  change (∫ v, f v ∂(volume.restrict (Set.Ioc a b)).withDensity (fun t => (density t : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul (by unfold density; fun_prop),intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht0 := ha.trans ht.1
  change (density t : ℝ) * f t = f t/t
  rw [density,Real.coe_toNNReal _ (inv_nonneg.mpr ht0.le),div_eq_mul_inv,mul_comm]

theorem finiteMeasure_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun s => primeLaw s a b) atTop (𝓝 (cellLaw a b ha hab)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  simp only [integral_primeLaw,integral_cellLaw]
  exact weighted_window ha hab f.continuous.continuousOn

theorem cellLaw_nonzero {a b : ℝ} (ha : 0 < a) (hab : a < b) : cellLaw a b ha hab.le ≠ 0 := by
  intro hz
  have h := integral_cellLaw ha hab.le (1 : BoundedContinuousFunction ℝ ℝ)
  rw [hz] at h
  simp only [FiniteMeasure.toMeasure_zero,integral_zero_measure,BoundedContinuousFunction.coe_one,
    Pi.one_apply,one_div,integral_inv_of_pos ha (ha.trans hab)] at h
  exact (log_pos ((one_lt_div ha).mpr hab)).ne' h.symm

instance cellLaw_nullSingleton {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    NullSingletonClass (cellLaw a b ha hab : Measure ℝ) := by
  change NullSingletonClass ((volume.restrict (Set.Ioc a b)).withDensity _)
  infer_instance

#print axioms finiteMeasure_tendsto
end Erdos490PrimeCells

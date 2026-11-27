import AtomicProduct

open Real MeasureTheory Set Finset
open scoped ENNReal NNReal
namespace Erdos490PrimeCells

theorem atomic_family {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (w : (i : ι) → κ i → ℝ≥0) (v : (i : ι) → κ i → ℝ) :
    Measure.pi (fun i => ∑ k, w i k • Measure.dirac (v i k)) =
      ∑ f : (i : ι) → κ i, (∏ i, w i (f i)) • Measure.dirac (fun i => v i (f i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hset := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,Measure.dirac_apply' _ hset]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro f _
  simp only [Set.indicator_apply,Pi.one_apply,Set.mem_univ_pi]
  by_cases h : ∀ i, v i (f i) ∈ s i
  · simp [h]
  · push Not at h
    obtain ⟨i,hi⟩ := h
    rw [if_neg (fun hh => hi (hh i)),mul_zero]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem pi_restore_family {ι : Type*} [Fintype ι] (μ : ι → FiniteMeasure ℝ) :
    Measure.pi (fun i => (μ i : Measure ℝ)) =
      (∏ i, (μ i).mass) • (ProbabilityMeasure.pi (fun i => (μ i).normalize) : Measure (ι → ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ProbabilityMeasure.toMeasure_pi,Measure.pi_pi]
  have h (i : ι) : (μ i : Measure ℝ) (s i) = ((μ i).mass:ℝ≥0∞) * ((μ i).normalize : Measure ℝ) (s i) := by
    simpa only [ENNReal.coe_mul,FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun a : ℝ≥0 => (a:ℝ≥0∞)) ((μ i).self_eq_mass_mul_normalize (s i))
  simp_rw [h]
  simp [Finset.prod_mul_distrib]

theorem prime_family_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (labels : ι → Label) :
    Measure.pi (fun i => (primeLaw t (labels i).lo (labels i).hi : Measure ℝ)) =
    ∑ f : (i : ι) → primeBand t (labels i).lo (labels i).hi,
      (∏ i, ((f i : ℕ):ℝ≥0)⁻¹) • Measure.dirac (fun i => log (f i : ℕ)/t) := by
  classical
  let S (i : ι) := primeBand t (labels i).lo (labels i).hi
  let w (i : ι) (p : S i) : ℝ≥0 := (p.val:ℝ≥0)⁻¹
  let v (i : ι) (p : S i) := log p.val/t
  have H (i : ι) : (primeLaw t (labels i).lo (labels i).hi : Measure ℝ) = ∑ p : S i,w i p • Measure.dirac (v i p) :=
    (Finset.sum_attach (S i) _).symm
  simp_rw [H]
  exact atomic_family w v

#print axioms prime_family_expansion
end Erdos490PrimeCells

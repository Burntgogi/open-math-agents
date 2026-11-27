import Simplices
import AtomicProduct
import Mathlib.MeasureTheory.Integral.Indicator

open Filter Real MeasureTheory Set
open scoped Topology ENNReal NNReal Classical
namespace Erdos490PrimeCells

theorem measurable_simplex (j : ℕ) (c : ℝ) : MeasurableSet (orderedSimplex j c) := by
  let pairs := {p : Fin j × Fin j // p.1 < p.2}
  have he : orderedSimplex j c =
      (⋂ p : pairs, {v : Fin j → ℝ | v p.val.1 < v p.val.2}) ∩ {v | ∑ i, v i ≤ c} := by
    ext v
    simp only [orderedSimplex,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    apply and_congr_left
    exact fun _ => ⟨fun hm p => hm p.property,fun hm i k hik => hm ⟨(i,k),hik⟩⟩
  rw [he]
  exact (MeasurableSet.iInter fun p : pairs => (isOpen_lt (continuous_apply p.val.1)
    (continuous_apply p.val.2)).measurableSet).inter (isClosed_le (show Continuous (fun v : Fin j → ℝ => ∑ i, v i) by fun_prop) (continuous_const (y := c))).measurableSet

theorem simplex_cdf_continuous {n : ℕ} (i : Label) :
    Continuous (fun c => (ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) :
      Measure (Fin (n+1) → ℝ)).real (orderedSimplex (n+1) c)) := by
  let μ := (ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) : Measure (Fin (n+1) → ℝ))
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 c)
    (measurable_simplex _ _) (fun h => measurable_simplex _ h)
  have hne : ∀ᵐ v ∂μ, ∑ r, v r ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using pi_sum_null (fun _ : Fin (n+1) => limitFactor i) c
  filter_upwards [hne] with v hv
  rcases lt_or_gt_of_ne hv with h|h
  · filter_upwards [eventually_gt_nhds h] with y hy
    change (StrictMono v ∧ _ ≤ _) ↔ (StrictMono v ∧ _ ≤ _)
    simp [hy.le,h.le]
  · filter_upwards [eventually_lt_nhds h] with y hy
    change (StrictMono v ∧ _ ≤ _) ↔ (StrictMono v ∧ _ ≤ _)
    simp [hy.not_ge,h.not_ge]

noncomputable def simplexLimit (n : ℕ) (i : Label) (h : ℝ) : ℝ :=
  ((cellLaw i.lo i.hi i.positive i.nonempty.le).mass : ℝ)^(n+1) *
    (ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) :
      Measure (Fin (n+1) → ℝ)).real (orderedSimplex (n+1) h)

theorem simplexLimit_continuous (n : ℕ) (i : Label) : Continuous (simplexLimit n i) :=
  continuous_const.mul (simplex_cdf_continuous i)

theorem finite_simplex_tendsto (n : ℕ) (i : Label) (h : ℝ) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (n+1) => (primeLaw t i.lo i.hi : Measure ℝ))).real
      (orderedSimplex (n+1) h)) atTop (𝓝 (simplexLimit n i h)) := by
  have hmass := (FiniteMeasure.continuous_mass.tendsto _).comp (finiteMeasure_tendsto i.positive i.nonempty.le)
  have hprob := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (ordered_simplex_tendsto (n := n) i h)
  have H := (((NNReal.continuous_coe.tendsto _).comp hmass).pow (n+1)).mul hprob
  apply H.congr'
  filter_upwards with t
  simp only [Function.comp_apply,pi_restore_mass (ι := Fin (n+1)),Measure.real,Measure.smul_apply,
    ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_pow,
    Fintype.card_fin,primeFactor]

#print axioms finite_simplex_tendsto
#print axioms simplexLimit_continuous
end Erdos490PrimeCells



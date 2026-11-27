import Measures
import Mathlib.MeasureTheory.Measure.Portmanteau

open Filter Real MeasureTheory Set
open scoped Topology ENNReal

namespace Erdos490PrimeCells

structure Label where
  lo : ℝ
  hi : ℝ
  positive : 0 < lo
  nonempty : lo < hi

noncomputable def limitFactor (i : Label) :=
  (cellLaw i.lo i.hi i.positive i.nonempty.le).normalize

noncomputable def primeFactor (s : ℝ) (i : Label) := (primeLaw s i.lo i.hi).normalize

theorem factor_tendsto (i : Label) :
    Tendsto (fun s => primeFactor s i) atTop (𝓝 (limitFactor i)) :=
  FiniteMeasure.tendsto_normalize_of_tendsto (finiteMeasure_tendsto i.positive i.nonempty.le)
    (cellLaw_nonzero i.positive i.nonempty)

private abbrev addPair (x : ℝ × ℝ) := x.1+x.2
private lemma continuous_addPair : Continuous addPair := continuous_fst.add continuous_snd

noncomputable def sumLaw (μ ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  (μ.prod ν).map continuous_addPair.measurable.aemeasurable

theorem sumLaw_continuous : Continuous (fun m : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ =>
    sumLaw m.1 m.2) :=
  (ProbabilityMeasure.continuous_map continuous_addPair).comp ProbabilityMeasure.continuous_prod

noncomputable def labelSum (μ : Label → ProbabilityMeasure ℝ) : List Label → ProbabilityMeasure ℝ
  | [] => ⟨Measure.dirac 0,inferInstance⟩
  | i::l => sumLaw (labelSum μ l) (μ i)

theorem labelSum_tendsto (labels : List Label) :
    Tendsto (fun s => labelSum (primeFactor s) labels) atTop (𝓝 (labelSum limitFactor labels)) := by
  induction labels with
  | nil => exact tendsto_const_nhds
  | cons i l ih => exact sumLaw_continuous.continuousAt.tendsto.comp (ih.prodMk_nhds (factor_tendsto i))

instance limitFactor_nullSingleton (i : Label) : NullSingletonClass (limitFactor i : Measure ℝ) := by
  unfold limitFactor
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (cellLaw_nonzero i.positive i.nonempty)]
  constructor
  intro x
  rw [Measure.smul_apply,measure_singleton,smul_zero]

theorem sumLaw_singleton (μ ν : ProbabilityMeasure ℝ) [NullSingletonClass (ν : Measure ℝ)] (v : ℝ) :
    (sumLaw μ ν : Measure ℝ) {v} = 0 := by
  unfold sumLaw
  rw [ProbabilityMeasure.map_apply' _ _ (measurableSet_singleton v), ProbabilityMeasure.toMeasure_prod,
    Measure.prod_apply (continuous_addPair.measurable (measurableSet_singleton v))]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro x
  have hs : Prod.mk x ⁻¹' (addPair ⁻¹' {v}) = {v-x} := by
    ext y
    simp only [Set.mem_preimage,Set.mem_singleton_iff,addPair]
    constructor <;> intro h <;> linarith
  change (ν : Measure ℝ) (Prod.mk x ⁻¹' (addPair ⁻¹' {v})) = 0
  rw [hs,measure_singleton]

/-- Probabilities of every translated strip converge for every nonempty tuple
of labels. The boundary is a pair of null singleton sets. -/
theorem labelStrip_tendsto (i : Label) (l : List Label) {a b : ℝ} (hab : a < b) :
    Tendsto (fun s => (labelSum (primeFactor s) (i::l) : Measure ℝ) (Set.Ioc a b)) atTop
      (𝓝 ((labelSum limitFactor (i::l) : Measure ℝ) (Set.Ioc a b))) := by
  apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (labelSum_tendsto _)
  rw [frontier_Ioc hab]
  apply le_antisymm _ bot_le
  calc
    _ ≤ (sumLaw (labelSum limitFactor l) (limitFactor i) : Measure ℝ) {a} +
        (sumLaw (labelSum limitFactor l) (limitFactor i) : Measure ℝ) {b} :=
      measure_union_le _ _
    _ = _ := by rw [sumLaw_singleton,sumLaw_singleton,add_zero]; rfl

#print axioms labelStrip_tendsto
end Erdos490PrimeCells

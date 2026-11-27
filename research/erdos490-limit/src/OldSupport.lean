import CellTuple
import WordLaw

open Finset Filter Real Set MeasureTheory
open scoped Topology
namespace Erdos490PrimeCells

theorem limitFactor_supported (i : Label) :
    ∀ᵐ v ∂(limitFactor i : Measure ℝ), v ∈ Icc i.lo i.hi := by
  rw [limitFactor,FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (cellLaw_nonzero i.positive i.nonempty)]
  apply Measure.ae_smul_measure
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact (ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := i.lo) (b := i.hi))).mono
    fun _ h => ⟨h.1.le,h.2⟩

theorem labelSum_supported {n : ℕ} (i : Fin n → Label) (center err : Fin n → ℝ)
    (h : ∀ j, ∀ v ∈ Icc (i j).lo (i j).hi, |v-center j| ≤ err j) :
    ∀ᵐ y ∂(labelSum limitFactor (List.ofFn i) : Measure ℝ),
      |y-∑ j,center j| ≤ ∑ j,err j := by
  rw [←labelSum_ofFn,ae_map_iff (by fun_prop) (isClosed_le (by fun_prop) continuous_const).measurableSet]
  have hall : ∀ᵐ v ∂Measure.pi (fun j => (limitFactor (i j) : Measure ℝ)),
      ∀ j, v j ∈ Icc (i j).lo (i j).hi :=
    ae_all_iff.mpr (fun j => Measure.tendsto_eval_ae_ae (i := j) (μ := fun r => (limitFactor (i r) : Measure ℝ)) (limitFactor_supported (i j)))
  filter_upwards [hall] with v hc
  change |(∑ j,v j)-∑ j,center j| ≤ _
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => h j _ (hc j))

theorem good_product_support {n : ℕ} (b : ℝ) (p : Fin n → ℕ) (hp : ∀ j,(p j).Prime)
    (e : Fin n → ℝ) (h : ∀ j, ∀ v ∈ Icc (boundary b (p j)) (boundary b (p j+1)),
       |v-log (p j)| ≤ e j) {δ : ℝ} (he : ∑ j,e j ≤ δ) :
    ∀ᵐ y ∂(labelSum limitFactor (List.ofFn fun j => cellLabel b (p j) (hp j)) : Measure ℝ),
      y ∈ Icc (log ((∏ j,p j:ℕ):ℝ)-δ) (log ((∏ j,p j:ℕ):ℝ)+δ) := by
  have ha := labelSum_supported (fun j => cellLabel b (p j) (hp j)) (fun j => log (p j)) e h
  filter_upwards [ha] with y hy
  rw [Nat.cast_prod,log_prod (fun j _ => (by exact_mod_cast (hp j).ne_zero))]
  exact ⟨by linarith [(abs_le.mp (hy.trans he)).1], by linarith [(abs_le.mp (hy.trans he)).2]⟩

#print axioms good_product_support
end Erdos490PrimeCells


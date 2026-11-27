import LabelSum
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

open Filter Real MeasureTheory Set
open scoped Topology ENNReal
namespace Erdos490PrimeCells

theorem pi_slice_null {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    (i : Fin (n+1)) [NullSingletonClass (μ i : Measure ℝ)]
    {A : Set (Fin (n+1) → ℝ)} (hA : MeasurableSet A)
    (h : ∀ y : Fin n → ℝ, ∃ v : ℝ, ∀ x : ℝ, i.insertNth x y ∈ A → x = v) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) A = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he := (measurePreserving_piFinSuccAbove (fun j => (μ j : Measure ℝ)) i).symm e
  change Measure.pi (fun j => (μ j : Measure ℝ)) A = 0
  rw [← he.map_eq,Measure.map_apply e.symm.measurable hA,
    Measure.prod_apply_symm (e.symm.measurable hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  obtain ⟨v,hv⟩ := h y
  apply measure_mono_null (t := {v}) _ (measure_singleton _)
  intro x hx
  exact hv x hx

theorem pi_sum_null {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    [∀ i, NullSingletonClass (μ i : Measure ℝ)] (c : ℝ) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) {v | ∑ i, v i = c} = 0 := by
  let i : Fin (n+1) := 0
  apply pi_slice_null μ i (isClosed_eq (by fun_prop) continuous_const).measurableSet
  intro y
  refine ⟨c - ∑ j, y j,fun x hx => ?_⟩
  change ∑ j, i.insertNth (α := fun _ => ℝ) x y j = c at hx
  rw [i.sum_univ_succAbove, i.insertNth_apply_same] at hx
  simpa only [Fin.insertNth_apply_succAbove,eq_sub_iff_add_eq] using hx

theorem pi_diagonal_null {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    [∀ i, NullSingletonClass (μ i : Measure ℝ)] {i j : Fin (n+1)} (hij : i ≠ j) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) {v | v i = v j} = 0 := by
  apply pi_slice_null μ i (isClosed_eq (continuous_apply i) (continuous_apply j)).measurableSet
  obtain ⟨r,hr⟩ := Fin.exists_succAbove_eq hij.symm
  intro y
  refine ⟨y r,fun x hx => ?_⟩
  change i.insertNth (α := fun _ => ℝ) x y i = i.insertNth (α := fun _ => ℝ) x y j at hx
  simpa only [←hr,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] using hx

private lemma frontier_inter_null {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) {A B : Set X} (hA : μ (frontier A) = 0) (hB : μ (frontier B) = 0) :
    μ (frontier (A ∩ B)) = 0 := by
  apply measure_mono_null (t := frontier A ∪ frontier B) _ (measure_union_null hA hB)
  exact (frontier_inter_subset A B).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)

def orderedSimplex (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {v | StrictMono v ∧ ∑ i, v i ≤ c}

theorem simplex_null_frontier {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    [∀ i, NullSingletonClass (μ i : Measure ℝ)] (c : ℝ) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) (frontier (orderedSimplex (n+1) c)) = 0 := by
  classical
  let pairs := {p : Fin (n+1) × Fin (n+1) // p.1 < p.2}
  let ν := (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ))
  let checks (s : Finset pairs) : Set (Fin (n+1) → ℝ) :=
    {v | ∀ p ∈ s, v p.val.1 < v p.val.2}
  have hchecks (s : Finset pairs) : ν (frontier (checks s)) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp [checks]
    | @insert p s _ ih =>
      have he : checks (insert p s) = {v | v p.val.1 < v p.val.2} ∩ checks s := by
        ext; simp [checks]
      rw [he]
      apply frontier_inter_null ν _ ih
      exact measure_mono_null (frontier_lt_subset_eq (continuous_apply p.val.1)
        (continuous_apply p.val.2)) (pi_diagonal_null μ p.property.ne)
  have he : orderedSimplex (n+1) c = checks Finset.univ ∩ {v | ∑ i, v i ≤ c} := by
    ext v
    change (StrictMono v ∧ _) ↔ ((∀ p ∈ (Finset.univ : Finset pairs), _) ∧ _)
    apply and_congr_left
    intro _
    exact ⟨fun h p _ => h p.property,fun h i j hij => h ⟨(i,j),hij⟩ (Finset.mem_univ _)⟩
  rw [he]
  apply frontier_inter_null ν (hchecks _) _
  exact measure_mono_null (frontier_le_subset_eq (by fun_prop) continuous_const) (pi_sum_null μ c)

theorem ordered_simplex_tendsto {n : ℕ} (i : Label) (c : ℝ) :
    Tendsto (fun t => (ProbabilityMeasure.pi (fun _ : Fin (n+1) => primeFactor t i) :
      Measure (Fin (n+1) → ℝ)) (orderedSimplex (n+1) c)) atTop
      (𝓝 ((ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) :
        Measure (Fin (n+1) → ℝ)) (orderedSimplex (n+1) c))) := by
  apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' _ (simplex_null_frontier _ _)
  exact ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr fun _ => factor_tendsto i)

#print axioms ordered_simplex_tendsto
end Erdos490PrimeCells


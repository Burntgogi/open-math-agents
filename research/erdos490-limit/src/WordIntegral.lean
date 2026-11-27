import WordLaw
import FamilyAtoms

open Finset Real MeasureTheory
open scoped Topology NNReal ENNReal
namespace Erdos490PrimeCells

/-- Harmonic products in distinct prime cells, including the exact finite masses.
The identity itself allows repeated labels. -/
theorem sum_tuple_test {n : ℕ} (t : ℝ) (i : Fin n → Label) (g : ℝ → ℝ)
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    (∑ f : (j : Fin n) → primeBand t (i j).lo (i j).hi,
      (∏ j,((f j : ℕ):ℝ)⁻¹) * g (∑ j,log (f j : ℕ)/t)) =
      (∏ j,((primeLaw t (i j).lo (i j).hi).mass:ℝ)) *
        ∫ y, g y ∂(labelSum (primeFactor t) (List.ofFn i) : Measure ℝ) := by
  classical
  let μ (j : Fin n) := primeLaw t (i j).lo (i j).hi
  let s (v : Fin n → ℝ) := ∑ j,v j
  let ν := Measure.pi (fun j => (μ j : Measure ℝ))
  have hs : Measurable s := by dsimp [s]; fun_prop
  let f (v : Fin n → ℝ) := g (s v)
  have hf : Measurable f := hg.comp hs
  have hfin (m : Measure (Fin n → ℝ)) [IsFiniteMeasure m] : Integrable f m :=
    (integrable_const (μ := m) C).mono' hf.aestronglyMeasurable (ae_of_all _ (fun v => hC (s v)))
  calc
    _ = ∫ v, f v ∂ν := by
      dsimp only [ν,μ]
      rw [prime_family_expansion,integral_finsetSum_measure]
      · apply Finset.sum_congr rfl
        intro vals _
        rw [← Measure.coe_nnreal_smul,integral_smul_measure,integral_dirac]
        simp [f,s,NNReal.coe_prod]
      · intro _ _
        apply hfin
    _ = _ := by
      change (∫ v, g (s v) ∂Measure.pi (fun j => (μ j : Measure ℝ))) = _
      rw [pi_restore_family,← Measure.coe_nnreal_smul,integral_smul_measure,smul_eq_mul]
      simp only [ENNReal.coe_toReal,NNReal.coe_prod]
      congr 1
      rw [←labelSum_ofFn (primeFactor t) i,integral_map hs.aemeasurable hg.aestronglyMeasurable]
      rfl

#print axioms sum_tuple_test
end Erdos490PrimeCells

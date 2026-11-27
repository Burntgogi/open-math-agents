import LabelSum
import AtomicProduct

open Finset Real MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Erdos490PrimeCells

theorem labelSum_ofFn {n : ℕ} (law : Label → ProbabilityMeasure ℝ) (labels : Fin n → Label) :
    Measure.map (fun v : Fin n → ℝ => ∑ i,v i) (Measure.pi (fun i => (law (labels i) : Measure ℝ))) =
      (labelSum law (List.ofFn labels) : Measure ℝ) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty,Measure.map_dirac' (by fun_prop)]
    simp [labelSum]
  | succ n ih =>
    let tail (j : Fin n) := labels j.succ

    let ν := Measure.pi (fun j : Fin n => (law (tail j) : Measure ℝ))
    let tot (v : Fin n → ℝ) := ∑ j,v j
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    let add (z : ℝ × ℝ) := z.1 + z.2
    have he := (measurePreserving_piFinSuccAbove (fun j => (law (labels j) : Measure ℝ)) (0 : Fin (n+1))).map_eq
    have ht : Measure.map tot ν = (labelSum law (List.ofFn tail) : Measure ℝ) := ih tail
    have ec : Measure.map e (Measure.pi (fun j => (law (labels j) : Measure ℝ))) =
        (law (labels 0) : Measure ℝ).prod ν := by simpa [e,ν,tail] using he
    have proj : Measurable (Prod.map tot (id : ℝ → ℝ)) := by dsimp [tot]; fun_prop
    have hadd : Measurable add := by dsimp [add]; fun_prop
    rw [List.ofFn_succ]
    change _ = Measure.map add ((labelSum law (List.ofFn tail) : Measure ℝ).prod (law (labels 0) : Measure ℝ))
    rw [← ht]
    conv_rhs => arg 2; arg 2; rw [← Measure.map_id (μ := (law (labels 0) : Measure ℝ))]
    rw [Measure.map_prod_map _ _ (by dsimp [tot]; fun_prop) measurable_id,
      ←Measure.prod_swap (μ := (law (labels 0) : Measure ℝ)) (ν := ν),← ec]
    rw [Measure.map_map measurable_swap e.measurable,Measure.map_map proj (measurable_swap.comp e.measurable),
      Measure.map_map hadd (proj.comp (measurable_swap.comp e.measurable))]
    congr 1
    funext v
    change ∑ j,v j = (∑ j : Fin n,v j.succ) + v 0
    rw [Fin.sum_univ_succ,add_comm]

end Erdos490PrimeCells

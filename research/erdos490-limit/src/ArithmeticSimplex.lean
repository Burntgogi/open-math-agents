import Enumerate
import AtomicProduct
import Simplices

open Real Filter MeasureTheory Finset Set
open scoped Topology ENNReal NNReal Classical
namespace Erdos490PrimeCells
open Erdos490Smooth

theorem log_tuple_simplex {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) {j : ℕ}
    (f : Fin j → S) {t : ℝ} (ht : 0 < t) (h : ℝ) :
    (fun i => log (f i : ℕ)/t) ∈ orderedSimplex j h ↔
      (StrictMono fun i => (f i : ℕ)) ∧ (∏ p ∈ tupleRange f, p) ≤ ⌊exp (t*h)⌋₊ := by
  have hp (i : Fin j) : (0 : ℝ) < (f i : ℕ) := by exact_mod_cast hS _ (f i).property
  have hmono : StrictMono (fun i => log (f i : ℕ)/t) ↔ StrictMono fun i => (f i : ℕ) := by
    constructor
    · intro H i k hik
      exact_mod_cast (log_lt_log_iff (hp i) (hp k)).mp ((div_lt_div_iff_of_pos_right ht).mp (H hik))
    · intro H i k hik
      exact div_lt_div_of_pos_right (log_lt_log (hp i) (by exact_mod_cast H hik)) ht
  change (_ ∧ _) ↔ _
  rw [hmono]
  apply and_congr_right
  intro H
  rw [← Finset.sum_div, div_le_iff₀ ht,tupleRange_prod H (fun p => p),Nat.le_floor_iff (exp_pos _).le]
  have prodpos : 0 < ∏ i, ((f i : ℕ):ℝ) := Finset.prod_pos fun i _ => hp i
  rw [Nat.cast_prod]
  change (∑ i, log (f i : ℕ)) ≤ h*t ↔ (∏ i, ((f i : ℕ):ℝ)) ≤ exp (t*h)
  rw [← Real.log_le_iff_le_exp prodpos,Real.log_prod (fun i _ => (hp i).ne'),mul_comm]

theorem primeTuple_eval (j : ℕ) (t a b : ℝ) (A : Set (Fin j → ℝ)) :
    (Measure.pi (fun _ : Fin j => (primeLaw t a b : Measure ℝ))).real A =
      ∑ f : Fin j → primeBand t a b with (fun i => log (f i : ℕ)/t) ∈ A,
        ∏ i, (((f i : ℕ):ℝ)⁻¹) := by
  classical
  let S := primeBand t a b
  let w (p : S) : ℝ≥0 := (p.val:ℝ≥0)⁻¹
  let v (p : S) : ℝ := log p.val/t
  have he : (primeLaw t a b : Measure ℝ) = ∑ p : S, w p • Measure.dirac (v p) := by
    change ∑ p ∈ S, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/t) = _
    exact (Finset.sum_attach S _).symm
  rw [Measure.real,he,atomic_product w v,Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (fun f _ => measure_ne_top ((∏ i, w (f i)) • Measure.dirac (fun i => v (f i))) A)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  rw [Measure.smul_apply,Measure.dirac_apply,ENNReal.smul_def,smul_eq_mul,Set.indicator_apply]
  by_cases ha : (fun i => v (f i)) ∈ A
  · simp [ha,w,v,NNReal.coe_prod]
  · simp [ha,w,v]

theorem primeTuple_simplex (j : ℕ) {t : ℝ} (ht : 0 < t) (a b h : ℝ) :
    (Measure.pi (fun _ : Fin j => (primeLaw t a b : Measure ℝ))).real (orderedSimplex j h) =
      ∑ V ∈ ((primeBand t a b).powersetCard j).filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊),
        ∏ p ∈ V,(p:ℝ)⁻¹ := by
  classical
  rw [primeTuple_eval]
  have hS : ∀ p ∈ primeBand t a b, 0 < p := fun _ hp => (Finset.mem_filter.mp hp).2.pos
  simp_rw [log_tuple_simplex hS _ ht h]
  exact tuple_subset_sum (primeBand t a b) j (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊) (fun p => (p:ℝ)⁻¹)

#print axioms primeTuple_simplex
end Erdos490PrimeCells



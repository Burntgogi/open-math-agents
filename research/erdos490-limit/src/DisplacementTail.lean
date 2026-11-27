import Mathlib

open Filter Finset Real
open scoped Topology

namespace Erdos490PrimeCells

private theorem reciprocal_log_step {n : ℕ} (hn : 2 ≤ n) :
    1 / (((n:ℝ)+1) * log ((n:ℝ)+1)^2) ≤ (log (n:ℝ))⁻¹ - (log ((n:ℝ)+1))⁻¹ := by
  have hn1 : 1 < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hp1 : 1 < (n:ℝ)+1 := by linarith
  have hp0 : 0 < (n:ℝ)+1 := by linarith
  have hln := log_pos hn1
  have hlp := log_pos hp1
  have hle : log (n:ℝ) ≤ log ((n:ℝ)+1) := log_le_log hn0 (by linarith)
  have h := log_le_sub_one_of_pos (div_pos hn0 hp0)
  rw [log_div hn0.ne' hp0.ne'] at h
  have hd : 1/((n:ℝ)+1) ≤ log ((n:ℝ)+1)-log n := by
    have h' : (n:ℝ)/((n:ℝ)+1) - 1 = -(1/((n:ℝ)+1)) := by field_simp; ring
    linarith [h']
  calc
    _ = (1/((n:ℝ)+1)) / (log ((n:ℝ)+1)*log ((n:ℝ)+1)) := by field_simp
    _ ≤ (log ((n:ℝ)+1)-log n) / (log n * log ((n:ℝ)+1)) := by gcongr
    _ = _ := by field_simp

theorem finite_displacement_tail {y : ℕ} (hy : 2 ≤ y) (z : ℕ) :
    ∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, 1 / ((p:ℝ)*log p^2) ≤ (log y)⁻¹ := by
  have hy1 : 1 < (y:ℝ) := by exact_mod_cast (by omega : 1 < y)
  by_cases hyz : y ≤ z
  · calc
      _ ≤ ∑ n ∈ Finset.Ioc y z, 1 / ((n:ℝ)*log n^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n _ _
        positivity
      _ ≤ (log y)⁻¹ - (log z)⁻¹ := by
        induction z, hyz using Nat.le_induction with
        | base => simp
        | succ z hz ih =>
          rw [Finset.sum_Ioc_succ_top hz]
          have h := reciprocal_log_step (hy.trans hz)
          rw [Nat.cast_succ]
          linarith
      _ ≤ _ := by
        have hz1 : 1 < (z:ℝ) := hy1.trans_le (by exact_mod_cast hyz)
        linarith [inv_pos.mpr (log_pos hz1)]
  · rw [Finset.Ioc_eq_empty (by omega : ¬y < z)]
    simpa only [Finset.filter_empty,Finset.sum_empty] using (inv_nonneg.mpr (log_pos hy1).le)

#print axioms finite_displacement_tail
end Erdos490PrimeCells

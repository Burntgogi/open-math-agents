import Mathlib

open Filter Finset
open scoped Topology Interval

namespace Erdos490PrimeCells

noncomputable def reciprocalBefore (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range n).filter Nat.Prime, (p : ℝ)⁻¹

noncomputable def boundary (b : ℝ) (n : ℕ) : ℝ :=
  Real.exp (reciprocalBefore n - b)

lemma before_succ (n : ℕ) :
    reciprocalBefore (n + 1) = reciprocalBefore n + if n.Prime then (n : ℝ)⁻¹ else 0 := by
  simp only [reciprocalBefore, Finset.sum_filter, Finset.sum_range_succ]

lemma boundary_succ (b : ℝ) {p : ℕ} (hp : p.Prime) :
    boundary b (p+1) = boundary b p * Real.exp (p : ℝ)⁻¹ := by
  simp only [boundary, before_succ, if_pos hp]
  rw [← Real.exp_add]
  congr 1
  ring

theorem integral_cell (b : ℝ) {p : ℕ} (hp : p.Prime) :
    (∫ x in boundary b p..boundary b (p+1), x⁻¹) = (p : ℝ)⁻¹ := by
  have h : 0 < boundary b p := Real.exp_pos _
  have hnext : 0 < boundary b (p+1) := Real.exp_pos _
  rw [integral_inv_of_pos h hnext, boundary_succ b hp,
    mul_div_cancel_left₀ _ h.ne', Real.log_exp]

/-- Exponentiating a bound for the reciprocal-prime sum loses one power of log. -/
theorem boundary_error {s b x K : ℝ} (hx : 1 < x)
    (hsmall : |s - b - Real.log (Real.log x)| ≤ 1)
    (hs : |s - b - Real.log (Real.log x)| ≤ K / Real.log x ^ 3) :
    |Real.exp (s-b) - Real.log x| ≤ 2*K / Real.log x ^ 2 := by
  have hlog := Real.log_pos hx
  let r := s - b - Real.log (Real.log x)
  have he : Real.exp (s-b) = Real.log x * Real.exp r := by
    rw [← Real.exp_log hlog, ← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  rw [he, ← mul_sub_one, abs_mul, abs_of_pos hlog]
  calc
    _ ≤ Real.log x * (2 * |r|) :=
      mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hsmall) hlog.le
    _ ≤ Real.log x * (2 * (K / Real.log x ^ 3)) := by gcongr
    _ = _ := by field_simp

theorem interior_error {u a b c D : ℝ} (hau : a ≤ u) (hub : u ≤ b)
    (ha : |a-c| ≤ D) (hb : |b-c| ≤ D) : |u-c| ≤ D := by
  rw [abs_le] at *
  constructor <;> linarith

end Erdos490PrimeCells

import PrimeNumberTheoremAnd.IEANTN.Mertens

open Finset Filter Real Asymptotics
open scoped Topology

namespace Erdos490PrimeCells

noncomputable def cutoffFactor (x : ℝ) : ℝ :=
  (∏ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, (1 - (1 : ℝ)/p)) *
    exp ((∑ p ∈ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ)/p) - Mertens.M) *
    exp eulerMascheroniConstant

theorem cutoffFactor_eq {x : ℝ} (hx : 1 < x) :
    cutoffFactor x = exp (Mertens.E₃ x + Mertens.E₂p x) := by
  unfold cutoffFactor
  rw [Mertens.prod_one_minus_div_prime_eq hx, Mertens.sum_prime_div_eq]
  rw [show log (log x) + Mertens.M + Mertens.E₂p x - Mertens.M =
      log (log x) + Mertens.E₂p x by ring, exp_add, exp_log (log_pos hx), exp_add, exp_neg]
  field_simp [(log_pos hx).ne']

theorem cutoffFactor_tendsto : Tendsto cutoffFactor atTop (𝓝 1) := by
  have h2 := (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h3 := (isLittleO_one_iff ℝ).mp Mertens.E₃.bound'
  have h := (h3.add h2).rexp
  simp only [add_zero, exp_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (cutoffFactor_eq hx).symm

#print axioms cutoffFactor_tendsto
end Erdos490PrimeCells

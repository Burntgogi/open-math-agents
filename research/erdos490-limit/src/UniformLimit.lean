import UniformError

open Filter Finset Real
open scoped Topology
namespace Erdos490Smooth
open Shift490

theorem uniform_sieve_approx (k : ℕ) {a w B : ℝ} (ha : 0 < a) (hw : 0 < w) (hwB : w ≤ B)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t : ℝ in atTop, ∀ h ∈ Set.Icc a B,
    |F (smoothLabels k (exp (t*w))) (t*h) -
      localProduct (Nat.primesLE k) * signedSum (smoothLabels ⌊exp (t*w)⌋₊ (exp (t*B))) (t*h)| < ε := by
  let C : ℝ := 2 ^ (Nat.primesLE k).card + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK : 0 ≤ K₀ := by unfold K₀; positivity
  have he := (tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hw)).eventually_ge_atTop (k:ℝ)
  have hM := (rough_mass_limit hw hwB).eventually_lt_const (by linarith : B/w < B/w+1)
  filter_upwards [he,hM,eventually_gt_atTop (C*K₀*(B/w+1)/(ε*a)),eventually_gt_atTop 0] with t hk hM ht ht0
  intro h hh
  obtain ⟨hah,hhB⟩ := hh
  have hth := mul_pos ht0 (ha.trans_le hah)
  apply (smooth_sieve_error k (Nat.le_floor hk) hth (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hhB ht0.le))).trans_lt
  change C * (K₀ * _ / (t*h)) < ε
  rw [← mul_div_assoc,div_lt_iff₀ hth]
  have hb := (div_lt_iff₀ (mul_pos hε ha)).mp ht
  calc
    _ ≤ C*K₀*(B/w+1) := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hM.le (mul_nonneg hC hK)
    _ < t*(ε*a) := hb
    _ ≤ ε*(t*h) := by nlinarith [mul_le_mul_of_nonneg_left hah (mul_pos hε ht0).le]

#print axioms uniform_sieve_approx
end Erdos490Smooth


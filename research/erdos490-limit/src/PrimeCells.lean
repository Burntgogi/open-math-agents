import Cells
import Reciprocal
import ThetaInput
import PrimeNumberTheoremAnd.StrongPNT

open Finset Filter Real Asymptotics
open scoped Topology Chebyshev

namespace Erdos490PrimeCells

theorem sharp_reciprocal_error :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Mertens.E₂p x| ≤ K / log x ^ 3 := by
  obtain ⟨C,hC,h⟩ := theta_log_error_of_psi StrongPNT
  exact ⟨3*C,by positivity,mertens_error_from_theta hC.le h⟩

private theorem before_succ_eq_mertens (n : ℕ) :
    reciprocalBefore (n+1) = log (log n) + Mertens.M + Mertens.E₂p n := by
  have h := Mertens.sum_prime_div_eq (n : ℝ)
  rw [Nat.floor_natCast] at h
  rw [← h, reciprocalBefore,Nat.range_succ_eq_Icc_zero]
  simp only [Finset.sum_filter,one_div]
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp

theorem cell_displacement :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      ∀ v ∈ Set.Icc (boundary Mertens.M p) (boundary Mertens.M (p+1)),
        |v - log p| ≤ C / log p ^ 2 := by
  obtain ⟨K,hK,h⟩ := sharp_reciprocal_error
  refine ⟨2*(K+1),by positivity,?_⟩
  have hpoly := (isLittleO_log_rpow_rpow_atTop (3:ℝ) (by norm_num : (0:ℝ)<1)).bound
    (by norm_num : (0:ℝ)<1)
  have hlog : ∀ᶠ t : ℝ in atTop, K+1 ≤ log t :=
    tendsto_log_atTop.eventually_ge_atTop _
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
    tendsto_natCast_atTop_atTop.eventually hpoly,
    tendsto_natCast_atTop_atTop.eventually hlog,eventually_ge_atTop 2] with p hpE hpG hpL hp2
  intro hp v hv
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp0 : 0 < (p:ℝ) := by linarith
  have hl := log_pos hp1
  change ‖log (p:ℝ) ^ (3:ℝ)‖ ≤ 1 * ‖(p:ℝ) ^ (1:ℝ)‖ at hpG
  rw [show (3:ℝ)=(3:ℕ) by norm_num,Real.rpow_natCast,Real.rpow_one,one_mul,
    Real.norm_eq_abs,abs_of_pos (by positivity),Real.norm_eq_abs,abs_of_pos hp0] at hpG
  have hrec := one_div_le_one_div_of_le (pow_pos hl 3) hpG
  have hcut : (K+1) / log p ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc
      K+1 ≤ log p := hpL
      _ = log (p:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ log (p:ℝ) ^ 3 := pow_le_pow_right₀ (by linarith : 1 ≤ log (p:ℝ)) (by decide)
  have hu : reciprocalBefore (p+1) - Mertens.M - log (log p) = Mertens.E₂p p := by
    rw [before_succ_eq_mertens]; ring
  have hd : reciprocalBefore p - Mertens.M - log (log p) = Mertens.E₂p p - (p:ℝ)⁻¹ := by
    rw [before_succ, if_pos hp] at hu
    linarith
  have hupper : |reciprocalBefore (p+1) - Mertens.M - log (log p)| ≤ (K+1) / log p ^ 3 := by
    rw [hu]; exact hpE.trans (by gcongr; linarith)
  have hlower : |reciprocalBefore p - Mertens.M - log (log p)| ≤ (K+1) / log p ^ 3 := by
    rw [hd,add_div]
    apply (abs_sub _ _).trans
    rw [abs_of_pos (inv_pos.mpr hp0)]
    exact add_le_add hpE (by simpa only [one_div] using hrec)
  exact interior_error hv.1 hv.2 (boundary_error hp1 (hlower.trans hcut) hlower)
    (boundary_error hp1 (hupper.trans hcut) hupper)

#print axioms sharp_reciprocal_error
#print axioms cell_displacement
end Erdos490PrimeCells


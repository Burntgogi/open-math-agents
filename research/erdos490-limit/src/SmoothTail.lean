import SmoothMass
import Rankin

open Filter Real Finset MeasureTheory Set
open scoped Topology
namespace Erdos490Smooth
open Shift490

private lemma tilt_envelope {S : Finset ℕ} (n : Integers S) (D : ℝ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    exp (-(max D (logN n))) ≤ exp (-σ*D) * tilted σ n := by
  have hn0 := nat_pos n
  change _ ≤ exp (-σ*D) * (((n:ℕ):ℝ)⁻¹ * exp (σ*logN n))
  have hlog : ((n:ℕ):ℝ)⁻¹ = exp (-(logN n)) := by rw [exp_neg,exp_log hn0]
  rw [hlog,← exp_add,← exp_add,exp_le_exp]
  have h1 := mul_le_mul_of_nonneg_left (le_max_left D (logN n)) hσ
  have h2 := mul_le_mul_of_nonneg_left (le_max_right D (logN n)) (sub_nonneg.mpr hσ1)
  linarith

theorem rankin_integral_tail (S : Finset ℕ) {X σ : ℝ} (hX : 1 ≤ X)
    (hS : ∀ p ∈ S, (p:ℝ) ≤ X) (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hsmall : σ * log X ≤ 1/4)
    (D : ℝ) :
    (∫ u in Ioi D, F S u) ≤ exp (-σ*D) * (P S * exp (8*σ*(log X + log 4 + 4))) := by
  have hsum := (tilted_sum S hσ1).mul_left (exp (-σ*D))
  rw [kernel_tail_integral]
  calc
    _ ≤ ∑' n : Integers S, exp (-σ*D) * tilted σ n := by
      have m := fun n : Integers S => tilt_envelope n D hσ hσ1.le
      exact (Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) m hsum.summable).tsum_le_tsum m hsum.summable
    _ = _ := hsum.tsum_eq
    _ ≤ _ := mul_le_mul_of_nonneg_left (tilted_product_bound hX hS hσ hsmall) (exp_pos _).le

theorem scaled_mass (S : Finset ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ h in Ioi 0, F S (t*h)) = P S / t := by
  rw [integral_comp_mul_left_Ioi _ _ ht,mul_zero,kernel_mass,smul_eq_mul,div_eq_inv_mul]

/-- Uniform exponential tightness, valid for every subset of the available primes. -/
theorem scaled_tail (S : Finset ℕ) {w t : ℝ} (ht : 0 < t) (hw : 0 < w) (htw : 1 ≤ t*w)
    (hS : ∀ p ∈ S, (p:ℝ) ≤ exp (t*w)) (H : ℝ) :
    (∫ h in Ioi H, F S (t*h)) ≤ (P S/t) * exp (2*(1+log 4+4)) * exp (-H/(4*w)) := by
  let σ := 1/(4*(t*w))
  have htw0 := mul_pos ht hw
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ1 : σ < 1 := by dsimp [σ]; rw [div_lt_one (by positivity)]; linarith
  have hx := one_le_exp htw0.le
  have hsmall : σ * log (exp (t*w)) ≤ 1/4 := by rw [log_exp]; dsimp [σ]; field_simp; linarith
  have htail := rankin_integral_tail S hx hS hσ.le hσ1 hsmall (t*H)
  rw [integral_comp_mul_left_Ioi _ _ ht,smul_eq_mul]
  have hx' : -σ*(t*H) = -H/(4*w) := by dsimp [σ]; field_simp
  rw [hx',log_exp] at htail
  have hexp : 8*σ*(t*w+log 4+4) ≤ 2*(1+log 4+4) := by
    dsimp [σ]
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr htw) (show 0 ≤ log 4 by positivity)]
  calc
    _ ≤ t⁻¹ * (exp (-H/(4*w)) * (P S * exp (8*σ*(t*w+log 4+4)))) :=
      mul_le_mul_of_nonneg_left htail (inv_nonneg.mpr ht.le)
    _ ≤ t⁻¹ * (exp (-H/(4*w)) * (P S * exp (2*(1+log 4+4))))  := by gcongr; exact (P_pos S).le
    _ = _ := by ring

#print axioms scaled_mass
#print axioms scaled_tail
end Erdos490Smooth

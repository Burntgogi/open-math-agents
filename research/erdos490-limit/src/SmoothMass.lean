import Arithmetic
import Mathlib

open Filter Real MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos490Smooth
open Shift490

private theorem atom_eq_indicator {S : Finset ℕ} (n : Integers S) :
    (fun w => atom w n) = (Ici (logN n)).indicator (fun w => exp (-w)) := by
  funext w
  simp only [atom,Set.indicator_apply,Set.mem_Ici]

theorem atom_integrable_tail {S : Finset ℕ} (n : Integers S) (D : ℝ) :
    IntegrableOn (fun w => atom w n) (Ioi D) := by
  rw [atom_eq_indicator]
  exact (integrableOn_exp_neg_Ioi D).indicator measurableSet_Ici

theorem integral_atom_tail {S : Finset ℕ} (n : Integers S) (D : ℝ) :
    (∫ w in Ioi D, atom w n) = exp (-(max D (logN n))) := by
  rw [atom_eq_indicator, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, ← integral_exp_neg_Ioi (max D (logN n))]
  apply setIntegral_congr_set
  rw [← Set.Ioi_inter_Ioi]
  filter_upwards [Ioi_ae_eq_Ici (μ := (volume : Measure ℝ)) (a := logN n)] with w hw
  change (logN n ≤ w ∧ D < w) = (D < w ∧ logN n < w)
  change (logN n < w) = (logN n ≤ w) at hw
  rw [hw, and_comm]

private theorem tail_summable (S : Finset ℕ) (D : ℝ) :
    Summable (fun n : Integers S => exp (-(max D (logN n)))) := by
  refine Summable.of_nonneg_of_le (fun _ => (exp_pos _).le) (fun n => ?_) (harmonic_sum S).summable
  rw [exp_neg,inv_le_inv₀ (exp_pos _) (nat_pos n)]
  rw [← Real.log_le_iff_le_exp (nat_pos n)]
  exact le_max_right _ _

theorem kernel_tail_integral (S : Finset ℕ) (D : ℝ) :
    (∫ w in Ioi D, F S w) = ∑' n : Integers S, exp (-(max D (logN n))) := by
  unfold F
  rw [integral_tsum]
  · exact tsum_congr fun n => integral_atom_tail n D
  · exact fun n => (atom_integrable_tail n D).aestronglyMeasurable
  · have h (n : Integers S) :
        (∫⁻ w in Ioi D, ‖atom w n‖ₑ) = ENNReal.ofReal (exp (-(max D (logN n)))) := by
      simp_rw [Real.enorm_eq_ofReal (atom_nonneg _)]
      rw [← ofReal_integral_eq_lintegral_ofReal (atom_integrable_tail n D)
        (Eventually.of_forall fun _ => atom_nonneg n), integral_atom_tail]
    simp_rw [h]
    exact (tail_summable S D).tsum_ofReal_ne_top

theorem kernel_mass (S : Finset ℕ) : (∫ w in Ioi 0, F S w) = P S := by
  rw [kernel_tail_integral,← (harmonic_sum S).tsum_eq]
  apply tsum_congr
  intro n
  have hn : 1 ≤ ((n:ℕ):ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.property.1
  rw [max_eq_right (log_nonneg hn),exp_neg,exp_log (nat_pos n)]

#print axioms kernel_mass
end Erdos490Smooth

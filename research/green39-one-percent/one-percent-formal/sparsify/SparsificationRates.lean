import FourierSparsification
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt

/-!
# The sample cap and tolerance in Green 39, Section 5

The constants are those of the review: the cap is the floor of `0.001 k`,
and the tolerance is `exp (-1000 - 0.22 x)` as in `Constants.lean`.
Every level has `x ≤ log (p / k)`.
-/

open Filter

set_option autoImplicit false

namespace OnePercent.Fourier

noncomputable section

/-- The maximum number of centers kept from the fitted piece. -/
def sparsificationCap (k : ℕ) : ℕ := k / 1000

/-- Natural division gives the floor used for the sample cap in the review. -/
theorem sparsificationCap_eq_floor (k : ℕ) :
    sparsificationCap k = ⌊(0.001 : ℝ) * k⌋₊ := by
  rw [show (0.001 : ℝ) * k = (k : ℝ) / 1000 by ring]
  exact (Nat.floor_div_eq_div k 1000).symm

/-- The fitting tolerance at level `x`. -/
def sparsificationEta (x : ℝ) : ℝ := Real.exp (-1000 - 0.22 * x)

/-- The rate `k^0.56` is uniform over levels up to `log (2k)`. -/
theorem sparsification_scale_lower {k : ℕ} (hk : 2000 ≤ k) {x : ℝ}
    (hx : x ≤ Real.log (2 * (k : ℝ))) :
    Real.exp (-2000) / 4000 * (k : ℝ) ^ (0.56 : ℝ) ≤
      (sparsificationCap k : ℝ) * sparsificationEta x ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkcap : (k : ℝ) / 2000 ≤ (sparsificationCap k : ℝ) := by
    have h : k ≤ 2000 * (k / 1000) := by omega
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2000), mul_comm]
    exact_mod_cast h
  have htwo : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-0.44 : ℝ) := by
    calc
      (1 / 2 : ℝ) = (2 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_one, one_div]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have heta : Real.exp (-2000) * ((1 / 2 : ℝ) * (k : ℝ) ^ (-0.44 : ℝ)) ≤
      sparsificationEta x ^ 2 := by
    calc
      _ ≤ Real.exp (-2000) * ((2 : ℝ) ^ (-0.44 : ℝ) * (k : ℝ) ^ (-0.44 : ℝ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo (by positivity))
          (Real.exp_nonneg _)
      _ = Real.exp (-2000 - 0.44 * Real.log (2 * (k : ℝ))) := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hkpos.le,
          Real.rpow_def_of_pos (mul_pos (by norm_num) hkpos), ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((-1000 - 0.22 * x) + (-1000 - 0.22 * x)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [sparsificationEta, sq, Real.exp_add]
  calc
    _ = ((k : ℝ) / 2000) *
        (Real.exp (-2000) * ((1 / 2 : ℝ) * (k : ℝ) ^ (-0.44 : ℝ))) := by
      rw [show (0.56 : ℝ) = 1 + (-0.44) by norm_num, Real.rpow_add hkpos, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul hkcap heta (by positivity) (Nat.cast_nonneg _)

/-- For every fixed multiple of `log (4p)`, the sample scale eventually exceeds
that multiple uniformly in the level, when `p ≤ 2 k²`. -/
theorem sparsification_scale_eventually (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ k : ℕ in atTop, ∀ p : ℕ, 0 < p → (p : ℝ) ≤ 2 * (k : ℝ) ^ 2 →
      ∀ x : ℝ, x ≤ Real.log ((p : ℝ) / k) →
        M * Real.log (4 * (p : ℝ)) < (sparsificationCap k : ℝ) * sparsificationEta x ^ 2 := by
  let c := Real.exp (-2000) / 4000
  have hc : 0 < c := by dsimp [c]; positivity
  have hDen : 0 < 5 * (M + 1) := by linarith
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.56)).bound
    (div_pos hc hDen)
  have hnat := tendsto_natCast_atTop_atTop.eventually hsmall
  filter_upwards [eventually_ge_atTop (2000 : ℕ), hnat] with k hk hlog p hp hpUpper x hx
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  have hLogPos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
  have hLogp : Real.log (4 * (p : ℝ)) ≤ 5 * Real.log (k : ℝ) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    calc
      _ ≤ Real.log (8 * (k : ℝ) ^ 2) := Real.log_le_log (by positivity) (by linarith)
      _ = 3 * Real.log (2 : ℝ) + 2 * Real.log (k : ℝ) := by
        rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_mul (by norm_num)
          (pow_ne_zero _ hkpos.ne'), Real.log_pow, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hk2]
  have hxUpper : x ≤ Real.log (2 * (k : ℝ)) := by
    refine hx.trans (Real.log_le_log (div_pos (by exact_mod_cast hp) hkpos) ?_)
    rw [div_le_iff₀ hkpos]
    nlinarith only [hpUpper]
  change ‖Real.log (k : ℝ)‖ ≤ c / (5 * (M + 1)) * ‖(k : ℝ) ^ (0.56 : ℝ)‖ at hlog
  rw [Real.norm_of_nonneg hLogPos.le, Real.norm_of_nonneg (by positivity),
    div_mul_eq_mul_div, le_div_iff₀ hDen] at hlog
  calc
    _ ≤ M * (5 * Real.log (k : ℝ)) := mul_le_mul_of_nonneg_left hLogp hM
    _ < Real.log (k : ℝ) * (5 * (M + 1)) := by nlinarith only [hLogPos]
    _ ≤ c * (k : ℝ) ^ (0.56 : ℝ) := hlog
    _ ≤ _ := sparsification_scale_lower hk hxUpper

/-- In the paper, `k = ⌊√p⌋`. The scale dominates every fixed multiple of the
logarithm as `p → ∞`, uniformly over all levels. -/
theorem sparsification_scale_eventually_sqrt (M : ℝ) (hM : 0 ≤ M) :
    ∀ᶠ p : ℕ in atTop, ∀ x : ℝ, x ≤ Real.log ((p : ℝ) / p.sqrt) →
      M * Real.log (4 * (p : ℝ)) <
        (sparsificationCap p.sqrt : ℝ) * sparsificationEta x ^ 2 := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp (sparsification_scale_eventually M hM)
  have hthreshold : ∀ᶠ p : ℕ in atTop, (max K 3) ^ 2 ≤ p := eventually_ge_atTop _
  filter_upwards [hthreshold] with p hp x hx
  have hsqrt := Nat.le_sqrt'.mpr hp
  have h3 : 3 ≤ p.sqrt := (le_max_right K 3).trans hsqrt
  have hp2 : p ≤ 2 * p.sqrt ^ 2 := by
    have hnext := Nat.lt_succ_sqrt' p
    rw [Nat.succ_eq_add_one] at hnext
    nlinarith [Nat.mul_le_mul_left p.sqrt h3]
  have hpPos : 0 < p := Nat.sqrt_pos.mp (by omega)
  exact hK p.sqrt ((le_max_left K 3).trans hsqrt) p hpPos (by exact_mod_cast hp2) x hx

/-- Equation (5) holds uniformly over all active levels for sufficiently large
moduli, with the paper's cap and tolerance. -/
theorem exists_fourierFit_sparsify_eventually :
    ∀ᶠ p : ℕ in atTop, ∀ [NeZero p], ∀ x : ℝ, x ≤ Real.log ((p : ℝ) / p.sqrt) →
      ∀ (F : Finset (ZMod p)) (μ : ZMod p → ℝ),
        FourierFit F μ (5 * sparsificationEta x * F.card) →
        ∃ S ⊆ F, S.card = min F.card (sparsificationCap p.sqrt) ∧
          FourierFit S μ (7 * sparsificationEta x * S.card) := by
  filter_upwards [sparsification_scale_eventually_sqrt 8 (by norm_num)] with p hp
  intro _ x hx F μ hfit
  exact exists_fourierFit_sparsify F μ _ (Real.exp_nonneg _) hfit (fun _ _ ↦ hp x hx)

end

end OnePercent.Fourier

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

noncomputable section
namespace Shift490
open MeasureTheory Real Finset

/-- The finite product can be the characteristic function of any independent selected
cells. Frequencies use exp(i t x), so a Plancherel conversion may carry a constant. -/
theorem spectral_energy {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℂ) (K : ℝ → ℂ)
    {c A : ℝ} (hc : 0 < c) (hm : 0 < s.card) (hk : ∀ t, ‖K t‖ ≤ A)
    (low : ∀ i ∈ s, ∀ t : ℝ, |t| ≤ 1 → ‖φ i t‖ ≤ exp (-c*t^2))
    (mid : ∀ i ∈ s, ∀ t : ℝ, 1 < |t| → |t| ≤ (s.card:ℝ)^2 → ‖φ i t‖ ≤ exp (-c))
    (unit : ∀ i ∈ s, ∀ t, ‖φ i t‖ ≤ 1)
    (hφ : ∀ i ∈ s, Continuous (φ i)) (hK : Continuous K)
    (I₂ : Integrable (fun t : ℝ => t^2 * ‖K t‖^2))
    (I₃ : Integrable (fun t : ℝ => |t| * (t^2 * ‖K t‖^2))) :
    let m : ℝ := s.card
    (∫ t : ℝ, t^2 * ‖K t‖^2 * ‖∏ i ∈ s, φ i t‖^2) ≤
      A^2 / (c*m) * √(π/(c*m)) +
      (c*m)⁻¹^2 * (∫ t : ℝ, t^2 * ‖K t‖^2) +
      (m^2)⁻¹ * (∫ t : ℝ, |t| * (t^2 * ‖K t‖^2)) := by
  let m : ℝ := s.card
  have hm' : 0 < m := by dsimp [m]; exact_mod_cast hm
  let b := c*m
  have hb : 0 < b := mul_pos hc hm'
  let W (t : ℝ) := t^2 * ‖K t‖^2
  let U (t : ℝ) := A^2/b * exp (-b*t^2)
  let V (t : ℝ) := b⁻¹^2 * W t
  let Z (t : ℝ) := (m^2)⁻¹ * (|t| * W t)
  let E (t : ℝ) := W t * ‖∏ i ∈ s, φ i t‖^2
  have major (t : ℝ) : E t ≤ U t + V t + Z t := by
    have hW : 0 ≤ W t := by dsimp [W]; positivity
    have hu : 0 ≤ U t := by dsimp [U]; positivity
    have hv : 0 ≤ V t := by dsimp [V]; positivity
    have hz : 0 ≤ Z t := by dsimp [Z]; positivity
    have prod_bound (r : ℝ) (h : ∀ i ∈ s, ‖φ i t‖ ≤ exp r) :
        ‖∏ i ∈ s, φ i t‖ ≤ exp (m*r) := by
      rw [norm_prod, show exp (m*r) = (exp r)^s.card from Real.exp_nat_mul r s.card]
      simpa using prod_le_prod (fun i _ => norm_nonneg (φ i t)) h
    by_cases h1 : |t| ≤ 1
    · have hh := prod_bound _ (fun i hi => low i hi t h1)
      rw [show m*(-c*t^2) = -(b*t^2) by dsimp [b]; ring, exp_neg] at hh
      have hx : b*t^2 ≤ exp (b*t^2) := (lt_add_one _).le.trans (Real.add_one_le_exp _)
      have hki := pow_le_pow_left₀ (norm_nonneg _) (hk t) 2
      have hE : E t ≤ U t := by
        calc
          E t ≤ t^2 * A^2 * ((exp (b*t^2))⁻¹)^2 := by
            dsimp [E,W]; gcongr
          _ ≤ U t := by
            dsimp [U]
            rw [neg_mul, exp_neg]
            field_simp
            rw [mul_comm b] at hx
            nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg A)]
      linarith
    · by_cases h2 : |t| ≤ m^2
      · have hh := prod_bound _ (fun i hi => mid i hi t (lt_of_not_ge h1) h2)
        rw [show m*(-c) = -b by dsimp [b]; ring, exp_neg] at hh
        have hi := (inv_le_inv₀ (exp_pos b) hb).mpr
          ((lt_add_one b).le.trans (Real.add_one_le_exp b))
        have hE : E t ≤ V t := by
          dsimp [E,V]
          rw [mul_comm (b⁻¹^2)]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hh.trans hi) 2) hW
        linarith
      · have hh := prod_bound 0 (by simpa using fun i hi => unit i hi t)
        simp only [mul_zero, exp_zero] at hh
        have hE : E t ≤ W t := by
          simpa [E] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) hW
        have hZ : W t ≤ Z t := by
          dsimp [Z]
          rw [← mul_assoc]
          calc
            _ = 1 * W t := (one_mul _).symm
            _ ≤ _ := mul_le_mul_of_nonneg_right (by rw [inv_mul_eq_div]; exact (one_le_div (by positivity)).mpr (le_of_not_ge h2)) hW
        linarith
  have iu : Integrable U := (integrable_exp_neg_mul_sq hb).const_mul _
  have iv : Integrable V := I₂.const_mul _
  have iz : Integrable Z := I₃.const_mul _
  have iM := (iu.add iv).add iz
  have ce : Continuous E := by
    dsimp [E,W]
    fun_prop (disch := assumption)
  have ie : Integrable E := iM.mono' ce.aestronglyMeasurable (ae_of_all _ fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [E,W]; positivity)]
    exact major t)
  change (∫ t, E t) ≤ _
  calc
    _ ≤ ∫ t, (U t + V t + Z t) := integral_mono ie iM major
    _ = _ := by
      have iuv : Integrable (fun t => U t + V t) := iu.add iv
      rw [integral_add iuv iz, integral_add iu iv]
      simp only [U,V,Z,W,integral_const_mul,integral_gaussian,b,m]

#print axioms spectral_energy
end Shift490

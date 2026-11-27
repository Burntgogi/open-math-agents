import Assembly
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
namespace Shift490
open Real Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- A smooth, compact probability density and its translated test-integral formula. -/
theorem compact_bump {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Measure ℝ) (g : 𝓢(ℝ,ℂ)), IsProbabilityMeasure κ ∧
      (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧ (∀ u, u ∉ Set.Icc 0 δ → g u = 0) ∧
      ∀ (f : ℝ → ℝ) s z, testAt κ f s z =
        ∫ v : ℝ, f (-v) * (g (v-(z-s))).re := by
  let b : ContDiffBump (δ/2) := ⟨δ/4,δ/2,by positivity,by linarith⟩
  let v := b.normed (volume : Measure ℝ)
  have hn (x) : 0 ≤ v x := b.nonneg_normed _
  have hv : Continuous v := b.continuous_normed
  let ρ (x : ℝ) := ENNReal.ofReal (v x)
  let κ := volume.withDensity ρ
  have hρ : Measurable ρ := hv.measurable.ennreal_ofReal
  have hκ : IsProbabilityMeasure κ := by
    constructor
    change volume.withDensity ρ Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    rw [show (∫⁻ x, ρ x) = ENNReal.ofReal (∫ x, v x) from
      (ofReal_integral_eq_lintegral_ofReal b.integrable_normed (ae_of_all _ hn)).symm,
      b.integral_normed,ENNReal.ofReal_one]
  have supp (x : ℝ) (hx : v x ≠ 0) : x ∈ Set.Icc 0 δ := by
    have hh : x ∈ Function.support v := hx
    rw [show Function.support v = Metric.ball (δ/2) (δ/2) from b.support_normed_eq] at hh
    rw [Metric.mem_ball,Real.dist_eq,abs_lt] at hh
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hsup : HasCompactSupport (fun x => (v x : ℂ)) := HasCompactSupport.comp_left (b.hasCompactSupport_normed (μ := volume)) Complex.ofReal_zero
  let g : 𝓢(ℝ,ℂ) := hsup.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (b.contDiff_normed (μ := volume)))
  refine ⟨κ,g,hκ,(ae_withDensity_iff hρ).mpr (ae_of_all _ fun u hu => supp u (fun hz => hu (by simp [ρ,hz]))),
    fun u hu => ?_,?_⟩
  · change ((v u:ℝ):ℂ) = 0
    exact_mod_cast not_ne_iff.mp (fun h => hu (supp u h))
  · intro f s z
    rw [testAt,integral_withDensity_eq_integral_toReal_smul hρ
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    change (∫ u, (ENNReal.ofReal (v u)).toReal • f (s-z-u)) = _
    simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
    rw [← integral_sub_right_eq_self (fun u => v u * f (s-z-u)) (z-s)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by change v _ * f _ = f _ * v _; rw [mul_comm]; congr 2; ring

/-- Pulling a Schwartz transform back to angular frequency preserves the two required
weighted integrability estimates. -/
theorem angular_weights (g : 𝓢(ℝ,ℂ)) {d : ℝ} (hd : d ≠ 0) :
    let K := fun t : ℝ => g (d*t)
    ∃ A : ℝ, Continuous K ∧ (∀ t, ‖K t‖ ≤ A) ∧
      Integrable (fun t : ℝ => t^2 * ‖K t‖^2) ∧
      Integrable (fun t : ℝ => |t| * (t^2 * ‖K t‖^2)) := by
  let A := SchwartzMap.seminorm ℝ 0 0 g
  have hb (x) : ‖g x‖ ≤ A := g.norm_le_seminorm ℝ _
  have hm (k : ℕ) : Integrable (fun t : ℝ => |t|^k * ‖g (d*t)‖^2) := by
    have h := (integrable_comp_mul_left_iff (fun x : ℝ => ‖x‖^k * ‖g x‖) hd).mpr
      (g.integrable_pow_mul volume k)
    have hdom := h.const_mul (A / |d|^k)
    refine hdom.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,abs_mul,mul_pow]
    have hfac : A / |d|^k * (|d|^k * |t|^k * ‖g (d*t)‖) = |t|^k * (A * ‖g (d*t)‖) := by
      field_simp [abs_ne_zero.mpr hd]
    rw [hfac,pow_two]
    gcongr
    exact hb _
  refine ⟨A,g.continuous.comp (continuous_const.mul continuous_id),fun _ => hb _,?_,?_⟩
  · simpa only [sq_abs] using hm 2
  · exact (hm 3).congr (ae_of_all _ fun t => by dsimp; rw [pow_succ,sq_abs]; ring)

end Shift490

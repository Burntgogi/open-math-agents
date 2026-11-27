import BumpKernel
import Grid

noncomputable section
namespace Shift490
open Real Filter Finset MeasureTheory
open scoped FourierTransform SchwartzMap Topology

def density {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s : ℝ) : 𝓢(ℝ,ℂ) :=
  ∑ y ∈ S, (w y:ℂ) • g.compSubConstCLM ℂ (z y-s)

lemma density_apply {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s x : ℝ) :
    density g S w z s x = ∑ y ∈ S, (w y:ℂ) * g (x-(z y-s)) := by
  simp [density,SchwartzMap.compSubConstCLM_apply]

private lemma ft_formula (g : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    𝓕 g ξ = ∫ x, phase (-2*π*ξ) x * g x := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq']
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp [phase,smul_eq_mul,mul_comm,mul_assoc,mul_left_comm]

private lemma ft_translate (g : 𝓢(ℝ,ℂ)) (a ξ : ℝ) :
    𝓕 (g.compSubConstCLM ℂ a) ξ = phase (-2*π*ξ) a * 𝓕 g ξ := by
  rw [ft_formula,ft_formula,← integral_const_mul]
  let t := -2*π*ξ
  change (∫ x, phase t x * g (x-a)) = ∫ x, phase t a * (phase t x * g x)
  rw [← integral_add_right_eq_self (fun x => phase t x * g (x-a)) a]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by dsimp only; rw [phase_add,add_sub_cancel_right]; ring

private lemma ft_density {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s ξ : ℝ) :
    𝓕 (density g S w z s) ξ =
      (∑ y ∈ S, (w y:ℂ)*phase (-2*π*ξ) (z y)) * 𝓕 g ξ * phase (-2*π*ξ) (-s) := by
  change (SchwartzMap.fourierTransformCLM ℂ (density g S w z s)) ξ = _
  simp only [density,map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    SchwartzMap.fourierTransformCLM_apply,ft_translate,smul_eq_mul,sum_mul]
  apply sum_congr rfl
  intro y _
  rw [sub_eq_add_neg,phase_add]; ring

private lemma phase_change (t s r : ℝ) : ‖phase t s-phase t r‖ ≤ 2*|t| * |s-r| := by
  have he : phase t s-phase t r = phase t r * (phase t (s-r)-1) := by
    rw [mul_sub,mul_one,← phase_add,add_sub_cancel]
  rw [he,norm_mul,norm_phase,one_mul]
  by_cases h : |t*(s-r)| ≤ 1
  · have heq : ‖((t*(s-r):ℝ):ℂ)*Complex.I‖ = |t*(s-r)| := by rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have hh := Complex.norm_exp_sub_one_le (x := ((t*(s-r):ℝ):ℂ)*Complex.I) (heq ▸ h)
    rw [heq,abs_mul] at hh
    simpa only [phase,mul_assoc] using hh
  · refine (norm_sub_le ..).trans ?_
    rw [norm_one,norm_phase]
    rw [abs_mul] at h
    linarith

lemma schwartz_sq (g : 𝓢(ℝ,ℂ)) : Integrable (fun x => ‖g x‖^2) := by
  apply (g.integrable.norm.const_mul (SchwartzMap.seminorm ℝ 0 0 g)).mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),pow_two]
  exact mul_le_mul_of_nonneg_right (g.norm_le_seminorm ℝ _) (norm_nonneg _)

theorem density_energy {Ω : Type} (g : 𝓢(ℝ,ℂ)) (S : Finset Ω) (w z : Ω → ℝ) (s r : ℝ) :
    let k := -2*π
    let E (t : ℝ) := t^2 * ‖𝓕 g (k⁻¹*t)‖^2 * ‖∑ y ∈ S, (w y:ℂ)*phase t (z y)‖^2
    (∫ x : ℝ, ‖(density g S w z s - density g S w z r) x‖^2) ≤
      (2*|s-r|)^2 * |k⁻¹| * ∫ t, E t := by
  intro k E
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let d := density g S w z s - density g S w z r
  have hFT (ξ : ℝ) : 𝓕 d ξ = (∑ y ∈ S, (w y:ℂ)*phase (k*ξ) (z y)) * 𝓕 g ξ *
      (phase (k*ξ) (-s) - phase (k*ξ) (-r)) := by
    change (SchwartzMap.fourierTransformCLM ℂ (density g S w z s - density g S w z r)) ξ = _
    rw [map_sub,_root_.sub_apply,SchwartzMap.fourierTransformCLM_apply,SchwartzMap.fourierTransformCLM_apply,
      ft_density,ft_density,mul_sub]
  have point (ξ : ℝ) : ‖𝓕 d ξ‖^2 ≤ (2*|s-r|)^2 * E (k*ξ) := by
    rw [hFT,norm_mul,norm_mul,mul_pow]
    have hh := phase_change (k*ξ) (-s) (-r)
    rw [show -s- -r = -(s-r) by ring,abs_neg] at hh
    dsimp [E]
    rw [← mul_assoc k⁻¹,inv_mul_cancel₀ hk,one_mul]
    calc
      _ ≤ _ * (2*|k*ξ| * |s-r|)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh 2) (sq_nonneg _)
      _ = _ := by simp only [mul_pow,sq_abs]; ring
  have iE : Integrable E := by
    obtain ⟨_,_,_,hi,_⟩ := angular_weights (𝓕 g) (inv_ne_zero hk)
    let N := ∑ y ∈ S, |w y|
    apply (hi.mul_const (N^2)).mono' (by dsimp [E,phase]; fun_prop)
    apply ae_of_all
    intro t
    dsimp [E]
    rw [abs_of_nonneg (by positivity)]
    gcongr
    refine (norm_sum_le ..).trans (sum_le_sum fun y _ => ?_)
    rw [norm_mul,norm_phase,mul_one,Complex.norm_real,Real.norm_eq_abs]
  rw [← SchwartzMap.integral_norm_sq_fourier d]
  have hi := (integrable_comp_mul_left_iff E hk).mpr iE
  calc
    _ ≤ ∫ ξ : ℝ, (2*|s-r|)^2 * E (k*ξ) := integral_mono (schwartz_sq (𝓕 d)) (hi.const_mul _) point
    _ = _ := by rw [integral_const_mul,Measure.integral_comp_mul_left,smul_eq_mul,mul_assoc]

#print axioms density_energy
end Shift490

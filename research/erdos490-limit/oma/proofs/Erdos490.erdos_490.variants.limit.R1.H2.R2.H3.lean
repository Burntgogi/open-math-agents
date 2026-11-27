import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1_H2_R2
import Mathlib

/-! Stable sample recovery from the effective θ estimate. The source combines the cofactor, log-prime cell, weighted-word, and two-color realization proofs from the local E490 development. -/

/- Mertens estimates -/
section
/-
# Mertens estimates used in Erdős problem 490

Adapted from `PrimeNumberTheoremAnd/IEANTN/Mertens.lean` by the
PrimeNumberTheoremAnd contributors, Apache License 2.0.
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/650d31264be65f4cd6e70c45d8b25d86d482a761/PrimeNumberTheoremAnd/IEANTN/Mertens.lean
See the accompanying `LICENSE` for the full license.

The upstream file credits Leo Goldmakher's “A quick proof of Mertens' theorem”.
This adaptation selects the declarations used by E490, drops blueprint
directives and proves measurability explicitly for the sums over `⌊x⌋₊`.
-/
namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

end Real

section Issue1584

open MeasureTheory Set Filter Topology

private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Ici 1)
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Ioi x) x for x ∈ Ioi 1
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Ici 1
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Ioi 1) = ContinuousOn g (Ioi 0)
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Ici 1) = IntegrableOn g (Ici 0)
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Ici 1) x for x ∈ Ici 1.
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Ici 1.
    have hinj : InjOn f (Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

namespace Mertens

open Real Finset Filter Asymptotics Topology

open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)

lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero, ge_iff_le,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring

theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert! summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrableOn_Ioi_zero integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]

theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private lemma measurable_floor_sum (f : ℕ → ℝ) :
    Measurable (fun t : ℝ => ∑ n ∈ Ioc 0 ⌊t⌋₊, f n) :=
  (measurable_of_countable (fun k : ℕ => ∑ n ∈ Ioc 0 k, f n)).comp Nat.measurable_floor

private lemma measurable_E₂Λ : Measurable E₂Λ :=
  ((measurable_floor_sum (fun d => (Λ d) / (d * log d))).sub
    (Real.measurable_log.comp Real.measurable_log)).sub measurable_const

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact (((measurable_floor_sum (fun d => (Λ d) / d)).sub Real.measurable_log).div
      (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · have hE : Measurable E₁p := by
      unfold E₁p
      simp only [Finset.sum_filter]
      exact (measurable_floor_sum (fun p => if p.Prime then log p / p else 0)).sub
        Real.measurable_log
    exact (hE.div (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert! MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert! HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_ofPred_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section

open MeasureTheory Set

namespace LogZetaInteg

private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]

@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg

end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) measurable_E₂Λ ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

section

open MeasureTheory Set

private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

end Mertens
end

open Filter in
def EffectivePrimeEstimate : Prop := ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 3

/- Cofactor -/
section
namespace Erdos490Transfer

open Finset

noncomputable section

open Classical

abbrev Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C

def semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (Active C)

lemma mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
  simp only [semigroup, mem_filter, mem_Icc]
  exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩

def primes (Y n : ℕ) := (Icc Y n).filter Nat.Prime

structure Colors (Y n : ℕ) where
  red : Finset ℕ
  blue : Finset ℕ
  cover : red ∪ blue = primes Y n
  separate : Disjoint red blue

lemma coprime_active {C D : Finset ℕ} {a b : ℕ} (hd : Disjoint C D)
    (ha : Active C a) (hb : Active D b) : a.Coprime b :=
  Nat.coprime_of_dvd fun p hp hx hy => disjoint_left.mp hd
    (Nat.mem_factoredNumbers'.mp ha p hp hx) (Nat.mem_factoredNumbers'.mp hb p hp hy)

lemma recover {a b c d : ℕ} (had : a.Coprime d) (hcb : c.Coprime b)
    (h : a*b=c*d) : a=c :=
  Nat.dvd_antisymm (had.dvd_of_dvd_mul_right (h ▸ dvd_mul_right a b))
    (hcb.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right c d))

end

end Erdos490Transfer
end


/- H2 -/
section
namespace Erdos490Transfer

open Finset Filter

noncomputable section

open Classical

def density (C : Finset ℕ) (n u : ℕ) : ℝ :=
  ((semigroup C (n/u)).card : ℝ)*u/n

end

end Erdos490Transfer
end


/- Harmonic -/
section
namespace Erdos490Transfer.Harmonic

open Finset Filter

noncomputable section

private noncomputable def smooth (n : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → P p)

private lemma mem_smooth {n m : ℕ} {P : ℕ → Prop} :
    m ∈ smooth n P ↔ (1 ≤ m ∧ m ≤ n) ∧ ∀ p, Nat.Prime p → p ∣ m → P p := by
  classical
  simp [smooth]

private noncomputable def mass (s : Finset ℕ) := ∑ m ∈ s, (m : ℝ)⁻¹

private lemma transport {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b)
    (hm : ∀ a ∈ s, f a ∈ t) (hi : Set.InjOn f s) :
    ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
  classical
  rw [← sum_image hi]
  apply sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hm)
  exact fun b _ _ => hg b

private lemma log_sum (n : ℕ) (P : ℕ → Prop) :
    ∑ m ∈ smooth n P, Real.log m ≤
      ((Real.log 4 + 4) * n) * mass (smooth n P) := by
  classical
  let s := smooth n P
  let U := s.sigma (fun m => m.divisors)
  let V := s.sigma (fun v => Ioc 0 ⌊(n : ℝ) / v⌋₊)
  let f (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨x.1 / x.2, x.2⟩
  have data {x : Σ _ : ℕ, ℕ} (hx : x ∈ U) :
      x.1 ∈ s ∧ x.2 ∣ x.1 ∧ 0 < x.2 ∧ 0 < x.1 / x.2 := by
    obtain ⟨hm,hd⟩ := mem_sigma.mp hx
    have h0 := Nat.pos_of_mem_divisors hd
    exact ⟨hm, Nat.dvd_of_mem_divisors hd, h0,
      Nat.div_pos (Nat.le_of_dvd (mem_smooth.mp hm).1.1 (Nat.dvd_of_mem_divisors hd)) h0⟩
  have hm : ∀ x ∈ U, f x ∈ V := by
    intro x hx
    obtain ⟨hs,hd,hp,hq⟩ := data hx
    obtain ⟨⟨_,hle⟩,hall⟩ := mem_smooth.mp hs
    refine mem_sigma.mpr ⟨mem_smooth.mpr ⟨⟨hq, (Nat.div_le_self ..).trans hle⟩,
      fun p hpr hdv => hall p hpr (hdv.trans (Nat.div_dvd_of_dvd hd))⟩, ?_⟩
    refine mem_Ioc.mpr ⟨hp, Nat.le_floor ((le_div_iff₀ (by exact_mod_cast hq)).mpr ?_)⟩
    exact_mod_cast (show x.2 * (x.1 / x.2) ≤ n by rwa [Nat.mul_div_cancel' hd])
  have hi : Set.InjOn f U := by
    intro x hx y hy h
    have he := congrArg (fun z : Σ _ : ℕ, ℕ => z.1 * z.2) h
    change x.1 / x.2 * x.2 = y.1 / y.2 * y.2 at he
    rw [Nat.div_mul_cancel (data hx).2.1, Nat.div_mul_cancel (data hy).2.1] at he
    have he' := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
    exact Sigma.ext he (heq_of_eq he')
  calc
    _ = ∑ x ∈ U, ArithmeticFunction.vonMangoldt (f x).2 := by
      simp [U, s, sum_sigma, f, ArithmeticFunction.vonMangoldt_sum]
    _ ≤ ∑ y ∈ V, ArithmeticFunction.vonMangoldt y.2 :=
      transport U V f _ (fun _ => ArithmeticFunction.vonMangoldt_nonneg) hm hi
    _ = ∑ v ∈ s, Chebyshev.psi ((n : ℝ) / v) := by rw [Finset.sum_sigma]; rfl
    _ ≤ ∑ v ∈ s, (Real.log 4 + 4) * ((n : ℝ) / v) :=
      sum_le_sum fun v _ => Chebyshev.psi_le_const_mul_self (by positivity)
    _ = _ := by simp [s, mass, mul_sum, div_eq_mul_inv, mul_assoc]

private lemma count (n : ℕ) (P : ℕ → Prop) :
    ((smooth n P).card : ℝ) * Real.log n ≤
      ((Real.log 4 + 5) * n) * mass (smooth n P) := by
  let s := smooth n P
  have h : ∀ m ∈ s, Real.log n ≤ Real.log m + (n : ℝ) * (m : ℝ)⁻¹ := by
    intro m hm
    obtain ⟨⟨ha,hb⟩,_⟩ := mem_smooth.mp hm
    have hm' : 0 < (m : ℝ) := by exact_mod_cast ha
    have hn' : 0 < (n : ℝ) := by exact_mod_cast ha.trans hb
    have := Real.log_le_sub_one_of_pos (div_pos hn' hm')
    rw [Real.log_div hn'.ne' hm'.ne', div_eq_mul_inv] at this
    linarith
  have hh := sum_le_sum h
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at hh
  change (s.card : ℝ) * Real.log n ≤ (∑ m ∈ s, Real.log m) + n * mass s at hh
  linarith only [hh, log_sum n P]

def scale (C : Finset ℕ) (n : ℕ) : ℝ := mass (semigroup C n) / Real.log n

private lemma smooth_eq (C : Finset ℕ) (n) :
    smooth n (· ∈ C) = semigroup C n := by
  ext h
  simp only [mem_smooth,semigroup,mem_filter,mem_Icc,Active,Nat.mem_factoredNumbers']

theorem count_le {n : ℕ} (hn : 0 < Real.log n) (C) :
    ((semigroup C n).card:ℝ)/(n:ℝ) ≤ (Real.log 4+5)*scale C n := by
  have h := count n (· ∈ C)
  rw [smooth_eq] at h
  have hn' : 0 < (n:ℝ) := by
    by_contra! he
    have : n = 0 := by exact_mod_cast le_antisymm he (Nat.cast_nonneg _)
    simp [this] at hn
  unfold scale
  field_simp [hn.ne',hn'.ne']
  nlinarith only [h]

end

end Erdos490Transfer.Harmonic
end


/- PrimeColorTransfer -/
section
namespace Erdos490Transfer

open Filter Finset

noncomputable section

def envelope (K : ℕ) : ℝ := (Real.log 4+5)*(K:ℝ)

lemma density_le_scale {n K u : ℕ} (hn : 0 < Real.log n) (hu : u ≤ K) (C) :
    density C n u ≤ envelope K * Harmonic.scale C n := by
  have hcard : (semigroup C (n/u)).card ≤ (semigroup C n).card :=
    card_le_card fun h hh => mem_semigroup.mpr ⟨(mem_semigroup.mp hh).1,
      (mem_semigroup.mp hh).2.trans (Nat.div_le_self ..)⟩
  calc
    _ = ((semigroup C (n/u)).card : ℝ)/n*u := by unfold density; ring
    _ ≤ ((semigroup C n).card : ℝ)/n * K := by gcongr
    _ ≤ ((Real.log 4+5)*Harmonic.scale C n) * K := by gcongr; exact Harmonic.count_le hn C
    _ = _ := by unfold envelope; ring

end

end Erdos490Transfer
end


/- EulerScale -/
section
namespace Erdos490Transfer

open Finset Filter

noncomputable section

open Classical

def euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹

def truncMass (C : Finset ℕ) (n : ℕ) : ℝ := ∑ h ∈ semigroup C n, (h:ℝ)⁻¹

lemma euler_pos {C : Finset ℕ} (hC : ∀ p ∈ C, Nat.Prime p) : 0 < euler C := by
  apply prod_pos
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (hC p hp).one_lt
  exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ h))

lemma truncMass_le_euler {C : Finset ℕ} (hC : ∀ p ∈ C, Nat.Prime p) (n : ℕ) :
    truncMass C n ≤ euler C := by
  let f : ℕ →* ℝ := { toFun := fun t => (t:ℝ)⁻¹, map_one' := by simp, map_mul' := by simp [mul_comm] }
  have h (p : ℕ) (hp : p.Prime) : ‖f p‖ < 1 := by
    change ‖(p:ℝ)⁻¹‖ < 1
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have he := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f:=f) (fun {p} hp => h p hp) C).2
  rw [filter_true_of_mem hC] at he
  let s := semigroup C n
  let g (x : {h // h ∈ s}) : Nat.factoredNumbers C := ⟨x.1,(mem_semigroup.mp x.2).1⟩
  have hi : Function.Injective g := fun _ _ e => Subtype.ext (congrArg (fun t : Nat.factoredNumbers C => (t:ℕ)) e)
  have hs := sum_le_hasSum (s.attach.image g) (fun (x : Nat.factoredNumbers C) _ =>
    show 0 ≤ f x.val by dsimp [f]; positivity) he
  rw [sum_image (fun _ _ _ _ => @hi _ _)] at hs
  change (∑ x ∈ s.attach, ((x.val:ℕ):ℝ)⁻¹) ≤ euler C at hs
  rw [sum_attach s (fun x : ℕ => (x:ℝ)⁻¹)] at hs
  exact hs

end

end Erdos490Transfer
end


/- EulerTransfer -/
section
namespace Erdos490Transfer

open Finset Filter

noncomputable section

def eulerScale (C : Finset ℕ) (n : ℕ) := euler C / Real.log n

end

end Erdos490Transfer
end


/- Arithmetic -/
section
noncomputable section

namespace Shift490

open Finset Filter

abbrev Integers := Nat.factoredNumbers

def P (S : Finset ℕ) : ℝ := ∏ p ∈ S with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹

theorem P_pos (S : Finset ℕ) : 0 < P S := by
  apply prod_pos
  intro p hp
  have h : 1 < (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  exact inv_pos.mpr (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))

def reciprocal : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' := by simp [mul_comm]

theorem harmonic_sum (S : Finset ℕ) :
    HasSum (fun n : Integers S => ((n : ℕ) : ℝ)⁻¹) (P S) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocal) ?_ S).2
  intro p hp
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  exact (inv_lt_one₀ (by positivity)).mpr h

def harmonic (S : Finset ℕ) (n : Integers S) := ((n : ℕ) : ℝ)⁻¹ / P S

theorem harmonic_probability (S : Finset ℕ) : HasSum (harmonic S) 1 := by
  unfold harmonic
  simpa only [div_self (P_pos S).ne'] using (harmonic_sum S).div_const (P S)

abbrev logN {S : Finset ℕ} (n : Integers S) := Real.log (n : ℕ)

def atom {S : Finset ℕ} (w : ℝ) (n : Integers S) : ℝ :=
  if logN n ≤ w then Real.exp (-w) else 0

def F (S : Finset ℕ) (w : ℝ) : ℝ := ∑' n : Integers S, atom w n

lemma nat_pos {S} (n : Integers S) : 0 < ((n : ℕ) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero n.property.1

lemma atom_nonneg {S w} (n : Integers S) : 0 ≤ atom w n := by
  unfold atom
  split <;> positivity

lemma atom_le {S w} (n : Integers S) : atom w n ≤ ((n : ℕ) : ℝ)⁻¹ := by
  unfold atom logN
  split_ifs with h
  · rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) (nat_pos n)]
    exact (Real.log_le_iff_le_exp (nat_pos n)).mp h
  · positivity

lemma summable_atom (S w) : Summable (@atom S w) :=
  Summable.of_nonneg_of_le atom_nonneg atom_le (harmonic_sum S).summable

def countSet (S : Finset ℕ) (w : ℝ) :=
  (range (⌊Real.exp w⌋₊ + 1)).filter (· ∈ Integers S)

theorem F_eq_card (S w) : F S w = Real.exp (-w) * (countSet S w).card := by
  classical
  let t := (countSet S w).subtype (· ∈ Integers S)
  have ht (n : Integers S) : n ∈ t ↔ logN n ≤ w := by
    simp [t, countSet, logN, Nat.le_floor_iff (Real.exp_pos w).le,
      Real.log_le_iff_le_exp (nat_pos n), n.property]
  rw [F, tsum_eq_sum (s := t) (fun n hn => by simp [atom, mt (ht n).mpr hn])]
  calc
    _ = ∑ _n ∈ t, Real.exp (-w) := sum_congr rfl fun n hn => if_pos ((ht n).mp hn)
    _ = _ := by
      have he : t.card = (countSet S w).card := by
        simp [t, Finset.card_subtype, Finset.filter_eq_self.mpr
          (show ∀ n ∈ countSet S w, n ∈ Integers S from fun n hn => (mem_filter.mp hn).2)]
      simp [he, mul_comm]

def multiply {A B : Finset ℕ} (x : Integers A × Integers B) : Integers (A ∪ B) :=
  ⟨x.1.val * x.2.val, Nat.mul_mem_factoredNumbers
    (Nat.factoredNumbers_mono subset_union_left x.1.property)
    (Nat.factoredNumbers_mono subset_union_right x.2.property)⟩

theorem multiply_bijective {A B : Finset ℕ} (hd : Disjoint A B) :
    Function.Bijective (@multiply A B) := by
  have cop (a : Integers A) (b : Integers B) : a.val.Coprime b.val :=
    Nat.coprime_of_dvd fun p hp ha hb => Finset.disjoint_left.mp hd
      (Nat.mem_factoredNumbers'.mp a.property p hp ha)
      (Nat.mem_factoredNumbers'.mp b.property p hp hb)
  constructor
  · rintro ⟨a,b⟩ ⟨c,d⟩ h
    have he : a.val * b.val = c.val * d.val := congrArg Subtype.val h
    have hac := (cop a d).dvd_of_dvd_mul_right (he ▸ dvd_mul_right a.val b.val)
    have hca := (cop c b).dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right c.val d.val)
    have h1 := Nat.dvd_antisymm hac hca
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero c.property.1) (h1 ▸ he)
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  · intro n
    let l := n.val.primeFactorsList
    have part := List.Perm.prod_eq (List.filter_append_perm (fun p => decide (p ∈ A)) l)
    rw [List.prod_append, Nat.prod_primeFactorsList n.property.1] at part
    have other : l.filter (fun x => !decide (x ∈ A)) = l.filter (· ∈ B) := by
      apply List.filter_congr
      intro p hp
      have := mem_union.mp (n.property.2 p hp)
      have hd' : p ∈ A → p ∉ B := fun ha => Finset.disjoint_left.mp hd ha
      grind
    rw [other] at part
    exact ⟨(⟨_, Nat.prod_mem_factoredNumbers A n.val⟩,
      ⟨_, Nat.prod_mem_factoredNumbers B n.val⟩), Subtype.ext part⟩

theorem normalized_convolution {A B : Finset ℕ} (hd : Disjoint A B) (w : ℝ) :
    F (A ∪ B) w = P A * ∑' a : Integers A, harmonic A a * F B (w - logN a) := by
  let e := Equiv.ofBijective _ (multiply_bijective hd)
  have hs : Summable (fun x => atom w (e x)) := (e.summable_iff).mpr (summable_atom (A ∪ B) w)
  rw [F, ← e.tsum_eq, hs.tsum_prod, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [← mul_assoc, harmonic, mul_comm (P A), div_mul_cancel₀ _ (P_pos A).ne', F, ← tsum_mul_left]
  apply tsum_congr
  intro b
  change (if Real.log ((a.val * b.val : ℕ) : ℝ) ≤ w then _ else _) = _
  simp only [Nat.cast_mul, Real.log_mul (nat_pos a).ne' (nat_pos b).ne', atom, logN]
  simp only [show Real.log (a : ℕ) + Real.log (b : ℕ) ≤ w ↔ Real.log (b : ℕ) ≤ w - Real.log (a : ℕ) by constructor <;> intro h <;> linarith]
  by_cases h : Real.log (b : ℕ) ≤ w - Real.log (a : ℕ)
  · simp only [if_pos h]
    rw [show -(w - Real.log (a : ℕ)) = Real.log (a : ℕ) + (-w) by ring, Real.exp_add,
      Real.exp_log (nat_pos a), ← mul_assoc, inv_mul_cancel₀ (nat_pos a).ne', one_mul]
  · simp [h]

end Shift490
end
end


/- Law -/
section
noncomputable section

namespace Shift490

open Finset Real Filter MeasureTheory

open scoped Topology

theorem P_union {D B : Finset ℕ} (hd : Disjoint D B) : P (D ∪ B) = P D * P B := by
  simp only [P,filter_union,prod_union (hd.mono (filter_subset Nat.Prime D) (filter_subset Nat.Prime B))]

theorem one_le_P (S : Finset ℕ) : 1 ≤ P S := by
  apply Finset.one_le_prod
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  apply (one_le_inv₀ (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))).mpr
  linarith [show 0 ≤ (p:ℝ)⁻¹ by positivity]

lemma hnonneg {D} (a : Integers D) : 0 ≤ harmonic D a :=
  div_nonneg (by positivity) (P_pos D).le

lemma avg_summable {D : Finset ℕ} {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    Summable (fun a : Integers D => harmonic D a * f (logN a)) :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg (hnonneg a) (hf _).1)
    (fun a => mul_le_mul_of_nonneg_left (hf _).2 (hnonneg a))
    ((harmonic_probability D).summable.mul_right M)

def rootReciprocal : ℕ →* ℝ where
  toFun n := (√(n:ℝ))⁻¹
  map_one' := by simp
  map_mul' := by simp [Real.sqrt_mul (Nat.cast_nonneg _), mul_comm]

theorem half_moment (D : Finset ℕ) :
    Summable (fun a : Integers D => harmonic D a * exp (logN a / 2)) := by
  have hp {p : ℕ} (h : p.Prime) : ‖rootReciprocal p‖ < 1 := by
    change ‖(√(p:ℝ))⁻¹‖ < 1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have h' : 1 < (p:ℝ) := by exact_mod_cast h.one_lt
    have hs : 1 < √(p:ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ)]
    exact (inv_lt_one₀ (by positivity)).mpr hs
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := rootReciprocal) hp D).2.summable.div_const (P D)
  apply h.congr
  intro a
  change (√(a.val:ℝ))⁻¹ / P D = ((a.val:ℝ)⁻¹ / P D) * exp (log (a.val:ℝ) / 2)
  rw [Real.exp_half, Real.exp_log (nat_pos a)]
  field_simp [Real.sqrt_ne_zero'.mpr (nat_pos a), (nat_pos a).ne', (P_pos D).ne']
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg a.val)]

def moment (D : Finset ℕ) := ∑' a : Integers D, harmonic D a * exp (logN a / 2)

end Shift490
end
end


/- Bounds -/
section
noncomputable section

namespace Shift490

open Finset Filter

private noncomputable def smooth (n : ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → P p)

private lemma mem_smooth {n m : ℕ} {P : ℕ → Prop} :
    m ∈ smooth n P ↔ (1 ≤ m ∧ m ≤ n) ∧ ∀ p, Nat.Prime p → p ∣ m → P p := by
  classical
  simp [smooth]

private noncomputable def truncatedMass (s : Finset ℕ) := ∑ m ∈ s, (m : ℝ)⁻¹

private lemma transport {α β : Type*} (s : Finset α) (t : Finset β)
    (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b)
    (hm : ∀ a ∈ s, f a ∈ t) (hi : Set.InjOn f s) :
    ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
  classical
  rw [← sum_image hi]
  apply sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hm)
  exact fun b _ _ => hg b

private lemma log_sum (n : ℕ) (P : ℕ → Prop) :
    ∑ m ∈ smooth n P, Real.log m ≤
      ((Real.log 4 + 4) * n) * truncatedMass (smooth n P) := by
  classical
  let s := smooth n P
  let U := s.sigma (fun m => m.divisors)
  let V := s.sigma (fun v => Ioc 0 ⌊(n : ℝ) / v⌋₊)
  let f (x : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨x.1 / x.2, x.2⟩
  have data {x : Σ _ : ℕ, ℕ} (hx : x ∈ U) :
      x.1 ∈ s ∧ x.2 ∣ x.1 ∧ 0 < x.2 ∧ 0 < x.1 / x.2 := by
    obtain ⟨hm,hd⟩ := mem_sigma.mp hx
    have h0 := Nat.pos_of_mem_divisors hd
    exact ⟨hm, Nat.dvd_of_mem_divisors hd, h0,
      Nat.div_pos (Nat.le_of_dvd (mem_smooth.mp hm).1.1 (Nat.dvd_of_mem_divisors hd)) h0⟩
  have hm : ∀ x ∈ U, f x ∈ V := by
    intro x hx
    obtain ⟨hs,hd,hp,hq⟩ := data hx
    obtain ⟨⟨_,hle⟩,hall⟩ := mem_smooth.mp hs
    refine mem_sigma.mpr ⟨mem_smooth.mpr ⟨⟨hq, (Nat.div_le_self ..).trans hle⟩,
      fun p hpr hdv => hall p hpr (hdv.trans (Nat.div_dvd_of_dvd hd))⟩, ?_⟩
    refine mem_Ioc.mpr ⟨hp, Nat.le_floor ((le_div_iff₀ (by exact_mod_cast hq)).mpr ?_)⟩
    exact_mod_cast (show x.2 * (x.1 / x.2) ≤ n by rwa [Nat.mul_div_cancel' hd])
  have hi : Set.InjOn f U := by
    intro x hx y hy h
    have he := congrArg (fun z : Σ _ : ℕ, ℕ => z.1 * z.2) h
    change x.1 / x.2 * x.2 = y.1 / y.2 * y.2 at he
    rw [Nat.div_mul_cancel (data hx).2.1, Nat.div_mul_cancel (data hy).2.1] at he
    have he' := congrArg (fun z : Σ _ : ℕ, ℕ => z.2) h
    exact Sigma.ext he (heq_of_eq he')
  calc
    _ = ∑ x ∈ U, ArithmeticFunction.vonMangoldt (f x).2 := by
      simp [U, s, sum_sigma, f, ArithmeticFunction.vonMangoldt_sum]
    _ ≤ ∑ y ∈ V, ArithmeticFunction.vonMangoldt y.2 :=
      transport U V f _ (fun _ => ArithmeticFunction.vonMangoldt_nonneg) hm hi
    _ = ∑ v ∈ s, Chebyshev.psi ((n : ℝ) / v) := by rw [Finset.sum_sigma]; rfl
    _ ≤ ∑ v ∈ s, (Real.log 4 + 4) * ((n : ℝ) / v) :=
      sum_le_sum fun v _ => Chebyshev.psi_le_const_mul_self (by positivity)
    _ = _ := by simp [s, truncatedMass, mul_sum, div_eq_mul_inv, mul_assoc]

theorem F_nonneg (S w) : 0 ≤ F S w := tsum_nonneg atom_nonneg

private theorem countSet_eq (S w) : countSet S w = smooth ⌊Real.exp w⌋₊ (· ∈ S) := by
  classical
  ext n
  simp only [countSet, smooth, mem_filter, mem_range, Nat.lt_succ_iff, mem_Icc]
  constructor
  · rintro ⟨h, hn⟩
    exact ⟨⟨Nat.pos_of_ne_zero hn.1,h⟩,Nat.mem_factoredNumbers'.mp hn⟩
  · rintro ⟨⟨_,h⟩,hn⟩
    exact ⟨h,Nat.mem_factoredNumbers'.mpr hn⟩

theorem F_le_one (S w) : F S w ≤ 1 := by
  classical
  rw [F_eq_card,countSet_eq,Real.exp_neg]
  have h := card_le_card (filter_subset (fun m => ∀ p, Nat.Prime p → p ∣ m → p ∈ S)
    (Icc 1 ⌊Real.exp w⌋₊))
  change (smooth ⌊Real.exp w⌋₊ (· ∈ S)).card ≤ _ at h
  simp at h
  rw [inv_mul_eq_div, div_le_one (Real.exp_pos _)]
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le (Real.exp_pos w).le)

def K₀ : ℝ := Real.log 4 + 5

lemma K₀_pos : 0 < K₀ := by unfold K₀; positivity

theorem counting_bound (S w) (hw : 0 < w) : F S w ≤ K₀ * P S / w := by
  classical
  let n := ⌊Real.exp w⌋₊
  let t := smooth n (· ∈ S)
  have hm : ∀ k ∈ t, k ∈ Integers S := fun k h => Nat.mem_factoredNumbers'.mpr (mem_smooth.mp h).2
  have hmP : truncatedMass t ≤ P S := by
    let u := t.subtype (· ∈ Integers S)
    have he : ∑ a ∈ u, ((a.val:ℕ):ℝ)⁻¹ = truncatedMass t := by
      exact sum_subtype_of_mem (s := t) (fun n : ℕ => (n:ℝ)⁻¹) hm
    rw [← he, ← (harmonic_sum S).tsum_eq]
    exact (harmonic_sum S).summable.sum_le_tsum u (fun _ _ => by positivity)
  have hnum : (n:ℝ) ≤ Real.exp w := Nat.floor_le (Real.exp_pos _).le
  have hl (k : ℕ) (hk : k ∈ t) : w ≤ Real.log k + Real.exp w * (k:ℝ)⁻¹ := by
    have hk' : 0 < (k:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (hm k hk).1
    have := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos w) hk')
    rw [Real.log_div (Real.exp_pos w).ne' hk'.ne', Real.log_exp, div_eq_mul_inv] at this
    linarith
  have hh := sum_le_sum hl
  simp only [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at hh
  have hlog := log_sum n (· ∈ S)
  have hmass : 0 ≤ truncatedMass t := sum_nonneg fun _ _ => by positivity
  change (∑ k ∈ t, Real.log k) ≤ ((Real.log 4 + 4)*n)*truncatedMass t at hlog
  have hc : (Real.log 4 + 4)*n ≤ (Real.log 4 + 4)*Real.exp w :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  rw [F_eq_card,countSet_eq,Real.exp_neg, inv_mul_eq_div, div_le_div_iff₀ (Real.exp_pos _) hw]
  change t.card * w ≤ _
  calc
    _ ≤ ((Real.log 4 + 4)*Real.exp w)*truncatedMass t + Real.exp w * truncatedMass t := by
      change (t.card : ℝ)*w ≤ (∑ k ∈ t, Real.log k) + Real.exp w * truncatedMass t at hh
      linarith [mul_le_mul_of_nonneg_right hc hmass]
    _ = (K₀ * truncatedMass t) * Real.exp w := by unfold K₀; ring
    _ ≤ _ := by gcongr; exact K₀_pos.le

end Shift490
end
end


/- StableTransfer -/
section
namespace Erdos490Transfer

open Finset Filter Real

noncomputable section

open Classical

def pick {Y n} (c : Colors Y n) (b : Bool) := if b then c.red else c.blue

lemma pick_prime {Y n} (c : Colors Y n) (b : Bool) : ∀ p ∈ pick c b, Nat.Prime p := by
  intro p hp
  have h : p ∈ c.red ∪ c.blue := by
    cases b <;> simp_all [pick]
  exact (mem_filter.mp (c.cover ▸ h)).2

lemma pick_scale {Y n} (c : Colors Y n) (b : Bool) :
    Shift490.P (pick c b)/log n = eulerScale (pick c b) n := by
  simp [Shift490.P,eulerScale,euler,filter_true_of_mem (pick_prime c b)]

theorem shifted_density (C : Finset ℕ) {n u : ℕ} (hn : 0 < n) (hu : 0 < u) :
    Shift490.F C (log n-log u) = density C n u := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hu' : (0:ℝ) < u := by exact_mod_cast hu
  have hex : exp (log n-log u) = (n:ℝ)/u := by rw [exp_sub,exp_log hn',exp_log hu']
  have hset : Shift490.countSet C (log n-log u) = semigroup C (n/u) := by
    ext x
    simp only [Shift490.countSet,hex,mem_filter,mem_range,Nat.lt_succ_iff,mem_semigroup]
    rw [Nat.le_floor_iff (by positivity),le_div_iff₀ hu',Nat.le_div_iff_mul_le hu]
    constructor
    · intro h
      exact ⟨h.2,by exact_mod_cast h.1⟩
    · intro h
      exact ⟨by exact_mod_cast h.2,h.1⟩
  rw [Shift490.F_eq_card,hset,exp_neg,hex]
  unfold density
  field_simp

def Stable {Y} (N : ℕ → ℕ) (c : ∀ k, Colors Y (N k)) (b : Bool) : Prop :=
  ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
    ∀ s : ℝ, |s| ≤ H →
      |Shift490.F (pick (c k) b) (log (N k)+s) - Shift490.F (pick (c k) b) (log (N k))|
        ≤ η*eulerScale (pick (c k) b) (N k)

def StableRecovery : Prop :=
  ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
    ∀ (c : ∀ k, Colors Y (N k)) (b : Bool), Stable N c b → ∃ᶠ k in atTop,
      2 ≤ N k ∧ ∃ w : ℝ, 0 < w ∧ ∃ d : (m : ℕ) → Colors Y m,
      (∀ i < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) (!b)) (N k) (i+1) ≤
        (w*(log m/log (N k))) * density (pick (d m) (!b)) m (i+1) + η*eulerScale (pick (c k) (!b)) (N k)) ∧
      (∀ j < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) b) (N k) 1 ≤
        w⁻¹*density (pick (d m) b) m (j+1) + η*eulerScale (pick (c k) b) (N k))

end

end Erdos490Transfer
end


/- Sampling -/
section
namespace Erdos490Transfer

open Filter Real

noncomputable section

def SampledRecovery : Prop :=
  ∀ Y K, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∀ N : ℕ → ℕ, StrictMono N → ∀ (c : ∀ k, Colors Y (N k)) (b : Bool),
    Stable N c b → ∃ᶠ k in atTop, 2 ≤ N k ∧ ∃ z a : ℝ,
      0 < z ∧ (1-θ)*log (N k) ≤ z ∧ 0 < a ∧ ∃ d : (m : ℕ) → Colors Y m,
      (∀ i < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) (!b)) (N k) (i+1) ≤
        (a*(log m/z))*density (pick (d m) (!b)) m (i+1) + θ*eulerScale (pick (c k) (!b)) (N k)) ∧
      (∀ j < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) b) (N k) 1 ≤
        a⁻¹*density (pick (d m) b) m (j+1) + θ*eulerScale (pick (c k) b) (N k))

lemma sparse_rescale {L M z a x X E B θ : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (hz : 0 < z) (ha : 0 ≤ a) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hclose : (1-θ)*L ≤ z)
    (hx : x ≤ B*E) (hh : x ≤ (a*(M/z))*X + θ*E) :
    x ≤ (a*(M/L))*X + (B+1)*θ*E := by
  have hdiv : (1-θ)*(M/z) ≤ M/L := by
    rw [le_div_iff₀ hL]
    calc
      _ = ((1-θ)*L)/z*M := by ring
      _ ≤ 1*M := by gcongr; exact (div_le_one hz).mpr hclose
      _ = M := one_mul M
  have h1 := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hθ')
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv ha) hX
  nlinarith only [h1,h2,mul_le_mul_of_nonneg_left hx hθ,mul_nonneg (sq_nonneg θ) hE]

theorem stableRecovery_of_sampled (sample : SampledRecovery) : StableRecovery := by
  intro Y K η hη N hN c b st
  let B := envelope K
  have hB : 0 ≤ B := by dsimp [B,envelope]; positivity
  let θ := min (1/2:ℝ) (η/(B+1))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hθ1 : θ < 1 := (min_le_left ..).trans_lt (by norm_num)
  have hb : (B+1)*θ ≤ η := by
    rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  have hsmall : θ ≤ η := by nlinarith [mul_nonneg hB hθ.le]
  apply (sample Y K θ hθ hθ1 N hN c b st).mono
  rintro k ⟨hn,z,a,hz,hclose,ha,d,hs,hr⟩
  have hL : 0 < log (N k) := log_pos (by exact_mod_cast (show 1 < N k by omega))
  have pos (b : Bool) : 0 ≤ eulerScale (pick (c k) b) (N k) :=
    div_nonneg (euler_pos (pick_prime _ _)).le hL.le
  refine ⟨hn,a,ha,d,?_,?_⟩
  · intro i hi
    filter_upwards [hs i hi] with m hm
    let C := pick (c k) (!b)
    have ec : Harmonic.scale C (N k) ≤ eulerScale C (N k) :=
      div_le_div_of_nonneg_right (truncMass_le_euler (pick_prime _ _) _) hL.le
    have hbound := (density_le_scale hL hi C).trans (mul_le_mul_of_nonneg_left ec hB)
    have hX : 0 ≤ density (pick (d m) (!b)) m (i+1) := by unfold density; positivity
    exact (sparse_rescale hL (log_natCast_nonneg _) hz ha.le hX (pos _) hθ.le hθ1.le hclose
      hbound hm).trans (add_le_add_right (mul_le_mul_of_nonneg_right hb (pos _)) _)
  · intro j hj
    filter_upwards [hr j hj] with m hm
    exact hm.trans (add_le_add_right (mul_le_mul_of_nonneg_right hsmall (pos _)) _)

end

end Erdos490Transfer
end


/- SmoothSieve -/
section
open Finset

namespace Erdos490Smooth

noncomputable def avoid (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∏ p ∈ S, ((if p ∣ m then (-1:ℝ) else 0) + 1)

private lemma all_dvd {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p) {m : ℕ} :
    (∏ p ∈ S, p) ∣ m ↔ ∀ p ∈ S, p ∣ m := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem id hp).trans h
  · intro h
    apply Finset.prod_dvd_of_isRelPrime _ h
    intro p hp q hq hne
    exact (Nat.coprime_iff_isRelPrime).mp (((hS p hp).coprime_iff_not_dvd).mpr
      (fun hd => hne (((Nat.prime_dvd_prime_iff_eq (hS p hp) (hS q hq)).mp hd))))

theorem avoid_iff (S : Finset ℕ) (m : ℕ) :
    avoid S m = if ∃ p ∈ S, p ∣ m then 0 else 1 := by
  classical
  unfold avoid
  split_ifs with hh
  · obtain ⟨p,hp,hd⟩ := hh
    exact Finset.prod_eq_zero hp (by simp [hd])
  · apply Finset.prod_eq_one
    intro p hp
    simp [show ¬p ∣ m by intro h; exact hh ⟨p,hp,h⟩]

theorem avoid_expand (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (m : ℕ) :
    avoid S m = ∑ T ∈ S.powerset,
      if (∏ p ∈ T, p) ∣ m then (-1 : ℝ)^T.card else 0 := by
  classical
  unfold avoid
  rw [Finset.prod_add_one]
  apply Finset.sum_congr rfl
  intro T hT
  have hs : T ⊆ S := Finset.mem_powerset.mp hT
  split_ifs with h
  · have hall := (all_dvd (fun p hp => hS p (hs hp))).mp h
    exact (Finset.prod_congr rfl fun p hp => if_pos (hall p hp)).trans (Finset.prod_const _)
  · obtain ⟨p,hp,hd⟩ := (by
      by_contra! hall
      exact h ((all_dvd (fun p hp => hS p (hs hp))).mpr hall) :
        ∃ p ∈ T, ¬p ∣ m)
    exact Finset.prod_eq_zero hp (if_neg hd)

theorem avoid_dilate (T : Finset ℕ) {d m : ℕ}
    (h : ∀ p ∈ T, p.Prime ∧ ¬p ∣ d) :
    avoid T (d*m) = avoid T m := by
  simp only [avoid_iff]
  congr 1
  apply propext
  constructor
  · rintro ⟨p,hp,hx⟩
    exact ⟨p,hp,((h p hp).1.dvd_mul.mp hx).resolve_left (h p hp).2⟩
  · rintro ⟨p,hp,hx⟩
    exact ⟨p,hp,dvd_mul_of_dvd_right hx _⟩

noncomputable def smallCount (S : Finset ℕ) (n : ℕ) : ℝ := ∑ m ∈ Finset.Ioc 0 n, avoid S m

theorem smallCount_formula (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) :
    smallCount S n = ∑ T ∈ S.powerset, (-1:ℝ)^T.card * (n/(∏ p ∈ T, p) : ℕ) := by
  classical
  unfold smallCount
  simp_rw [avoid_expand S hS]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← Finset.sum_filter,Finset.sum_const, Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul,mul_comm]

end Erdos490Smooth
end


/- SieveError -/
section
open Finset

namespace Erdos490Smooth

noncomputable def localProduct (S : Finset ℕ) : ℝ := ∏ p ∈ S, (1 - (p:ℝ)⁻¹)

theorem localProduct_expand (S : Finset ℕ) : localProduct S =
    ∑ T ∈ S.powerset, (-1:ℝ)^T.card / (∏ p ∈ T, p : ℕ) := by
  unfold localProduct
  calc
    _ = ∏ p ∈ S, ((-1:ℝ)*(p:ℝ)⁻¹ + 1) := by
      apply Finset.prod_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.prod_add_one]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_inv_distrib,Nat.cast_prod,div_eq_mul_inv]

private theorem div_error (n : ℕ) {d : ℕ} (hd : 0 < d) :
    |((n/d:ℕ):ℝ) - (n:ℝ)/d| ≤ 1 := by
  have h : ((n%d:ℕ):ℝ) + (d:ℝ)*(n/d:ℕ) = n := by exact_mod_cast Nat.mod_add_div n d
  have hl : ((n%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt n hd
  have hp : 0 < (d:ℝ) := by exact_mod_cast hd
  rw [abs_le]
  constructor
  · apply (le_sub_iff_add_le).mpr
    rw [← le_sub_iff_add_le', div_le_iff₀ hp]
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    rw [add_comm,← sub_le_iff_le_add,le_div_iff₀ hp]
    nlinarith [Nat.cast_nonneg (n%d) (α := ℝ)]

theorem cofactor_rounding (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) {d : ℕ} (hd : 0 < d) :
    |smallCount S (n/d) - ((n:ℝ)/d)*localProduct S| ≤ 2 ^ S.card := by
  classical
  rw [smallCount_formula S hS,localProduct_expand,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _T ∈ S.powerset, (1:ℝ) := by
      refine Finset.sum_le_sum fun T hT => ?_
      let m := ∏ p ∈ T,p
      have hm : 0 < m := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
      have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
      have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
      change |(-1:ℝ)^T.card * ((n/d/m:ℕ):ℝ) - ((n:ℝ)/d)*((-1:ℝ)^T.card / m)| ≤ 1
      rw [Nat.div_div_eq_div_mul,show (n:ℝ)/d*((-1:ℝ)^T.card/m) =
        (-1:ℝ)^T.card * ((n:ℝ)/(d*m:ℕ)) by push_cast; ring, ← mul_sub,
        abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      exact div_error n (Nat.mul_pos hd hm)
    _ = _ := by simp

end Erdos490Smooth
end


/- OldStrip -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490Smooth

noncomputable section

open Classical

private def dprod (T : Finset ℕ) := ∏ p ∈ T, p

private def coeff (T : Finset ℕ) : ℝ := (-1:ℝ)^T.card / dprod T

private lemma product_active {C T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (hc : T ⊆ C) :
    Active C (dprod T) := by
  refine Nat.mem_factoredNumbers_of_primeFactors_subset
    (Finset.prod_ne_zero_iff.mpr (fun p hp => (hT p hp).ne_zero)) ?_
  simpa only [dprod,Nat.primeFactors_prod hT] using hc

private lemma div_count {C : Finset ℕ} {d : ℕ} (hd : Active C d) (n : ℕ) :
    ((semigroup C n).filter (d ∣ ·)).card = (semigroup C (n/d)).card := by
  have hpos := Nat.pos_of_ne_zero hd.1
  have eq : (semigroup C n).filter (d ∣ ·) = (semigroup C (n/d)).image (· * d) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hm'⟩ := mem_filter.mp hm
      obtain ⟨hc,hl⟩ := mem_semigroup.mp hm
      refine mem_image.mpr ⟨m/d,mem_semigroup.mpr ⟨Nat.mem_factoredNumbers_of_dvd hc
        (Nat.div_dvd_of_dvd hm'),Nat.div_le_div_right hl⟩,Nat.div_mul_cancel hm'⟩
    · rintro hm
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hm
      obtain ⟨hc,hl⟩ := mem_semigroup.mp ha
      exact mem_filter.mpr ⟨mem_semigroup.mpr ⟨Nat.mul_mem_factoredNumbers hc hd,
        (Nat.le_div_iff_mul_le hpos).mp hl⟩,dvd_mul_left ..⟩
  rw [eq,card_image_of_injective _ (fun _ _ e => Nat.eq_of_mul_eq_mul_right hpos e)]

theorem stripped_count {S C : Finset ℕ} (hs : S ⊆ C) (hp : ∀ p ∈ S, p.Prime) (n : ℕ) :
    ((semigroup (C \ S) n).card:ℝ) = ∑ T ∈ S.powerset,
      (-1:ℝ)^T.card * (semigroup C (n/dprod T)).card := by
  have eq : semigroup (C \ S) n = (semigroup C n).filter (fun m => ¬∃ p ∈ S, p ∣ m) := by
    ext m
    simp only [mem_filter,mem_semigroup,Nat.mem_factoredNumbers']
    constructor
    · intro ⟨h,hl⟩
      exact ⟨⟨fun p hp hd => (mem_sdiff.mp (h p hp hd)).1,hl⟩,
        fun ⟨p,hm,hd⟩ => (mem_sdiff.mp (h p (hp p hm) hd)).2 hm⟩
    · rintro ⟨⟨h,hl⟩,ha⟩
      exact ⟨fun p hp hd => mem_sdiff.mpr ⟨h p hp hd, fun hm => ha ⟨p,hm,hd⟩⟩,hl⟩
  calc
    _ = ∑ m ∈ semigroup C n, avoid S m := by
      rw [eq,card_filter]
      push_cast
      simp only [avoid_iff]
      apply sum_congr rfl
      intro m _
      split_ifs <;> norm_num
    _ = _ := by
      simp_rw [avoid_expand S hp]
      rw [sum_comm]
      apply sum_congr rfl
      intro T hT
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      change (((semigroup C n).filter (dprod T ∣ ·)).card:ℝ) * _ = _
      rw [div_count (product_active
        (fun p h => hp p (mem_powerset.mp hT h)) ((mem_powerset.mp hT).trans hs)),mul_comm]

lemma F_eq_semigroup (C : Finset ℕ) (w : ℝ) :
    F C w = exp (-w) * (semigroup C ⌊exp w⌋₊).card := by
  rw [F_eq_card]
  congr 3
  ext m
  simp only [countSet,mem_filter,mem_range,Nat.lt_succ_iff,mem_semigroup]
  exact and_comm

theorem stripped_density {S C : Finset ℕ} (hs : S ⊆ C) (hp : ∀ p ∈ S, p.Prime) (w : ℝ) :
    F (C \ S) w = ∑ T ∈ S.powerset, coeff T * F C (w-log (dprod T)) := by
  rw [F_eq_semigroup,stripped_count hs hp,mul_sum]
  apply sum_congr rfl
  intro T hT
  have hpos := Nat.pos_of_ne_zero (product_active (fun p h => hp p (mem_powerset.mp hT h))
    ((mem_powerset.mp hT).trans hs)).1
  have hpos' : 0 < (dprod T:ℝ) := by exact_mod_cast hpos
  rw [F_eq_semigroup,exp_sub,exp_log hpos',Nat.floor_div_natCast,
    show -(w-log (dprod T)) = -w+log (dprod T) by ring,exp_add,exp_log hpos']
  unfold coeff
  field_simp

private lemma coeff_sum {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) :
    (∑ T ∈ S.powerset, coeff T) = (P S)⁻¹ := by
  change (∑ T ∈ S.powerset, (-1:ℝ)^T.card / (∏ p ∈ T, p:ℕ)) = _
  rw [← localProduct_expand,P,filter_true_of_mem hp,prod_inv_distrib,inv_inv]
  rfl

theorem stable_strip {Y N c b} (st : Stable (Y:=Y) N c b) (pool : Finset ℕ)
    (hp : ∀ p ∈ pool, Nat.Prime p) (H η : ℝ) (hH : 0 ≤ H) (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ S ⊆ pool, S ⊆ pick (c k) b → ∀ h : ℝ, |h| ≤ H →
      |F (pick (c k) b \ S) (log (N k)+h) - (P S)⁻¹ * F (pick (c k) b) (log (N k))|
        ≤ η * (P (pick (c k) b \ S) / log (N k)) := by
  let radius := ∑ T ∈ pool.powerset, |log (dprod T)|
  let B := (pool.powerset.card:ℝ)*P pool
  have hcount : 0 < pool.powerset.card := card_pos.mpr ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  have hB : 0 < B := mul_pos (by exact_mod_cast hcount) (P_pos _)
  have hrad : 0 ≤ radius := sum_nonneg fun _ _ => abs_nonneg _
  filter_upwards [st (H+radius) (by positivity) (η/B) (div_pos hη hB)] with k hk
  intro S hS hs h hh
  let C := pick (c k) b
  let L := log (N k:ℝ)
  have hSp := fun p (hx : p ∈ S) => hp p (hS hx)
  have mult {A D : Finset ℕ} (h : A ⊆ D) : P D = P A*P (D \ A) := by
    rw [← P_union (show Disjoint A (D \ A) from disjoint_left.mpr (fun {_} ha hb => (mem_sdiff.mp hb).2 ha)),
      union_sdiff_of_subset h]
  have hPS : P S ≤ P pool := by
    rw [mult hS]; exact le_mul_of_one_le_right (P_pos _).le (one_le_P _)
  have hEC : eulerScale C (N k) = P C/L := (pick_scale ..).symm
  let E := η/B*(P C/L)
  have hE : 0 ≤ E := mul_nonneg (div_nonneg hη.le hB.le) (div_nonneg (P_pos _).le (log_natCast_nonneg _))
  have term (T) (ht : T ∈ S.powerset) :
      |coeff T * (F C (L+h-log (dprod T)) - F C L)| ≤ E := by
    have htp := mem_powerset.mpr ((mem_powerset.mp ht).trans hS)
    have hbound : |log (dprod T)| ≤ radius :=
      single_le_sum (fun T _ => abs_nonneg (log (dprod T))) htp
    have hsft : |h-log (dprod T)| ≤ H+radius := (abs_sub _ _).trans (add_le_add hh hbound)
    have hdiff := hk _ hsft
    rw [← add_sub_assoc,hEC] at hdiff
    have hd := Nat.pos_of_ne_zero (product_active (fun p h => hSp p (mem_powerset.mp ht h))
      (mem_powerset.mp ht)).1
    have hcoeff : |coeff T| ≤ 1 := by
      simp only [coeff,abs_div,abs_pow,abs_neg,abs_one,one_pow,abs_of_nonneg (show 0 ≤ (dprod T:ℝ) by positivity)]
      exact one_div_le_one_div_of_le zero_lt_one (by exact_mod_cast hd) |>.trans_eq (one_div_one)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)).trans (mul_le_of_le_one_left hE hcoeff)
  change |F (C \ S) (L+h) - (P S)⁻¹*F C L| ≤ _
  rw [stripped_density hs hSp,← coeff_sum hSp,sum_mul,← sum_sub_distrib]
  calc
    _ ≤ ∑ T ∈ S.powerset, |coeff T * (F C (L+h-log (dprod T))-F C L)| := by
      simp only [mul_sub]
      exact abs_sum_le_sum_abs .. 
    _ ≤ ∑ _T ∈ S.powerset, E := sum_le_sum term
    _ ≤ (pool.powerset.card:ℝ)*E := by
      simp only [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_card (powerset_mono.mpr hS)) hE
    _ ≤ _ := by
      change _ ≤ η*(P (C \ S)/L)
      dsimp only [E,B]
      rw [mult (show S ⊆ C from hs)]
      have hb : (pool.powerset.card:ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
      have hcancel : (pool.powerset.card:ℝ)*(η/((pool.powerset.card:ℝ)*P pool)*(P S*P (C \ S)/L))
          = (P S/P pool)*(η*(P (C \ S)/L)) := by field_simp [hb,(P_pos pool).ne']
      rw [hcancel]
      exact mul_le_of_le_one_left (mul_nonneg hη.le (div_nonneg (P_pos _).le (log_natCast_nonneg _)))
        ((div_le_one (P_pos _)).mpr hPS)

end

end Erdos490Transfer
end


/- SmoothMass -/
section
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

end Erdos490Smooth
end


/- OldWindow -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 MeasureTheory

open scoped Interval Topology

noncomputable section

open Classical

def oldWindow (C : Finset ℕ) (a b : ℝ) : Finset ℕ :=
  (semigroup C ⌊exp b⌋₊).filter (fun m : ℕ => a < log m)

def windowMass (C : Finset ℕ) (a b : ℝ) :=
  ∑ m ∈ oldWindow C a b, (m:ℝ)⁻¹

lemma mem_oldWindow {m : ℕ} {C : Finset ℕ} {a b : ℝ} : m ∈ oldWindow C a b ↔
    Active C m ∧ a < log m ∧ log m ≤ b := by
  rw [oldWindow,mem_filter,mem_semigroup]
  constructor
  · rintro ⟨⟨hm,hl⟩,ha⟩
    exact ⟨hm,ha,(log_le_iff_le_exp (nat_pos ⟨m,hm⟩)).mpr ((Nat.le_floor_iff (exp_pos b).le).mp hl)⟩
  · rintro ⟨hm,ha,hb⟩
    exact ⟨⟨hm,Nat.le_floor ((log_le_iff_le_exp (nat_pos ⟨m,hm⟩)).mp hb)⟩,ha⟩

private def after (C : Finset ℕ) (a : ℝ) (n : Integers C) : ℝ :=
  if a < logN n then ((n:ℕ):ℝ)⁻¹ else 0

private lemma after_sum (C a) : Summable (after C a) := by
  apply Summable.of_nonneg_of_le _ _ (harmonic_sum C).summable
  · intro n; unfold after; split <;> positivity
  · intro n; unfold after; split <;> simp

private lemma tail_decompose (C a) :
    (∫ t in Set.Ioi a, F C t) = F C a + ∑' n : Integers C, after C a n := by
  rw [Erdos490Smooth.kernel_tail_integral,F,← (summable_atom C a).tsum_add (after_sum C a)]
  apply tsum_congr
  intro n
  by_cases hn : logN n ≤ a
  · simp [atom,after,hn,not_lt.mpr hn]
  · simp [max_eq_right (le_of_not_ge hn),atom,after,hn,lt_of_not_ge hn,exp_neg,logN,exp_log (nat_pos n)]

private lemma after_split (C : Finset ℕ) {a b : ℝ} (hab : a ≤ b) :
    (∑' n, after C a n) = windowMass C a b + ∑' n, after C b n := by
  let f (n : Integers C) : ℝ := if a < logN n ∧ logN n ≤ b then ((n:ℕ):ℝ)⁻¹ else 0
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le _ _ (harmonic_sum C).summable
    · intro n; dsimp [f]; split <;> positivity
    · intro n; dsimp [f]; split <;> simp
  have hwin : windowMass C a b = ∑' n, f n := by
    let s := (oldWindow C a b).subtype (· ∈ Integers C)
    have hm (n : Integers C) : n ∈ s ↔ a < logN n ∧ logN n ≤ b := by
      simp [s,mem_oldWindow,n.property,logN]
    rw [tsum_eq_sum (s:=s) (fun n hn => by simp [f,mt (hm n).mpr hn])]
    calc
      _ = ∑ n ∈ s, ((n.val:ℕ):ℝ)⁻¹ := by
        have eq : s.image Subtype.val = oldWindow C a b := by
          ext m
          constructor
          · rintro hx
            obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
            exact mem_oldWindow.mpr ⟨v.property,(hm v).mp hv⟩
          · intro hx
            obtain ⟨hact,ha,hb⟩ := mem_oldWindow.mp hx
            exact mem_image.mpr ⟨⟨m,hact⟩,(hm _).mpr ⟨ha,hb⟩,rfl⟩
        rw [windowMass,← eq,sum_image (fun _ _ _ _ he => Subtype.ext he)]
      _ = _ := sum_congr rfl (fun n hn => (if_pos ((hm n).mp hn)).symm)
  rw [hwin,← hf.tsum_add (after_sum C b)]
  apply tsum_congr
  intro n
  dsimp [after,f]
  by_cases h1 : a < logN n <;> by_cases h2 : b < logN n <;> simp_all [not_lt]
  linarith

theorem window_identity (C : Finset ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    windowMass C a b = F C b-F C a + ∫ t in a..b, F C t := by
  have h0 : IntegrableOn (F C) (Set.Ioi 0) := by
    by_contra hn
    have eq := integral_undef hn
    rw [Erdos490Smooth.kernel_mass] at eq
    exact (P_pos C).ne' eq
  have ht := intervalIntegral.integral_Ioi_sub_Ioi (h0.mono_set (Set.Ioi_subset_Ioi ha)) hab
  rw [tail_decompose,tail_decompose,after_split C hab] at ht
  linarith

theorem window_flat (C : Finset ℕ) {a b r e : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (h : ∀ t ∈ Set.Icc a b, |F C t-r| ≤ e) :
    |windowMass C a b-(b-a)*r| ≤ (2+b-a)*e := by
  have h0 : IntegrableOn (F C) (Set.Ioi 0) := by
    by_contra hn
    have eq := integral_undef hn
    rw [Erdos490Smooth.kernel_mass] at eq
    exact (P_pos C).ne' eq
  have hint : IntervalIntegrable (F C) volume a b :=
    intervalIntegrable_iff_integrableOn_Ioc_of_le hab |>.mpr
      (h0.mono_set (fun x hx => ha.trans_lt hx.1))
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t => F C t-r) (a:=a) (b:=b) (C:=e) (fun t ht =>
      by rw [Set.uIoc_of_le hab] at ht; exact h t ⟨ht.1.le,ht.2⟩)
  rw [Real.norm_eq_abs,intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const,smul_eq_mul,abs_of_nonneg (sub_nonneg.mpr hab)] at he
  have hl := abs_le.mp (h a ⟨le_rfl,hab⟩)
  have hr := abs_le.mp (h b ⟨hab,le_rfl⟩)
  rw [window_identity C ha hab,abs_le]
  constructor <;> linarith [(abs_le.mp he).1,(abs_le.mp he).2]

end

end Erdos490Transfer
end


/- OldBadMass -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490

noncomputable section

open Classical

def recMass (S : Finset ℕ) := ∑ m ∈ S, (m:ℝ)⁻¹

lemma window_cap (C : Finset ℕ) (a b : ℝ) :
    windowMass C a b ≤ exp (b-a)*F C b := by
  rw [F_eq_semigroup]
  calc
    _ ≤ ∑ _m ∈ oldWindow C a b, exp (-a) := by
      apply sum_le_sum
      intro m hm
      obtain ⟨ha,hl,_⟩ := mem_oldWindow.mp hm
      have he := Real.exp_le_exp.mpr hl.le
      rw [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero ha.1)] at he
      rw [Real.exp_neg]
      exact inv_anti₀ (exp_pos _) he
    _ ≤ (exp (-a))*((semigroup C ⌊exp b⌋₊).card:ℝ) := by
      rw [sum_const,nsmul_eq_mul,mul_comm]
      gcongr
      exact filter_subset (fun m : ℕ => a < log m) (semigroup C ⌊exp b⌋₊)
    _ = _ := by rw [← mul_assoc,← exp_add]; ring_nf

lemma window_total (C : Finset ℕ) (hp : ∀ p ∈ C, p.Prime) (a b : ℝ) :
    windowMass C a b ≤ P C := by
  calc
    _ ≤ truncMass C ⌊exp b⌋₊ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)
    _ ≤ euler C := truncMass_le_euler hp _
    _ = _ := by simp [P,euler,filter_true_of_mem hp]

theorem window_multiple {C d} (hd : Active C d) (a b : ℝ) :
    recMass ((oldWindow C a b).filter (d ∣ ·)) =
    (d:ℝ)⁻¹ * windowMass C (a-log d) (b-log d) := by
  have hd0 := Nat.pos_of_ne_zero hd.1
  let V := oldWindow C (a-log d) (b-log d)
  have logs {x : ℕ} (hx : Active C x) : log ((x*d:ℕ):ℝ) = log x + log d := by
    rw [Nat.cast_mul,log_mul (by exact_mod_cast hx.1) (by exact_mod_cast hd.1)]
  have eq : ((oldWindow C a b).filter (d ∣ ·)) = V.image (· * d) := by
    ext m
    constructor
    · intro hm
      obtain ⟨hm,hm'⟩ := mem_filter.mp hm
      obtain ⟨hc,hl,hr⟩ := mem_oldWindow.mp hm
      have hq := Nat.mem_factoredNumbers_of_dvd hc (Nat.div_dvd_of_dvd hm')
      have he := Nat.div_mul_cancel hm'
      have hlog := logs hq
      rw [he] at hlog
      exact mem_image.mpr ⟨m/d,mem_oldWindow.mpr ⟨hq,by linarith,by linarith⟩,he⟩
    · intro hm
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hm
      obtain ⟨hc,hl,hr⟩ := mem_oldWindow.mp hx
      exact mem_filter.mpr ⟨mem_oldWindow.mpr ⟨Nat.mul_mem_factoredNumbers hc hd,
        by rw [logs hc]; linarith,by rw [logs hc]; linarith⟩,dvd_mul_left ..⟩
  rw [recMass,eq,sum_image (fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_right hd0 he),windowMass,mul_sum]
  simp [V]

def badWindow (C : Finset ℕ) (a b δ : ℝ) (e : ℕ → ℝ) :=
  (oldWindow C a b).filter (fun m => (∃ p ∈ C, p^2 ∣ m) ∨
    δ ≤ ∑ p ∈ C with p ∣ m, e p)

theorem bad_window_bound (C : Finset ℕ) (hp : ∀ p ∈ C, p.Prime) (a b : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (e : ℕ → ℝ) (he : ∀ p ∈ C, 0 ≤ e p) :
    recMass (badWindow C a b δ e) ≤
      (∑ p ∈ C, ((p^2:ℕ):ℝ)⁻¹ * windowMass C (a-log (p^2:ℕ)) (b-log (p^2:ℕ))) +
      δ⁻¹ * ∑ p ∈ C, e p*((p:ℝ)⁻¹ * windowMass C (a-log p) (b-log p)) := by
  let W := oldWindow C a b
  let mult (p m : ℕ) : ℝ := if p ∣ m then (m:ℝ)⁻¹ else 0
  have active {p} (hm : p ∈ C) : Active C p := by
    simp [Active,Nat.mem_factoredNumbers,Nat.primeFactorsList_prime (hp _ hm),(hp _ hm).ne_zero,hm]
  have sum_mult {p} (hm : Active C p) :
      (∑ m ∈ W, mult p m) = (p:ℝ)⁻¹ * windowMass C (a-log p) (b-log p) := by
    rw [← window_multiple hm]
    simp [recMass,sum_filter,mult,W]
  have m0 (p m : ℕ) : 0 ≤ mult p m := by dsimp [mult]; split <;> positivity
  have squareSum m : 0 ≤ ∑ p ∈ C, mult (p^2) m := sum_nonneg (fun _ _ => m0 ..)
  have eSum m : 0 ≤ ∑ p ∈ C, e p * mult p m :=
    sum_nonneg fun p h => mul_nonneg (he p h) (m0 ..)
  calc
    _ ≤ ∑ m ∈ W, ((∑ p ∈ C, mult (p^2) m) + δ⁻¹*(∑ p ∈ C, e p*mult p m)) := by
      unfold recMass badWindow
      rw [sum_filter]
      apply sum_le_sum
      intro m _
      split_ifs with hbad
      · rcases hbad with ⟨p,hp',hd⟩|hl
        · have h := single_le_sum (fun p (_ : p ∈ C) => m0 (p^2) m) hp'
          rw [show mult (p^2) m = (m:ℝ)⁻¹ from if_pos hd] at h
          exact h.trans (le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hδ.le) (eSum m)))
        · have hh := mul_le_mul_of_nonneg_right hl (show 0 ≤ (m:ℝ)⁻¹ by positivity)
          have eq : (∑ p ∈ C with p ∣ m, e p)*(m:ℝ)⁻¹ = ∑ p ∈ C, e p*mult p m := by
            rw [sum_mul,sum_filter]
            exact sum_congr rfl fun p _ => by simp [mult,mul_ite]
          rw [eq] at hh
          have h := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hδ.le)
          rw [← mul_assoc,inv_mul_cancel₀ hδ.ne',one_mul] at h
          linarith [squareSum m]
      · exact add_nonneg (squareSum m) (mul_nonneg (inv_nonneg.mpr hδ.le) (eSum m))
    _ = _ := by
      rw [sum_add_distrib,← mul_sum,sum_comm]
      congr 1
      · apply sum_congr rfl
        intro p h
        exact sum_mult (by simpa [pow_two] using Nat.mul_mem_factoredNumbers (active h) (active h))
      · rw [sum_comm]
        apply congrArg (δ⁻¹ * ·)
        apply sum_congr rfl
        intro p h
        rw [← mul_sum,sum_mult (active h)]

end

end Erdos490Transfer
end


/- DisplacementTail -/
section
open Filter Finset Real

open scoped Topology

namespace Erdos490PrimeCells

private theorem reciprocal_log_step {n : ℕ} (hn : 2 ≤ n) :
    1 / (((n:ℝ)+1) * log ((n:ℝ)+1)^2) ≤ (log (n:ℝ))⁻¹ - (log ((n:ℝ)+1))⁻¹ := by
  have hn1 : 1 < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hn0 : 0 < (n:ℝ) := by linarith
  have hp1 : 1 < (n:ℝ)+1 := by linarith
  have hp0 : 0 < (n:ℝ)+1 := by linarith
  have hln := log_pos hn1
  have hlp := log_pos hp1
  have hle : log (n:ℝ) ≤ log ((n:ℝ)+1) := log_le_log hn0 (by linarith)
  have h := log_le_sub_one_of_pos (div_pos hn0 hp0)
  rw [log_div hn0.ne' hp0.ne'] at h
  have hd : 1/((n:ℝ)+1) ≤ log ((n:ℝ)+1)-log n := by
    have h' : (n:ℝ)/((n:ℝ)+1) - 1 = -(1/((n:ℝ)+1)) := by field_simp; ring
    linarith [h']
  calc
    _ = (1/((n:ℝ)+1)) / (log ((n:ℝ)+1)*log ((n:ℝ)+1)) := by field_simp
    _ ≤ (log ((n:ℝ)+1)-log n) / (log n * log ((n:ℝ)+1)) := by gcongr
    _ = _ := by field_simp

theorem finite_displacement_tail {y : ℕ} (hy : 2 ≤ y) (z : ℕ) :
    ∑ p ∈ (Finset.Ioc y z).filter Nat.Prime, 1 / ((p:ℝ)*log p^2) ≤ (log y)⁻¹ := by
  have hy1 : 1 < (y:ℝ) := by exact_mod_cast (by omega : 1 < y)
  by_cases hyz : y ≤ z
  · calc
      _ ≤ ∑ n ∈ Finset.Ioc y z, 1 / ((n:ℝ)*log n^2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro n _ _
        positivity
      _ ≤ (log y)⁻¹ - (log z)⁻¹ := by
        induction z, hyz using Nat.le_induction with
        | base => simp
        | succ z hz ih =>
          rw [Finset.sum_Ioc_succ_top hz]
          have h := reciprocal_log_step (hy.trans hz)
          rw [Nat.cast_succ]
          linarith
      _ ≤ _ := by
        have hz1 : 1 < (z:ℝ) := hy1.trans_le (by exact_mod_cast hyz)
        linarith [inv_pos.mpr (log_pos hz1)]
  · rw [Finset.Ioc_eq_empty (by omega : ¬y < z)]
    simpa only [Finset.filter_empty,Finset.sum_empty] using (inv_nonneg.mpr (log_pos hy1).le)

end Erdos490PrimeCells
end


/- AbelCells -/
section
open Filter Finset Real MeasureTheory Set

open scoped Topology Interval Chebyshev

namespace Erdos490PrimeCells

noncomputable def kernel (x : ℝ) := (x * log x)⁻¹

noncomputable def slope (x : ℝ) := -(log x + 1) / (x ^ 2 * log x ^ 2)

private theorem kernel_hasDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt kernel (slope x) x := by
  have hx' := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0.ne')).inv (mul_ne_zero hx0.ne' hx'.ne')
  apply h.congr_deriv
  dsimp [slope]
  field_simp

theorem slope_cont {x : ℝ} (hx : 1 < x) : ContinuousAt slope x := by
  have := (Real.log_pos hx).ne'
  unfold slope
  fun_prop (disch := positivity)

noncomputable def reciprocalInterval (x y : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime, (n : ℝ)⁻¹

theorem abel_reciprocal {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    reciprocalInterval x y =
      kernel y * θ y - kernel x * θ x - ∫ t in x..y, slope t * θ t := by
  let c (n : ℕ) : ℝ := if n.Prime then log n else 0
  have hc (z : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊z⌋₊, c n) = θ z := by
    simp [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, c]
  have hk : IntegrableOn (deriv kernel) (Set.Icc x y) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.congr (f := slope)
    · exact fun t ht => (slope_cont (hx.trans_le ht.1)).continuousWithinAt
    · exact fun t ht => (kernel_hasDeriv (hx.trans_le ht.1)).deriv
  have ha := sum_mul_eq_sub_sub_integral_mul c (by linarith : 0 ≤ x) hxy
    (fun t ht => (kernel_hasDeriv (hx.trans_le ht.1)).differentiableAt) hk
  simp only [hc, ← intervalIntegral.integral_of_le hxy] at ha
  convert ha using 1
  · unfold reciprocalInterval
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p.Prime
    · have h : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
      simp [c,hp,kernel,field]
      exact (div_self (log_pos h).ne').symm
    · simp [c,hp]
  · congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hxy] at ht
    change slope t * θ t = deriv kernel t * θ t
    rw [(kernel_hasDeriv (hx.trans_le ht.1)).deriv]

private theorem primitive_hasDeriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => (log t)⁻¹ - log (log t)) (slope x * x) x := by
  have hx0 : 0 < x := by linarith
  have hl := log_pos hx
  have logDer := Real.hasDerivAt_log hx0.ne'
  apply ((logDer.inv hl.ne').sub (logDer.log hl.ne')).congr_deriv
  unfold slope
  field_simp
  ring

theorem abel_main_term {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    kernel y * y - kernel x * x - (∫ t in x..y, slope t * t) =
      log (log y) - log (log x) := by
  have hpt {t : ℝ} (ht : t ∈ Set.uIcc x y) : 1 < t := by
    rw [Set.uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => primitive_hasDeriv (hpt ht))
    (ContinuousOn.intervalIntegrable (fun t ht =>
      ((slope_cont (hpt ht)).mul continuousAt_id).continuousWithinAt))]
  have hx0 : x ≠ 0 := by linarith
  have hy0 : y ≠ 0 := by linarith
  simp [kernel, mul_inv_rev, hx0, hy0]
  ring

end Erdos490PrimeCells
end


/- Remainder -/
section
open Filter Finset Real MeasureTheory Set

open scoped Topology Interval Chebyshev

namespace Erdos490PrimeCells

private lemma logEnvelope {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    (∫ t in x..y, 1 / (t * log t ^ 4)) =
      (1 / log x ^ 3 - 1 / log y ^ 3) / 3 := by
  have hpt {t : ℝ} (ht : t ∈ Set.uIcc x y) : 1 < t := by
    rw [Set.uIcc_of_le hxy] at ht
    exact hx.trans_le ht.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -(log t ^ 3)⁻¹ / 3)
    (f' := fun t => 1 / (t * log t ^ 4)) (a := x) (b := y) (fun t ht => ?_) ?_
  · rw [h]; ring
  · have ht1 := hpt ht
    have ht0 : 0 < t := by linarith
    have hl := log_pos ht1
    apply (((((Real.hasDerivAt_log ht0.ne').pow 3).inv (pow_ne_zero 3 hl.ne')).neg).div_const 3).congr_deriv
    simp only [Pi.pow_apply]
    field_simp
    ring
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht1 := hpt ht
    have ht0 : 0 < t := by linarith
    have hl := log_pos ht1
    exact (continuousAt_const.div (continuousAt_id.mul ((continuousAt_log ht0.ne').pow 4))
      (mul_ne_zero ht0.ne' (pow_ne_zero _ hl.ne'))).continuousWithinAt

private theorem pointwise {x K : ℝ} (hx : 1 < x) (hl : 1 ≤ log x)
    (h : |θ x - x| ≤ K*x / log x ^ 3) :
    |slope x * (θ x - x)| ≤ (2*K) * (1 / (x * log x ^ 4)) := by
  have hx0 : 0 < x := by linarith
  have hl0 := log_pos hx
  have hK : 0 ≤ K := by
    have hpos := (abs_nonneg _).trans h
    by_contra! hn
    exact (not_lt_of_ge hpos) (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hn hx0) (by positivity))
  have hsl : |slope x| = (log x + 1) / (x ^ 2 * log x ^ 2) := by
    unfold slope
    rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  rw [abs_mul, hsl]
  calc
    _ ≤ ((2 * log x) / (x ^ 2 * log x ^ 2)) * (K*x / log x ^ 3) := by
      gcongr
      linarith
    _ = _ := by field_simp

theorem reciprocal_remainder {x y K : ℝ} (hx : 1 < x) (hxy : x ≤ y) (hl : 1 ≤ log x)
    (hK : 0 ≤ K) (hθ : ∀ t ∈ Set.Icc x y, |θ t - t| ≤ K*t / log t ^ 3) :
    |reciprocalInterval x y - (log (log y) - log (log x))| ≤ 3*K / log x ^ 3 := by
  have hpos {t : ℝ} (ht : x ≤ t) : 0 < t := by linarith
  have hlog {t : ℝ} (ht : x ≤ t) : 1 ≤ log t := hl.trans (log_le_log (hpos le_rfl) ht)
  have hlogpos {t : ℝ} (ht : x ≤ t) : 0 < log t := log_pos (hx.trans_le ht)
  have hs : ContinuousOn slope (Set.uIcc x y) := by
    rw [Set.uIcc_of_le hxy]
    exact fun t ht => (slope_cont (hx.trans_le ht.1)).continuousWithinAt
  have hi : IntervalIntegrable (fun t => slope t * θ t) volume x y :=
    Chebyshev.theta_mono.intervalIntegrable.continuousOn_mul hs
  have hj : IntervalIntegrable (fun t => slope t * t) volume x y :=
    (hs.mul continuousOn_id).intervalIntegrable
  have hk {t : ℝ} (ht : t ∈ Set.Icc x y) :
      |kernel t * (θ t - t)| ≤ K / log x ^ 3 := by
    have ht0 := hpos ht.1
    have hl0 := hlogpos ht.1
    rw [abs_mul, kernel, abs_of_pos (inv_pos.mpr (mul_pos ht0 hl0))]
    calc
      _ ≤ (t * log t)⁻¹ * (K*t / log t ^ 3) := by gcongr; exact hθ t ht
      _ = K / log t ^ 4 := by field_simp
      _ ≤ K / log x ^ 3 := by
        gcongr
        calc
          log x ^ 3 ≤ log t ^ 3 := by gcongr; exact ht.1
          _ ≤ log t ^ 4 := pow_le_pow_right₀ (hlog ht.1) (by decide)
  have herr : IntervalIntegrable (fun t => slope t * (θ t - t)) volume x y := by
    simpa only [mul_sub] using hi.sub hj
  have he : |∫ t in x..y, slope t * (θ t - t)| ≤ K / log x ^ 3 := by
    apply (intervalIntegral.abs_integral_le_integral_abs hxy).trans
    calc
      _ ≤ ∫ t in x..y, (2*K) * (1 / (t * log t ^ 4)) := by
        apply intervalIntegral.integral_mono_on hxy herr.abs
        · apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hxy]
          intro t ht
          have ht0 := hpos ht.1
          have hl0 := hlogpos ht.1
          fun_prop (disch := positivity)
        · intro t ht
          exact pointwise (hx.trans_le ht.1) (hlog ht.1) (hθ t ht)
      _ = (2*K) * ((1 / log x ^ 3 - 1 / log y ^ 3) / 3) := by
        rw [intervalIntegral.integral_const_mul, logEnvelope hx hxy]
      _ ≤ _ := by
        have h1 : 0 ≤ K * (1 / log y ^ 3) := by have := hlogpos hxy; positivity
        have h2 : 0 ≤ K * (1 / log x ^ 3) := by have := hlogpos (le_rfl (a := x)); positivity
        rw [div_eq_mul_one_div K]
        linarith only [h1,h2]
  rw [abel_reciprocal hx hxy, ← abel_main_term hx hxy, show
    kernel y * θ y - kernel x * θ x - (∫ t in x..y, slope t * θ t) -
    (kernel y * y - kernel x * x - (∫ t in x..y, slope t * t)) =
    kernel y * (θ y-y) - kernel x * (θ x-x) -
    ((∫ t in x..y, slope t * θ t) - ∫ t in x..y, slope t * t) by ring,
    ← intervalIntegral.integral_sub hi hj]
  simp only [← mul_sub]
  have h1 := abs_sub (kernel y * (θ y - y) - kernel x * (θ x - x)) (∫ t in x..y, slope t * (θ t-t))
  have h2 := abs_sub (kernel y * (θ y-y)) (kernel x * (θ x-x))
  rw [mul_div_assoc]
  linarith [hk (t := y) ⟨hxy,le_rfl⟩, hk (t := x) ⟨le_rfl,hxy⟩]

end Erdos490PrimeCells
end


/- Reciprocal -/
section
open Finset Filter Real Asymptotics

open scoped Chebyshev Topology

namespace Erdos490PrimeCells

theorem error_increment {x y : ℝ} (hxy : x ≤ y) :
    reciprocalInterval x y - (log (log y) - log (log x)) = Mertens.E₂p y - Mertens.E₂p x := by
  have h := Finset.sum_Ioc_consecutive (fun p : ℕ => if p.Prime then (1:ℝ)/p else 0)
    (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxy)
  have hx := Mertens.sum_prime_div_eq x
  have hy := Mertens.sum_prime_div_eq y
  simp only [Finset.sum_filter,one_div] at h hx hy
  unfold reciprocalInterval
  rw [Finset.sum_filter]
  linarith

theorem mertens_error_from_theta {K : ℝ} (hK : 0 ≤ K)
    (hθ : ∀ᶠ t : ℝ in atTop, |θ t - t| ≤ K*t / log t ^ 3) :
    ∀ᶠ x : ℝ in atTop, |Mertens.E₂p x| ≤ 3*K / log x ^ 3 := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp hθ
  filter_upwards [eventually_gt_atTop 1,eventually_ge_atTop X,tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hxX hlog
  have hlim := (((isLittleO_one_iff ℝ).mp Mertens.E₂p.bound').sub
    (tendsto_const_nhds (x := Mertens.E₂p x) (f := atTop))).abs
  simp only [zero_sub, abs_neg] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hy
  rw [← error_increment hy]
  exact reciprocal_remainder hx hy hlog hK fun t ht => hX _ (hxX.trans ht.1)

end Erdos490PrimeCells
end


/- Dilation -/
section
open Filter Real Asymptotics

open scoped Topology

namespace Erdos490PrimeCells

theorem dilated_window_mass {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun s : ℝ => reciprocalInterval (exp (s*a)) (exp (s*b))) atTop
      (𝓝 (log (b/a))) := by
  have hb := ha.trans_le hab
  have lim (c : ℝ) (hc : 0 < c) : Tendsto (fun s : ℝ => exp (s*c)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hc)
  have he := (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h := ((he.comp (lim b hb)).sub (he.comp (lim a ha))).add
    (tendsto_const_nhds (x := log (b/a)) (f := atTop))
  simp only [sub_self,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hid := error_increment (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hs.le))
  rw [log_exp,log_exp,log_mul hs.ne' hb.ne',log_mul hs.ne' ha.ne'] at hid
  dsimp [Function.comp_def]
  rw [log_div hb.ne' ha.ne']
  linarith

end Erdos490PrimeCells
end


/- OldBadEstimate -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490PrimeCells

open scoped Topology

noncomputable section

open Classical

private def wt (p : ℕ) : ℝ := 1 / ((p:ℝ)*log p^2)

private def cap (W : ℝ) : ℝ := 2*exp W*K₀

private lemma cap_pos (W : ℝ) : 0 < cap W := by unfold cap; exact mul_pos (mul_pos (by norm_num) (exp_pos _)) K₀_pos

private lemma local_cap (C : Finset ℕ) {x a d W : ℝ} (hx : 0 < x) (ha : x-W ≤ a)
    (hd : d ≤ x/2) : windowMass C (a-d) (x-d) ≤ cap W*(P C/x) := by
  have hpos : 0 < x-d := by linarith
  calc
    _ ≤ exp ((x-d)-(a-d))*F C (x-d) := window_cap .. 
    _ ≤ exp W * (K₀*P C/(x-d)) := mul_le_mul (exp_le_exp.mpr (by linarith))
      (counting_bound C _ hpos) (F_nonneg ..) (exp_pos _).le
    _ ≤ _ := by
      unfold cap
      have h : x ≤ 2*(x-d) := by linarith
      have h' := mul_le_mul_of_nonneg_left h (mul_nonneg K₀_pos.le (P_pos C).le)
      field_simp [hx.ne',hpos.ne']
      nlinarith only [h']

private lemma wt_window {y Z : ℕ} {C : Finset ℕ} (hy : 2 ≤ y)
    (hC : C ⊆ (Ioc y Z).filter Nat.Prime) {x a W : ℝ} (hx : 0 < x) (ha : x-W ≤ a)
    (hZ : (Z:ℝ) ≤ exp (x*2)) (A : ℝ)
    (hmass : reciprocalInterval (exp (x*(1/4))) (exp (x*2)) ≤ A)
    (d : ℕ → ℝ) (hd : ∀ p ∈ C, d p ≤ 2*log p) :
    (∑ p ∈ C, wt p * windowMass C (a-d p) (x-d p)) ≤
      (cap W*(P C/x))*(log y)⁻¹ + (16/x^2*P C)*A := by
  let B := C.filter (fun p : ℕ => x/4 < log p)
  have hp : ∀ p ∈ C, p.Prime := fun _ h => (mem_filter.mp (hC h)).2
  have hB : B ⊆ (Ioc ⌊exp (x*(1/4))⌋₊ ⌊exp (x*2)⌋₊).filter Nat.Prime := by
    intro p h
    obtain ⟨hc,hl⟩ := mem_filter.mp h
    have h0 : 0 < (p:ℝ) := by exact_mod_cast (hp p hc).pos
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.floor_lt (exp_pos _).le |>.mpr
      ((lt_log_iff_exp_lt h0).mp (by linarith)),Nat.le_floor ((by exact_mod_cast
        (mem_Ioc.mp (mem_filter.mp (hC hc)).1).2 : (p:ℝ) ≤ Z).trans hZ)⟩,hp p hc⟩
  have hW : (∑ p ∈ C, wt p) ≤ (log y)⁻¹ := (sum_le_sum_of_subset_of_nonneg hC
    (fun _ _ _ => by unfold wt; positivity)).trans (finite_displacement_tail hy Z)
  have hFar : (∑ p ∈ B, (p:ℝ)⁻¹) ≤ A := (sum_le_sum_of_subset_of_nonneg hB
    (fun _ _ _ => by positivity)).trans hmass
  have hs : 0 ≤ cap W*(P C/x) := mul_nonneg (cap_pos W).le (div_nonneg (P_pos C).le hx.le)
  have ht : 0 ≤ 16/x^2*P C := mul_nonneg (by positivity) (P_pos C).le
  calc
    _ ≤ ∑ p ∈ C, (cap W*(P C/x)*wt p + (16/x^2*P C)*(if x/4 < log p then (p:ℝ)⁻¹ else 0)) := by
      apply sum_le_sum
      intro p hc
      have h0 : 0 < (p:ℝ) := by exact_mod_cast (hp p hc).pos
      have hw : 0 ≤ wt p := by unfold wt; positivity
      by_cases h : x/4 < log p
      · rw [if_pos h]
        refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg hs hw))
        have hl : 0 < log (p:ℝ) := by linarith
        have bound : wt p ≤ 16/x^2 * (p:ℝ)⁻¹ := by
          unfold wt
          field_simp [hx.ne',hl.ne',h0.ne']
          nlinarith [sq_nonneg (4*log (p:ℝ)-x),mul_pos (by linarith : 0 < 4*log (p:ℝ)-x)
            (by linarith : 0 < 4*log (p:ℝ)+x)]
        calc
          _ ≤ (16/x^2 * (p:ℝ)⁻¹)*P C := mul_le_mul bound (window_total C hp ..)
            (sum_nonneg (fun _ _ => by positivity)) (by positivity)
          _ = _ := by ring
      · rw [if_neg h,mul_zero,add_zero,mul_comm]
        exact mul_le_mul_of_nonneg_right (local_cap C hx ha (by linarith [hd p hc])) hw
    _ = cap W*(P C/x)*(∑ p ∈ C, wt p) + (16/x^2*P C)*(∑ p ∈ B, (p:ℝ)⁻¹) := by
      rw [sum_add_distrib,← mul_sum,← mul_sum,sum_filter]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hW hs) (mul_le_mul_of_nonneg_left hFar ht)

private lemma square_le_wt : ∀ᶠ p : ℕ in atTop, ((p^2:ℕ):ℝ)⁻¹ ≤ wt p := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,eventually_ge_atTop 2] with p hp h2
  have h1 : 1 < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hl := log_pos h1
  change ‖log (p:ℝ) ^ (2:ℝ)‖ ≤ 1 * ‖(p:ℝ) ^ (1:ℝ)‖ at hp
  rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.rpow_natCast,Real.rpow_one,one_mul,
    Real.norm_eq_abs,abs_of_pos (by positivity),Real.norm_eq_abs,abs_of_pos (by linarith)] at hp
  rw [wt,one_div,Nat.cast_pow,pow_two (p:ℝ)]
  exact inv_anti₀ (mul_pos (by linarith) (sq_pos_of_pos hl)) (mul_le_mul_of_nonneg_left hp (by linarith))

theorem old_bad_negligible_of_width (W : ℝ) {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ Z : ℕ, (Z:ℝ) ≤ exp (x*2) →
    ∀ C ⊆ (Ioc y Z).filter Nat.Prime, ∀ a : ℝ, x-W ≤ a →
      recMass (badWindow C a x δ (fun p => c/log p^2)) ≤ ε*(P C/x) := by
  let B := 1+δ⁻¹*c
  have hB : 0 < B := by dsimp [B]; positivity
  let A := log (2/(1/4:ℝ))+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hmass := (dilated_window_mass (a:=(1/4:ℝ)) (b:=2) (by norm_num) (by norm_num)).eventually
    (gt_mem_nhds (show log (2/(1/4:ℝ)) < A by dsimp [A]; linarith))
  have ly := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have near := (ly.inv_tendsto_atTop.const_mul (B*cap W)).eventually (gt_mem_nhds (show B*cap W*0 < ε/2 by linarith))
  have far := ((tendsto_inv_atTop_zero : Tendsto (fun x:ℝ => x⁻¹) atTop (𝓝 0)).const_mul
    (B*16*A)).eventually (gt_mem_nhds (show B*16*A*0 < ε/2 by linarith))
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp square_le_wt
  filter_upwards [near,eventually_ge_atTop p₀,eventually_ge_atTop 2] with y hy hp hy2
  filter_upwards [far,hmass,eventually_gt_atTop 0] with x hx hM hx0
  intro Z hZ C hC a ha
  have hpC : ∀ p ∈ C, p.Prime := fun _ h => (mem_filter.mp (hC h)).2
  let V := cap W*(P C/x)*(log y)⁻¹ + (16/x^2*P C)*A
  let window (d : ℝ) := windowMass C (a-d) (x-d)
  have wpos (d : ℝ) : 0 ≤ window d := sum_nonneg (fun _ _ => by positivity)
  have line (d : ℕ → ℝ) (hd : ∀ p ∈ C, d p ≤ 2*log p) :
      (∑ p ∈ C, wt p*window (d p)) ≤ V := wt_window hy2 hC hx0 ha hZ A hM.le d hd
  have sq : (∑ p ∈ C, ((p^2:ℕ):ℝ)⁻¹*window (log (p^2:ℕ))) ≤ V := by
    apply le_trans _ (line (fun p => log (p^2:ℕ)) (fun p _ => by simp [Nat.cast_pow,log_pow]))
    exact sum_le_sum (fun p h => mul_le_mul_of_nonneg_right (hp₀ _ (hp.trans
      (mem_Ioc.mp (mem_filter.mp (hC h)).1).1.le)) (wpos _))
  have disp : (∑ p ∈ C, c/log p^2*((p:ℝ)⁻¹*window (log p))) ≤ c*V := by
    have eq : (∑ p ∈ C, c/log p^2*((p:ℝ)⁻¹*window (log p))) =
        c * ∑ p ∈ C, wt p*window (log p) := by
      rw [mul_sum]; apply sum_congr rfl; intro p _; simp [wt,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
    rw [eq]
    exact mul_le_mul_of_nonneg_left (line (fun p => log p) (fun p _ => by linarith [log_natCast_nonneg p])) hc
  have hb := bad_window_bound C hpC a x hδ (fun p => c/log p^2) (fun p _ => div_nonneg hc (sq_nonneg _))
  apply hb.trans ((add_le_add sq (mul_le_mul_of_nonneg_left disp (inv_nonneg.mpr hδ.le))).trans _)
  change B*cap W*(log (y:ℝ))⁻¹ < ε/2 at hy
  change B*16*A*x⁻¹ < ε/2 at hx
  have h := add_le_add hy.le hx.le
  have hn := mul_le_mul_of_nonneg_right h (div_nonneg (P_pos C).le hx0.le)
  calc
    V+δ⁻¹*(c*V) = (B*cap W*(log y)⁻¹+B*16*A*x⁻¹)*(P C/x) := by dsimp [V,B]; ring
    _ ≤ _ := by simpa only [add_halves] using hn

theorem old_bad_negligible {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ᶠ x : ℝ in atTop, ∀ Z : ℕ, (Z:ℝ) ≤ exp (x*2) →
    ∀ C ⊆ (Ioc y Z).filter Nat.Prime, ∀ a : ℝ, x-1 ≤ a →
      recMass (badWindow C a x δ (fun p => c/log p^2)) ≤ ε*(P C/x) :=
  old_bad_negligible_of_width 1 hc hδ hε

end

end Erdos490Transfer
end


/- Cells -/
section
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
end


/- PrimeCells -/
section
open Finset Filter Real Asymptotics

open scoped Topology Chebyshev

namespace Erdos490PrimeCells

theorem sharp_reciprocal_error (primeEstimate : EffectivePrimeEstimate) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Mertens.E₂p x| ≤ K / log x ^ 3 := by
  obtain ⟨C,hC,h⟩ := primeEstimate
  exact ⟨3*C,by positivity,mertens_error_from_theta hC.le h⟩

private theorem before_succ_eq_mertens (n : ℕ) :
    reciprocalBefore (n+1) = log (log n) + Mertens.M + Mertens.E₂p n := by
  have h := Mertens.sum_prime_div_eq (n : ℝ)
  rw [Nat.floor_natCast] at h
  rw [← h, reciprocalBefore,Nat.range_succ_eq_Icc_zero]
  simp only [Finset.sum_filter,one_div]
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp

theorem cell_displacement (primeEstimate : EffectivePrimeEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ p : ℕ in atTop, p.Prime →
      ∀ v ∈ Set.Icc (boundary Mertens.M p) (boundary Mertens.M (p+1)),
        |v - log p| ≤ C / log p ^ 2 := by
  obtain ⟨K,hK,h⟩ := (sharp_reciprocal_error primeEstimate)
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

end Erdos490PrimeCells
end


/- SparseStrip -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490

noncomputable section

open Classical

open scoped Topology

private lemma finite_peak (S T : Finset ℕ) (w J : ℝ) (hJ : 0 ≤ J) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧ ∀ a : Integers S, logN a ≤ J →
      F T (w-logN a) ≤ F T (w-v) := by
  let choices := semigroup S ⌊exp J⌋₊
  have h1 : 1 ∈ choices := mem_semigroup.mpr ⟨by simp [Active,Nat.mem_factoredNumbers],
    Nat.le_floor (by simpa using Real.one_le_exp hJ)⟩
  obtain ⟨u,hu,hm⟩ := choices.exists_max_image (fun x => F T (w-log x)) ⟨1,h1⟩
  have hu0 := Nat.pos_of_ne_zero (mem_semigroup.mp hu).1.1
  refine ⟨log u,log_natCast_nonneg _,(log_le_iff_le_exp (by exact_mod_cast hu0)).mpr
    ((Nat.le_floor_iff (exp_pos _).le).mp (mem_semigroup.mp hu).2),?_⟩
  intro a ha
  exact hm _ (mem_semigroup.mpr ⟨a.property,Nat.le_floor ((log_le_iff_le_exp (nat_pos a)).mp ha)⟩)

private theorem sparse_finite_bound {S T : Finset ℕ} (hd : Disjoint S T)
    {H h J L : ℝ} (hL : 0 < L) (hsize : 4*H ≤ L) (hh : |h| ≤ H) (hJ : 0 ≤ J) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧
      F (S ∪ T) (L+h) / P S ≤ F T (L+h-v) +
        (4*K₀*P T/L)*moment S*exp (-J/2) + moment S*exp (-L/4) := by
  obtain ⟨v,hv0,hv,hmax⟩ := finite_peak S T (L+h) J hJ
  let M := 4*K₀*P T/L
  have hM : 0 ≤ M := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) K₀_pos.le) (P_pos _).le) hL.le
  let coef := M*exp (-J/2)+exp (-L/4)
  have hc : 0 ≤ coef := add_nonneg (mul_nonneg hM (exp_pos _).le) (exp_pos _).le
  have point (a : Integers S) :
      F T (L+h-logN a) ≤ F T (L+h-v) + exp (logN a/2)*coef := by
    have hpos := F_nonneg T (L+h-v)
    by_cases near : logN a ≤ J
    · exact (hmax a near).trans (le_add_of_nonneg_right (mul_nonneg (exp_pos _).le hc))
    by_cases mid : logN a ≤ L/2
    · have h4 : L/4 ≤ L+h-logN a := by linarith [(abs_le.mp hh).1]
      have hcut : 0 < L+h-logN a := by linarith
      have hcap : F T (L+h-logN a) ≤ M := (counting_bound _ _ hcut).trans
        ((div_le_div_iff₀ hcut hL).mpr (by nlinarith [mul_nonneg (mul_nonneg K₀_pos.le (P_pos T).le) (show 0 ≤ 4*(L+h-logN a)-L by linarith)]))
      have e : 1 ≤ exp (logN a/2)*exp (-J/2) := by rw [← exp_add]; apply one_le_exp; linarith
      dsimp only [coef]
      nlinarith only [hcap,hpos,mul_le_mul_of_nonneg_left e hM,mul_nonneg (exp_pos (logN a/2)).le (exp_pos (-L/4)).le]
    · have e : 1 ≤ exp (logN a/2)*exp (-L/4) := by rw [← exp_add]; apply one_le_exp; linarith
      dsimp only [coef]
      nlinarith only [F_le_one T (L+h-logN a),e,hpos,mul_nonneg (exp_pos (logN a/2)).le (mul_nonneg hM (exp_pos (-J/2)).le)]
  have hsum := (harmonic_probability S).mul_right (F T (L+h-v))
  have hsum' := (half_moment S).hasSum.mul_right coef
  have htot := hasSum_le (fun a : Integers S => by
    simpa only [mul_add,mul_assoc] using mul_le_mul_of_nonneg_left (point a) (hnonneg a))
    (avg_summable (D:=S) (f:=fun x => F T (L+h-x)) (M:=1) (fun _ => ⟨F_nonneg ..,F_le_one ..⟩)).hasSum
    (hsum.add hsum')
  refine ⟨v,hv0,hv,?_⟩
  rw [normalized_convolution hd,mul_div_cancel_left₀ _ (P_pos S).ne']
  change _ ≤ F T (L+h-v)+M*moment S*exp (-J/2)+moment S*exp (-L/4)
  change _ ≤ 1*F T (L+h-v)+moment S*coef at htot
  simpa only [one_mul,coef,mul_add,← mul_assoc,mul_comm (moment S) M,add_assoc] using htot

theorem sparse_strip (S : Finset ℕ) (H ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ L : ℝ in atTop, ∀ T : Finset ℕ, Disjoint S T →
      ∀ h : ℝ, |h| ≤ H → ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧
        F (S ∪ T) (L+h)/P S ≤ F T (L+h-v) + ε*(P T/L) := by
  have halfExp : Tendsto (fun x : ℝ => exp (-x/2)) atTop (𝓝 0) := by
    apply tendsto_exp_atBot.comp
    simpa only [neg_div,Function.comp_def,id_eq] using (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2)))
  have small := halfExp.const_mul (4*K₀*moment S)
  rw [mul_zero] at small
  obtain ⟨J,hnear,hJ⟩ := ((small.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop 0)).exists
  refine ⟨J,hJ,?_⟩
  have hquarter : Tendsto (fun L : ℝ => L/4) atTop atTop := tendsto_id.atTop_div_const (by norm_num)
  have tail : Tendsto (fun L : ℝ => L*(moment S*exp (-L/4))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hquarter).const_mul (4*moment S)
    simpa only [mul_zero] using h.congr (fun x => by
      dsimp [Function.comp_def]; rw [pow_one,neg_div]; ring)
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ge_atTop (4*H),
    tail.eventually (gt_mem_nhds (half_pos hε))] with L hL hH htail
  intro T hd h hh
  obtain ⟨v,hv,hv',hbound⟩ := sparse_finite_bound hd hL hH hh hJ
  refine ⟨v,hv,hv',hbound.trans ?_⟩
  change 4*K₀*moment S*exp (-J/2) < ε/2 at hnear
  change L*(moment S*exp (-L/4)) < ε/2 at htail
  have hp := P_pos T
  have h1 := one_le_P T
  have h2 := mul_le_mul_of_nonneg_right hnear.le hp.le
  have h3 := le_mul_of_one_le_right (half_pos hε).le h1
  apply (mul_le_mul_iff_of_pos_left hL).mp
  simp only [neg_div] at h2 htail
  field_simp [hL.ne']
  nlinarith only [h2,htail,h3]

end

end Erdos490Transfer
end


/- StrippedProfiles -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490

noncomputable section

open Classical

lemma P_split {C S : Finset ℕ} (hs : S ⊆ C) : P C = P S * P (C \ S) := by
  rw [← P_union (disjoint_left.mpr (fun {_} hx hy => (mem_sdiff.mp hy).2 hx)),
    union_sdiff_of_subset hs]

private theorem sparse_pool (pool : Finset ℕ) (H η : ℝ) (he : 0 < η) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ L : ℝ in atTop, ∀ S ⊆ pool, ∀ C : Finset ℕ, S ⊆ C →
      ∀ h : ℝ, |h| ≤ H → ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧
        F C (L+h) ≤ P S * F (C \ S) (L+h-v) + η*(P C/L) := by
  choose cut hc hlim using (fun S : Finset ℕ => sparse_strip S H η he)
  let J := ∑ S ∈ pool.powerset, cut S
  refine ⟨J,sum_nonneg (fun S _ => hc S),?_⟩
  filter_upwards [(eventually_all_finset pool.powerset).mpr (fun S _ => hlim S)] with L hL
  intro S hS C hs h hh
  have dis : Disjoint S (C \ S) := disjoint_left.mpr (fun {_} hx hy => (mem_sdiff.mp hy).2 hx)
  have hm := mem_powerset.mpr hS
  obtain ⟨v,h0,hv,hx⟩ := hL S hm _ dis h hh
  refine ⟨v,h0,hv.trans (single_le_sum (fun S _ => hc S) hm),?_⟩
  rw [union_sdiff_of_subset hs] at hx
  have hmul := (div_le_iff₀ (P_pos S)).mp hx
  rw [P_split hs]
  linarith only [hmul,
    show (F (C \ S) (L+h-v) + η*(P (C \ S)/L))*P S =
      P S * F (C \ S) (L+h-v) + η*(P S*P (C \ S)/L) by ring]

theorem sparse_common_peak (pool : Finset ℕ) (K : ℕ) (η : ℝ) (he : 0 < η) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ᶠ n : ℕ in atTop, ∀ C : Finset ℕ, ∀ S ⊆ pool, S ⊆ C →
      ∃ z : ℝ, |z-log n| ≤ W ∧ ∀ i < K, density C n (i+1) ≤
        P S*F (C \ S) z + η*(P C/log n) := by
  let H := log (K+1:ℕ)
  have hH : 0 ≤ H := log_natCast_nonneg _
  obtain ⟨J,hJ,hl⟩ := sparse_pool pool H η he
  refine ⟨H+J,by positivity,?_⟩
  filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hl,
    eventually_gt_atTop (0:ℕ)] with n hL hn
  intro C S hS hs
  obtain ⟨i,hi,hmax⟩ := (range (K+1)).exists_max_image (fun i => density C n (i+1))
    ⟨0,mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hih : |-(log (i+1:ℕ))| ≤ H := by
    rw [abs_neg,abs_of_nonneg (log_natCast_nonneg _)]
    apply log_le_log (by positivity)
    exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hi))
  obtain ⟨v,hv0,hv,hval⟩ := hL S hS C hs _ hih
  let z := log (n:ℝ)-log (i+1:ℕ)-v
  refine ⟨z,?_,?_⟩
  · dsimp [z]
    have hi0 := log_natCast_nonneg (i+1)
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hih).1]
  · intro j hj
    simp only [Function.comp_apply,← sub_eq_add_neg] at hval
    rw [shifted_density (u:=i+1) C hn (by omega)] at hval
    exact (hmax j (mem_range.mpr (by omega))).trans hval

theorem removed_mass {Y n} (c : Colors Y n) {pool : Finset ℕ} (hp : pool ⊆ primes Y n) :
    P (pool ∩ c.red) * P (pool ∩ c.blue) = P pool := by
  rw [← P_union (c.separate.mono inter_subset_right inter_subset_right)]
  congr 1
  rw [← inter_union_distrib_left,c.cover,inter_eq_left.mpr hp]

end

end Erdos490Transfer
end


/- LargeLabelTransfer -/
section
namespace Erdos490Transfer

open Finset Filter Shift490 Real

noncomputable section

open Classical

def low (pool C : Finset ℕ) := pool ∩ C

def roughColor (pool C : Finset ℕ) := C \ low pool C

def RoughFlat (N : ℕ → ℕ) (R : ℕ → Finset ℕ) : Prop :=
  ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ h : ℝ, |h| ≤ H →
    |F (R k) (log (N k)+h) - F (R k) (log (N k))| ≤ ε*(P (R k)/log (N k))

def LargeLabelRecovery : Prop :=
  ∀ Y K, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ P₀ : ℕ, Y ≤ P₀ ∧
    ∀ N : ℕ → ℕ, StrictMono N → ∀ (c : ∀ k, Colors Y (N k)) (b : Bool),
    let pool := primes Y P₀
    let Q := fun k => roughColor pool (pick (c k) (!b))
    let R := fun k => roughColor pool (pick (c k) b)
    RoughFlat N R → ∀ peak : ℕ → ℝ, (∃ W : ℝ, ∀ᶠ k in atTop, |peak k-log (N k)| ≤ W) →
      ∃ᶠ k in atTop, 2 ≤ N k ∧ ∃ z : ℝ, 0 < z ∧ (1-ε)*log (N k) ≤ z ∧
        ∃ d : (m : ℕ) → Colors Y m,
        (∀ i < K, ∀ᶠ m : ℕ in atTop, F (Q k) (peak k) ≤
          log m/z*density (pick (d m) (!b)) m (i+1) + ε*(P (Q k)/log (N k))) ∧
        (∀ j < K, ∀ᶠ m : ℕ in atTop, F (R k) (log (N k)) ≤
          (P pool)⁻¹*density (pick (d m) b) m (j+1) + ε*(P (R k)/log (N k)))

theorem rough_flat_of_stable {Y N c b} (st : Stable (Y:=Y) N c b)
    (pool : Finset ℕ) (hp : ∀ p ∈ pool, p.Prime) :
    RoughFlat N (fun k => roughColor pool (pick (c k) b)) := by
  intro H hH ε he
  filter_upwards [stable_strip st pool hp H (ε/2) hH (half_pos he)] with k hk
  intro h hh
  let S := low pool (pick (c k) b)
  have step := hk S inter_subset_left inter_subset_right
  have hi := abs_le.mp (step h hh)
  have h0 := abs_le.mp (step 0 (by simpa using hH))
  rw [add_zero] at h0
  unfold roughColor
  rw [abs_le]
  constructor <;> linarith

private lemma combine {p x y f t η E M : ℝ} (hp : 0 < p) (he : p*E=M)
    (hx : x ≤ p*f+η*M) (hf : f ≤ t*y+η*E) :
    x ≤ (p*t)*y + (2*η)*M := by
  have h := mul_le_mul_of_nonneg_left hf hp.le
  nlinarith only [hx,h,congrArg (η * ·) he]

theorem sampled_of_large_labels (labels : LargeLabelRecovery) : SampledRecovery := by
  intro Y K θ hθ hθ1 N hN c b st
  let η := θ/2
  have hη : 0 < η := half_pos hθ
  have heq : 2*η=θ := by dsimp [η]; ring
  obtain ⟨P₀,_,build⟩ := labels Y K η hη (by dsimp [η]; linarith)
  let pool := primes Y P₀
  have hp : ∀ p ∈ pool, p.Prime := fun p h => (mem_filter.mp h).2
  let Q (k) := pick (c k) (!b)
  let R (k) := pick (c k) b
  let q (k) := low pool (Q k)
  let r (k) := low pool (R k)
  let L (k) := log (N k:ℝ)
  obtain ⟨W,_,hpeak⟩ := sparse_common_peak pool K η hη
  let good (k : ℕ) (z : ℝ) := |z-L k| ≤ W ∧ ∀ i < K, density (Q k) (N k) (i+1) ≤
    P (q k)*F (roughColor pool (Q k)) z + η*(P (Q k)/L k)
  have existsPeak : ∀ᶠ k in atTop, ∃ z, good k z := by
    filter_upwards [hN.tendsto_atTop.eventually hpeak] with k hk
    exact hk _ _ inter_subset_left inter_subset_right
  let peak (k : ℕ) := if h : ∃ z, good k z then h.choose else L k
  have chosen : ∀ᶠ k in atTop, good k (peak k) := existsPeak.mono (fun k hk => by
    simp only [peak,dif_pos hk]; exact hk.choose_spec)
  have late := build N hN c b (rough_flat_of_stable st pool hp) peak ⟨W,chosen.mono (fun _ h => h.1)⟩
  have old := stable_strip st pool hp 0 η le_rfl hη
  apply (late.and_eventually ((chosen.and old).and (hN.tendsto_atTop.eventually_ge_atTop P₀))).mono
  rintro k ⟨⟨hn,z,hz,hclose,d,hs,hr⟩,⟨hk,hb⟩,hP⟩
  have hL : 0 < L k := log_pos (by exact_mod_cast (show 1 < N k by omega))
  have hpool : pool ⊆ primes Y (N k) := fun p h => mem_filter.mpr ⟨mem_Icc.mpr
    ⟨(mem_Icc.mp (mem_filter.mp h).1).1,(mem_Icc.mp (mem_filter.mp h).1).2.trans hP⟩,(mem_filter.mp h).2⟩
  have masses : P (q k)*P (r k)=P pool := by
    have h := removed_mass (c k) hpool
    cases b <;> simpa [q,r,Q,R,low,pick,mul_comm] using h
  have split (C : Finset ℕ) : P (low pool C)*(P (roughColor pool C)/L k) = P C/L k := by
    rw [roughColor,← mul_div_assoc,← P_split (show low pool C ⊆ C from inter_subset_right)]
  refine ⟨hn,z,P (q k),hz,?_,P_pos _,d,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (by dsimp [η]; linarith) hL.le).trans hclose
  · intro i hi
    filter_upwards [hs i hi] with m hm
    have h := combine (P_pos _) (split (Q k)) (hk.2 i hi) hm
    rw [heq] at h
    rw [← pick_scale]
    exact h
  · have hh := hb (r k) inter_subset_left inter_subset_right 0 (by simp)
    rw [add_zero] at hh
    have hb0 := (abs_le.mp hh).1
    have hold : density (R k) (N k) 1 ≤
        P (r k)*F (roughColor pool (R k)) (L k) + η*(P (R k)/L k) := by
      have hden := shifted_density (R k) (by omega : 0 < N k) (by decide : 0 < 1)
      simp only [Nat.cast_one,log_one,sub_zero] at hden
      rw [← hden]
      change -(η*(P (roughColor pool (R k))/L k)) ≤
        F (roughColor pool (R k)) (L k) - (P (r k))⁻¹*F (R k) (L k) at hb0
      have h := mul_le_mul_of_nonneg_left hb0 (P_pos (r k)).le
      rw [mul_sub,← mul_assoc,mul_inv_cancel₀ (P_pos _).ne',one_mul] at h
      change F (R k) (L k) ≤ _
      nlinarith only [h,congrArg (η * ·) (split (R k))]
    intro j hj
    filter_upwards [hr j hj] with m hm
    have h := combine (P_pos _) (split (R k)) hold hm
    have gain : P (r k)*(P pool)⁻¹=(P (q k))⁻¹ := by
      rw [← masses]; field_simp [(P_pos (q k)).ne',(P_pos (r k)).ne']
    rw [gain,heq] at h
    rw [← pick_scale]
    exact h

end

end Erdos490Transfer
end


/- OldStableMass -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490PrimeCells

noncomputable section

open Classical

def goodWindow (C : Finset ℕ) (a d δ : ℝ) (e : ℕ → ℝ) :=
  oldWindow C a d \ badWindow C a d δ e

lemma good_mass (C : Finset ℕ) (a d δ : ℝ) (e : ℕ → ℝ) :
    recMass (goodWindow C a d δ e) = windowMass C a d - recMass (badWindow C a d δ e) :=
  (sub_eq_iff_eq_add.mpr (sum_sdiff (show badWindow C a d δ e ⊆ oldWindow C a d from filter_subset ..)).symm).symm

theorem stable_good_strips {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hd : δ < 1/2) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ N : ℕ → ℕ, StrictMono N → ∀ C : ℕ → Finset ℕ,
      (∀ k, C k ⊆ (Ioc y (N k)).filter Nat.Prime) → RoughFlat N C →
      ∀ H : ℝ, 0 ≤ H → ∀ᶠ k in atTop, ∀ v : ℝ, |v-log (N k)| ≤ H →
        (1-2*δ)*F (C k) (log (N k)) - ε*(P (C k)/log (N k)) ≤
          recMass (goodWindow (C k) (v-1+δ) (v-δ) δ (fun p => c/log p^2)) := by
  filter_upwards [old_bad_negligible hc hδ (show 0 < ε/4 by positivity)] with y hy
  intro N hN C hC flat H hH
  obtain ⟨X,hX⟩ := eventually_atTop.mp hy
  have lim := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop)
  have scale := flat (H+2) (by linarith) (ε/8) (by positivity)
  filter_upwards [lim.eventually_ge_atTop (max X 1+2*H+4),scale,
    hN.tendsto_atTop.eventually_gt_atTop 0] with k hk hflat hn
  let L := log (N k:ℝ)
  change max X 1+2*H+4 ≤ L at hk
  intro v hv
  change |v-L| ≤ H at hv
  have h1 := (abs_le.mp hv).1
  have h2 := (abs_le.mp hv).2
  have hlarge : 1+2*H+4 ≤ L := by linarith [le_max_right X (1:ℝ)]
  have hx : X ≤ v-δ := by linarith [le_max_left X (1:ℝ)]
  have hL : 0 < L := by linarith
  have hhalf : L/2 ≤ v-δ := by linarith
  have hvp : 0 < v-δ := by linarith
  have hnexp : (N k:ℝ) ≤ exp ((v-δ)*2) := by
    rw [← log_le_iff_le_exp (by exact_mod_cast hn)]
    change L ≤ _; linarith
  have bad := hX (v-δ) hx (N k) hnexp (C k) (hC k) (v-1+δ) (by linarith)
  have win := window_flat (C k) (by linarith : 0 ≤ v-1+δ) (by linarith : v-1+δ ≤ v-δ)
    (r:=F (C k) L) (e:=ε/8*(P (C k)/L)) (by
      intro t ht
      have h := hflat (t-L) (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩)
      change |F (C k) (L+(t-L))-F (C k) L| ≤ _ at h
      rwa [show L+(t-L)=t by ring] at h)
  have err : P (C k)/(v-δ) ≤ 2*(P (C k)/L) := by
    rw [← mul_div_assoc,div_le_div_iff₀ hvp hL]
    nlinarith only [mul_le_mul_of_nonneg_left hhalf (P_pos (C k)).le]
  have pos : 0 ≤ ε*(P (C k)/L) := mul_nonneg hε.le (div_nonneg (P_pos _).le hL.le)
  rw [good_mass]
  change (1-2*δ)*F (C k) L - ε*(P (C k)/L) ≤ _
  have low := (abs_le.mp win).1
  nlinarith only [low,bad,mul_le_mul_of_nonneg_left err (show 0 ≤ ε/4 by positivity),
    pos,mul_nonneg hδ.le pos]

end

end Erdos490Transfer
end


/- OldSparseMass -/
section
namespace Erdos490Transfer

open Finset Real Filter Shift490

open scoped Topology

noncomputable section

open Classical

private lemma window_count {C : Finset ℕ} {a z : ℝ} (ha : a ≤ z) :
    (semigroup C ⌊exp z⌋₊).card =
      (semigroup C ⌊exp a⌋₊).card + (oldWindow C a z).card := by
  let A := semigroup C ⌊exp a⌋₊
  let T := semigroup C ⌊exp z⌋₊
  have sub : A ⊆ T := fun m h => mem_semigroup.mpr ⟨(mem_semigroup.mp h).1,
    (mem_semigroup.mp h).2.trans (Nat.floor_mono (exp_le_exp.mpr ha))⟩
  have eq : oldWindow C a z = T \ A := by
    apply Finset.ext
    intro m
    rw [mem_oldWindow,Finset.mem_sdiff]
    simp only [T,A,mem_semigroup]
    constructor
    · rintro ⟨hm,hl,hr⟩
      have hm0 := nat_pos (⟨m,hm⟩ : Integers C)
      refine ⟨⟨hm,Nat.le_floor ((log_le_iff_le_exp hm0).mp hr)⟩,fun h => hl.not_ge ?_⟩
      exact (log_le_iff_le_exp hm0).mpr ((Nat.le_floor_iff (exp_pos _).le).mp h.2)
    · rintro ⟨⟨hm,hr⟩,hn⟩
      have hm0 := nat_pos (⟨m,hm⟩ : Integers C)
      refine ⟨hm,lt_of_not_ge (fun h => hn ⟨hm,Nat.le_floor ((log_le_iff_le_exp hm0).mp h)⟩),
        (log_le_iff_le_exp hm0).mpr ((Nat.le_floor_iff (exp_pos _).le).mp hr)⟩
  rw [eq,card_sdiff_of_subset sub]
  have := card_le_card sub
  change T.card=A.card+(T.card-A.card)
  omega

theorem sparse_good_finite (C : Finset ℕ) {a z δ : ℝ} (ha : a ≤ z) (e : ℕ → ℝ) :
    F C z ≤ exp (a-z)*F C a + recMass (badWindow C a z δ e)
      + exp (-z)*(goodWindow C a z δ e).card := by
  let B := badWindow C a z δ e
  have sub : B ⊆ oldWindow C a z := filter_subset ..
  have hbad : exp (-z)*B.card ≤ recMass B := by
    rw [mul_comm,← nsmul_eq_mul,← sum_const]
    apply sum_le_sum
    intro m hm
    obtain ⟨hc,_,hr⟩ := mem_oldWindow.mp (sub hm)
    have h := (log_le_iff_le_exp (nat_pos (⟨m,hc⟩ : Integers C))).mp hr
    rw [exp_neg]
    exact inv_anti₀ (nat_pos (⟨m,hc⟩ : Integers C)) h
  have hgood : (oldWindow C a z).card = B.card+(goodWindow C a z δ e).card := by
    rw [goodWindow,card_sdiff_of_subset sub]
    have := card_le_card sub
    change _=B.card+(_-B.card)
    omega
  rw [F_eq_semigroup,F_eq_semigroup,window_count ha,hgood,Nat.cast_add,Nat.cast_add,
    ← mul_assoc,← exp_add,show a-z+ -a = -z by ring]
  change _ ≤ _ + recMass B + _
  linarith only [hbad]

theorem sparse_good_window {c δ ε : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ y : ℕ in atTop, ∀ᶠ z : ℝ in atTop,
      ∀ N : ℕ, (N:ℝ) ≤ exp (z*2) → ∀ C ⊆ (Ioc y N).filter Nat.Prime,
      F C z - ε*(P C/z) ≤ exp (-z)*(goodWindow C (z-B) z δ (fun p => c/log p^2)).card := by
  have lim := (tendsto_exp_neg_atTop_nhds_zero.const_mul (2*K₀)).eventually
    (gt_mem_nhds (show 2*K₀*0 < ε/2 by linarith))
  obtain ⟨B,hB,hcut⟩ := ((eventually_gt_atTop (0:ℝ)).and lim).exists
  refine ⟨B,hB,?_⟩
  filter_upwards [old_bad_negligible_of_width B hc hδ (show 0 < ε/2 by positivity)] with y hy
  filter_upwards [hy,eventually_gt_atTop (2*B)] with z hz hzB
  intro N hN C hC
  have bad := hz N hN C hC (z-B) le_rfl
  have half : 0 < z-B := by linarith
  have pos : 0 < z := by linarith
  have count : F C (z-B) ≤ 2*(K₀*P C/z) := (counting_bound _ _ half).trans (by
    rw [← mul_div_assoc,div_le_div_iff₀ half pos]
    nlinarith only [mul_le_mul_of_nonneg_left hzB.le (mul_nonneg K₀_pos.le (P_pos C).le)])
  have low := sparse_good_finite C (by linarith : z-B ≤ z) (δ:=δ) (fun p => c/log p^2)
  rw [show z-B-z = -B by ring] at low
  change 2*K₀*exp (-B) < ε/2 at hcut
  have htail : exp (-B)*F C (z-B) ≤ ε/2*(P C/z) := calc
    _ ≤ exp (-B)*(2*(K₀*P C/z)) := mul_le_mul_of_nonneg_left count (exp_pos _).le
    _ = (2*K₀*exp (-B))*(P C/z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcut.le (div_nonneg (P_pos C).le pos.le)
  linarith only [low,bad,htail]

end

end Erdos490Transfer
end


/- LabelEmbedding -/
section
namespace Erdos490Transfer

open Finset

noncomputable section

open Classical

theorem extend_colors (Y m : ℕ) {Q R : Finset ℕ} (hd : Disjoint Q R) :
    ∃ c : Colors Y m, Q ∩ primes Y m ⊆ c.red ∧ R ∩ primes Y m ⊆ c.blue := by
  let A := Q ∩ primes Y m
  have sub : A ⊆ primes Y m := inter_subset_right
  refine ⟨⟨A,primes Y m \ A,union_sdiff_of_subset sub,
    disjoint_left.mpr (fun {_} hx hy => (mem_sdiff.mp hy).2 hx)⟩,Subset.rfl,?_⟩
  intro p hp
  exact mem_sdiff.mpr ⟨(mem_inter.mp hp).2,fun ha =>
    disjoint_left.mp hd (mem_inter.mp ha).1 (mem_inter.mp hp).1⟩

theorem complete_supports {Y m : ℕ} {Q R : Finset ℕ} (hd : Disjoint Q R)
    (hY : ∀ p ∈ Q ∪ R, Nat.Prime p → Y ≤ p) :
    ∃ c : Colors Y m, ∀ u : ℕ, semigroup Q (m/u) ⊆ semigroup c.red (m/u) ∧
      semigroup R (m/u) ⊆ semigroup c.blue (m/u) := by
  obtain ⟨c,hr,hb⟩ := extend_colors Y m hd
  have lift {D E : Finset ℕ} (hD : D ⊆ Q ∪ R) (keep : D ∩ primes Y m ⊆ E) (u : ℕ) :
      semigroup D (m/u) ⊆ semigroup E (m/u) := by
    intro z hz
    obtain ⟨ha,hl⟩ := mem_semigroup.mp hz
    refine mem_semigroup.mpr ⟨Nat.mem_factoredNumbers'.mpr ?_,hl⟩
    intro p hp hdv
    have hm := Nat.mem_factoredNumbers'.mp ha p hp hdv
    exact keep (mem_inter.mpr ⟨hm,mem_filter.mpr ⟨mem_Icc.mpr ⟨hY _ (hD hm) hp,
      (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.1) hdv).trans (hl.trans (Nat.div_le_self ..))⟩,hp⟩⟩)
  exact ⟨c,fun u => ⟨lift subset_union_left hr u,lift subset_union_right hb u⟩⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ValidLabels (cell : ι → Finset ℕ) (f : ι → ℕ) := ∀ i, f i = 1 ∨ f i ∈ cell i

def high (f : ι → ℕ) := ∏ i, f i

omit [DecidableEq ι] in

lemma high_active {cell : ι → Finset ℕ} {C : Finset ℕ}
    (prime : ∀ i p, p ∈ cell i → Nat.Prime p) (sub : ∀ i, cell i ⊆ C)
    {f : ι → ℕ} (hf : ValidLabels cell f) : Active C (high f) := by
  apply Nat.mem_factoredNumbers'.mpr
  intro p hp hd
  obtain ⟨i,_,hi⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  rcases hf i with h|h
  · exact (hp.not_dvd_one (h ▸ hi)).elim
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (prime i _ h)).mp hi
    exact sub i h

lemma high_injective {cell : ι → Finset ℕ} (prime : ∀ i p, p ∈ cell i → Nat.Prime p)
    (apart : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)) {f g : ι → ℕ}
    (hf : ValidLabels cell f) (hg : ValidLabels cell g) (eq : high f = high g) : f=g := by
  have identify {p} (i : ι) (hp : p ∈ cell i) {v : ι → ℕ} (hv : ValidLabels cell v)
      (hd : p ∣ high v) : p=v i := by
    have hpr := prime i p hp
    obtain ⟨j,_,hj⟩ := (hpr.prime.dvd_finsetProd_iff _).mp hd
    rcases hv j with h|h
    · exact (hpr.not_dvd_one (h ▸ hj)).elim
    · have he := (Nat.prime_dvd_prime_iff_eq hpr (prime j _ h)).mp hj
      have hij : i=j := by
        by_contra hne
        exact disjoint_left.mp (apart i j hne) hp (he ▸ h)
      simpa [hij] using he
  funext i
  rcases hf i with h|h
  · rcases hg i with h'|h'
    · exact h.trans h'.symm
    · exact (identify i h' hf (eq ▸ dvd_prod_of_mem g (mem_univ i))).symm
  · exact identify i h hg (eq ▸ dvd_prod_of_mem f (mem_univ i))

theorem label_mass (choices : ι → Finset ℕ) :
    (∑ f ∈ Fintype.piFinset choices, ((high f:ℕ):ℝ)⁻¹) =
      ∏ i, ∑ q ∈ choices i, (q:ℝ)⁻¹ := by
  rw [prod_univ_sum]
  simp [high,prod_inv_distrib]

end

end Erdos490Transfer
end


/- PrimeLabelMass -/
section
namespace Erdos490Transfer

open Filter Finset Real Erdos490PrimeCells

open scoped Topology

noncomputable section

open Classical

def newCell (b t : ℝ) (p : ℕ) :=
  (Ioc ⌊exp (t*boundary b p)⌋₊ ⌊exp (t*boundary b (p+1))⌋₊).filter Nat.Prime

lemma boundary_mono (b : ℝ) : Monotone (boundary b) := by
  apply monotone_nat_of_le_succ
  intro i
  unfold boundary
  rw [before_succ]
  apply exp_le_exp.mpr
  split_ifs <;> linarith [show (0:ℝ) ≤ (i:ℝ)⁻¹ by positivity]

lemma newCell_disjoint {b t : ℝ} (ht : 0 ≤ t) {p q : ℕ} (hne : p ≠ q) :
    Disjoint (newCell b t p) (newCell b t q) := by
  have ord {u v : ℕ} (hl : u < v) : Disjoint (newCell b t u) (newCell b t v) := by
    apply disjoint_left.mpr
    intro h hu hv
    have hend := (mem_Ioc.mp (mem_filter.mp hu).1).2
    have hstart := (mem_Ioc.mp (mem_filter.mp hv).1).1
    exact hstart.not_ge (hend.trans (Nat.floor_mono (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (boundary_mono b hl) ht))))
  rcases lt_or_gt_of_ne hne with h|h
  · exact ord h
  · exact (ord h).symm

def newProducts (b t : ℝ) (S : Finset ℕ) :=
  (Fintype.piFinset (fun p : S => newCell b t p)).image high

theorem newProducts_mass (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (b : ℝ) :
    Tendsto (fun t : ℝ => ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹)
      atTop (𝓝 (((∏ p ∈ S, p:ℕ):ℝ)⁻¹)) := by
  have one (p : S) : Tendsto (fun t : ℝ => ∑ q ∈ newCell b t p, (q:ℝ)⁻¹)
      atTop (𝓝 ((p.val:ℝ)⁻¹)) := by
    have hp := hS _ p.property
    have h := dilated_window_mass (a:=boundary b p) (b:=boundary b (p.val+1))
      (exp_pos _) (boundary_mono b (Nat.le_succ _))
    have hpos : 0 < boundary b p := exp_pos _
    have ratio : log (boundary b (p.val+1) / boundary b p) = (p.val:ℝ)⁻¹ := by
      rw [boundary_succ b hp,mul_div_cancel_left₀ _ hpos.ne',log_exp]
    rw [ratio] at h
    exact h
  have h := tendsto_finsetProd (univ : Finset S) (fun p _ => one p)
  have goalEq : (∏ p : S, (p.val:ℝ)⁻¹) = (((∏ p ∈ S, p:ℕ):ℝ)⁻¹) := by
    rw [prod_inv_distrib,Nat.cast_prod]
    congr 1
    exact prod_attach S (fun p => (p:ℝ))
  rw [← goalEq]
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [newProducts,sum_image]
  · exact (label_mass (fun p : S => newCell b t p)).symm
  · intro f hf g hg he
    apply high_injective (cell:=fun p : S => newCell b t p)
      (fun _ _ hq => (mem_filter.mp hq).2)
      (fun i j hne => newCell_disjoint ht (fun he => hne (Subtype.ext he))) _ _ he
    · exact fun i => Or.inr (Fintype.mem_piFinset.mp hf i)
    · exact fun i => Or.inr (Fintype.mem_piFinset.mp hg i)

end

end Erdos490Transfer
end


/- SegmentMass -/
section
open Filter Finset Real MeasureTheory Set Asymptotics

open scoped Topology

namespace Erdos490Smooth

open Shift490

noncomputable def smoothLabels (k : ℕ) (x : ℝ) := (Finset.Ioc k ⌊x⌋₊).filter Nat.Prime

noncomputable def smallProduct (k : ℕ) :=
  ∏ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, (1 - (p:ℝ)⁻¹)

private theorem smallProduct_pos (k : ℕ) : 0 < smallProduct k := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hp1)

theorem segment_product {k : ℕ} {x : ℝ} (hk : k ≤ ⌊x⌋₊) :
    P (smoothLabels k x) = smallProduct k / smallProduct ⌊x⌋₊ := by
  have h := prod_Ioc_consecutive (fun p : ℕ => if p.Prime then 1-(p:ℝ)⁻¹ else 1)
    (Nat.zero_le k) hk
  unfold P smoothLabels
  rw [Finset.filter_filter]
  simp only [and_self,Finset.prod_inv_distrib]
  have h1 : smallProduct k *
      (∏ p ∈ (Finset.Ioc k ⌊x⌋₊).filter Nat.Prime, (1-(p:ℝ)⁻¹)) = smallProduct ⌊x⌋₊ := by
    simpa only [smallProduct,Finset.prod_filter] using h
  rw [← h1]
  field_simp [(smallProduct_pos k).ne']

theorem smoothLabels_mass_limit (k : ℕ) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun t : ℝ => P (smoothLabels k (exp (t*w)))/t) atTop
      (𝓝 (exp eulerMascheroniConstant * smallProduct k * w)) := by
  have hlin := tendsto_id.atTop_mul_const hw
  have hxp : Tendsto (fun t : ℝ => exp (t*w)) atTop atTop := tendsto_exp_atTop.comp hlin
  have hE := ((isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp hxp
  have hlim := (tendsto_const_nhds (x := exp eulerMascheroniConstant * smallProduct k * w)
    (f := atTop)).mul hE.neg.rexp
  simp only [neg_zero,exp_zero,mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0,hxp.eventually_ge_atTop (k:ℝ),hxp.eventually_gt_atTop 1]
    with t ht hk hx
  rw [segment_product (Nat.le_floor hk)]
  have h := Mertens.prod_one_minus_div_prime_eq hx
  simp only [one_div,log_exp] at h
  change smallProduct ⌊exp (t*w)⌋₊ = _ at h
  dsimp only [Function.comp_apply]
  rw [h,exp_neg,exp_neg]
  field_simp

end Erdos490Smooth
end


/- TransplantColors -/
section
namespace Erdos490Transfer

open Finset Filter Real Erdos490PrimeCells Erdos490Smooth

noncomputable section

open Classical

def bands (b t : ℝ) (S : Finset ℕ) := S.biUnion (newCell b t)

lemma bands_disjoint (b : ℝ) {t : ℝ} (ht : 0 ≤ t) {S T : Finset ℕ}
    (h : Disjoint S T) : Disjoint (bands b t S) (bands b t T) := by
  apply disjoint_left.mpr
  intro v hs hr
  obtain ⟨p,hp,hv⟩ := mem_biUnion.mp hs
  obtain ⟨q,hq,hw⟩ := mem_biUnion.mp hr
  exact disjoint_left.mp (newCell_disjoint ht (fun h' => disjoint_left.mp h (h' ▸ hp) hq)) hv hw

lemma bands_above (b : ℝ) {t : ℝ} (ht : 0 ≤ t) {y : ℕ} {S : Finset ℕ}
    (hs : ∀ p ∈ S, y < p) {v} (hv : v ∈ bands b t S) :
    ⌊exp (t*boundary b (y+1))⌋₊ < v := by
  obtain ⟨p,hp,hv⟩ := mem_biUnion.mp hv
  exact lt_of_le_of_lt (Nat.floor_mono (exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (boundary_mono b (hs p hp)) ht))) (mem_Ioc.mp (mem_filter.mp hv).1).1

theorem transplant_colors {Y y n : ℕ} {S T : Finset ℕ} (h : Disjoint S T)
    (hs : ∀ p ∈ S, y < p) (hr : ∀ p ∈ T, y < p) (b : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hY : Y ≤ ⌊exp (t*boundary b (y+1))⌋₊+1) :
    let U := smoothLabels (Y-1) (exp (t*boundary b (y+1)))
    Disjoint (bands b t T) U ∧ ∃ c : Colors Y n, ∀ u : ℕ,
      semigroup (bands b t S) (n/u) ⊆ semigroup c.red (n/u) ∧
      semigroup (bands b t T ∪ U) (n/u) ⊆ semigroup c.blue (n/u) := by
  let U := smoothLabels (Y-1) (exp (t*boundary b (y+1)))
  have sep {D : Finset ℕ} (hd : ∀ p ∈ D, y < p) : Disjoint (bands b t D) U :=
    disjoint_left.mpr fun {_} h1 h2 =>
      (bands_above b ht hd h1).not_ge (mem_Ioc.mp (mem_filter.mp h2).1).2
  refine ⟨sep hr,complete_supports (disjoint_union_right.mpr ⟨bands_disjoint b ht h,sep hs⟩) ?_⟩
  intro v hv hp
  rcases mem_union.mp hv with hv|hv
  · exact hY.trans (bands_above b ht hs hv)
  rcases mem_union.mp hv with hv|hv
  · exact hY.trans (bands_above b ht hr hv)
  · have hl := (mem_Ioc.mp (mem_filter.mp hv).1).1
    change Y-1 < v at hl
    omega

theorem eventually_transplant_cutoff (Y y : ℕ) (b : ℝ) :
    ∀ᶠ t : ℝ in atTop, Y ≤ ⌊exp (t*boundary b (y+1))⌋₊+1 := by
  have lim := tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const (exp_pos (reciprocalBefore (y+1)-b)))
  filter_upwards [lim.eventually_ge_atTop (Y:ℝ)] with t ht
  exact (Nat.le_floor ht).trans (Nat.le_succ _)

end

end Erdos490Transfer
end


/- RedGood -/
section
namespace Erdos490Transfer

open Filter Finset Real Shift490 Erdos490Smooth Erdos490PrimeCells

noncomputable section

open Classical

def RedGoodRealization : Prop :=
  ∀ (C : Finset ℕ), (∀ p ∈ C, p.Prime) → ∀ c : ℝ,
    (∀ p ∈ C, ∀ v ∈ Set.Icc (boundary Mertens.M p) (boundary Mertens.M (p+1)),
      |v-log p| ≤ c/log p^2) →
    ∀ z B δ : ℝ, 0 < B → 0 < δ → 0 < z-B-δ →
    let G := goodWindow C (z-B) z δ (fun p => c/log p^2)
    G.Nonempty → ∃ x ∈ Set.Icc (z-B-δ) (z+δ), ∀ u : ℕ, 0 < u → ∀ η > 0,
      ∀ᶠ m : ℕ in atTop, exp (-2*δ)*exp (-z)*(G.card:ℝ) - η ≤
        (log m/x)*density (bands Mertens.M (log m/x) C) m u

private lemma red_absorb {F₀ G X a E θ : ℝ} (ha : 0 ≤ a) (hE : 0 ≤ E)
    (hcap : F₀ ≤ 2*K₀*E) (ho : F₀-2*a*E ≤ G) (hG : 0 ≤ G)
    (hr : exp (-2*a)*G-a*E ≤ X) (hsmall : (4*K₀+3)*a ≤ θ) :
    F₀ ≤ X+θ*E := by
  have hex : 1-2*a ≤ exp (-2*a) := by linarith [add_one_le_exp (-2*a)]
  by_cases h : F₀-2*a*E ≤ 0
  · have hX := mul_nonneg (exp_pos (-2*a)).le hG
    have h3 : 3*a ≤ θ := by nlinarith [mul_nonneg K₀_pos.le ha]
    nlinarith only [h,hr,hX,mul_le_mul_of_nonneg_right h3 hE]
  have low := mul_le_mul hex ho (le_of_not_ge h) (exp_pos _).le
  nlinarith only [low,hr,mul_le_mul_of_nonneg_left hcap (show 0 ≤ 2*a by positivity),
    mul_le_mul_of_nonneg_right hsmall hE,mul_nonneg (sq_nonneg a) hE]

theorem red_from_good (primeEstimate : EffectivePrimeEstimate) (realize : RedGoodRealization) {ε : ℝ} (hε : 0 < ε) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ᶠ y : ℕ in atTop, ∀ᶠ z : ℝ in atTop,
    ∀ N : ℕ, 0 < log (N:ℝ) → log N ≤ 2*z →
    ∀ C ⊆ (Ioc y N).filter Nat.Prime,
      ∃ x : ℝ, 0 < x ∧ |x-z| ≤ B' ∧ ∀ u : ℕ, 0 < u → ∀ᶠ m : ℕ in atTop,
      F C z ≤ (log m/x)*density (bands Mertens.M (log m/x) C) m u + ε*(P C/log N) := by
  let a := ε/(4*K₀+3)
  have denom : 0 < 4*K₀+3 := by linarith [K₀_pos]
  have ha : 0 < a := div_pos hε denom
  have hcoef : (4*K₀+3)*a = ε := by dsimp [a]; field_simp
  obtain ⟨c,hc,hdisp⟩ := (cell_displacement primeEstimate)
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp hdisp
  obtain ⟨B,hB,hy⟩ := sparse_good_window hc.le ha ha
  refine ⟨B+a,by positivity,?_⟩
  filter_upwards [hy,eventually_ge_atTop p₀] with y hy hy0
  filter_upwards [hy,eventually_gt_atTop (B+a)] with z hz hz0
  intro N hN hL C hC
  have nz : 0 < z := by linarith
  have hNp : 0 < (N:ℝ) := by
    by_contra! h
    have : N=0 := by exact_mod_cast (le_antisymm h (Nat.cast_nonneg _))
    simp [this] at hN
  have hnexp := (log_le_iff_le_exp hNp).mp hL
  have hl := hz N (by simpa [mul_comm] using hnexp) C hC
  let E := P C/log N
  let G := goodWindow C (z-B) z a (fun p => c/log p^2)
  have hE : 0 < E := div_pos (P_pos _) hN
  have ratio : P C/z ≤ 2*E := by
    dsimp [E]
    rw [← mul_div_assoc,div_le_div_iff₀ nz hN]
    nlinarith only [mul_le_mul_of_nonneg_left hL (P_pos C).le]
  have old : F C z-2*a*E ≤ exp (-z)*G.card := by
    change F C z-a*(P C/z) ≤ exp (-z)*G.card at hl
    linarith only [hl,mul_le_mul_of_nonneg_left ratio ha.le]
  have cap : F C z ≤ 2*K₀*E := (counting_bound C z nz).trans (by
    rw [mul_div_assoc]; nlinarith only [mul_le_mul_of_nonneg_left ratio K₀_pos.le])
  have pr : ∀ p ∈ C, p.Prime := fun _ h => (mem_filter.mp (hC h)).2
  by_cases nonempty : G.Nonempty
  · obtain ⟨x,hx,hr⟩ := realize C pr c (fun p h => hp₀ p (hy0.trans
      (mem_Ioc.mp (mem_filter.mp (hC h)).1).1.le) (pr _ h)) z B a hB ha (by linarith) nonempty
    refine ⟨x,by linarith [hx.1],abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
    intro u hu
    filter_upwards [hr u hu (a*E) (mul_pos ha hE)] with m hm
    apply red_absorb ha.le hE.le cap old (by positivity) _ hcoef.le
    simpa only [mul_assoc] using hm
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    rw [hempty,card_empty,Nat.cast_zero,mul_zero] at old
    refine ⟨z,nz,by simp; positivity,?_⟩
    intro u hu
    apply Eventually.of_forall
    intro m
    have nonneg : 0 ≤ (log (m:ℝ)/z)*density (bands Mertens.M (log m/z) C) m u :=
      mul_nonneg (div_nonneg (log_natCast_nonneg _) nz.le) (by unfold density; positivity)
    have h2 : 2*a ≤ ε := by nlinarith [mul_nonneg K₀_pos.le ha.le]
    linarith only [old,nonneg,mul_le_mul_of_nonneg_right h2 hE.le]

end

end Erdos490Transfer
end


/- BlueProducts -/
section
namespace Erdos490Transfer

open Finset Filter Real

noncomputable section

open Classical

theorem newProducts_recognize {b t : ℝ} (ht : 0 ≤ t) {S : Finset ℕ} {z : ℕ}
    (hz : z ∈ newProducts b t S) (p : ℕ) :
    p ∈ S ↔ ∃ q ∈ newCell b t p, q ∣ z := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
  have selected : ∀ j : S, f j ∈ newCell b t j.val := Fintype.mem_piFinset.mp hf
  constructor
  · intro hp
    let i : S := ⟨p,hp⟩
    have dv : f i ∣ high f := dvd_prod_of_mem f (mem_univ i)
    exact ⟨f i,selected i,dv⟩
  · rintro ⟨q,hq,hd⟩
    have hprime : Nat.Prime q := (mem_filter.mp hq).2
    obtain ⟨j,_,hj⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hd
    have hq' := selected j
    have he := (Nat.prime_dvd_prime_iff_eq hprime (mem_filter.mp hq').2).mp hj
    have hp : p=j.val := by
      by_contra h
      exact disjoint_left.mp (newCell_disjoint ht h) hq (he ▸ hq')
    exact hp ▸ j.property

theorem products_apart {b t : ℝ} (ht : 0 ≤ t) {S T : Finset ℕ} (h : S ≠ T) :
    Disjoint (newProducts b t S) (newProducts b t T) := by
  apply disjoint_left.mpr
  intro z hs hr
  exact h (Finset.ext (fun p => (newProducts_recognize ht hs p).trans (newProducts_recognize ht hr p).symm))

lemma newProduct_active {b t : ℝ} {C S : Finset ℕ} (hs : S ⊆ C) {z : ℕ}
    (hz : z ∈ newProducts b t S) : Active (bands b t C) z := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
  apply high_active (cell:=fun i : S => newCell b t i)
    (fun _ _ h => (mem_filter.mp h).2) (fun i _ h => mem_biUnion.mpr ⟨i.val,hs i.property,h⟩)
  exact fun i => Or.inr (Fintype.mem_piFinset.mp hf i)

lemma in_newCell {b t : ℝ} (ht : 0 < t) {p q : ℕ} (h : q ∈ newCell b t p) :
    Erdos490PrimeCells.boundary b p < log q/t ∧ log q/t ≤ Erdos490PrimeCells.boundary b (p+1) := by
  have hp := (mem_filter.mp h).2.pos
  have hh := mem_Ioc.mp (mem_filter.mp h).1
  have hq : 0 < (q:ℝ) := by exact_mod_cast hp
  constructor
  · rw [lt_div_iff₀ ht,mul_comm]
    exact (lt_log_iff_exp_lt hq).mpr ((Nat.floor_lt (exp_pos _).le).mp hh.1)
  · rw [div_le_iff₀ ht,mul_comm]
    exact (log_le_iff_le_exp hq).mpr ((Nat.le_floor_iff (exp_pos _).le).mp hh.2)

theorem newProduct_displacement {b t : ℝ} (ht : 0 < t) {S : Finset ℕ}
    (hp : ∀ p ∈ S, p.Prime) (e : ℕ → ℝ) (hc : ∀ p ∈ S, ∀ v ∈ Set.Ioc (Erdos490PrimeCells.boundary b p)
      (Erdos490PrimeCells.boundary b (p+1)), |v-log p| ≤ e p)
    {z : ℕ} (hz : z ∈ newProducts b t S) :
    |log z/t-log (∏ p ∈ S, p:ℕ)| ≤ ∑ p ∈ S, e p := by
  obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
  have hq (i : S) := Fintype.mem_piFinset.mp hf i
  have id1 : log ((high f:ℕ):ℝ) = ∑ i : S, log (f i) := by
    rw [high,Nat.cast_prod,log_prod (fun i _ => by exact_mod_cast (mem_filter.mp (hq i)).2.ne_zero)]
  have id2 : log ((∏ p ∈ S, p:ℕ):ℝ) = ∑ p ∈ S, log p := by
    rw [Nat.cast_prod,log_prod (fun p h => by exact_mod_cast (hp p h).ne_zero)]
  rw [id1,id2,sum_div,← sum_attach S (fun p : ℕ => log (p:ℝ)),← sum_attach S e,attach_eq_univ,← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => hc i.val i.property _ (in_newCell ht (hq i))))

private lemma residual_count {D U A : Finset ℕ} (sep : Disjoint D U)
    (ha : ∀ z ∈ A, Active D z) (N : ℕ) :
    (∑ z ∈ A, (semigroup U (N/z)).card) ≤ (semigroup (D ∪ U) N).card := by
  let V := A.sigma (fun z => semigroup U (N/z))
  let f (w : Sigma (fun _ : ℕ => ℕ)) := w.1*w.2
  have hinj : Set.InjOn f V := by
    rintro ⟨z,v⟩ hv ⟨w,r⟩ hr eq
    obtain ⟨hz,hv⟩ := mem_sigma.mp hv
    obtain ⟨hw,hr⟩ := mem_sigma.mp hr
    change z*v=w*r at eq
    obtain rfl := recover (coprime_active sep (ha _ hz) (mem_semigroup.mp hr).1)
      (coprime_active sep (ha _ hw) (mem_semigroup.mp hv).1) eq
    obtain rfl := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (ha _ hz).1) eq
    rfl
  have sub : V.image f ⊆ semigroup (D ∪ U) N := by
    intro z hz
    obtain ⟨⟨w,v⟩,h,rfl⟩ := mem_image.mp hz
    obtain ⟨hw,hv⟩ := mem_sigma.mp h
    obtain ⟨hact,hcut⟩ := mem_semigroup.mp hv
    exact mem_semigroup.mpr ⟨Nat.mul_mem_factoredNumbers
      (Nat.factoredNumbers_mono subset_union_left (ha _ hw))
      (Nat.factoredNumbers_mono subset_union_right hact),by
      simpa [f,mul_comm] using (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (ha _ hw).1)).mp hcut⟩
  simpa [card_image_of_injOn hinj,V,card_sigma] using card_le_card sub

theorem family_density_lower {b t : ℝ} (ht : 0 ≤ t) (C U : Finset ℕ)
    (sep : Disjoint (bands b t C) U) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C)
    (n u : ℕ) :
    (∑ S ∈ G, ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹*density U n (u*z)) ≤
      density (bands b t C ∪ U) n u := by
  let A := G.biUnion (newProducts b t)
  have apart : (G:Set (Finset ℕ)).PairwiseDisjoint (newProducts b t) :=
    fun _ _ _ _ h => products_apart ht h
  have active : ∀ z ∈ A, Active (bands b t C) z := by
    intro z h
    obtain ⟨S,hS,hz⟩ := mem_biUnion.mp h
    exact newProduct_active (hG _ hS) hz
  rw [← sum_biUnion apart]
  calc
    _ = (∑ z ∈ A, ((semigroup U (n/u/z)).card:ℝ))*u/n := by
      rw [sum_mul,sum_div]; apply sum_congr rfl; intro z hz
      have h0 : (z:ℝ) ≠ 0 := by exact_mod_cast (active z hz).1
      unfold density
      rw [Nat.div_div_eq_div_mul,Nat.cast_mul]
      by_cases hn : n=0
      · simp [hn]
      field_simp
    _ ≤ _ := by
      unfold density
      gcongr
      exact_mod_cast residual_count sep active (n/u)

end

end Erdos490Transfer
end


/- Enumerate -/
section
open Finset

namespace Erdos490Smooth

def tupleRange {S : Finset ℕ} {j : ℕ} (f : Fin j → S) : Finset ℕ :=
  univ.image fun i => (f i : ℕ)

theorem tupleRange_card {j : ℕ} {S : Finset ℕ} {f : Fin j → S}
    (hf : StrictMono fun i => (f i : ℕ)) : (tupleRange f).card = j := by
  rw [tupleRange, card_image_of_injective _ hf.injective,card_univ,Fintype.card_fin]

theorem tupleRange_prod {M : Type*} [CommMonoid M] {j : ℕ} {S : Finset ℕ}
    {f : Fin j → S} (hf : StrictMono fun i => (f i : ℕ)) (w : ℕ → M) :
    ∏ p ∈ tupleRange f, w p = ∏ i, w (f i : ℕ) :=
  Finset.prod_image hf.injective.injOn

theorem tuple_subset_sum {M : Type*} [CommMonoid M] [AddCommMonoid M]
    (S : Finset ℕ) (j : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] (w : ℕ → M) :
    ∑ f : Fin j → S with (StrictMono fun i => (f i : ℕ)) ∧ P (tupleRange f),
      ∏ i, w (f i : ℕ) =
      ∑ V ∈ (S.powersetCard j).filter P, ∏ p ∈ V, w p := by
  classical
  apply Finset.sum_bij (fun f _ => tupleRange f)
  · intro f hf
    have h := (Finset.mem_filter.mp hf).2
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨by
      intro p hp
      obtain ⟨i,_,rfl⟩ := mem_image.mp hp
      exact (f i).property,tupleRange_card h.1⟩,h.2⟩
  · intro f hf g hg he
    have hf' := (mem_filter.mp hf).2.1
    have hg' := (mem_filter.mp hg).2.1
    have hfc := tupleRange_card hf'
    have hfm (i : Fin j) : (f i : ℕ) ∈ tupleRange f := mem_image_of_mem _ (mem_univ i)
    have hgm (i : Fin j) : (g i : ℕ) ∈ tupleRange f := he ▸ mem_image_of_mem _ (mem_univ i)
    have h := (orderEmbOfFin_unique hfc hfm hf').trans (orderEmbOfFin_unique hfc hgm hg').symm
    exact funext fun i => Subtype.ext (congrFun h i)
  · intro V hV
    obtain ⟨hV,hP⟩ := mem_filter.mp hV
    obtain ⟨hVS,hc⟩ := mem_powersetCard.mp hV
    let f (i : Fin j) : S := ⟨V.orderEmbOfFin hc i,hVS (V.orderEmbOfFin_mem hc i)⟩
    have he : tupleRange f = V := image_orderEmbOfFin_univ V hc
    exact ⟨f,mem_filter.mpr ⟨mem_univ _,(V.orderEmbOfFin hc).strictMono,he ▸ hP⟩,he⟩
  · intro f hf
    exact (tupleRange_prod (mem_filter.mp hf).2.1 w).symm

end Erdos490Smooth
end


/- Weighted -/
section
open Finset Filter Real MeasureTheory Set

open scoped Topology Interval

namespace Erdos490PrimeCells

noncomputable def primeBand (s a b : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊exp (s*a)⌋₊ ⌊exp (s*b)⌋₊).filter Nat.Prime

noncomputable def weighted (s a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ p ∈ primeBand s a b, f (log p/s) / p

noncomputable def bandMass (s a b : ℝ) := reciprocalInterval (exp (s*a)) (exp (s*b))

theorem band_point {s a b : ℝ} {p : ℕ} (hs : 0 < s) (hp : p ∈ primeBand s a b) :
    log (p:ℝ)/s ∈ Set.Icc a b := by
  obtain ⟨h,hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1,h2⟩ := Finset.mem_Ioc.mp h
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hprime.pos
  have h1' : exp (s*a) < (p:ℝ) := (Nat.floor_lt' hprime.ne_zero).mp h1
  have h2' : (p:ℝ) ≤ exp (s*b) := (Nat.le_floor_iff (exp_pos _).le).mp h2
  constructor
  · rw [le_div_iff₀ hs,mul_comm]
    simpa only [Real.log_exp] using Real.log_le_log (exp_pos _) h1'.le
  · rw [div_le_iff₀ hs,mul_comm]
    exact (log_le_iff_le_exp hp0).mpr h2'

theorem weighted_add (f : ℝ → ℝ) {s a b c : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) (hbc : b ≤ c) :
    weighted s a b f + weighted s b c f = weighted s a c f := by
  unfold weighted primeBand
  simp only [Finset.sum_filter]
  apply Finset.sum_Ioc_consecutive
  all_goals apply Nat.floor_mono; apply exp_le_exp.mpr; gcongr

theorem weighted_const (s a b z : ℝ) :
    weighted s a b (fun _ => z) = z * bandMass s a b := by
  unfold weighted primeBand bandMass reciprocalInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem weighted_oscillation {s a b δ : ℝ} {f : ℝ → ℝ} (hs : 0 < s)
    (h : ∀ v ∈ Set.Icc a b, |f v-f a| ≤ δ) :
    |weighted s a b f - f a * bandMass s a b| ≤ δ * bandMass s a b := by
  rw [← weighted_const, ← weighted_const]
  unfold weighted
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [← sub_div, abs_div,abs_of_nonneg (Nat.cast_nonneg p : 0 ≤ (p:ℝ))]
  exact div_le_div_of_nonneg_right (h _ (band_point hs hp)) (Nat.cast_nonneg _)

theorem integral_oscillation {a b δ : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : ∀ v ∈ Set.Icc a b, |f v-f a| ≤ δ) :
    |(∫ v in a..b, f v/v) - f a * log (b/a)| ≤ δ * log (b/a) := by
  have hb := ha.trans_le hab
  have hdiv (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc a b)) :
      IntervalIntegrable (fun v => g v/v) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hg.div continuousOn_id (fun v hv => (ha.trans_le hv.1).ne')
  have hconst (c : ℝ) : (∫ v in a..b, c/v) = c*log (b/a) := by
    simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul]
    rw [integral_inv_of_pos ha hb,div_eq_mul_inv]
  rw [← hconst,← hconst,← intervalIntegral.integral_sub (hdiv f hf) (hdiv _ continuousOn_const)]
  apply (intervalIntegral.abs_integral_le_integral_abs hab).trans
  refine intervalIntegral.integral_mono_on hab
    ((hdiv f hf).sub (hdiv _ continuousOn_const)).abs (hdiv _ continuousOn_const) ?_
  intro v hv
  rw [← sub_div,abs_div,abs_of_pos (ha.trans_le hv.1)]
  exact div_le_div_of_nonneg_right (h v hv) (ha.trans_le hv.1).le

end Erdos490PrimeCells
end


/- Weak -/
section
open Finset Filter Real MeasureTheory Set

open scoped Topology Interval

namespace Erdos490PrimeCells

private def BandApprox (f : ℝ → ℝ) (δ a b : ℝ) : Prop :=
  ∀ ε > (0:ℝ), ∀ᶠ s : ℝ in atTop, |weighted s a b f - ∫ v in a..b, f v/v| ≤
    2*δ*log (b/a) + ε

private lemma approx_small {a b δ : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (h : ∀ v ∈ Set.Icc a b, |f v-f a| ≤ δ) :
    BandApprox f δ a b := by
  intro ε hε
  let L := log (b/a)
  have hlim : Tendsto (fun s => bandMass s a b) atTop (𝓝 L) := dilated_window_mass ha hab
  have hz : Tendsto (fun s => δ * bandMass s a b + |f a| * |bandMass s a b - L| + δ*L) atTop
      (𝓝 (2*δ*L)) := by
    have t := (((tendsto_const_nhds (x := δ)).mul hlim).add
      ((tendsto_const_nhds (x := |f a|)).mul (hlim.sub_const L).abs)).add_const (δ*L)
    convert t using 2
    simp; ring
  filter_upwards [eventually_gt_atTop 0,hz.eventually_lt_const (by linarith : 2*δ*L < 2*δ*L + ε)]
    with s hs he
  have h1 := weighted_oscillation hs h
  have h2 := integral_oscillation ha hab hf h
  calc
    _ ≤ |weighted s a b f - f a * bandMass s a b| + |f a * bandMass s a b - f a * L| +
        |f a * L - ∫ v in a..b, f v/v| := by
      linarith only [abs_sub_le (weighted s a b f) (f a * bandMass s a b) (f a * L),
        abs_sub_le (weighted s a b f) (f a * L) (∫ v in a..b, f v/v)]
    _ ≤ _ := by
      rw [← mul_sub, abs_mul, abs_sub_comm (f a * L)]
      dsimp only [L] at *
      linarith

private lemma approx_join {a b c δ : ℝ} {f : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ContinuousOn f (Set.Icc a c)) (h1 : BandApprox f δ a b) (h2 : BandApprox f δ b c) :
    BandApprox f δ a c := by
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have hi {u v : ℝ} (hu : a ≤ u) (hv : v ≤ c) (huv : u ≤ v) :
      IntervalIntegrable (fun w => f w/w) volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    exact (hf.mono (Set.Icc_subset_Icc hu hv)).div continuousOn_id
      (fun w hw => ((ha.trans_le hu).trans_le hw.1).ne')
  intro ε hε
  filter_upwards [eventually_ge_atTop 0,h1 (ε/2) (by linarith),h2 (ε/2) (by linarith)]
    with s hs hleft hright
  rw [← weighted_add f hs hab hbc, ← intervalIntegral.integral_add_adjacent_intervals
    (hi le_rfl hbc hab) (hi hab le_rfl hbc)]
  rw [show weighted s a b f + weighted s b c f - ((∫ v in a..b, f v / v) + ∫ v in b..c, f v/v) =
    (weighted s a b f - ∫ v in a..b, f v/v) + (weighted s b c f - ∫ v in b..c, f v/v) by ring]
  apply (abs_add_le _ _).trans
  rw [log_div hb.ne' ha.ne'] at hleft
  rw [log_div hc.ne' hb.ne'] at hright
  rw [log_div hc.ne' ha.ne']
  linarith

theorem weighted_window {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    Tendsto (fun s : ℝ => weighted s a b f) atTop (𝓝 (∫ v in a..b, f v/v)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  have hL : 0 ≤ log (b/a) := log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  let δ := ε / (8*(log (b/a)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨η,hη,hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) δ hδ
  obtain ⟨m,hm⟩ := exists_nat_gt ((b-a)/η + 1)
  have hm0 : 0 < (m : ℝ) := by linarith [div_nonneg (sub_nonneg.mpr hab) hη.le]
  let w := (b-a)/m
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hab) hm0.le
  have hw : w < η := by
    dsimp [w]; rw [div_lt_iff₀ hm0]
    have : (b-a)/η < m := by linarith
    exact (div_lt_iff₀' hη).mp this
  let g (i : ℕ) := a + i*w
  have g0 : g 0 = a := by simp [g]
  have gm : g m = b := by dsimp [g,w]; field_simp; ring
  have mono : Monotone g := fun i j hij => by dsimp [g]; gcongr
  have rangeg {i : ℕ} (hi : i ≤ m) : g i ∈ Set.Icc a b := ⟨g0 ▸ mono (Nat.zero_le i),gm ▸ mono hi⟩
  have step (i : ℕ) (hi : i < m) : BandApprox f δ (g i) (g (i+1)) := by
    have sub := Set.Icc_subset_Icc (rangeg hi.le).1 (rangeg hi).2
    apply approx_small (ha.trans_le (rangeg hi.le).1) (mono (by omega)) (hf.mono sub)
    intro v hv
    apply le_of_lt
    rw [← Real.dist_eq]
    apply hunif v (sub hv) (g i) (rangeg hi.le)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
    have hgap : g (i+1) - g i = w := by simp [g]; ring
    linarith [hv.2]
  have all_steps (i : ℕ) (hi : i ≤ m) : BandApprox f δ a (g i) := by
    induction i with
    | zero =>
      rw [g0]
      apply approx_small ha le_rfl (hf.mono (Set.Icc_subset_Icc le_rfl hab))
      intro v hv
      have : v = a := le_antisymm hv.2 hv.1
      simpa [this] using hδ.le
    | succ i ih =>
      exact approx_join ha (rangeg (by omega : i ≤ m)).1 (mono (by omega))
        (hf.mono (Set.Icc_subset_Icc le_rfl (rangeg hi).2)) (ih (by omega)) (step i hi)
  have hfinal := all_steps m le_rfl
  rw [gm] at hfinal
  filter_upwards [hfinal (ε/2) (by linarith)] with s hs
  rw [Real.dist_eq]
  apply hs.trans_lt
  dsimp [δ]
  have hp : 0 < 8*(log (b/a)+1) := by positivity
  field_simp
  nlinarith [mul_nonneg hε.le hL]

end Erdos490PrimeCells
end


/- Measures -/
section
open Filter Real MeasureTheory

open scoped Topology Interval ENNReal NNReal

namespace Erdos490PrimeCells

noncomputable def primeLaw (s a b : ℝ) : FiniteMeasure ℝ :=
  ⟨∑ p ∈ primeBand s a b, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/s), inferInstance⟩

private lemma integral_primeLaw (s a b : ℝ) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ v, f v ∂(primeLaw s a b : Measure ℝ)) = weighted s a b f := by
  change (∫ v, f v ∂(∑ p ∈ primeBand s a b, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/s))) = _
  unfold weighted
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro p _
    rw [← Measure.coe_nnreal_smul,integral_smul_measure,integral_dirac]
    simp [div_eq_mul_inv, mul_comm]
  · intro p _
    exact f.integrable (μ := ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/s))

private noncomputable def density (x : ℝ) : ℝ≥0 := Real.toNNReal x⁻¹

noncomputable def cellLaw (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Set.Ioc a b)).withDensity (fun t => (density t : ℝ≥0∞)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,MeasureTheory.setLIntegral_univ]
    have hi : IntervalIntegrable (fun t : ℝ => t⁻¹) volume a b := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hab]
      exact continuousOn_id.inv₀ (fun t ht => (ha.trans_le ht.1).ne')
    apply lt_of_le_of_lt (lintegral_mono (g := fun t : ℝ => ‖t⁻¹‖ₑ) (fun t => ?_))
      (hi.1.hasFiniteIntegral)
    exact Real.ofReal_le_enorm _⟩

private theorem integral_cellLaw {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (f : BoundedContinuousFunction ℝ ℝ) :
    (∫ v, f v ∂(cellLaw a b ha hab : Measure ℝ)) = ∫ v in a..b, f v/v := by
  change (∫ v, f v ∂(volume.restrict (Set.Ioc a b)).withDensity (fun t => (density t : ℝ≥0∞))) = _
  rw [integral_withDensity_eq_integral_smul (by unfold density; fun_prop),intervalIntegral.integral_of_le hab]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  have ht0 := ha.trans ht.1
  change (density t : ℝ) * f t = f t/t
  rw [density,Real.coe_toNNReal _ (inv_nonneg.mpr ht0.le),div_eq_mul_inv,mul_comm]

theorem finiteMeasure_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun s => primeLaw s a b) atTop (𝓝 (cellLaw a b ha hab)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  simp only [integral_primeLaw,integral_cellLaw]
  exact weighted_window ha hab f.continuous.continuousOn

theorem cellLaw_nonzero {a b : ℝ} (ha : 0 < a) (hab : a < b) : cellLaw a b ha hab.le ≠ 0 := by
  intro hz
  have h := integral_cellLaw ha hab.le (1 : BoundedContinuousFunction ℝ ℝ)
  rw [hz] at h
  simp only [FiniteMeasure.toMeasure_zero,integral_zero_measure,BoundedContinuousFunction.coe_one,
    Pi.one_apply,one_div,integral_inv_of_pos ha (ha.trans hab)] at h
  exact (log_pos ((one_lt_div ha).mpr hab)).ne' h.symm

instance cellLaw_nullSingleton {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    NullSingletonClass (cellLaw a b ha hab : Measure ℝ) := by
  change NullSingletonClass ((volume.restrict (Set.Ioc a b)).withDensity _)
  infer_instance

end Erdos490PrimeCells
end


/- LabelSum -/
section
open Filter Real MeasureTheory Set

open scoped Topology ENNReal

namespace Erdos490PrimeCells

structure Label where
  lo : ℝ
  hi : ℝ
  positive : 0 < lo
  nonempty : lo < hi

noncomputable def limitFactor (i : Label) :=
  (cellLaw i.lo i.hi i.positive i.nonempty.le).normalize

noncomputable def primeFactor (s : ℝ) (i : Label) := (primeLaw s i.lo i.hi).normalize

theorem factor_tendsto (i : Label) :
    Tendsto (fun s => primeFactor s i) atTop (𝓝 (limitFactor i)) :=
  FiniteMeasure.tendsto_normalize_of_tendsto (finiteMeasure_tendsto i.positive i.nonempty.le)
    (cellLaw_nonzero i.positive i.nonempty)

private abbrev addPair (x : ℝ × ℝ) := x.1+x.2

private lemma continuous_addPair : Continuous addPair := continuous_fst.add continuous_snd

noncomputable def sumLaw (μ ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  (μ.prod ν).map continuous_addPair.measurable.aemeasurable

theorem sumLaw_continuous : Continuous (fun m : ProbabilityMeasure ℝ × ProbabilityMeasure ℝ =>
    sumLaw m.1 m.2) :=
  (ProbabilityMeasure.continuous_map continuous_addPair).comp ProbabilityMeasure.continuous_prod

noncomputable def labelSum (μ : Label → ProbabilityMeasure ℝ) : List Label → ProbabilityMeasure ℝ
  | [] => ⟨Measure.dirac 0,inferInstance⟩
  | i::l => sumLaw (labelSum μ l) (μ i)

theorem labelSum_tendsto (labels : List Label) :
    Tendsto (fun s => labelSum (primeFactor s) labels) atTop (𝓝 (labelSum limitFactor labels)) := by
  induction labels with
  | nil => exact tendsto_const_nhds
  | cons i l ih => exact sumLaw_continuous.continuousAt.tendsto.comp (ih.prodMk_nhds (factor_tendsto i))

instance limitFactor_nullSingleton (i : Label) : NullSingletonClass (limitFactor i : Measure ℝ) := by
  unfold limitFactor
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (cellLaw_nonzero i.positive i.nonempty)]
  constructor
  intro x
  rw [Measure.smul_apply,measure_singleton,smul_zero]

end Erdos490PrimeCells
end


/- AtomicProduct -/
section
open Real MeasureTheory Set Finset

open scoped ENNReal NNReal

namespace Erdos490PrimeCells

theorem atomic_product {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (w : κ → ℝ≥0) (v : κ → ℝ) :
    Measure.pi (fun _ : ι => ∑ k, w k • Measure.dirac (v k)) =
      ∑ f : ι → κ, (∏ i, w (f i)) • Measure.dirac (fun i => v (f i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hset := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,Measure.dirac_apply' _ hset]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro f _
  simp only [Set.indicator_apply,Pi.one_apply,Set.mem_univ_pi]
  by_cases h : ∀ i, v (f i) ∈ s i
  · simp [h]
  · push Not at h
    obtain ⟨i,hi⟩ := h
    rw [if_neg (fun hh => hi (hh i)),mul_zero]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem pi_restore_mass {ι : Type*} [Fintype ι] (μ : FiniteMeasure ℝ) :
    Measure.pi (fun _ : ι => (μ : Measure ℝ)) =
      (μ.mass ^ Fintype.card ι) • (ProbabilityMeasure.pi (fun _ : ι => μ.normalize) : Measure (ι → ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ProbabilityMeasure.toMeasure_pi,Measure.pi_pi]
  have h (i : ι) : (μ : Measure ℝ) (s i) = (μ.mass:ℝ≥0∞) * (μ.normalize : Measure ℝ) (s i) := by
    simpa only [ENNReal.coe_mul,FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun a : ℝ≥0 => (a:ℝ≥0∞)) (μ.self_eq_mass_mul_normalize (s i))
  simp_rw [h]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,ENNReal.coe_pow]

end Erdos490PrimeCells
end


/- Simplices -/
section
open Filter Real MeasureTheory Set

open scoped Topology ENNReal

namespace Erdos490PrimeCells

theorem pi_slice_null {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    (i : Fin (n+1)) [NullSingletonClass (μ i : Measure ℝ)]
    {A : Set (Fin (n+1) → ℝ)} (hA : MeasurableSet A)
    (h : ∀ y : Fin n → ℝ, ∃ v : ℝ, ∀ x : ℝ, i.insertNth x y ∈ A → x = v) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) A = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have he := (measurePreserving_piFinSuccAbove (fun j => (μ j : Measure ℝ)) i).symm e
  change Measure.pi (fun j => (μ j : Measure ℝ)) A = 0
  rw [← he.map_eq,Measure.map_apply e.symm.measurable hA,
    Measure.prod_apply_symm (e.symm.measurable hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  obtain ⟨v,hv⟩ := h y
  apply measure_mono_null (t := {v}) _ (measure_singleton _)
  intro x hx
  exact hv x hx

theorem pi_sum_null {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    [∀ i, NullSingletonClass (μ i : Measure ℝ)] (c : ℝ) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) {v | ∑ i, v i = c} = 0 := by
  let i : Fin (n+1) := 0
  apply pi_slice_null μ i (isClosed_eq (by fun_prop) continuous_const).measurableSet
  intro y
  refine ⟨c - ∑ j, y j,fun x hx => ?_⟩
  change ∑ j, i.insertNth (α := fun _ => ℝ) x y j = c at hx
  rw [i.sum_univ_succAbove, i.insertNth_apply_same] at hx
  simpa only [Fin.insertNth_apply_succAbove,eq_sub_iff_add_eq] using hx

theorem pi_diagonal_null {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    [∀ i, NullSingletonClass (μ i : Measure ℝ)] {i j : Fin (n+1)} (hij : i ≠ j) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) {v | v i = v j} = 0 := by
  apply pi_slice_null μ i (isClosed_eq (continuous_apply i) (continuous_apply j)).measurableSet
  obtain ⟨r,hr⟩ := Fin.exists_succAbove_eq hij.symm
  intro y
  refine ⟨y r,fun x hx => ?_⟩
  change i.insertNth (α := fun _ => ℝ) x y i = i.insertNth (α := fun _ => ℝ) x y j at hx
  simpa only [←hr,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove] using hx

private lemma frontier_inter_null {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) {A B : Set X} (hA : μ (frontier A) = 0) (hB : μ (frontier B) = 0) :
    μ (frontier (A ∩ B)) = 0 := by
  apply measure_mono_null (t := frontier A ∪ frontier B) _ (measure_union_null hA hB)
  exact (frontier_inter_subset A B).trans
    (Set.union_subset_union Set.inter_subset_left Set.inter_subset_right)

def orderedSimplex (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {v | StrictMono v ∧ ∑ i, v i ≤ c}

theorem simplex_null_frontier {n : ℕ} (μ : Fin (n+1) → ProbabilityMeasure ℝ)
    [∀ i, NullSingletonClass (μ i : Measure ℝ)] (c : ℝ) :
    (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ)) (frontier (orderedSimplex (n+1) c)) = 0 := by
  classical
  let pairs := {p : Fin (n+1) × Fin (n+1) // p.1 < p.2}
  let ν := (ProbabilityMeasure.pi μ : Measure (Fin (n+1) → ℝ))
  let checks (s : Finset pairs) : Set (Fin (n+1) → ℝ) :=
    {v | ∀ p ∈ s, v p.val.1 < v p.val.2}
  have hchecks (s : Finset pairs) : ν (frontier (checks s)) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp [checks]
    | @insert p s _ ih =>
      have he : checks (insert p s) = {v | v p.val.1 < v p.val.2} ∩ checks s := by
        ext; simp [checks]
      rw [he]
      apply frontier_inter_null ν _ ih
      exact measure_mono_null (frontier_lt_subset_eq (continuous_apply p.val.1)
        (continuous_apply p.val.2)) (pi_diagonal_null μ p.property.ne)
  have he : orderedSimplex (n+1) c = checks Finset.univ ∩ {v | ∑ i, v i ≤ c} := by
    ext v
    change (StrictMono v ∧ _) ↔ ((∀ p ∈ (Finset.univ : Finset pairs), _) ∧ _)
    apply and_congr_left
    intro _
    exact ⟨fun h p _ => h p.property,fun h i j hij => h ⟨(i,j),hij⟩ (Finset.mem_univ _)⟩
  rw [he]
  apply frontier_inter_null ν (hchecks _) _
  exact measure_mono_null (frontier_le_subset_eq (by fun_prop) continuous_const) (pi_sum_null μ c)

theorem ordered_simplex_tendsto {n : ℕ} (i : Label) (c : ℝ) :
    Tendsto (fun t => (ProbabilityMeasure.pi (fun _ : Fin (n+1) => primeFactor t i) :
      Measure (Fin (n+1) → ℝ)) (orderedSimplex (n+1) c)) atTop
      (𝓝 ((ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) :
        Measure (Fin (n+1) → ℝ)) (orderedSimplex (n+1) c))) := by
  apply ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' _ (simplex_null_frontier _ _)
  exact ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr fun _ => factor_tendsto i)

end Erdos490PrimeCells
end


/- ArithmeticSimplex -/
section
open Real Filter MeasureTheory Finset Set

open scoped Topology ENNReal NNReal Classical

namespace Erdos490PrimeCells

open Erdos490Smooth

theorem log_tuple_simplex {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) {j : ℕ}
    (f : Fin j → S) {t : ℝ} (ht : 0 < t) (h : ℝ) :
    (fun i => log (f i : ℕ)/t) ∈ orderedSimplex j h ↔
      (StrictMono fun i => (f i : ℕ)) ∧ (∏ p ∈ tupleRange f, p) ≤ ⌊exp (t*h)⌋₊ := by
  have hp (i : Fin j) : (0 : ℝ) < (f i : ℕ) := by exact_mod_cast hS _ (f i).property
  have hmono : StrictMono (fun i => log (f i : ℕ)/t) ↔ StrictMono fun i => (f i : ℕ) := by
    constructor
    · intro H i k hik
      exact_mod_cast (log_lt_log_iff (hp i) (hp k)).mp ((div_lt_div_iff_of_pos_right ht).mp (H hik))
    · intro H i k hik
      exact div_lt_div_of_pos_right (log_lt_log (hp i) (by exact_mod_cast H hik)) ht
  change (_ ∧ _) ↔ _
  rw [hmono]
  apply and_congr_right
  intro H
  rw [← Finset.sum_div, div_le_iff₀ ht,tupleRange_prod H (fun p => p),Nat.le_floor_iff (exp_pos _).le]
  have prodpos : 0 < ∏ i, ((f i : ℕ):ℝ) := Finset.prod_pos fun i _ => hp i
  rw [Nat.cast_prod]
  change (∑ i, log (f i : ℕ)) ≤ h*t ↔ (∏ i, ((f i : ℕ):ℝ)) ≤ exp (t*h)
  rw [← Real.log_le_iff_le_exp prodpos,Real.log_prod (fun i _ => (hp i).ne'),mul_comm]

theorem primeTuple_eval (j : ℕ) (t a b : ℝ) (A : Set (Fin j → ℝ)) :
    (Measure.pi (fun _ : Fin j => (primeLaw t a b : Measure ℝ))).real A =
      ∑ f : Fin j → primeBand t a b with (fun i => log (f i : ℕ)/t) ∈ A,
        ∏ i, (((f i : ℕ):ℝ)⁻¹) := by
  classical
  let S := primeBand t a b
  let w (p : S) : ℝ≥0 := (p.val:ℝ≥0)⁻¹
  let v (p : S) : ℝ := log p.val/t
  have he : (primeLaw t a b : Measure ℝ) = ∑ p : S, w p • Measure.dirac (v p) := by
    change ∑ p ∈ S, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/t) = _
    exact (Finset.sum_attach S _).symm
  rw [Measure.real,he,atomic_product w v,Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum (fun f _ => measure_ne_top ((∏ i, w (f i)) • Measure.dirac (fun i => v (f i))) A)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  rw [Measure.smul_apply,Measure.dirac_apply,ENNReal.smul_def,smul_eq_mul,Set.indicator_apply]
  by_cases ha : (fun i => v (f i)) ∈ A
  · simp [ha,w,v,NNReal.coe_prod]
  · simp [ha,w,v]

theorem primeTuple_simplex (j : ℕ) {t : ℝ} (ht : 0 < t) (a b h : ℝ) :
    (Measure.pi (fun _ : Fin j => (primeLaw t a b : Measure ℝ))).real (orderedSimplex j h) =
      ∑ V ∈ ((primeBand t a b).powersetCard j).filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊),
        ∏ p ∈ V,(p:ℝ)⁻¹ := by
  classical
  rw [primeTuple_eval]
  have hS : ∀ p ∈ primeBand t a b, 0 < p := fun _ hp => (Finset.mem_filter.mp hp).2.pos
  simp_rw [log_tuple_simplex hS _ ht h]
  exact tuple_subset_sum (primeBand t a b) j (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊) (fun p => (p:ℝ)⁻¹)

end Erdos490PrimeCells
end


/- CDFLimit -/
section
open Filter Real MeasureTheory Set

open scoped Topology ENNReal NNReal Classical

namespace Erdos490PrimeCells

theorem measurable_simplex (j : ℕ) (c : ℝ) : MeasurableSet (orderedSimplex j c) := by
  let pairs := {p : Fin j × Fin j // p.1 < p.2}
  have he : orderedSimplex j c =
      (⋂ p : pairs, {v : Fin j → ℝ | v p.val.1 < v p.val.2}) ∩ {v | ∑ i, v i ≤ c} := by
    ext v
    simp only [orderedSimplex,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    apply and_congr_left
    exact fun _ => ⟨fun hm p => hm p.property,fun hm i k hik => hm ⟨(i,k),hik⟩⟩
  rw [he]
  exact (MeasurableSet.iInter fun p : pairs => (isOpen_lt (continuous_apply p.val.1)
    (continuous_apply p.val.2)).measurableSet).inter (isClosed_le (show Continuous (fun v : Fin j → ℝ => ∑ i, v i) by fun_prop) (continuous_const (y := c))).measurableSet

theorem simplex_cdf_continuous {n : ℕ} (i : Label) :
    Continuous (fun c => (ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) :
      Measure (Fin (n+1) → ℝ)).real (orderedSimplex (n+1) c)) := by
  let μ := (ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) : Measure (Fin (n+1) → ℝ))
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (𝓝 c)
    (measurable_simplex _ _) (fun h => measurable_simplex _ h)
  have hne : ∀ᵐ v ∂μ, ∑ r, v r ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using pi_sum_null (fun _ : Fin (n+1) => limitFactor i) c
  filter_upwards [hne] with v hv
  rcases lt_or_gt_of_ne hv with h|h
  · filter_upwards [eventually_gt_nhds h] with y hy
    change (StrictMono v ∧ _ ≤ _) ↔ (StrictMono v ∧ _ ≤ _)
    simp [hy.le,h.le]
  · filter_upwards [eventually_lt_nhds h] with y hy
    change (StrictMono v ∧ _ ≤ _) ↔ (StrictMono v ∧ _ ≤ _)
    simp [hy.not_ge,h.not_ge]

noncomputable def simplexLimit (n : ℕ) (i : Label) (h : ℝ) : ℝ :=
  ((cellLaw i.lo i.hi i.positive i.nonempty.le).mass : ℝ)^(n+1) *
    (ProbabilityMeasure.pi (fun _ : Fin (n+1) => limitFactor i) :
      Measure (Fin (n+1) → ℝ)).real (orderedSimplex (n+1) h)

theorem simplexLimit_continuous (n : ℕ) (i : Label) : Continuous (simplexLimit n i) :=
  continuous_const.mul (simplex_cdf_continuous i)

theorem finite_simplex_tendsto (n : ℕ) (i : Label) (h : ℝ) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (n+1) => (primeLaw t i.lo i.hi : Measure ℝ))).real
      (orderedSimplex (n+1) h)) atTop (𝓝 (simplexLimit n i h)) := by
  have hmass := (FiniteMeasure.continuous_mass.tendsto _).comp (finiteMeasure_tendsto i.positive i.nonempty.le)
  have hprob := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (ordered_simplex_tendsto (n := n) i h)
  have H := (((NNReal.continuous_coe.tendsto _).comp hmass).pow (n+1)).mul hprob
  apply H.congr'
  filter_upwards with t
  simp only [Function.comp_apply,pi_restore_mass (ι := Fin (n+1)),Measure.real,Measure.smul_apply,
    ENNReal.smul_def,smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_pow,
    Fintype.card_fin,primeFactor]

end Erdos490PrimeCells
end


/- SplitSieve -/
section
open Finset

namespace Erdos490Smooth

private theorem multiples (n : ℕ) {d : ℕ} (hd : 0 < d) :
    (Finset.Ioc 0 n).filter (d ∣ ·) = (Finset.Ioc 0 (n/d)).image (d*·) := by
  ext m
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_image]
  constructor
  · rintro ⟨⟨hm,hmn⟩,⟨j,rfl⟩⟩
    exact ⟨j,⟨Nat.pos_of_mul_pos_left hm,(Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hmn)⟩,rfl⟩
  · rintro ⟨j,⟨hj,hjn⟩,rfl⟩
    exact ⟨⟨Nat.mul_pos hd hj,by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hjn⟩,dvd_mul_right _ _⟩

private theorem count_multiples (S : Finset ℕ) (n : ℕ) {d : ℕ} (hd : 0 < d)
    (h : ∀ p ∈ S, p.Prime ∧ ¬p ∣ d) :
    ∑ m ∈ (Finset.Ioc 0 n).filter (d ∣ ·), avoid S m = smallCount S (n/d) := by
  rw [multiples n hd,Finset.sum_image]
  · unfold smallCount
    exact Finset.sum_congr rfl fun _ _ => avoid_dilate S h
  · exact fun _ _ _ _ he => Nat.eq_of_mul_eq_mul_left hd he

theorem split_sieve (S L : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hL : ∀ p ∈ L, p.Prime)
    (hd : Disjoint S L) (n : ℕ) :
    smallCount (S ∪ L) n = ∑ T ∈ L.powerset,
      (-1:ℝ)^T.card * smallCount S (n/(∏ p ∈ T,p)) := by
  conv_lhs => unfold smallCount
  have ha (m : ℕ) : avoid (S ∪ L) m = avoid S m * avoid L m := by
    unfold avoid; exact Finset.prod_union hd
  simp_rw [ha,avoid_expand L hL,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T hT => ?_
  let d := ∏ p ∈ T, p
  have hs := Finset.mem_powerset.mp hT
  have hd0 : 0 < d := Finset.prod_pos fun p hp => (hL p (hs hp)).pos
  have hfree (p : ℕ) (hp : p ∈ S) : p.Prime ∧ ¬p ∣ d := by
    refine ⟨hS p hp, (hS p hp).coprime_iff_not_dvd.mp ?_⟩
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    apply ((hS p hp).coprime_iff_not_dvd).mpr
    intro hdiv
    have he := (Nat.prime_dvd_prime_iff_eq (hS p hp) (hL q (hs hq))).mp hdiv
    exact Finset.disjoint_left.mp hd hp (he ▸ hs hq)
  change (∑ m ∈ Finset.Ioc 0 n, avoid S m * (if d ∣ m then (-1:ℝ)^T.card else 0)) =
    (-1:ℝ)^T.card * smallCount S (n/d)
  rw [← count_multiples S n hd0 hfree,Finset.mul_sum,Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  split_ifs <;> ring

theorem truncated_error (S L : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hL : ∀ p ∈ L, p.Prime)
    (hd : Disjoint S L) (n : ℕ) :
    let T := L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ n)
    |smallCount (S ∪ L) n - n * localProduct S * ∑ U ∈ T, (-1:ℝ)^U.card / (∏ p ∈ U,p : ℕ)| ≤
      2 ^ S.card * T.card := by
  classical
  dsimp only
  rw [split_sieve S L hS hL hd]
  let T := L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ n)
  have hp : (∑ U ∈ L.powerset, (-1:ℝ)^U.card * smallCount S (n/(∏ p ∈ U,p))) =
      ∑ U ∈ T, (-1:ℝ)^U.card * smallCount S (n/(∏ p ∈ U,p)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro U hU hout
    have hgt : n < ∏ p ∈ U,p := by
      by_contra! hh
      exact hout (Finset.mem_filter.mpr ⟨hU,hh⟩)
    simp [Nat.div_eq_of_lt hgt,smallCount]
  rw [hp,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _U ∈ T, (2:ℝ)^S.card := by
      refine Finset.sum_le_sum fun U hU => ?_
      let d := ∏ p ∈ U, p
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      have hd0 : 0 < d := Finset.prod_pos fun p hp => (hL p (hsub hp)).pos
      have he := cofactor_rounding S hS n hd0
      calc
        _ = |(-1:ℝ)^U.card * (smallCount S (n/d) - n/d*localProduct S)| := by congr 1; ring
        _ ≤ _ := by rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]; exact he
    _ = _ := by simp [mul_comm,T]

end Erdos490Smooth
end


/- RoughCounts -/
section
open Finset Real Filter Asymptotics

open scoped Topology

namespace Erdos490Smooth

open Shift490

theorem supported_subsets_bound {L : Finset ℕ} (hL : ∀ p ∈ L, Nat.Prime p) {z : ℝ}
    (hz : 0 < z) :
    exp (-z) * ((L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ ⌊exp z⌋₊)).card : ℝ) ≤
      K₀ * P L / z := by
  have hc : (L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ ⌊exp z⌋₊)).card ≤ (countSet L z).card := by
    apply Finset.card_le_card_of_injOn (fun U : Finset ℕ => ∏ p ∈ U,p)
    · intro U hU
      have h := Finset.mem_filter.mp hU
      have hsub := Finset.mem_powerset.mp h.1
      have hp : ∀ p ∈ U, p.Prime := fun p h => hL p (hsub h)
      have pos : 0 < ∏ p ∈ U,p := Finset.prod_pos fun p h => (hp p h).pos
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h.2),Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr ⟨pos.ne',?_⟩⟩
      rwa [Nat.primeFactors_prod hp]
    · intro U hU V hV he
      have hsU := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      have hsV := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
      have h := congrArg Nat.primeFactors he
      simpa only [Nat.primeFactors_prod (fun p h => hL p (hsU h)),
        Nat.primeFactors_prod (fun p h => hL p (hsV h))] using h
  apply le_trans (b := exp (-z) * ((countSet L z).card : ℝ)) (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (exp_pos _).le)
  rw [← F_eq_card]
  exact counting_bound L z hz

theorem rough_mass_limit {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun t : ℝ => P (smoothLabels ⌊exp (t*a)⌋₊ (exp (t*b)))) atTop (𝓝 (b/a)) := by
  have hb := ha.trans_le hab
  have hlim (r : ℝ) (hr : 0 < r) :
      Tendsto (fun t : ℝ => Mertens.E₃ (exp (t*r))) atTop (𝓝 0) :=
    ((isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp
      (tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hr))
  have h := (tendsto_const_nhds (x := b/a) (f := atTop)).mul ((hlim a ha).sub (hlim b hb)).rexp
  simp only [sub_zero, exp_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [segment_product (Nat.floor_mono (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab ht.le)))]
  have he (r : ℝ) (hr : 0 < r) : smallProduct ⌊exp (t*r)⌋₊ =
      exp (-eulerMascheroniConstant)*exp (Mertens.E₃ (exp (t*r))) / (t*r) := by
    simpa only [smallProduct,one_div,log_exp] using
      (Mertens.prod_one_minus_div_prime_eq (one_lt_exp_iff.mpr (mul_pos ht hr)))
  rw [he a ha, he b hb, exp_sub]
  field_simp

end Erdos490Smooth
end


/- SmoothCount -/
section
open Finset Real Filter

open scoped Topology

namespace Erdos490Smooth

open Shift490

private theorem specification {k u n m : ℕ} (hm0 : 0 < m) (hmn : m ≤ n) :
    m ∈ Nat.factoredNumbers (smoothLabels k (u:ℝ)) ↔
      ¬ ∃ p ∈ Nat.primesLE k ∪ smoothLabels u (n:ℝ), p ∣ m := by
  rw [Nat.mem_factoredNumbers_iff_primeFactors_subset]
  simp only [smoothLabels,Nat.floor_natCast]
  constructor
  · rintro ⟨_,hs⟩ ⟨p,hp,hd⟩
    have hprime : p.Prime := by
      rcases Finset.mem_union.mp hp with h|h
      · exact (Nat.mem_primesLE.mp h).2
      · exact (Finset.mem_filter.mp h).2
    have hlim := Finset.mem_Ioc.mp (Finset.mem_filter.mp (hs (Nat.mem_primeFactors.mpr ⟨hprime,hd,hm0.ne'⟩))).1
    rcases Finset.mem_union.mp hp with h|h
    · exact (not_lt_of_ge (Nat.mem_primesLE.mp h).1) hlim.1
    · exact (not_lt_of_ge hlim.2) (Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1).1
  · intro h
    refine ⟨hm0.ne',?_⟩
    intro p hp
    obtain ⟨hp0,hd,_⟩ := Nat.mem_primeFactors.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp0⟩
    · by_contra! hl
      exact h ⟨p,Finset.mem_union_left _ (Nat.mem_primesLE.mpr ⟨hl,hp0⟩),hd⟩
    · by_contra! hl
      have hpn := (Nat.le_of_dvd hm0 hd).trans hmn
      exact h ⟨p,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hl,hpn⟩,hp0⟩),hd⟩

theorem smooth_count_eq_sieve_with_cap (k : ℕ) {U z cap : ℝ} (hcap : exp z ≤ cap) :
    F (smoothLabels k U) z = exp (-z) * smallCount (Nat.primesLE k ∪ smoothLabels ⌊U⌋₊ cap) ⌊exp z⌋₊ := by
  classical
  rw [F_eq_card]
  congr 1
  let A := smoothLabels k U
  have hset : countSet A z = (Finset.Ioc 0 ⌊exp z⌋₊).filter (· ∈ Nat.factoredNumbers A) := by
    ext m
    simp only [countSet,Finset.mem_filter,Finset.mem_range,Finset.mem_Ioc,Nat.lt_succ_iff]
    constructor
    · rintro ⟨hm,hh⟩
      exact ⟨⟨Nat.pos_of_ne_zero hh.1,hm⟩,hh⟩
    · rintro ⟨hm,hh⟩
      exact ⟨hm.2,hh⟩
  change ((countSet A z).card:ℝ) = _
  rw [hset,Finset.card_filter]
  unfold smallCount
  push_cast
  refine Finset.sum_congr rfl fun m hm => ?_
  have h := specification (k := k) (u := ⌊U⌋₊) (Finset.mem_Ioc.mp hm).1
    ((Finset.mem_Ioc.mp hm).2.trans (Nat.floor_mono hcap))
  simp only [smoothLabels,Nat.floor_natCast] at h
  rw [avoid_iff]
  unfold smoothLabels
  by_cases hmem : m ∈ Nat.factoredNumbers A
  · rw [if_pos hmem, if_neg (h.mp hmem)]
  · rw [if_neg hmem, if_pos (not_not.mp (fun e => hmem (h.mpr e)))]

end Erdos490Smooth
end


/- UniformError -/
section
open Real Filter Finset

open scoped Topology

namespace Erdos490Smooth

open Shift490

noncomputable def signedSum (L : Finset ℕ) (z : ℝ) :=
  ∑ U ∈ L.powerset with (∏ p ∈ U,p) ≤ ⌊exp z⌋₊, (-1:ℝ)^U.card / (∏ p ∈ U,p : ℕ)

theorem smooth_sieve_error (k : ℕ) {U z cap : ℝ} (hk : k ≤ ⌊U⌋₊)
    (hz : 0 < z) (hcap : exp z ≤ cap) :
    let L := smoothLabels ⌊U⌋₊ cap
    |F (smoothLabels k U) z - localProduct (Nat.primesLE k) * signedSum L z| ≤
      (2 ^ (Nat.primesLE k).card + 1) * (K₀ * P L / z) := by
  classical
  let S := Nat.primesLE k
  let L := smoothLabels ⌊U⌋₊ cap
  let T := L.powerset.filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp z⌋₊)
  have hs (p : ℕ) (hp : p ∈ S) := (Nat.mem_primesLE.mp hp).2
  have hl (p : ℕ) (hp : p ∈ L) := (Finset.mem_filter.mp hp).2
  have hd : Disjoint S L := Finset.disjoint_left.mpr fun p hp hq =>
    (not_lt_of_ge ((Nat.mem_primesLE.mp hp).1.trans hk)) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
  have hlocal : |localProduct S| ≤ 1 := by
    rw [localProduct, Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro p hp
    have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast (hs p hp).one_le
    have hi := inv_le_one_of_one_le₀ hp1
    exact abs_le.mpr ⟨by linarith, by have := inv_nonneg.mpr (by positivity : (0:ℝ) ≤ p); linarith⟩
  have hsum : |signedSum L z| ≤ T.card := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _V ∈ T, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro V hV
        have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
        have hp : 0 < ∏ p ∈ V,p := Finset.prod_pos fun p h => (hl p (hsub h)).pos
        rw [abs_div, abs_pow, abs_neg,abs_one,one_pow,abs_of_nonneg (by positivity)]
        exact (div_le_one (by exact_mod_cast hp)).mpr (by exact_mod_cast hp)
      _ = _ := by simp
  let M := localProduct S * signedSum L z
  have hm : |M| ≤ T.card := by
    rw [abs_mul]
    exact (mul_le_mul hlocal hsum (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have herr := truncated_error S L hs hl hd ⌊exp z⌋₊
  change |smallCount (S ∪ L) ⌊exp z⌋₊ - ⌊exp z⌋₊ * localProduct S * signedSum L z| ≤
    2^S.card * (T.card:ℝ) at herr
  have hround : |(⌊exp z⌋₊:ℝ) - exp z| ≤ 1 := by
    have h₁ := Nat.floor_le (exp_pos z).le
    have h₂ := Nat.lt_floor_add_one (exp z)
    rw [abs_le]; constructor <;> linarith
  have hex := calc
    |smallCount (S ∪ L) ⌊exp z⌋₊ - exp z * M| =
      |(smallCount (S ∪ L) ⌊exp z⌋₊ - ⌊exp z⌋₊ * localProduct S * signedSum L z) +
        ((⌊exp z⌋₊:ℝ) - exp z) * M| := by dsimp [M]; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ 2^S.card * (T.card:ℝ) + 1 * (T.card:ℝ) := by
      rw [abs_mul]
      exact add_le_add herr (mul_le_mul hround hm (abs_nonneg _) zero_le_one)
  dsimp only
  rw [smooth_count_eq_sieve_with_cap k hcap]
  change |exp (-z) * smallCount (S ∪ L) ⌊exp z⌋₊ - M| ≤ _
  calc
    _ = exp (-z) * |smallCount (S ∪ L) ⌊exp z⌋₊ - exp z * M| := by
      rw [← abs_of_pos (exp_pos (-z)) , ← abs_mul]
      congr 1
      rw [mul_sub,← mul_assoc,←exp_add,neg_add_cancel,exp_zero,one_mul,abs_of_pos (exp_pos _)]
    _ ≤ exp (-z) * (2 ^ S.card * (T.card:ℝ) + 1 * (T.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hex (exp_pos _).le
    _ = (2 ^ S.card + 1) * (exp (-z) * (T.card:ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (supported_subsets_bound hl hz) (by positivity)

end Erdos490Smooth
end


/- GradeSum -/
section
open Finset Real

namespace Erdos490PrimeCells

theorem primeBand_eq_smoothLabels (t w B : ℝ) :
    primeBand t w B = Erdos490Smooth.smoothLabels ⌊exp (t * w)⌋₊ (exp (t * B)) :=
  rfl

end Erdos490PrimeCells

namespace Erdos490Smooth

open Erdos490PrimeCells

noncomputable def gradeMass (L : Finset ℕ) (j : ℕ) (z : ℝ) : ℝ :=
  ∑ V ∈ (L.powersetCard j).filter (fun V => (∏ p ∈ V, p) ≤ ⌊exp z⌋₊),
    ∏ p ∈ V, (p : ℝ)⁻¹

theorem gradeMass_zero (L : Finset ℕ) {z : ℝ} (hz : 0 ≤ z) : gradeMass L 0 z = 1 := by
  have hcut : 1 ≤ ⌊exp z⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hz)
  simp [gradeMass, Finset.powersetCard_zero, Finset.filter_singleton, hcut]

private theorem card_le_floor_of_primeBand_product {t w B h : ℝ} (ht : 0 < t)
    (hw : 0 < w) (hwB : w ≤ B) (hhB : h ≤ B) {V : Finset ℕ}
    (hsub : V ⊆ primeBand t w B) (hprod : (∏ p ∈ V, p) ≤ ⌊exp (t * h)⌋₊) :
    V.card ≤ ⌊B / w⌋₊ := by
  have hprime (p : ℕ) (hp : p ∈ V) : p.Prime := (Finset.mem_filter.mp (hsub hp)).2
  have hpos (p : ℕ) (hp : p ∈ V) : 0 < (p : ℝ) := by
    exact_mod_cast (hprime p hp).pos
  have hlog (p : ℕ) (hp : p ∈ V) : t * w ≤ log (p : ℝ) := by
    have hpband := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hsub hp)).1).1
    have hexp : exp (t * w) < (p : ℝ) := (Nat.floor_lt' (hprime p hp).ne_zero).mp hpband
    simpa only [Real.log_exp] using (Real.log_lt_log (exp_pos _) hexp).le
  have hprod' : (∏ p ∈ V, (p : ℝ)) ≤ exp (t * h) := by
    rw [← Nat.cast_prod]
    exact (Nat.le_floor_iff (exp_pos _).le).mp hprod
  have hbound : (V.card : ℝ) * (t * w) ≤ t * B := calc
    _ = ∑ _p ∈ V, t * w := by simp
    _ ≤ ∑ p ∈ V, log (p : ℝ) := Finset.sum_le_sum hlog
    _ = log (∏ p ∈ V, (p : ℝ)) := (Real.log_prod fun p hp => (hpos p hp).ne').symm
    _ ≤ t * h := (Real.log_le_iff_le_exp (Finset.prod_pos hpos)).mpr hprod'
    _ ≤ t * B := mul_le_mul_of_nonneg_left hhB ht.le
  apply (Nat.le_floor_iff (div_nonneg (hw.le.trans hwB) hw.le)).mpr
  apply (le_div_iff₀ hw).mpr
  apply le_of_mul_le_mul_left _ ht
  simpa only [mul_left_comm, mul_assoc] using hbound

theorem signedSum_eq_gradeSum {t w B h : ℝ} (ht : 0 < t) (hw : 0 < w) (hwB : w ≤ B)
    (_hh : 0 < h) (hhB : h ≤ B) :
    signedSum (primeBand t w B) (t * h) =
      ∑ j ∈ Finset.range (⌊B / w⌋₊ + 1), (-1 : ℝ) ^ j * gradeMass (primeBand t w B) j (t * h) := by
  classical
  let L := primeBand t w B
  let P (V : Finset ℕ) := (∏ p ∈ V, p) ≤ ⌊exp (t * h)⌋₊
  let S := L.powerset.filter P
  have hcard (V : Finset ℕ) (hV : V ∈ S) : V.card ∈ Finset.range (⌊B / w⌋₊ + 1) := by
    obtain ⟨hsub, hprod⟩ := Finset.mem_filter.mp hV
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (card_le_floor_of_primeBand_product ht hw hwB hhB (Finset.mem_powerset.mp hsub) hprod))
  have hfiber (j : ℕ) : S.filter (fun V => V.card = j) = (L.powersetCard j).filter P := by
    ext V
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    tauto
  change (∑ V ∈ S, (-1 : ℝ) ^ V.card / (∏ p ∈ V, p : ℕ)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hcard]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfiber, gradeMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  have hVcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hV).1).2
  rw [hVcard, div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib]

end Erdos490Smooth
end


/- UniformLimit -/
section
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

end Erdos490Smooth
end


/- KernelLimit -/
section
open Filter Finset Real Set

open scoped Topology

namespace Erdos490Smooth

open Shift490 Erdos490PrimeCells

noncomputable def limitingGrade (i : Label) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | j+1 => simplexLimit j i

theorem grade_tendsto (i : Label) (j : ℕ) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun t : ℝ => gradeMass (primeBand t i.lo i.hi) j (t*h)) atTop
      (𝓝 (limitingGrade i j h)) := by
  cases j with
  | zero =>
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact (gradeMass_zero _ (mul_nonneg ht.le hh.le)).symm
  | succ n =>
    apply (finite_simplex_tendsto n i h).congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    exact primeTuple_simplex _ ht _ _ _

theorem limitingGrade_continuous (i : Label) (j : ℕ) : Continuous (limitingGrade i j) := by
  cases j with
  | zero => exact continuous_const
  | succ n => exact simplexLimit_continuous n i

noncomputable def kernelOn (k : ℕ) (i : Label) (h : ℝ) :=
  localProduct (Nat.primesLE k) * ∑ j ∈ Finset.range (⌊i.hi/i.lo⌋₊+1),
    (-1:ℝ)^j * limitingGrade i j h

theorem kernelOn_tendsto (k : ℕ) (i : Label) {h : ℝ} (hh : 0 < h) (hb : h ≤ i.hi) :
    Tendsto (fun t : ℝ => F (smoothLabels k (exp (t*i.lo))) (t*h)) atTop
      (𝓝 (kernelOn k i h)) := by
  let approx (t : ℝ) := localProduct (Nat.primesLE k) * signedSum (primeBand t i.lo i.hi) (t*h)
  have h0 : Tendsto approx atTop (𝓝 (kernelOn k i h)) := by
    have hsum := tendsto_finsetSum (Finset.range (⌊i.hi/i.lo⌋₊+1))
      (fun j _ => (tendsto_const_nhds (x := (-1:ℝ)^j)).mul (grade_tendsto i j hh))
    apply ((tendsto_const_nhds (x := localProduct (Nat.primesLE k))).mul hsum).congr'
    filter_upwards [eventually_gt_atTop 0] with t ht
    dsimp [approx]
    rw [signedSum_eq_gradeSum ht i.positive i.nonempty.le hh hb]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have half := half_pos hε
  filter_upwards [uniform_sieve_approx k hh i.positive i.nonempty.le half,
    (Metric.tendsto_nhds.mp h0) _ half] with t herr hlim
  exact (dist_triangle _ (approx t) _).trans_lt (by
    have hE : dist (F (smoothLabels k (exp (t*i.lo))) (t*h)) (approx t) < ε/2 :=
      (Real.dist_eq ..) ▸ herr h ⟨le_rfl,hb⟩
    linarith)

noncomputable def smoothKernel (k : ℕ) (w : ℝ) (hw : 0 < w) (h : ℝ) : ℝ :=
  kernelOn k ⟨w,max w h+1,hw,lt_of_le_of_lt (le_max_left ..) (lt_add_one _)⟩ h

theorem smoothKernel_tendsto (k : ℕ) {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    Tendsto (fun t : ℝ => F (smoothLabels k (exp (t*w))) (t*h)) atTop
      (𝓝 (smoothKernel k w hw h)) :=
  kernelOn_tendsto k ⟨w,max w h+1,hw,lt_of_le_of_lt (le_max_left ..) (lt_add_one _)⟩ hh ((le_max_right w h).trans (le_add_of_nonneg_right zero_le_one))

theorem smoothKernel_agrees (k : ℕ) (i : Label) {h : ℝ} (hh : 0 < h) (hb : h ≤ i.hi) :
    smoothKernel k i.lo i.positive h = kernelOn k i h :=
  tendsto_nhds_unique (smoothKernel_tendsto k i.positive hh) (kernelOn_tendsto k i hh hb)

end Erdos490Smooth
end


/- Rankin -/
section
open Real Finset Filter

open scoped Topology

namespace Erdos490Smooth

open Shift490

noncomputable def tilted (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹ * exp (σ * log n)
  map_one' := by simp
  map_mul' a b := by
    rcases eq_or_ne a 0 with rfl|ha
    · simp
    rcases eq_or_ne b 0 with rfl|hb
    · simp
    rw [Nat.cast_mul,log_mul (by exact_mod_cast ha) (by exact_mod_cast hb),mul_add,exp_add,mul_inv_rev]
    ring

theorem tilted_prime_eq (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    tilted σ p = exp ((σ-1)*log p) := by
  change (p:ℝ)⁻¹ * exp (σ * log p) = _
  rw [sub_mul,one_mul,exp_sub,exp_log (by exact_mod_cast hp.pos)]
  ring

theorem tilted_sum (S : Finset ℕ) {σ : ℝ} (hσ : σ < 1) :
    HasSum (fun n : Integers S => tilted σ n)
      (∏ p ∈ S.filter Nat.Prime,(1 - tilted σ p)⁻¹) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := tilted σ) ?_ S).2
  intro p hp
  rw [tilted_prime_eq σ hp,Real.norm_eq_abs,abs_of_pos (exp_pos _),exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hσ) (log_pos (by exact_mod_cast hp.one_lt))

private theorem local_tilt_bound {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsmall : σ*log p ≤ 1/4) :
    (1-tilted σ p)⁻¹ ≤ (1-(p:ℝ)⁻¹)⁻¹ * exp (8*σ*(log p / p)) := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp2 : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hl := log_pos hp1
  have hu := mul_nonneg hσ hl.le
  have hex := abs_exp_sub_one_le (x := σ*log p) (by rw [abs_of_nonneg hu]; linarith)
  rw [abs_of_nonneg hu, abs_of_nonneg (sub_nonneg.mpr (one_le_exp hu))] at hex
  have hq : tilted σ p = exp (σ*log p)/p := by unfold tilted; simp [mul_comm,div_eq_mul_inv]
  have hq' : tilted σ p ≤ 3/4 := by
    rw [hq,div_le_iff₀ hp0]
    linarith
  have hq0 : 0 < 1-tilted σ p := by linarith
  have hpden : 0 < 1-(p:ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ hp0).mpr hp1)
  have hf : (1-(p:ℝ)⁻¹) / (1-tilted σ p) ≤ 1 + 8*σ*(log p/p) := by
    rw [div_le_iff₀ hq0]
    have hu' : 0 ≤ 8*σ*(log p/p) := by positivity
    have ht := mul_le_mul_of_nonneg_right hq' hu'
    have hd : tilted σ p - (p:ℝ)⁻¹ ≤ 2*σ*(log p/p) := by
      rw [hq,← one_div,← sub_div]
      rw [div_le_iff₀ hp0]
      field_simp at *
      linarith
    linarith
  have hmain := hf.trans (by linarith [Real.add_one_le_exp (8*σ*(log p/p))] :
    1 + 8*σ*(log p/p) ≤ exp (8*σ*(log p/p)))
  rw [← div_eq_inv_mul] at *
  exact (le_div_iff₀ hpden).mpr (by simpa [div_eq_mul_inv,mul_comm] using hmain)

theorem tilted_product_bound {X σ : ℝ} {S : Finset ℕ} (hX : 1 ≤ X)
    (hS : ∀ p ∈ S, (p:ℝ) ≤ X) (hσ : 0 ≤ σ) (hsmall : σ * log X ≤ 1/4) :
    (∏ p ∈ S.filter Nat.Prime, (1-tilted σ p)⁻¹) ≤
    P S * exp (8*σ*(log X + log 4 + 4)) := by
  have hloc {p} (hp : p ∈ S.filter Nat.Prime) := local_tilt_bound (Finset.mem_filter.mp hp).2 hσ
    (le_trans (mul_le_mul_of_nonneg_left (log_le_log (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
      (hS p (Finset.mem_filter.mp hp).1)) hσ) hsmall)
  have hsum : ∑ p ∈ S.filter Nat.Prime, log (p:ℝ)/p ≤ log X + log 4 + 4 := by
    have hM := (abs_le.mp (Mertens.sum_log_prime_div_eq_log hX)).2
    refine le_trans (b := ∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime, log (p:ℝ)/p) ?_ (by linarith only [hM])
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp'.2.pos,Nat.le_floor (hS p hp'.1)⟩,hp'.2⟩
    · intro p hp _
      exact div_nonneg (log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∏ p ∈ S.filter Nat.Prime, ((1-(p:ℝ)⁻¹)⁻¹ * exp (8*σ*(log p/p))) := by
      apply Finset.prod_le_prod _ (fun p hp => hloc hp)
      intro p hp
      apply inv_nonneg.mpr
      have hx := hloc hp
      have h0 : 0 < 1-tilted σ p := by
        have hσ' : σ < 1 := by
          have hl := log_le_log (by norm_num : (0:ℝ)<2) (show 2 ≤ (p:ℝ) by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le)
          have ht := log_two_gt_d9
          by_contra! h
          have hge : log X ≤ σ*log X := le_mul_of_one_le_left (log_nonneg hX) h
          linarith [log_le_log (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos) (hS p (Finset.mem_filter.mp hp).1)]
        rw [tilted_prime_eq σ (Finset.mem_filter.mp hp).2]
        exact sub_pos.mpr (exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hσ')
          (log_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt))))
      exact h0.le
    _ = P S * exp (8*σ*(∑ p ∈ S.filter Nat.Prime, log (p:ℝ)/p)) := by
      rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.exp_sum]
      rfl
    _ ≤ _ := by gcongr; exact (P_pos S).le

end Erdos490Smooth
end


/- SmoothTail -/
section
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

end Erdos490Smooth
end


/- CompactCDF -/
section
open Filter MeasureTheory Real Set

open scoped Interval Topology

namespace Erdos490Smooth

theorem eventually_uniform_Icc_of_monotone {A : ℝ → ℝ → ℝ} {K : ℝ → ℝ} {a b : ℝ}
    (hmono : ∀ᶠ t in atTop, MonotoneOn (A t) (Icc a b) ∨ AntitoneOn (A t) (Icc a b))
    (hlim : ∀ x ∈ Icc a b, Tendsto (fun t => A t x) atTop (𝓝 (K x)))
    (hK : ContinuousOn K (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in atTop, ∀ h ∈ Icc a b, |A t h - K h| < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hK) (ε / 2) (by positivity)
  let U (x : Icc a b) := Metric.ball (x : ℝ) (δ / 2)
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => Metric.isOpen_ball) (by
    intro h hh
    exact mem_iUnion.mpr ⟨⟨h, hh⟩, Metric.mem_ball_self (by positivity)⟩)
  let l (x : Icc a b) := max a ((x : ℝ) - δ / 2)
  let r (x : Icc a b) := min b ((x : ℝ) + δ / 2)
  have hl (x : Icc a b) : l x ∈ Icc a b := by
    have hx := x.property
    exact ⟨le_max_left .., max_le (hx.1.trans hx.2) (by linarith [hx.2])⟩
  have hr (x : Icc a b) : r x ∈ Icc a b := by
    have hx := x.property
    exact ⟨le_min (hx.1.trans hx.2) (by linarith [hx.1]), min_le_left ..⟩
  have hends : ∀ᶠ t in atTop, ∀ x ∈ s,
      |A t (l x) - K (l x)| < ε / 2 ∧ |A t (r x) - K (r x)| < ε / 2 := by
    apply (eventually_all_finset s).mpr
    intro x _
    exact ((Metric.tendsto_nhds.mp (hlim _ (hl x)) (ε / 2) (by positivity)).and
      (Metric.tendsto_nhds.mp (hlim _ (hr x)) (ε / 2) (by positivity))).mono fun _ ht => by
        simpa only [Real.dist_eq] using ht
  filter_upwards [hmono, hends] with t htmono htends
  intro h hh
  obtain ⟨x, hxs, hx⟩ := mem_iUnion₂.mp (hs hh)
  have hxh : |h - (x : ℝ)| < δ / 2 := by
    simpa only [U, Metric.mem_ball, Real.dist_eq] using hx
  obtain ⟨hxlower, hxupper⟩ := abs_lt.mp hxh
  have hlh : l x ≤ h := max_le hh.1 (by linarith)
  have hhr : h ≤ r x := le_min hh.2 (by linarith)
  have hld : dist (l x) h < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlh)]
    linarith [le_max_right a ((x : ℝ) - δ / 2)]
  have hrd : dist (r x) h < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hhr)]
    linarith [min_le_right b ((x : ℝ) + δ / 2)]
  have leftError := hclose _ (hl x) h hh hld
  have rightError := hclose _ (hr x) h hh hrd
  rw [Real.dist_eq, abs_lt] at leftError rightError
  obtain ⟨htl, htr⟩ := htends x hxs
  rw [abs_lt] at htl htr ⊢
  rcases htmono with hm | hm
  · exact ⟨by linarith [hm (hl x) hh hlh], by linarith [hm hh (hr x) hhr]⟩
  · exact ⟨by linarith [hm hh (hr x) hhr], by linarith [hm (hl x) hh hlh]⟩

open Shift490

private theorem smoothLabels_mono (k : ℕ) : Monotone (smoothLabels k) := by
  intro x y hxy p hp
  obtain ⟨hpIoc, hpPrime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hkp, hpf⟩ := Finset.mem_Ioc.mp hpIoc
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hkp, hpf.trans (Nat.floor_mono hxy)⟩, hpPrime⟩

private theorem kernel_mono_labels {S T : Finset ℕ} (hST : S ⊆ T) (z : ℝ) :
    F S z ≤ F T z := by
  rw [F_eq_card, F_eq_card]
  apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
  exact Nat.cast_le.mpr (Finset.card_le_card (fun n hn => by
    obtain ⟨hnr, hnf⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnr, Nat.factoredNumbers_mono hST hnf⟩))

theorem smooth_limit_antitone (k : ℕ) {w : ℝ} (hw : 0 < w) {K : ℝ → ℝ}
    (hlim : ∀ h > 0, Tendsto (fun t : ℝ => F (smoothLabels k (exp (t * w))) (t * h))
      atTop (𝓝 (K h))) :
    AntitoneOn K (Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  let c := y / x
  have hc : 0 < c := div_pos hy0 hx0
  have hc1 : 1 ≤ c := (le_div_iff₀ hx0).mpr (by simpa using hxy)
  have hcx : c * x = y := div_mul_cancel₀ _ hx0.ne'
  have hxlim := (hlim x hx0).comp (tendsto_id.atTop_mul_const hc)
  apply le_of_tendsto_of_tendsto (hlim y hy0) hxlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change F (smoothLabels k (exp (t * w))) (t * y) ≤
    F (smoothLabels k (exp ((t * c) * w))) ((t * c) * x)
  rw [mul_assoc t c x, hcx]
  exact kernel_mono_labels (smoothLabels_mono k (exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ht hc1) hw.le))) _

theorem smooth_limit_mem_Icc (k : ℕ) {w : ℝ} {K : ℝ → ℝ}
    (hlim : ∀ h > 0, Tendsto (fun t : ℝ => F (smoothLabels k (exp (t * w))) (t * h))
      atTop (𝓝 (K h))) {h : ℝ} (hh : 0 < h) :
    K h ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (hlim h hh)
    (Eventually.of_forall fun _ => ⟨F_nonneg _ _, F_le_one _ _⟩)

theorem smooth_limit_mass (k : ℕ) {w : ℝ} (hw : 0 < w) {K : ℝ → ℝ}
    (hlim : ∀ h > 0, Tendsto (fun t : ℝ => F (smoothLabels k (exp (t * w))) (t * h))
      atTop (𝓝 (K h))) :
    IntegrableOn K (Ioi 0) ∧
      (∫ h in Ioi 0, K h) = exp eulerMascheroniConstant * smallProduct k * w := by
  let S (t : ℝ) := smoothLabels k (exp (t * w))
  let f (t h : ℝ) := F (S t) (t * h)
  let M := exp eulerMascheroniConstant * smallProduct k * w
  let C := exp (2 * (1 + log 4 + 4))
  have hmass : Tendsto (fun t => P (S t) / t) atTop (𝓝 M) := smoothLabels_mass_limit k hw
  have hscaled {t : ℝ} (ht : 0 < t) : IntegrableOn (f t) (Ioi 0) := by
    by_contra hn
    have hzero := integral_undef hn
    change (∫ h in Ioi 0, F (S t) (t * h)) = 0 at hzero
    rw [scaled_mass (S t) ht] at hzero
    exact (div_pos (P_pos (S t)) ht).ne' hzero
  have hfinite {H : ℝ} (hH : 0 ≤ H) :
      Tendsto (fun t => ∫ h in (0 : ℝ)..H, f t h) atTop
        (𝓝 (∫ h in (0 : ℝ)..H, K h)) := by
    simp only [intervalIntegral.integral_of_le hH]
    apply tendsto_integral_filter_of_norm_le_const
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      exact ((hscaled ht).mono_set Ioc_subset_Ioi_self).aestronglyMeasurable
    · exact ⟨1, Eventually.of_forall fun t => ae_of_all _ fun h => by
        rw [Real.norm_of_nonneg (F_nonneg (S t) (t * h))]
        exact F_le_one _ _⟩
    · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := H))]
        with h hh
      exact hlim h hh.1
  have hbounds (H : ℝ) (hH : 0 ≤ H) :
      M - M * C * exp (-H / (4 * w)) ≤ (∫ h in (0 : ℝ)..H, K h) ∧
      (∫ h in (0 : ℝ)..H, K h) ≤ M := by
    have hlow : Tendsto (fun t => P (S t) / t - P (S t) / t * C * exp (-H / (4 * w)))
        atTop (𝓝 (M - M * C * exp (-H / (4 * w)))) :=
      hmass.sub ((hmass.mul_const C).mul_const _)
    have htw := (tendsto_id.atTop_mul_const hw).eventually_ge_atTop (1 : ℝ)
    have ht_bounds : ∀ᶠ t in atTop,
        P (S t) / t - P (S t) / t * C * exp (-H / (4 * w)) ≤ (∫ h in (0 : ℝ)..H, f t h) ∧
        (∫ h in (0 : ℝ)..H, f t h) ≤ P (S t) / t := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), htw] with t ht ht1
      have hS : ∀ p ∈ S t, (p : ℝ) ≤ exp (t * w) := by
        intro p hp
        exact (Nat.le_floor_iff (exp_pos _).le).mp
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
      have htail := scaled_tail (S t) ht hw ht1 hS H
      have hpos : 0 ≤ ∫ h in Ioi H, f t h := integral_nonneg (fun h => F_nonneg _ _)
      have hsplit := intervalIntegral.integral_interval_add_Ioi (hscaled ht)
        ((hscaled ht).mono_set (Ioi_subset_Ioi hH))
      rw [show (∫ h in Ioi 0, f t h) = P (S t) / t from scaled_mass (S t) ht] at hsplit
      change (∫ h in Ioi H, f t h) ≤ P (S t) / t * C * exp (-H / (4 * w)) at htail
      exact ⟨by linarith, by linarith⟩
    exact ⟨le_of_tendsto_of_tendsto hlow (hfinite hH) (ht_bounds.mono fun _ ht => ht.1),
      le_of_tendsto_of_tendsto (hfinite hH) hmass (ht_bounds.mono fun _ ht => ht.2)⟩
  have he : Tendsto (fun H : ℝ => exp (-H / (4 * w))) atTop (𝓝 0) := by
    have hscale : Tendsto (fun H : ℝ => H * (4 * w)⁻¹) atTop atTop :=
      tendsto_id.atTop_mul_const (by positivity)
    apply tendsto_exp_atBot.comp
    simpa only [div_eq_mul_inv, neg_mul, Function.comp_def] using
      tendsto_neg_atTop_atBot.comp hscale
  have hlower := tendsto_const_nhds (x := M) |>.sub (he.const_mul (M * C))
  simp only [mul_zero, sub_zero] at hlower
  have htrunc : Tendsto (fun H : ℝ => ∫ h in (0 : ℝ)..H, K h) atTop (𝓝 M) :=
    hlower.squeeze' tendsto_const_nhds
      ((eventually_ge_atTop 0).mono fun H hH => (hbounds H hH).1)
      ((eventually_ge_atTop 0).mono fun H hH => (hbounds H hH).2)
  have hKfinite (H : ℝ) : IntegrableOn K (Ioc 0 H) :=
    (integrable_const (1 : ℝ)).mono'
      (aemeasurable_restrict_of_antitoneOn measurableSet_Ioc
        ((smooth_limit_antitone k hw hlim).mono Ioc_subset_Ioi_self)).aestronglyMeasurable
      ((ae_restrict_mem (μ := volume) measurableSet_Ioc).mono fun h hh => by
        obtain ⟨hn, hb⟩ := smooth_limit_mem_Icc k hlim hh.1
        simpa only [Real.norm_of_nonneg hn] using hb)
  have hK : IntegrableOn K (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto M 0 hKfinite tendsto_id
    refine htrunc.congr' ((eventually_ge_atTop 0).mono fun H hH => ?_)
    simp only [intervalIntegral.integral_of_le hH]
    exact setIntegral_congr_fun measurableSet_Ioc fun h hh =>
      (Real.norm_of_nonneg (smooth_limit_mem_Icc k hlim hh.1).1).symm
  exact ⟨hK, tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hK tendsto_id) htrunc⟩

end Erdos490Smooth
end


/- BlueKernel -/
section
open Real Filter Finset MeasureTheory Set

open scoped Topology

namespace Erdos490Smooth

open Shift490 Erdos490PrimeCells

theorem smoothKernel_mass (k : ℕ) {w : ℝ} (hw : 0 < w) :
    IntegrableOn (smoothKernel k w hw) (Ioi 0) ∧
      (∫ h in Ioi 0, smoothKernel k w hw h) = exp eulerMascheroniConstant * smallProduct k * w :=
  smooth_limit_mass k hw (fun _ hh => smoothKernel_tendsto k hw hh)

theorem smoothKernel_antitone (k : ℕ) {w : ℝ} (hw : 0 < w) :
    AntitoneOn (smoothKernel k w hw) (Ioi 0) :=
  smooth_limit_antitone k hw (fun _ hh => smoothKernel_tendsto k hw hh)

private theorem monotone_grade (L : Finset ℕ) (j : ℕ) : Monotone (gradeMass L j) := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro V hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2.trans (Nat.floor_mono (exp_le_exp.mpr hxy))⟩
  · intros; positivity

private theorem grade_uniform (i : Label) {a b : ℝ} (ha : 0 < a) (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ h ∈ Icc a b,
      |gradeMass (primeBand t i.lo i.hi) j (t*h) - limitingGrade i j h| < ε := by
  apply eventually_uniform_Icc_of_monotone _ _ (limitingGrade_continuous i j).continuousOn hε
  · filter_upwards [eventually_gt_atTop 0] with t ht
    exact Or.inl (fun x _ y _ h => monotone_grade _ _ (mul_le_mul_of_nonneg_left h ht.le))
  · exact fun h hx => grade_tendsto i j (ha.trans_le hx.1)

theorem kernelOn_uniform (k : ℕ) (i : Label) {a b : ℝ} (ha : 0 < a) (hb : b ≤ i.hi)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ t : ℝ in atTop, ∀ h ∈ Icc a b,
      |F (smoothLabels k (exp (t*i.lo))) (t*h) - kernelOn k i h| < ε := by
  let J := Finset.range (⌊i.hi/i.lo⌋₊+1)
  let V := localProduct (Nat.primesLE k)
  let δ := (ε/2)/((|V|+1)*(J.card+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hall := (Finset.eventually_all (I := J)).mpr (fun j _ => grade_uniform i (b := b) ha j hδ)
  filter_upwards [hall,uniform_sieve_approx k ha i.positive i.nonempty.le (half_pos hε),eventually_gt_atTop 0]
    with t he herr ht
  intro h hh
  have hh0 := ha.trans_le hh.1
  have hhi := hh.2.trans hb
  let A (j : ℕ) := gradeMass (primeBand t i.lo i.hi) j (t*h)
  let B (j : ℕ) := limitingGrade i j h
  have hs : |(∑ j ∈ J, (-1:ℝ)^j * A j) - ∑ j ∈ J,(-1:ℝ)^j * B j| ≤ J.card*δ := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _j ∈ J, δ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [←mul_sub, abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
        exact (he j hj h hh).le
      _ = _ := by simp
  let p := V * ∑ j ∈ J, (-1:ℝ)^j * A j
  have he' : |F (smoothLabels k (exp (t*i.lo))) (t*h) - p| < ε/2 := by
    have hn := herr h ⟨hh.1,hhi⟩
    rw [← primeBand_eq_smoothLabels, signedSum_eq_gradeSum ht i.positive i.nonempty.le hh0 hhi] at hn
    exact hn
  have hdiff : |p - kernelOn k i h| ≤ ε/2 := by
    change |V * _ - V * _| ≤ _
    rw [←mul_sub,abs_mul]
    apply (mul_le_mul_of_nonneg_left hs (abs_nonneg V)).trans
    have hc : |V| * (J.card:ℝ) ≤ (|V|+1)*(J.card+1) := by nlinarith [abs_nonneg V, show (0:ℝ) ≤ J.card by positivity]
    calc
      _ = (|V| * J.card) * δ := by ring
      _ ≤ ((|V|+1)*(J.card+1)) * δ := mul_le_mul_of_nonneg_right hc hδ.le
      _ = _ := by dsimp [δ]; field_simp
  exact (abs_sub_le _ p _).trans_lt (by linarith)

theorem smoothKernel_uniform (k : ℕ) {w a b : ℝ} (hw : 0 < w) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ h ∈ Icc a b,
      |F (smoothLabels k (exp (t*w))) (t*h) - smoothKernel k w hw h| < ε := by
  let i : Label := ⟨w,max w b+1,hw,lt_of_le_of_lt (le_max_left ..) (lt_add_one _)⟩
  have hb : b ≤ i.hi := (le_max_right w b).trans (le_add_of_nonneg_right zero_le_one)
  filter_upwards [kernelOn_uniform k i ha hb hε] with t hh
  intro h hx
  rw [smoothKernel_agrees k i (ha.trans_le hx.1) (hx.2.trans hb)]
  exact hh h hx

end Erdos490Smooth
end


/- KernelRange -/
section
open Real Filter Finset Set

open scoped Topology

namespace Erdos490Smooth

open Shift490 Erdos490PrimeCells

theorem smallProduct_eq_local (k : ℕ) : smallProduct k = localProduct (Nat.primesLE k) := by
  unfold smallProduct localProduct
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE]
  constructor
  · exact fun h => ⟨h.1.2,h.2⟩
  · exact fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩

private theorem no_large_divisor {t w B h : ℝ} (ht : 0 < t) (hh : 0 < h) (hw : h ≤ w) :
    signedSum (primeBand t w B) (t*h) = 1 := by
  let L := primeBand t w B
  have he : L.powerset.filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊) = {∅} := by
    ext V
    simp only [Finset.mem_filter,Finset.mem_powerset,Finset.mem_singleton]
    constructor
    · rintro ⟨hV,hprod⟩
      by_contra hn
      obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      have hpos : 0 < ∏ l ∈ V,l := Finset.prod_pos fun l hl => (Finset.mem_filter.mp (hV hl)).2.pos
      have hp' := (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem id hp)).trans hprod
      have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hV hp)).1).1
      exact (not_lt_of_ge (hp'.trans (Nat.floor_mono (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw ht.le))))) hlow
    · rintro rfl
      simp [Nat.one_le_floor_iff,Real.one_le_exp_iff,(mul_pos ht hh).le]
  change ∑ U ∈ L.powerset.filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊), _ = _
  simp [he]

theorem smoothKernel_initial (k : ℕ) {w h : ℝ} (hw : 0 < w) (hh : 0 < h) (hb : h ≤ w) :
    smoothKernel k w hw h = smallProduct k := by
  apply tendsto_nhds_unique (smoothKernel_tendsto k hw hh)
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [uniform_sieve_approx k hh hw le_rfl he,eventually_gt_atTop 0] with t ht ht0
  have H := ht h ⟨le_rfl,hb⟩
  rw [← primeBand_eq_smoothLabels,no_large_divisor ht0 hh hb,mul_one] at H
  rwa [Real.dist_eq,smallProduct_eq_local]

theorem smoothKernel_range (k : ℕ) {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    smoothKernel k w hw h ∈ Icc 0 (smallProduct k) := by
  refine ⟨(smooth_limit_mem_Icc k (fun _ hx => smoothKernel_tendsto k hw hx) hh).1,?_⟩
  rcases le_total h w with hle|hge
  · exact (smoothKernel_initial k hw hh hle).le
  · rw [← smoothKernel_initial k hw hw le_rfl]
    exact (smooth_limit_antitone k hw (fun _ hx => smoothKernel_tendsto k hw hx)) hw hh hge

end Erdos490Smooth
end


/- BlueMoving -/
section
open Real Filter MeasureTheory Set

open scoped Topology

namespace Erdos490Smooth

open Shift490 Erdos490PrimeCells

theorem blue_strip_minorant (k : ℕ) {w j c : ℝ} (hw : 0 < w) (hj : 0 < j) (hc : 0 ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ r ∈ Icc j (j+1),
      smoothKernel k w hw (j+1) - ε ≤ F (smoothLabels k (exp (t*w))) (t*r-c) := by
  have hd : Tendsto (fun t : ℝ => c/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [hd.eventually_lt_const (half_pos hj),eventually_gt_atTop 0,
    smoothKernel_uniform k hw (half_pos hj) (b := j+1) hε] with t hcut ht hh
  intro r hr
  have hnon : 0 ≤ c/t := div_nonneg hc ht.le
  have hlow : j/2 ≤ r-c/t := by linarith [hr.1]
  have hhigh : r-c/t ≤ j+1 := by linarith [hr.2]
  have hh' := (abs_lt.mp (hh _ ⟨hlow,hhigh⟩)).1
  have hm := smoothKernel_antitone k hw (a := r-c/t) (b := j+1) (lt_of_lt_of_le (half_pos hj) hlow)
    (by change 0 < j+1; linarith) hhigh
  rw [show t*(r-c/t) = t*r-c by field_simp] at hh'
  linarith

end Erdos490Smooth
end


/- BlueRecovery -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells

open scoped Topology

noncomputable section

open Classical

theorem blue_good_recovery {C : Finset ℕ} (hc : ∀ p ∈ C, p.Prime) {b x δ : ℝ}
    (hx : 0 < x) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C)
    (e : ℕ → ℝ) (he : ∀ p ∈ C, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (good : ∀ S ∈ G, ∑ p ∈ S, e p ≤ δ) (j : Finset ℕ → ℝ)
    (hj : ∀ S ∈ G, 0 < j S) (lo : ∀ S ∈ G, x-j S-1+δ < log (∏ p ∈ S, p:ℕ))
    (hi : ∀ S ∈ G, log (∏ p ∈ S, p:ℕ) ≤ x-j S-δ)
    (k : ℕ) {w : ℝ} (hw : 0 < w)
    (sep : ∀ᶠ t : ℝ in atTop, Disjoint (bands b t C) (smoothLabels k (exp (t*w))))
    {u : ℕ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      let t := log n/x
      (∑ S ∈ G, (((∏ p ∈ S, p:ℕ):ℝ)⁻¹ * smoothKernel k w hw (j S+1))) - ε ≤
        density (bands b t C ∪ smoothLabels k (exp (t*w))) n u := by
  let mass (S : Finset ℕ) := (((∏ p ∈ S, p:ℕ):ℝ)⁻¹)
  let kern (S : Finset ℕ) := smoothKernel k w hw (j S+1)
  let H := ∑ S ∈ G, mass S
  have hH : 0 ≤ H := sum_nonneg (fun _ _ => by dsimp [mass]; positivity)
  let η := ε/(2*(H+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have loss : H*η ≤ ε/2 := by
    dsimp [η]
    rw [mul_div_assoc',div_le_iff₀ (by positivity)]
    nlinarith
  let massAt (t : ℝ) (S : Finset ℕ) := ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹
  have lim : Tendsto (fun t => ∑ S ∈ G, massAt t S*(kern S-η)) atTop
      (𝓝 (∑ S ∈ G, mass S*(kern S-η))) := tendsto_finsetSum _ (fun S h =>
    (newProducts_mass S (fun p hp => hc p (hG S h hp)) b).mul_const _)
  have compare : (∑ S ∈ G, mass S*kern S)-ε < ∑ S ∈ G, mass S*(kern S-η) := by
    simp only [mul_sub,sum_sub_distrib,← sum_mul]
    change _ < _ - H*η
    linarith
  have scale : Tendsto (fun n : ℕ => log n/x) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hx
  have kernels := (eventually_all_finset G).mpr (fun S h =>
    blue_strip_minorant k hw (hj S h) (log_natCast_nonneg u) hη)
  filter_upwards [scale.eventually (lim.eventually_const_lt compare),scale.eventually kernels,
    scale.eventually sep,scale.eventually_gt_atTop 0,eventually_gt_atTop (0:ℕ)] with n hsum hk hh ht hn
  let t := log (n:ℝ)/x
  let U := smoothLabels k (exp (t*w))
  have pair (S : Finset ℕ) (hS : S ∈ G) (z : ℕ) (hz : z ∈ newProducts b t S) :
      kern S-η ≤ density U n (u*z) := by
    have hshift := newProduct_displacement ht (fun p hp => hc _ (hG _ hS hp)) e
      (fun p hp => he _ (hG _ hS hp)) hz
    change |log (z:ℝ)/t-log (∏ p ∈ S, p:ℕ)| ≤ ∑ p ∈ S, e p at hshift
    have hdist := (abs_le.mp (hshift.trans (good _ hS)))
    have hs : x-log (z:ℝ)/t ∈ Set.Icc (j S) (j S+1) :=
      ⟨by linarith [hi _ hS,hdist.2],by linarith [lo _ hS,hdist.1]⟩
    have h := hk S hS _ hs
    have hz0 := Nat.pos_of_ne_zero (newProduct_active (hG _ hS) hz).1
    rw [← shifted_density U hn (Nat.mul_pos hu hz0),Nat.cast_mul,
      log_mul (by exact_mod_cast hu.ne') (by exact_mod_cast hz0.ne')]
    have htx : t*x=log (n:ℝ) := div_mul_cancel₀ _ hx.ne'
    change kern S-η ≤ F U (t*(x-log z/t)-log u) at h
    rw [mul_sub,show t*(log z/t)=log z by field_simp [show t ≠ 0 from ht.ne'],htx] at h
    convert h using 2
    ring
  apply hsum.le.trans (le_trans _ (family_density_lower ht.le C U hh G hG n u))
  apply sum_le_sum
  intro S hS
  rw [show massAt t S*(kern S-η) = ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹*(kern S-η) from sum_mul ..]
  exact sum_le_sum fun z hz => mul_le_mul_of_nonneg_left (pair S hS z hz) (by positivity)

end

end Erdos490Transfer
end


/- BlueBins -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells

noncomputable section

open Classical

theorem good_properties {C : Finset ℕ} (hp : ∀ p ∈ C, p.Prime)
    {a b δ : ℝ} {e : ℕ → ℝ} {m : ℕ} (hm : m ∈ goodWindow C a b δ e) :
    m.primeFactors ⊆ C ∧ (∏ p ∈ m.primeFactors, p) = m ∧
      (∑ p ∈ m.primeFactors, e p) ≤ δ ∧ a < log m ∧ log m ≤ b := by
  obtain ⟨hw,hn⟩ := mem_sdiff.mp hm
  obtain ⟨ha,hl,hr⟩ := mem_oldWindow.mp hw
  have hgood : ¬ ((∃ p ∈ C, p^2 ∣ m) ∨ δ ≤ ∑ p ∈ C with p ∣ m, e p) :=
    fun h => hn (mem_filter.mpr ⟨hw,h⟩)
  have hs : m.primeFactors ⊆ C := fun p h => Nat.mem_factoredNumbers'.mp ha p
    (Nat.prime_of_mem_primeFactors h) (Nat.dvd_of_mem_primeFactors h)
  have eq : C.filter (· ∣ m) = m.primeFactors := by
    ext p; simp only [mem_filter,Nat.mem_primeFactors]
    exact ⟨fun h => ⟨hp p h.1,h.2,ha.1⟩,fun h => ⟨hs (Nat.mem_primeFactors.mpr h),h.2.1⟩⟩
  have sq : Squarefree m := Nat.squarefree_iff_prime_squarefree.mpr (fun p hp' hd => by
    have h := Nat.mem_factoredNumbers'.mp ha p hp' (dvd_trans (dvd_mul_right p p) hd)
    exact hgood (.inl ⟨p,h,by simpa [pow_two] using hd⟩))
  exact ⟨hs,Nat.prod_primeFactors_of_squarefree sq,by
    rw [← eq]; exact le_of_not_ge (fun h => hgood (.inr h)),hl,hr⟩

theorem blue_bin_recovery {C : Finset ℕ} (hp : ∀ p ∈ C, p.Prime) {b x δ : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (J : Finset ℕ) (hJ : ∀ j ∈ J, 0 < j)
    (e : ℕ → ℝ) (he : ∀ p ∈ C, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (k : ℕ) {w : ℝ} (hw : 0 < w)
    (sep : ∀ᶠ t : ℝ in atTop, Disjoint (bands b t C) (smoothLabels k (exp (t*w))))
    {u : ℕ} (hu : 0 < u) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, let t := log n/x
      (∑ j ∈ J, recMass (goodWindow C (x-j-1+δ) (x-j-δ) δ e)*smoothKernel k w hw (j+1)) - ε ≤
        density (bands b t C ∪ smoothLabels k (exp (t*w))) n u := by
  let bin (j : ℕ) := goodWindow C (x-j-1+δ) (x-j-δ) δ e
  let A := J.sigma bin
  let g (s : Sigma (fun _ : ℕ => ℕ)) := s.2.primeFactors
  let prop (s : Sigma (fun _ : ℕ => ℕ)) (hs : s ∈ A) := good_properties hp (mem_sigma.mp hs).2
  have inj : Set.InjOn g A := by
    rintro ⟨j,m⟩ h1 ⟨l,n⟩ h2 eq
    have a := prop _ h1
    have d := prop _ h2
    obtain rfl : m=n := a.2.1.symm.trans ((congrArg (fun T : Finset ℕ => ∏ p ∈ T, p) eq).trans d.2.1)
    have same : j=l := by
      rcases lt_trichotomy j l with h|h|h
      · have hl : (j:ℝ)+1 ≤ l := by exact_mod_cast h
        have h1' : x-j-1+δ < log m := a.2.2.2.1
        have h2' : log m ≤ x-l-δ := d.2.2.2.2
        linarith
      · exact h
      · have hl : (l:ℝ)+1 ≤ j := by exact_mod_cast h
        have h1' : x-l-1+δ < log m := d.2.2.2.1
        have h2' : log m ≤ x-j-δ := a.2.2.2.2
        linarith
    cases same; rfl
  let G := A.image g
  let source (S : Finset ℕ) := if h : ∃ s ∈ A, g s=S then h.choose else ⟨0,0⟩
  have inv {s} (hs : s ∈ A) : source (g s) = s := by
    have h : ∃ q ∈ A, g q=g s := ⟨_,hs,rfl⟩
    exact (dif_pos h).trans (inj h.choose_spec.1 hs h.choose_spec.2)
  have member {S} (hS : S ∈ G) : source S ∈ A ∧ g (source S)=S := by
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hS
    rw [inv hs]; exact ⟨hs,rfl⟩
  let index (S : Finset ℕ) := ((source S).1:ℝ)
  have data {S} (hS : S ∈ G) := prop _ (member hS).1
  have hG : ∀ S ∈ G, S ⊆ C := fun S h => by
    rw [← (member h).2]; exact (data h).1
  have hE : ∀ S ∈ G, ∑ p ∈ S, e p ≤ δ := fun S h => by
    rw [← (member h).2]; exact (data h).2.2.1
  have hprod {S} (h : S ∈ G) : (∏ p ∈ S,p) = (source S).2 := by
    nth_rw 1 [← (member h).2]; exact (data h).2.1
  have hr := blue_good_recovery hp hx G hG e he hE index (fun S h => by
    dsimp only [index]
    exact_mod_cast hJ _ (mem_sigma.mp (member h).1).1)
    (fun S h => by rw [hprod h]; exact (data h).2.2.2.1)
    (fun S h => by rw [hprod h]; exact (data h).2.2.2.2) k hw sep hu hε
  apply hr.mono
  intro n hn
  apply le_trans _ hn
  apply sub_le_sub_right
  apply le_of_eq
  rw [show G = A.image g from rfl,sum_image inj]
  dsimp only [A]
  rw [sum_sigma]
  apply sum_congr rfl
  intro j hj
  rw [recMass,sum_mul]
  apply sum_congr rfl
  intro m hm
  have hmem : (⟨j,m⟩ : Sigma (fun _ : ℕ => ℕ)) ∈ A := mem_sigma.mpr ⟨hj,hm⟩
  have hi : index (g ⟨j,m⟩) = j := by simp [index,inv hmem]
  rw [hi,hprod (mem_image_of_mem g hmem),inv hmem]

end

end Erdos490Transfer
end


/- BlueStrips -/
section
open Filter MeasureTheory Set

open scoped Topology

namespace Erdos490PrimeCells

private theorem intervalIntegrable_of_integrableOn_Ioi_zero {K : ℝ → ℝ}
    (hK : IntegrableOn K (Ioi 0)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable K volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (hK.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha)))

theorem strip_sum_integral_comparison {K : ℝ → ℝ}
    (hmono : AntitoneOn K (Ioi 0)) (hK : IntegrableOn K (Ioi 0))
    {D : ℕ} (hD : 1 ≤ D) :
    (∫ z in Ioc 2 ((D : ℝ) + 2), K z) ≤ ∑ j ∈ Finset.Icc 1 D, K ((j : ℝ) + 1) ∧
    (∑ j ∈ Finset.Icc 1 D, K ((j : ℝ) + 1)) ≤ ∫ z in Ioc 1 ((D : ℝ) + 1), K z := by
  have hindices : Finset.Ico 1 (D + 1) = Finset.Icc 1 D := by
    ext j
    simp
  have hD_nonneg : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hsum (c : ℝ) (hc : 0 ≤ c) :
      (∑ j ∈ Finset.Icc 1 D, ∫ z in (j : ℝ) + c..(j : ℝ) + c + 1, K z) =
        ∫ z in 1 + c..(D : ℝ) + 1 + c, K z := by
    have h := intervalIntegral.sum_integral_adjacent_intervals_Ico
      (μ := volume) (f := K) (a := fun j => (j : ℝ) + c) (m := 1) (n := D + 1)
      (by omega) fun j _ => by
        push_cast
        exact intervalIntegrable_of_integrableOn_Ioi_zero hK (by positivity) (by linarith)
    rw [hindices] at h
    push_cast at h
    simpa only [add_right_comm (↑_ : ℝ) 1 c] using h
  constructor
  · rw [← intervalIntegral.integral_of_le (by linarith : (2 : ℝ) ≤ (D : ℝ) + 2),
      show (2 : ℝ) = 1 + 1 by norm_num, ← add_assoc, ← hsum 1 zero_le_one]
    apply Finset.sum_le_sum
    intro j _
    have hleft : 0 < (j : ℝ) + 1 := by positivity
    have hab : (j : ℝ) + 1 ≤ (j : ℝ) + 1 + 1 := by linarith
    calc
      _ ≤ ∫ _ in (j : ℝ) + 1..(j : ℝ) + 1 + 1, K ((j : ℝ) + 1) :=
        intervalIntegral.integral_mono_on hab
          (intervalIntegrable_of_integrableOn_Ioi_zero hK hleft.le hab)
          intervalIntegrable_const (fun _ hz => hmono hleft (hleft.trans_le hz.1) hz.1)
      _ = _ := by simp
  · rw [← intervalIntegral.integral_of_le (by linarith : (1 : ℝ) ≤ (D : ℝ) + 1)]
    have hsum0 := hsum 0 le_rfl
    simp only [add_zero] at hsum0
    rw [← hsum0]
    apply Finset.sum_le_sum
    intro j hj
    have hj_pos : 0 < (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hab : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    calc
      K ((j : ℝ) + 1) = ∫ _ in (j : ℝ)..(j : ℝ) + 1, K ((j : ℝ) + 1) := by simp
      _ ≤ _ := intervalIntegral.integral_mono_on hab intervalIntegrable_const
        (intervalIntegrable_of_integrableOn_Ioi_zero hK hj_pos.le hab)
        (fun _ hz => hmono (hj_pos.trans_le hz.1) (hj_pos.trans_le hab) hz.2)

theorem exists_strip_sum_bounds {K : ℝ → ℝ} {V η : ℝ}
    (hmono : AntitoneOn K (Ioi 0)) (hbound : ∀ z > 0, K z ∈ Icc 0 V)
    (hK : IntegrableOn K (Ioi 0)) (hη : 0 < η) :
    ∃ D : ℕ, 1 ≤ D ∧
      (∫ z in Ioi 0, K z) - 2 * V - η ≤ ∑ j ∈ Finset.Icc 1 D, K ((j : ℝ) + 1) ∧
      (∑ j ∈ Finset.Icc 1 D, K ((j : ℝ) + 1)) ≤ ∫ z in Ioi 0, K z := by
  let J := ∫ z in Ioi 0, K z
  have hcutoff : Tendsto (fun D : ℕ => (D : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hK hcutoff
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_const_lt (sub_lt_self J hη))
  let D := max 1 N
  have hD : 1 ≤ D := le_max_left ..
  have htrunc : J - η < ∫ z in (0 : ℝ)..(D : ℝ) + 2, K z := hN D (le_max_right ..)
  have hfirst : (∫ z in (0 : ℝ)..2, K z) ≤ 2 * V := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ ∫ _ in Ioc (0 : ℝ) 2, V :=
        setIntegral_mono_on (hK.mono_set Ioc_subset_Ioi_self)
          (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc (fun z hz => (hbound z hz.1).2)
      _ = _ := by norm_num [setIntegral_const, measureReal_def, Real.volume_Ioc, smul_eq_mul]
  have hle : (2 : ℝ) ≤ (D : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) D]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_integrableOn_Ioi_zero hK le_rfl (by norm_num : (0 : ℝ) ≤ 2))
    (intervalIntegrable_of_integrableOn_Ioi_zero hK (by norm_num) hle)
  rw [intervalIntegral.integral_of_le hle] at hsplit
  obtain ⟨hlower, hupper⟩ := strip_sum_integral_comparison hmono hK hD
  refine ⟨D, hD, by linarith, hupper.trans ?_⟩
  exact setIntegral_mono_set hK
    ((ae_restrict_mem measurableSet_Ioi).mono fun z hz => (hbound z hz).1)
    ((Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)).eventuallyLE)

end Erdos490PrimeCells

namespace Erdos490Smooth

open Erdos490PrimeCells

end Erdos490Smooth
end


/- Cutoff -/
section
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

end Erdos490PrimeCells
end


/- BlueScale -/
section
namespace Erdos490Transfer

open Asymptotics Finset Filter Real MeasureTheory Shift490 Erdos490Smooth Erdos490PrimeCells

open scoped Topology

noncomputable section

open Classical

def width (y : ℕ) := boundary Mertens.M (y+1)

lemma width_pos (y : ℕ) : 0 < width y := exp_pos _

lemma segment_eq (Y y : ℕ) : primes Y y = smoothLabels (Y-1) y := by
  ext p
  simp only [primes,smoothLabels,mem_filter,mem_Icc,mem_Ioc,Nat.floor_natCast]
  constructor <;> intro h
  · exact ⟨⟨by have := h.2.pos; omega,h.1.2⟩,h.2⟩
  · exact ⟨⟨by omega,h.1.2⟩,h.2⟩

private lemma prod_pos' (n : ℕ) : 0 < smallProduct n := by
  rw [smallProduct_eq_local]
  exact Finset.prod_pos (fun p hp => by
    have h : 1 < (p:ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr h))

private lemma before_eq (n : ℕ) : reciprocalBefore (n+1) =
    ∑ p ∈ (Ioc 0 n).filter Nat.Prime, (p:ℝ)⁻¹ := by
  rw [reciprocalBefore,Nat.range_succ_eq_Icc_zero]
  simp only [sum_filter]
  rw [← add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
  simp

theorem blue_gain_eq {Y y : ℕ} (h : Y ≤ y) :
    exp eulerMascheroniConstant*smallProduct (Y-1)*width y / P (primes Y y) =
    cutoffFactor y := by
  have hk : Y-1 ≤ ⌊(y:ℝ)⌋₊ := by rw [Nat.floor_natCast]; omega
  rw [segment_eq,segment_product hk,Nat.floor_natCast,div_div_eq_mul_div]
  unfold cutoffFactor width boundary
  rw [Nat.floor_natCast,before_eq]
  simp only [one_div]
  change _ = smallProduct y * _ * _
  field_simp [(prod_pos' (Y-1)).ne']

private lemma smallProduct_zero : Tendsto smallProduct atTop (𝓝 0) := by
  have h := (((isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp tendsto_natCast_atTop_atTop).rexp
  have l := (h.const_mul (exp (-eulerMascheroniConstant))).div_atTop
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply l.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with y hy
  change exp (-eulerMascheroniConstant)*exp (Mertens.E₃ (y:ℝ))/log (y:ℝ) = smallProduct y
  simpa only [Nat.floor_natCast,one_div,smallProduct] using
    (Mertens.prod_one_minus_div_prime_eq (by exact_mod_cast hy : 1 < (y:ℝ))).symm

theorem blue_strip_normalized (Y : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∃ D : ℕ, 1 ≤ D ∧
      let T := ∑ j ∈ Icc 1 D, smoothKernel (Y-1) (width y) (width_pos y) (j+1)
      (1-ε)*P (primes Y y) ≤ T ∧ T ≤ (1+ε)*P (primes Y y) := by
  let V := smallProduct (Y-1)
  have hV := prod_pos' (Y-1)
  have lim := cutoffFactor_tendsto.comp tendsto_natCast_atTop_atTop
  have err := (smallProduct_zero.const_mul (2:ℝ)).eventually_lt_const (show 2*0<ε/3 by linarith)
  filter_upwards [eventually_ge_atTop Y,lim.eventually_const_lt (show 1-ε/3 < 1 by linarith),
    lim.eventually_lt_const (show 1 < 1+ε by linarith),err] with y hy hlo hhi hsmall
  let H := P (primes Y y)
  have hH : 0 < H := P_pos _
  let J := exp eulerMascheroniConstant*V*width y
  have he : J/H = cutoffFactor y := blue_gain_eq hy
  change 1-ε/3 < cutoffFactor y at hlo
  change cutoffFactor y < 1+ε at hhi
  rw [← he,lt_div_iff₀ hH] at hlo
  rw [← he,div_lt_iff₀ hH] at hhi
  have eH : 0 < ε/3*H := by positivity
  have hk : Y-1 ≤ ⌊(y:ℝ)⌋₊ := by rw [Nat.floor_natCast]; omega
  have hvh : smallProduct y*H=V := by
    dsimp [H,V]
    rw [segment_eq,segment_product hk,Nat.floor_natCast]
    field_simp [(prod_pos' y).ne']
  have lowV := mul_le_mul_of_nonneg_right hsmall.le hH.le
  obtain ⟨D,hD,hlo',hhi'⟩ := exists_strip_sum_bounds (smoothKernel_antitone (Y-1) (width_pos y))
    (fun _ hh => smoothKernel_range (Y-1) (width_pos y) hh)
    (smoothKernel_mass (Y-1) (width_pos y)).1 eH
  rw [(smoothKernel_mass (Y-1) (width_pos y)).2] at hlo' hhi'
  refine ⟨D,hD,?_,hhi'.trans hhi.le⟩
  change J-2*V-ε/3*H ≤ _ at hlo'
  rw [mul_assoc,hvh] at lowV
  linarith only [hlo,hlo',lowV]

end

end Erdos490Transfer
end


/- BlueStable -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells

noncomputable section

open Classical

private lemma blue_absorb {H T a F₀ E D ε : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hF : 0 ≤ F₀) (hE : 0 ≤ E) (hcap : F₀ ≤ K₀*E)
    (hsmall : (5*K₀+3)*a ≤ ε) (hl : (1-a)*H ≤ T) (hu : T ≤ (1+a)*H)
    (hd : ((1-2*a)*F₀-a*E)*T-a*E*H ≤ D) : F₀ ≤ H⁻¹*D + ε*E := by
  have upper : T ≤ 2*H := hu.trans (mul_le_mul_of_nonneg_right (by linarith) hH.le)
  have h1 := mul_le_mul_of_nonneg_left hl hF
  have h2 := mul_le_mul_of_nonneg_left upper (add_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha) hF) (mul_nonneg ha hE))
  have h3 := mul_le_mul_of_nonneg_right hcap (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 5) ha) hH.le)
  have h4 := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hE hH.le)
  rw [← div_eq_inv_mul,← sub_le_iff_le_add,le_div_iff₀ hH]
  nlinarith only [hd,h1,h2,h3,h4]

theorem blue_stable_recovery (primeEstimate : EffectivePrimeEstimate) (Y : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop, ∀ N : ℕ → ℕ, StrictMono N → ∀ C : ℕ → Finset ℕ,
    (∀ k, C k ⊆ (Ioc y (N k)).filter Nat.Prime) → RoughFlat N C →
    ∀ H : ℝ, 0 ≤ H → ∀ᶠ k in atTop, ∀ x : ℝ, |x-log (N k)| ≤ H →
      ∀ u : ℕ, 0 < u → ∀ᶠ m : ℕ in atTop,
        let t := log m/x
        F (C k) (log (N k)) ≤ (P (primes Y y))⁻¹*
          density (bands Mertens.M t (C k) ∪ smoothLabels (Y-1) (exp (t*width y))) m u +
          ε*(P (C k)/log (N k)) := by
  let a := min (1/8:ℝ) (ε/(5*K₀+3))
  have hden : 0 < 5*K₀+3 := by linarith [K₀_pos]
  have ha : 0 < a := lt_min (by norm_num) (div_pos hε hden)
  have ha8 : a ≤ 1/8 := min_le_left .. 
  have hsmall : (5*K₀+3)*a ≤ ε := by
    rw [mul_comm]; exact (le_div_iff₀ hden).mp (min_le_right ..)
  obtain ⟨c,hc,hdis⟩ := (cell_displacement primeEstimate)
  obtain ⟨p₀,hp₀⟩ := eventually_atTop.mp hdis
  filter_upwards [stable_good_strips hc.le ha (by linarith : a < 1/2) ha,
    blue_strip_normalized Y ha,eventually_ge_atTop p₀] with y hgoods hy hp
  obtain ⟨D,hD,hlo,hhi⟩ := hy
  intro N mono C hC flat H hH
  let J := Icc 1 D
  let E (k : ℕ) := P (C k)/log (N k)
  let M := P (primes Y y)
  let T := ∑ j ∈ J, smoothKernel (Y-1) (width y) (width_pos y) (j+1)
  have hM : 0 < M := P_pos _
  have large := (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp mono.tendsto_atTop)).eventually_gt_atTop (H+2)
  filter_upwards [hgoods N mono C hC flat (H+D+2) (by positivity),large] with k hs hL
  intro x hx u hu
  let L := log (N k:ℝ)
  change H+2 < L at hL
  change |x-L| ≤ H at hx
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < x := by linarith [(abs_le.mp hx).1]
  have hE : 0 < E k := div_pos (P_pos _) hL0
  have hpr : ∀ p ∈ C k, Nat.Prime p := fun p h => (mem_filter.mp (hC _ h)).2
  have high : ∀ p ∈ C k, y < p := fun p h => (mem_Ioc.mp (mem_filter.mp (hC _ h)).1).1
  have hsep : ∀ᶠ t : ℝ in atTop, Disjoint (bands Mertens.M t (C k))
      (smoothLabels (Y-1) (exp (t*width y))) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact disjoint_left.mpr fun {_} hz hu =>
      (bands_above Mertens.M ht high hz).not_ge (mem_Ioc.mp (mem_filter.mp hu).1).2
  have hnew := blue_bin_recovery hpr hx0 ha.le J (fun j h => (mem_Icc.mp h).1)
    (fun p => c/log p^2) (fun p h v hv =>
      hp₀ p (hp.trans (high p h).le) (hpr p h) v ⟨hv.1.le,hv.2⟩)
    (Y-1) (width_pos y) hsep hu (mul_pos (mul_pos ha hE) hM)
  have hsum : ((1-2*a)*F (C k) L-a*E k)*T ≤
      ∑ j ∈ J, recMass (goodWindow (C k) (x-j-1+a) (x-j-a) a (fun p => c/log p^2))*
        smoothKernel (Y-1) (width y) (width_pos y) (j+1) := by
    rw [show T = _ from rfl,mul_sum]
    apply sum_le_sum
    intro j hj
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
    have hjD : (j:ℝ) ≤ D := by exact_mod_cast (mem_Icc.mp hj).2
    have h := hs (x-j) (abs_le.mpr ⟨by change _ ≤ x-j-L; linarith [(abs_le.mp hx).1],
      by change x-j-L ≤ _; linarith [(abs_le.mp hx).2]⟩)
    exact mul_le_mul_of_nonneg_right h (smoothKernel_range _ (width_pos y) (by positivity)).1
  filter_upwards [hnew] with m hm
  apply blue_absorb hM ha.le (by linarith) (F_nonneg ..) hE.le _ hsmall hlo hhi
    ((sub_le_sub_right hsum _).trans hm)
  simpa only [E,L,mul_div_assoc] using counting_bound (C k) L hL0

end

end Erdos490Transfer
end


/- FinalTransfer -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490 Erdos490Smooth Erdos490PrimeCells

noncomputable section

open Classical

private lemma coarse_subset {Y n y} (co : Colors Y n) (b : Bool) :
    roughColor (primes Y y) (pick co b) ⊆ (Ioc y n).filter Nat.Prime := by
  intro p h
  obtain ⟨hC,hlo⟩ := mem_sdiff.mp h
  have hu : p ∈ co.red ∪ co.blue := by cases b <;> simp_all [pick]
  rw [co.cover] at hu
  obtain ⟨hp,pr⟩ := mem_filter.mp hu
  have hpy : y < p := by
    by_contra! hn
    exact hlo (mem_inter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hp).1,hn⟩,pr⟩,hC⟩)
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hpy,(mem_Icc.mp hp).2⟩,pr⟩

private def swap {Y n} (c : Colors Y n) : Colors Y n :=
  ⟨c.blue,c.red,(union_comm ..).trans c.cover,c.separate.symm⟩

private theorem oriented_target {Y y : ℕ} {x : ℝ} (hx : 0 < x) (b : Bool) {Q R : Finset ℕ}
    (hd : Disjoint Q R) (hq : ∀ p ∈ Q, y < p) (hr : ∀ p ∈ R, y < p) :
    ∃ d : ∀ n, Colors Y n, ∀ᶠ n : ℕ in atTop, ∀ u : ℕ,
      let t := log n/x
      density (bands Mertens.M t Q) n u ≤ density (pick (d n) (!b)) n u ∧
      density (bands Mertens.M t R ∪ smoothLabels (Y-1) (exp (t*width y))) n u ≤
        density (pick (d n) b) n u := by
  let pred (n : ℕ) (c : Colors Y n) := ∀ u : ℕ, let t := log n/x
    density (bands Mertens.M t Q) n u ≤ density (pick c (!b)) n u ∧
    density (bands Mertens.M t R ∪ smoothLabels (Y-1) (exp (t*width y))) n u ≤ density (pick c b) n u
  let blank (n : ℕ) : Colors Y n := ⟨∅,primes Y n,empty_union _,disjoint_empty_left _⟩
  let d (n : ℕ) := if h : ∃ c, pred n c then h.choose else blank n
  refine ⟨d,?_⟩
  have lim := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hx
  filter_upwards [lim.eventually (eventually_transplant_cutoff Y y Mertens.M),
    lim.eventually_ge_atTop 0] with n hY ht
  obtain ⟨_,c,hc⟩ := transplant_colors (n:=n) hd hq hr Mertens.M ht hY
  have den {A B : Finset ℕ} {u : ℕ} (h : semigroup A (n/u) ⊆ semigroup B (n/u)) :
      density A n u ≤ density B n u := by
    unfold density
    gcongr
  have he : ∃ c, pred n c := by
    cases b
    · exact ⟨c,fun u => by simpa [pick,width] using And.intro (den (hc u).1) (den (hc u).2)⟩
    · exact ⟨swap c,fun u => by simpa [pick,swap,width] using And.intro (den (hc u).1) (den (hc u).2)⟩
  change pred n (d n)
  simpa only [d,dif_pos he] using he.choose_spec

theorem large_labels_of_red_good (primeEstimate : EffectivePrimeEstimate) (red : RedGoodRealization) : LargeLabelRecovery := by
  intro Y K ε hε hε1
  obtain ⟨B,hB,hy⟩ := (red_from_good primeEstimate) red hε
  obtain ⟨y,⟨hs,hb⟩,hyY⟩ := ((hy.and ((blue_stable_recovery primeEstimate) Y hε)).and (eventually_ge_atTop Y)).exists
  refine ⟨y,hyY,?_⟩
  intro N mono co b
  dsimp only
  let Q (k : ℕ) := roughColor (primes Y y) (pick (co k) (!b))
  let R (k : ℕ) := roughColor (primes Y y) (pick (co k) b)
  intro flat z hz
  obtain ⟨W,hW⟩ := hz
  let H := |W|+B
  have hH : 0 ≤ H := add_nonneg (abs_nonneg _) hB
  have cq (k : ℕ) := coarse_subset (y:=y) (co k) (!b)
  have cr (k : ℕ) := coarse_subset (y:=y) (co k) b
  have blue := hb N mono R cr flat H hH
  let L (k : ℕ) := log (N k:ℝ)
  have lim : Tendsto L atTop atTop :=
    tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp mono.tendsto_atTop)
  have zlim : Tendsto z atTop atTop := tendsto_atTop.mpr (fun r => by
    filter_upwards [hW,lim.eventually_ge_atTop (r+W)] with k h hk
    change |z k-L k| ≤ W at h
    linarith [(abs_le.mp h).1])
  apply Eventually.frequently
  filter_upwards [blue,zlim.eventually hs,hW,lim.eventually_gt_atTop (2*|W|+2),
    lim.eventually_ge_atTop (H/ε),mono.tendsto_atTop.eventually_ge_atTop 2] with k hk hred hw hL hsize hn
  change |z k-L k| ≤ W at hw
  have hL0 : 0 < L k := by linarith [abs_nonneg W]
  obtain ⟨x,hx,hxz,hqr⟩ := hred (N k) hL0 (by
    change L k ≤ 2*z k; linarith [(abs_le.mp hw).1,le_abs_self W]) (Q k) (cq k)
  have near : |x-L k| ≤ H := (abs_sub_le x (z k) (L k)).trans (by
    dsimp [H]; linarith [le_abs_self W])
  have close : (1-ε)*L k ≤ x := by
    have h := (div_le_iff₀ hε).mp hsize
    linarith [(abs_le.mp near).1]
  have sep : Disjoint (Q k) (R k) := by
    apply Disjoint.mono sdiff_subset sdiff_subset
    cases b <;> simp [pick,(co k).separate,(co k).separate.symm]
  obtain ⟨d,hd⟩ := oriented_target (Y:=Y) hx b sep
    (fun p h => (mem_Ioc.mp (mem_filter.mp (cq _ h)).1).1)
    (fun p h => (mem_Ioc.mp (mem_filter.mp (cr _ h)).1).1)
  refine ⟨hn,x,hx,close,d,?_,?_⟩
  · intro i _
    filter_upwards [hd,hqr (i+1) (by omega)] with m hm hr
    exact hr.trans (add_le_add (mul_le_mul_of_nonneg_left (hm (i+1)).1
      (div_nonneg (log_natCast_nonneg m) hx.le)) le_rfl)
  · intro i _
    filter_upwards [hd,hk x near (i+1) (by omega)] with m hm hr
    exact hr.trans (add_le_add (mul_le_mul_of_nonneg_left (hm (i+1)).2 (inv_pos.mpr (P_pos (primes Y y))).le) le_rfl)

end

end Erdos490Transfer
end


/- OldTransport -/
section
namespace Erdos490Transfer

open Finset Filter Real MeasureTheory Erdos490PrimeCells

open scoped Topology ENNReal

noncomputable section

open Classical

def oldLabel (b : ℝ) (p : ℕ) : Label :=
  if h : p.Prime then ⟨boundary b p,boundary b (p+1),exp_pos _,by
    rw [boundary_succ b h]
    exact lt_mul_of_one_lt_right (exp_pos _) (one_lt_exp_iff.mpr (by exact inv_pos.mpr (by exact_mod_cast h.pos)))⟩
  else ⟨1,2,by norm_num,by norm_num⟩

lemma factor_in_cell (i : Label) :
    ∀ᵐ v ∂(limitFactor i : Measure ℝ), v ∈ Set.Ioc i.lo i.hi := by
  unfold limitFactor
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (cellLaw_nonzero i.positive i.nonempty)]
  apply Measure.ae_smul_measure
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

def law (b : ℝ) (s : List ℕ) := labelSum limitFactor (s.map (oldLabel b))

lemma law_displacement (b : ℝ) (s : List ℕ) (e : ℕ → ℝ)
    (he : ∀ p ∈ s, ∀ v ∈ Set.Ioc (oldLabel b p).lo (oldLabel b p).hi, |v-log p| ≤ e p) :
    ∀ᵐ v ∂(law b s : Measure ℝ),
      |v-(s.map (fun p : ℕ => log (p:ℝ))).sum| ≤ (s.map e).sum := by
  induction s with
  | nil =>
    change ∀ᵐ v ∂Measure.dirac (0:ℝ), |v-0| ≤ 0
    simp
  | cons p s ih =>
    let μ := law b s
    let ν := limitFactor (oldLabel b p)
    have ht := ih (fun q h => he q (List.mem_cons_of_mem _ h))
    have hh := (factor_in_cell (oldLabel b p)).mono (fun v h => he p (List.mem_cons_self) v h)
    change ∀ᵐ v ∂(sumLaw μ ν : Measure ℝ), |v-(_+_)| ≤ _+_
    let center := log (p:ℝ)+(s.map (fun q : ℕ => log (q:ℝ))).sum
    let radius := e p+(s.map e).sum
    let f (z : ℝ × ℝ) := z.1+z.2
    have hf : Measurable f := measurable_fst.add measurable_snd
    rw [sumLaw,ProbabilityMeasure.toMeasure_map,ProbabilityMeasure.toMeasure_prod]
    change ∀ᵐ v ∂Measure.map f ((μ:Measure ℝ).prod ν), |v-center| ≤ radius
    apply (ae_map_iff (p:=fun v => |v-center| ≤ radius) hf.aemeasurable (measurableSet_le (measurable_id.sub measurable_const).abs measurable_const)).mpr
    apply (Measure.ae_prod_iff_ae_ae (p:=fun z => |f z-center| ≤ radius) (measurableSet_le (hf.sub measurable_const).abs measurable_const)).mpr
    filter_upwards [ht] with a ha
    filter_upwards [hh] with d hd
    change |a+d-center| ≤ radius
    dsimp only [center,radius]
    rw [abs_le] at ha hd ⊢
    constructor <;> linarith [ha.1,ha.2,hd.1,hd.2]

end

end Erdos490Transfer
end


/- Counting -/
section
open Filter Real

open scoped Topology Chebyshev

namespace Erdos490PrimeCells

noncomputable def piReal (x : ℝ) : ℝ := Nat.primeCounting ⌊x⌋₊

theorem counting_pnt (primeEstimate : EffectivePrimeEstimate) : Tendsto (fun x : ℝ => piReal x * log x / x) atTop (𝓝 1) := by
  obtain ⟨K,hK,hθ⟩ := primeEstimate
  obtain ⟨B,hB,hπ⟩ := Chebyshev.primeCounting_sub_theta_div_log_isBigO.exists_pos
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun x : ℝ => (B+K)/log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := B+K) (f := atTop)).mul (tendsto_inv_atTop_zero.comp tendsto_log_atTop)
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_gt_atTop 1,tendsto_log_atTop.eventually_ge_atTop 1,hθ,hπ.bound]
    with x hx hlog ht hp
  have hx0 : 0 < x := by linarith
  have hl := log_pos hx
  change |piReal x - θ x/log x| ≤ B*|x/log x^2| at hp
  rw [abs_of_pos (div_pos hx0 (pow_pos hl 2))] at hp
  have hrep : piReal x*log x/x-1 =
      (piReal x-θ x/log x)*(log x/x)+(θ x-x)/x := by field_simp; ring
  rw [Real.norm_eq_abs,hrep]
  apply (abs_add_le _ _).trans
  simp only [abs_mul,abs_div,abs_of_pos hx0,abs_of_pos hl]
  calc
    _ ≤ (B*(x/log x^2))*(log x/x)+(K*x/log x^3)/x := by gcongr
    _ = B/log x+K/log x^3 := by field_simp
    _ ≤ B/log x+K/log x := by
      gcongr
      simpa only [pow_one] using pow_le_pow_right₀ hlog (by decide : 1 ≤ 3)
    _ = _ := by ring

theorem counting_at_moving_scale (primeEstimate : EffectivePrimeEstimate) {y : ℝ → ℝ} {w : ℝ} (hw : 0 < w)
    (hy : Tendsto y atTop (𝓝 w)) (c : ℝ) :
    Tendsto (fun t : ℝ => t * piReal (exp (t*y t-c)) / exp (t*y t-c))
      atTop (𝓝 w⁻¹) := by
  have hlin : Tendsto (fun t : ℝ => t * y t - c) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-c) (Filter.Tendsto.atTop_mul_pos hw tendsto_id hy)
  have hp := (counting_pnt primeEstimate).comp (tendsto_exp_atTop.comp hlin)
  have hdiv : Tendsto (fun t : ℝ => c/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply] using
      (tendsto_const_nhds (x := c) (f := atTop)).mul tendsto_inv_atTop_zero
  have hi := (hy.sub hdiv).inv₀ (by simpa using hw.ne' : w-0 ≠ 0)
  have h := hp.mul hi
  simp only [sub_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0,hlin.eventually_gt_atTop 0] with t ht hu
  dsimp only [Function.comp_apply]
  rw [log_exp]
  have hy0 : y t-c/t ≠ 0 := by
    rw [sub_ne_zero,ne_eq,eq_div_iff ht.ne']
    linarith [mul_comm (y t) t]
  field_simp

end Erdos490PrimeCells
end


/- LastLabel -/
section
open Real Filter Finset

open scoped Topology

namespace Erdos490PrimeCells

private lemma count_interval {L U : ℝ} (hLU : L ≤ U) :
    (((Finset.Ioc ⌊L⌋₊ ⌊U⌋₊).filter Nat.Prime).card : ℝ) = piReal U - piReal L := by
  have h : (Nat.primesLE ⌊L⌋₊) ∪ ((Finset.Ioc ⌊L⌋₊ ⌊U⌋₊).filter Nat.Prime) =
      Nat.primesLE ⌊U⌋₊ := by
    ext p
    have hfloor := Nat.floor_mono hLU
    simp only [Finset.mem_union,Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Ioc]
    by_cases hp : p.Prime <;> simp [hp]; omega
  have hd : Disjoint (Nat.primesLE ⌊L⌋₊) ((Finset.Ioc ⌊L⌋₊ ⌊U⌋₊).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Nat.mem_primesLE,Finset.mem_filter,Finset.mem_Ioc] at hp hq
    omega
  have hc := congrArg Finset.card h
  rw [Finset.card_union_of_disjoint hd,Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting] at hc
  unfold piReal
  exact eq_sub_of_add_eq' (mod_cast hc)

noncomputable def cappedCount (t a b z : ℝ) : ℝ :=
  ((Finset.Ioc ⌊exp (t*a)⌋₊ ⌊min (exp (t*b)) (exp z)⌋₊).filter Nat.Prime).card

theorem last_label_interior (primeEstimate : EffectivePrimeEstimate) {a b w : ℝ} (ha : 0 < a) (haw : a < w) (hwb : w < b)
    {y : ℝ → ℝ} (hy : Tendsto y atTop (𝓝 w)) (c : ℝ) :
    Tendsto (fun t : ℝ => t*cappedCount t a b (t*y t-c)/exp (t*y t-c)) atTop (𝓝 w⁻¹) := by
  have hz : Tendsto (fun t : ℝ => c/t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := c) (f := atTop)).mul tendsto_inv_atTop_zero
  have hn : Tendsto (fun t : ℝ => y t - c/t) atTop (𝓝 w) := by simpa using hy.sub hz
  have hu := (counting_at_moving_scale primeEstimate) (ha.trans haw) hy c
  have hlow := (counting_at_moving_scale primeEstimate) ha (tendsto_const_nhds (x := a)) 0
  simp only [sub_zero] at hlow
  have hgap := tendsto_id.atTop_mul_pos (sub_pos.mpr haw)
    (hy.sub_const a)
  have hg : Tendsto (fun t : ℝ => exp (-(t*(y t-a))+c)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_atBot_add_const_right atTop c (tendsto_neg_atTop_atBot.comp hgap))
  have h := hu.sub (hlow.mul hg)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0, hn.eventually (Ioi_mem_nhds haw), hn.eventually_lt_const hwb]
    with t ht h1 h2
  change a < y t - c / t at h1
  change y t - c / t < b at h2
  have htne := ht.ne'
  have heq : t*(y t-c/t) = t*y t-c := by field_simp
  have hl : t*a < t*y t-c := heq ▸ mul_lt_mul_of_pos_left h1 ht
  have hh : t*y t-c < t*b := heq ▸ mul_lt_mul_of_pos_left h2 ht
  rw [cappedCount,min_eq_right (exp_le_exp.mpr hh.le),count_interval (exp_le_exp.mpr hl.le)]
  have he : exp (-(t*(y t-a))+c) = exp (t*a)/exp (t*y t-c) := by
    rw [← exp_sub]; congr 1; ring
  rw [he]
  field_simp

end Erdos490PrimeCells
end


/- Envelope -/
section
open Finset Real Filter

open scoped Topology

namespace Erdos490PrimeCells

private theorem cappedCount_le (t a b z : ℝ) : cappedCount t a b z ≤ piReal (exp z) := by
  unfold cappedCount piReal
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast Finset.card_le_card (by
    intro p hp
    obtain ⟨h,hp'⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp h).2.trans (Nat.floor_mono (min_le_right _ _)),hp'⟩)

private theorem cappedCount_zero {t a b z : ℝ} (hz : z ≤ t*a) : cappedCount t a b z = 0 := by
  unfold cappedCount
  have hle := Nat.floor_mono ((min_le_right (exp (t*b)) (exp z)).trans (exp_le_exp.mpr hz))
  simp [Finset.Ioc_eq_empty (not_lt_of_ge hle)]

theorem uniform_last_label_bound (primeEstimate : EffectivePrimeEstimate) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℝ, t*cappedCount t a b z / exp z ≤ 2/a := by
  have hb := (counting_pnt primeEstimate).eventually_lt_const (by norm_num : (1:ℝ) < 2)
  obtain ⟨X,hX⟩ := eventually_atTop.mp hb
  have hlim : Tendsto (fun t : ℝ => exp (t*a)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const ha)
  filter_upwards [eventually_gt_atTop 0,hlim.eventually_ge_atTop X] with t ht hta
  intro z
  by_cases h : z ≤ t*a
  · rw [cappedCount_zero h,mul_zero,zero_div]
    positivity
  have hx := hX (exp z) (hta.trans (exp_le_exp.mpr (le_of_not_ge h)))
  simp only [log_exp] at hx
  have hz : 0 < z := (mul_pos ht ha).trans (lt_of_not_ge h)
  have hx' : piReal (exp z) * z ≤ 2 * exp z := (le_of_lt ((div_lt_iff₀ (exp_pos z)).mp hx))
  have hn : 0 ≤ piReal (exp z) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) hn
  calc
    _ ≤ t*piReal (exp z)/exp z := by gcongr; exact cappedCount_le _ _ _ _
    _ ≤ _ := by
      rw [div_le_div_iff₀ (exp_pos z) ha]
      nlinarith only [hh,hx']

end Erdos490PrimeCells
end


/- MovingLabel -/
section
open Filter MeasureTheory Real Set

open scoped Topology

namespace Erdos490PrimeCells

noncomputable def movingLabelKernel (i : Label) (c t w : ℝ) : ℝ :=
  t * exp (-(t * w - c)) * cappedCount t i.lo i.hi (t * w - c)

theorem movingLabelKernel_eq_div (i : Label) (c t w : ℝ) :
    movingLabelKernel i c t w = t * cappedCount t i.lo i.hi (t * w - c) / exp (t * w - c) := by
  rw [movingLabelKernel, exp_neg, div_eq_mul_inv, mul_right_comm]

theorem movingLabelKernel_nonneg (i : Label) (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (w : ℝ) :
    0 ≤ movingLabelKernel i c t w := by
  unfold movingLabelKernel cappedCount
  positivity

theorem movingLabelKernel_measurable (i : Label) (c t : ℝ) :
    Measurable (movingLabelKernel i c t) := by
  let count (n : ℕ) : ℝ := ((Finset.Ioc ⌊exp (t * i.lo)⌋₊ n).filter Nat.Prime).card
  have hcount : Measurable count := measurable_of_countable count
  have hcut : Measurable (fun w : ℝ => min (exp (t * i.hi)) (exp (t * w - c))) := by
    fun_prop
  exact (by fun_prop : Measurable (fun w : ℝ => t * exp (-(t * w - c)))).mul
    (hcount.comp (Nat.measurable_floor.comp hcut))

private theorem movingLabelKernel_joint (primeEstimate : EffectivePrimeEstimate) (i : Label) (c : ℝ) {w : ℝ} (hw : w ∈ Ioo i.lo i.hi) :
    Tendsto (fun p : ℝ × ℝ => movingLabelKernel i c p.1 p.2)
      (atTop ×ˢ 𝓝 w) (𝓝 w⁻¹) := by
  apply tendsto_of_subseq_tendsto
  intro u hu
  have ht : Tendsto (fun n => (u n).1) atTop atTop := tendsto_fst.comp hu
  have hv : Tendsto (fun n => (u n).2) atTop (𝓝 w) := tendsto_snd.comp hu
  
  obtain ⟨φ, hφ, hmono⟩ := strictMono_subseq_of_tendsto_atTop ht
  let T (n : ℕ) := (u (φ n)).1
  let W (n : ℕ) := (u (φ n)).2
  have hT : Function.Injective T := hmono.injective
  have ht' : Tendsto T atTop atTop := ht.comp hφ.tendsto_atTop
  have hw' : Tendsto W atTop (𝓝 w) := hv.comp hφ.tendsto_atTop
  let z := Function.extend T W (fun _ => w)
  have hz : Tendsto z atTop (𝓝 w) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hw' ε hε)
    filter_upwards [eventually_ge_atTop (T N)] with t htN
    by_cases ht : ∃ n, T n = t
    · obtain ⟨n, rfl⟩ := ht
      rw [show z (T n) = W n from hT.extend_apply W _ n]
      exact hN n (hmono.le_iff_le.mp htN)
    · rw [show z t = w from Function.extend_apply' W _ _ ht, dist_self]
      exact hε
  refine ⟨φ, ?_⟩
  have h := ((last_label_interior primeEstimate) i.positive hw.1 hw.2 hz c).comp ht'
  refine h.congr fun n => ?_
  change T n * cappedCount (T n) i.lo i.hi (T n * z (T n) - c) /
      exp (T n * z (T n) - c) = movingLabelKernel i c (T n) (W n)
  rw [show z (T n) = W n from hT.extend_apply W _ n, movingLabelKernel_eq_div]

theorem movingLabelKernel_uniform (primeEstimate : EffectivePrimeEstimate) (i : Label) (c : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hKi : K ⊆ Ioo i.lo i.hi) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ w ∈ K, |movingLabelKernel i c t w - w⁻¹| < ε := by
  have hlocal : TendstoLocallyUniformlyOn (movingLabelKernel i c) (fun w => w⁻¹) atTop
      (Ioo i.lo i.hi) := by
    apply isOpen_Ioo.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro w hw
    apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
    have hinv := (tendsto_snd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 w) (𝓝 w)).inv₀
      (i.positive.trans hw.1).ne'
    simpa only [dist_self] using hinv.dist ((movingLabelKernel_joint primeEstimate) i c hw)
  have hunif := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hlocal.mono hKi)
  simpa only [dist_comm _ (movingLabelKernel i c _ _), Real.dist_eq] using
    Metric.tendstoUniformlyOn_iff.mp hunif ε hε

private def stripGap (i : Label) (w : ℝ) : ℝ := min (w - i.lo) (i.hi - w)

private noncomputable def interiorWeight (i : Label) (n : ℕ) (w : ℝ) : ℝ :=
  max 0 (min 1 (((n : ℝ) + 1) * stripGap i w - 1)) * (max i.lo w)⁻¹

private theorem interiorWeight_bounds (i : Label) (n : ℕ) (w : ℝ) :
    0 ≤ interiorWeight i n w ∧ interiorWeight i n w ≤ (max i.lo w)⁻¹ := by
  have hp : 0 ≤ (max i.lo w)⁻¹ := inv_nonneg.mpr (i.positive.le.trans (le_max_left _ _))
  exact ⟨mul_nonneg (le_max_left _ _) hp,
    mul_le_of_le_one_left hp (max_le zero_le_one (min_le_left _ _))⟩

private theorem interiorWeight_zero (i : Label) (n : ℕ) (w : ℝ)
    (h : ((n : ℝ) + 1) * stripGap i w ≤ 1) : interiorWeight i n w = 0 := by
  have hm : min 1 (((n : ℝ) + 1) * stripGap i w - 1) ≤ 0 :=
    (min_le_right _ _).trans (sub_nonpos.mpr h)
  simp [interiorWeight, max_eq_left hm]

private noncomputable def interiorTest (i : Label) (x : ℝ) (n : ℕ) :
    BoundedContinuousFunction ℝ ℝ :=
  .ofNormedAddCommGroup (fun y => interiorWeight i n (x - y)) (by
    unfold interiorWeight stripGap
    exact (by fun_prop : Continuous fun y : ℝ =>
      max 0 (min 1 (((n : ℝ) + 1) * min (x - y - i.lo) (i.hi - (x - y)) - 1))).mul
        ((by fun_prop : Continuous fun y : ℝ => max i.lo (x - y)).inv₀ fun y =>
          (i.positive.trans_le (le_max_left i.lo (x - y))).ne')) i.lo⁻¹ (fun y => by
    obtain ⟨hn, hb⟩ := interiorWeight_bounds i n (x - y)
    rw [Real.norm_of_nonneg hn]
    exact hb.trans (inv_anti₀ i.positive (le_max_left _ _)))

private theorem interiorTest_tendsto (i : Label) (x y : ℝ) :
    Tendsto (fun n : ℕ => interiorTest i x n y) atTop
      (𝓝 ((Ioo (x - i.hi) (x - i.lo)).indicator (fun v => (x - v)⁻¹) y)) := by
  change Tendsto (fun n : ℕ => interiorWeight i n (x - y)) atTop (𝓝 _)
  by_cases hy : y ∈ Ioo (x - i.hi) (x - i.lo)
  · have ha : i.lo < x - y := by linarith [hy.2]
    have hg : 0 < stripGap i (x - y) := lt_min (by linarith [hy.2]) (by linarith [hy.1])
    have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * stripGap i (x - y)) atTop atTop :=
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_mul_const hg
    rw [Set.indicator_of_mem hy]
    apply tendsto_const_nhds.congr'
    filter_upwards [hn.eventually_ge_atTop 2] with n hn
    have hh : 1 ≤ ((n : ℝ) + 1) * stripGap i (x - y) - 1 := by linarith
    simp [interiorWeight, min_eq_left hh, max_eq_right ha.le]
  · have hg : stripGap i (x - y) ≤ 0 := by
      by_contra! h
      obtain ⟨ha, hb⟩ := lt_min_iff.mp h
      exact hy ⟨by linarith, by linarith⟩
    rw [Set.indicator_of_notMem hy]
    apply tendsto_const_nhds.congr
    intro n
    exact (interiorWeight_zero i n (x - y)
      ((mul_nonpos_of_nonneg_of_nonpos (by positivity) hg).trans zero_le_one)).symm

private theorem integral_interiorTest_tendsto (i : Label) (x : ℝ) (μ : ProbabilityMeasure ℝ) :
    Tendsto (fun n : ℕ => ∫ y, interiorTest i x n y ∂(μ : Measure ℝ)) atTop
      (𝓝 (∫ y in Ioo (x - i.hi) (x - i.lo), (x - y)⁻¹ ∂(μ : Measure ℝ))) := by
  rw [← integral_indicator measurableSet_Ioo]
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall fun n => (interiorTest i x n).continuous.aestronglyMeasurable
  · refine ⟨i.lo⁻¹, Eventually.of_forall fun n => ae_of_all _ fun y => ?_⟩
    obtain ⟨hn, hb⟩ := interiorWeight_bounds i n (x - y)
    change ‖interiorWeight i n (x - y)‖ ≤ i.lo⁻¹
    rw [Real.norm_of_nonneg hn]
    exact hb.trans (inv_anti₀ i.positive (le_max_left _ _))
  · exact ae_of_all _ (interiorTest_tendsto i x)

private theorem interiorTest_eventually_le_kernel (primeEstimate : EffectivePrimeEstimate) (i : Label) (x c : ℝ) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, ∀ y, interiorTest i x n y - δ ≤ movingLabelKernel i c t (x - y) := by
  let d := ((n : ℝ) + 1)⁻¹
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : 0 < d := inv_pos.mpr hn
  let K := Icc (i.lo + d) (i.hi - d)
  have hKi : K ⊆ Ioo i.lo i.hi := by
    intro w hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  filter_upwards [(movingLabelKernel_uniform primeEstimate) i c (K := K) isCompact_Icc hKi hδ,
    eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro y
  let w := x - y
  change interiorWeight i n w - δ ≤ movingLabelKernel i c t w
  by_cases hw : w ∈ K
  · have hb := (interiorWeight_bounds i n w).2
    rw [max_eq_right (hKi hw).1.le] at hb
    linarith [(abs_lt.mp (ht w hw)).1]
  · have hb : ((n : ℝ) + 1) * stripGap i w ≤ 1 := by
      by_contra! h
      have hg : d < stripGap i w := by
        rw [show d = 1 / ((n : ℝ) + 1) by simp [d], div_lt_iff₀ hn, mul_comm]
        exact h
      obtain ⟨hl, hr⟩ := lt_min_iff.mp hg
      exact hw ⟨by linarith, by linarith⟩
    rw [interiorWeight_zero i n w hb]
    linarith [movingLabelKernel_nonneg i c ht0 w]

theorem movingLabel_integral_lower (primeEstimate : EffectivePrimeEstimate) (i : Label) (L : List Label) (x c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      (∫ y in Ioo (x - i.hi) (x - i.lo), (x - y)⁻¹ ∂(labelSum limitFactor L : Measure ℝ)) - ε ≤
        ∫ y, movingLabelKernel i c t (x - y) ∂(labelSum (primeFactor t) L : Measure ℝ) := by
  let μ := labelSum limitFactor L
  let A := ∫ y in Ioo (x - i.hi) (x - i.lo), (x - y)⁻¹ ∂(μ : Measure ℝ)
  have hA : ∀ᶠ n : ℕ in atTop, A - ε / 3 < ∫ y, interiorTest i x n y ∂(μ : Measure ℝ) :=
    (integral_interiorTest_tendsto i x μ).eventually_const_lt (by dsimp [A]; linarith)
  obtain ⟨n, hn⟩ := hA.exists
  let g := interiorTest i x n
  have hweak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (labelSum_tendsto L)) g
  have hg : ∀ᶠ t : ℝ in atTop, (∫ y, g y ∂(μ : Measure ℝ)) - ε / 3 <
      ∫ y, g y ∂(labelSum (primeFactor t) L : Measure ℝ) :=
    hweak.eventually_const_lt (by linarith)
  filter_upwards [hg, (interiorTest_eventually_le_kernel primeEstimate) i x c n (by positivity : 0 < ε / 3),
    (uniform_last_label_bound primeEstimate) i.positive i.hi, eventually_ge_atTop (0 : ℝ)] with t hgt hpt henv ht
  let ν := labelSum (primeFactor t) L
  have hmeas : Measurable (fun y => movingLabelKernel i c t (x - y)) :=
    (movingLabelKernel_measurable i c t).comp (by fun_prop)
  have hi : Integrable (fun y => movingLabelKernel i c t (x - y)) (ν : Measure ℝ) := by
    apply (integrable_const (2 / i.lo)).mono' hmeas.aestronglyMeasurable
    apply ae_of_all
    intro y
    rw [Real.norm_of_nonneg (movingLabelKernel_nonneg i c ht (x - y)), movingLabelKernel_eq_div]
    exact henv _
  have hgi : Integrable (fun y => g y) (ν : Measure ℝ) := g.integrable (μ := (ν : Measure ℝ))
  have hci : Integrable (fun _ : ℝ => ε / 3) (ν : Measure ℝ) := integrable_const _
  change ∀ y, g y - ε / 3 ≤ movingLabelKernel i c t (x - y) at hpt
  have hcomp : (∫ y, g y - ε / 3 ∂(ν : Measure ℝ)) ≤
      ∫ y, movingLabelKernel i c t (x - y) ∂(ν : Measure ℝ) :=
    integral_mono (hgi.sub hci) hi hpt
  rw [integral_sub hgi hci] at hcomp
  simp only [integral_const, probReal_univ, one_smul] at hcomp
  change A - ε ≤ ∫ y, movingLabelKernel i c t (x - y) ∂(ν : Measure ℝ)
  change A - ε / 3 < ∫ y, g y ∂(μ : Measure ℝ) at hn
  change (∫ y, g y ∂(μ : Measure ℝ)) - ε / 3 < ∫ y, g y ∂(ν : Measure ℝ) at hgt
  linarith

end Erdos490PrimeCells
end


/- LabelDensity -/
section
open MeasureTheory Real Set

open scoped ENNReal

namespace Erdos490PrimeCells

noncomputable def labelDensity (i : Label) (L : List Label) (x : ℝ) : ℝ :=
  ∫ y in Ioo (x - i.hi) (x - i.lo), (x - y)⁻¹ ∂(labelSum limitFactor L : Measure ℝ)

private noncomputable def openBand (i : Label) (t : ℝ) : ℝ :=
  (Ioo i.lo i.hi).indicator (fun v : ℝ => v⁻¹) t

private theorem openBand_measurable (i : Label) : Measurable (openBand i) :=
  measurable_id.inv.indicator measurableSet_Ioo

private theorem openBand_bounds (i : Label) (t : ℝ) :
    0 ≤ openBand i t ∧ openBand i t ≤ i.lo⁻¹ := by
  by_cases ht : t ∈ Ioo i.lo i.hi
  · rw [openBand, indicator_of_mem ht]
    exact ⟨inv_nonneg.mpr (i.positive.trans ht.1).le, inv_anti₀ i.positive ht.1.le⟩
  · rw [openBand, indicator_of_notMem ht]
    exact ⟨le_rfl, inv_nonneg.mpr i.positive.le⟩

private theorem labelDensity_eq_integral (i : Label) (L : List Label) (x : ℝ) :
    labelDensity i L x = ∫ y, openBand i (x - y) ∂(labelSum limitFactor L : Measure ℝ) := by
  rw [labelDensity, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change (Ioo (x - i.hi) (x - i.lo)).indicator (fun v => (x - v)⁻¹) y =
    (Ioo i.lo i.hi).indicator (fun v => v⁻¹) (x - y)
  have h : y ∈ Ioo (x - i.hi) (x - i.lo) ↔ x - y ∈ Ioo i.lo i.hi := by
    simp only [mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hy : y ∈ Ioo (x - i.hi) (x - i.lo)
  · rw [indicator_of_mem hy, indicator_of_mem (h.mp hy)]
  · rw [indicator_of_notMem hy, indicator_of_notMem (mt h.mpr hy)]

private theorem openBand_integrable (i : Label) (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ) :
    Integrable (fun y => openBand i (x - y)) μ := by
  have hm : Measurable (fun y : ℝ => openBand i (x - y)) :=
    (openBand_measurable i).comp (by fun_prop)
  apply (integrable_const i.lo⁻¹).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun y => by
    obtain ⟨hn, hb⟩ := openBand_bounds i (x - y)
    rwa [Real.norm_of_nonneg hn]

theorem labelDensity_bounds (i : Label) (L : List Label) (x : ℝ) :
    0 ≤ labelDensity i L x ∧ labelDensity i L x ≤ i.lo⁻¹ := by
  rw [labelDensity_eq_integral]
  refine ⟨integral_nonneg fun y => (openBand_bounds i (x - y)).1, ?_⟩
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono (openBand_integrable i (labelSum limitFactor L : Measure ℝ) x)
      (integrable_const i.lo⁻¹) (fun y => (openBand_bounds i (x - y)).2)

private theorem ofReal_labelDensity (i : Label) (L : List Label) (x : ℝ) :
    ENNReal.ofReal (labelDensity i L x) =
      ∫⁻ y, ENNReal.ofReal (openBand i (x - y)) ∂(labelSum limitFactor L : Measure ℝ) := by
  rw [labelDensity_eq_integral, ofReal_integral_eq_lintegral_ofReal]
  · exact openBand_integrable i _ x
  · exact ae_of_all _ fun y => (openBand_bounds i (x - y)).1

theorem labelDensity_measurable (i : Label) (L : List Label) : Measurable (labelDensity i L) := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (openBand i (p.1 - p.2))) :=
    ((openBand_measurable i).comp (by fun_prop)).ennreal_ofReal
  have hg := (hm.lintegral_prod_right' (ν := (labelSum limitFactor L : Measure ℝ))).ennreal_toReal
  have he : (fun x => (∫⁻ y, ENNReal.ofReal (openBand i (x - y))
      ∂(labelSum limitFactor L : Measure ℝ)).toReal) = labelDensity i L := by
    funext x
    rw [← ofReal_labelDensity, ENNReal.toReal_ofReal (labelDensity_bounds i L x).1]
  rw [← he]
  exact hg

private theorem cellLaw_mass (i : Label) :
    (cellLaw i.lo i.hi i.positive i.nonempty.le : Measure ℝ) univ =
      ENNReal.ofReal (log (i.hi / i.lo)) := by
  change ((volume.restrict (Ioc i.lo i.hi)).withDensity (fun t => ENNReal.ofReal t⁻¹)) univ = _
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le i.nonempty.le]
    simpa only [one_div] using congrArg ENNReal.ofReal
      (integral_inv_of_pos i.positive (i.positive.trans i.nonempty))
  · exact (ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le i.nonempty.le]
      exact continuousOn_id.inv₀ (fun t ht => (i.positive.trans_le ht.1).ne'))).1
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
      inv_nonneg.mpr (i.positive.trans ht.1).le

private theorem cellLaw_eq_smul (i : Label) :
    (cellLaw i.lo i.hi i.positive i.nonempty.le : Measure ℝ) =
      ENNReal.ofReal (log (i.hi / i.lo)) • (limitFactor i : Measure ℝ) := by
  let ν := cellLaw i.lo i.hi i.positive i.nonempty.le
  have h := congrArg (fun m : FiniteMeasure ℝ => (m : Measure ℝ)) ν.self_eq_mass_smul_normalize
  rw [FiniteMeasure.toMeasure_smul, ← Measure.coe_nnreal_smul, FiniteMeasure.ennreal_mass,
    cellLaw_mass] at h
  exact h

private theorem lintegral_openBand_translate (i : Label) {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (y : ℝ) :
    (∫⁻ x, ENNReal.ofReal (openBand i (x - y)) * φ x) =
      ∫⁻ t, φ (y + t) ∂(cellLaw i.lo i.hi i.positive i.nonempty.le : Measure ℝ) := by
  calc
    _ = ∫⁻ t, ENNReal.ofReal (openBand i t) * φ (y + t) := by
      simpa only [add_sub_cancel_left] using
        (lintegral_add_left_eq_self (μ := (volume : Measure ℝ))
          (fun x => ENNReal.ofReal (openBand i (x - y)) * φ x) y).symm
    _ = ∫⁻ t in Ioo i.lo i.hi, ENNReal.ofReal t⁻¹ * φ (y + t) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Ioo i.lo i.hi <;> simp [openBand, ht]
    
    _ = ∫⁻ t in Ioc i.lo i.hi, ENNReal.ofReal t⁻¹ * φ (y + t) := by
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
    _ = _ := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul _ (measurable_id.inv.ennreal_ofReal)
        (hφ.comp (by fun_prop))

theorem labelDensity_withDensity (i : Label) (L : List Label) :
    volume.withDensity (fun x => ENNReal.ofReal (labelDensity i L x)) =
      ENNReal.ofReal (log (i.hi / i.lo)) • (labelSum limitFactor (i :: L) : Measure ℝ) := by
  let μ : Measure ℝ := labelSum limitFactor L
  let ν : Measure ℝ := cellLaw i.lo i.hi i.positive i.nonempty.le
  let add : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  have hadd : Measurable add := by fun_prop
  have hsum : Measure.map add (μ.prod ν) =
      ENNReal.ofReal (log (i.hi / i.lo)) • (labelSum limitFactor (i :: L) : Measure ℝ) := by
    change Measure.map add ((labelSum limitFactor L : Measure ℝ).prod
      (cellLaw i.lo i.hi i.positive i.nonempty.le : Measure ℝ)) = _
    rw [cellLaw_eq_smul, Measure.prod_smul_right, Measure.map_smul]
    rfl
  rw [← hsum]
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hK : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (openBand i (p.1 - p.2)) * φ p.1) :=
    (((openBand_measurable i).comp (by fun_prop)).ennreal_ofReal).mul (hφ.comp measurable_fst)
  rw [lintegral_withDensity_eq_lintegral_mul _ (labelDensity_measurable i L).ennreal_ofReal hφ,
    lintegral_map hφ hadd]
  rw [lintegral_prod (fun p => φ (add p)) (hφ.comp hadd).aemeasurable]
  calc
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (openBand i (x - y)) * φ x ∂μ := by
      apply lintegral_congr
      intro x
      rw [Pi.mul_apply, ofReal_labelDensity]
      exact (lintegral_mul_const _ ((openBand_measurable i).comp (by fun_prop)).ennreal_ofReal).symm
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (openBand i (x - y)) * φ x ∂volume ∂μ :=
      lintegral_lintegral_swap (μ := (volume : Measure ℝ)) (ν := μ)
        (f := fun x y => ENNReal.ofReal (openBand i (x - y)) * φ x) hK.aemeasurable
    _ = _ := lintegral_congr (lintegral_openBand_translate i hφ)

theorem integral_mul_labelDensity (i : Label) (L : List Label) (φ : ℝ → ℝ) :
    (∫ x, φ x * labelDensity i L x) =
      log (i.hi / i.lo) * (∫ x, φ x ∂(labelSum limitFactor (i :: L) : Measure ℝ)) := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    (labelDensity_measurable i L).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) φ
  rw [labelDensity_withDensity, integral_smul_measure,
    ENNReal.toReal_ofReal (log_nonneg ((one_le_div i.positive).2 i.nonempty.le))] at h
  simpa only [smul_eq_mul, ENNReal.toReal_ofReal (labelDensity_bounds i L _).1, mul_comm] using h.symm

end Erdos490PrimeCells
end


/- RedSampling -/
section
open MeasureTheory Real Set

open scoped Interval

namespace Erdos490PrimeCells

theorem redSampling_weight_integral {z B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ) :
    (∫ x in Icc (z - B - δ) (z + δ), exp (x - z - δ)) =
      1 - exp (-B - 2 * δ) := by
  have hab : z - B - δ ≤ z + δ := by linarith
  have hcont : Continuous (fun x : ℝ => exp (x - z - δ)) := by fun_prop
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ => exp (t - z - δ)) (exp (x - z - δ)) x := by
    simpa only [id_eq, mul_one] using (((hasDerivAt_id x).sub_const z).sub_const δ).exp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hcont.intervalIntegrable _ _)]
  rw [show z + δ - z - δ = 0 by ring, exp_zero,
    show z - B - δ - z - δ = -B - 2 * δ by ring]

theorem redSampling_integral_lower {ι : Type*} (S : Finset ι) (y c : ι → ℝ)
    (μ : ι → ProbabilityMeasure ℝ) (d : ι → ℝ → ℝ) {z B δ : ℝ}
    (hy : ∀ s ∈ S, y s ∈ Icc (z - B) z) (hc : ∀ s ∈ S, 0 ≤ c s)
    (hidentity : ∀ s ∈ S, ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x, φ x * d s x) = ∫ x, φ x ∂(μ s : Measure ℝ))
    (hsupport : ∀ s ∈ S, ∀ᵐ x ∂(μ s : Measure ℝ), x ∈ Icc (y s - δ) (y s + δ)) :
    IntegrableOn (fun x => exp (x - z - δ) * ∑ s ∈ S, c s * d s x)
      (Icc (z - B - δ) (z + δ)) ∧
    exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z)) ≤
      ∫ x in Icc (z - B - δ) (z + δ), exp (x - z - δ) * ∑ s ∈ S, c s * d s x := by
  let W := Icc (z - B - δ) (z + δ)
  let w (x : ℝ) := exp (x - z - δ)
  let φ := W.indicator w
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hφ : Measurable φ := hw.indicator measurableSet_Icc
  have hw_bound : ∀ x ∈ W, ‖w x‖ ≤ 1 := by
    intro x hx
    rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
    have hupper : x ≤ z + δ := hx.2
    linarith
  have hφ_bound (x : ℝ) : ‖φ x‖ ≤ 1 := by
    change ‖W.indicator w x‖ ≤ 1
    by_cases hx : x ∈ W
    · rw [indicator_of_mem hx]
      exact hw_bound x hx
    · rw [indicator_of_notMem hx, norm_zero]
      exact zero_le_one
  have hterm (s : ι) (hs : s ∈ S) :
      IntegrableOn (fun x => w x * (c s * d s x)) W := by
    have hm : (∫ x, d s x) = 1 := by
      simpa only [one_mul, integral_const, probReal_univ, one_smul] using
        hidentity s hs (fun _ => 1) measurable_const (fun _ => by simp)
    have hdi : Integrable (d s) := by
      by_contra h
      rw [integral_undef h] at hm
      exact zero_ne_one hm
    have hw_bound_ae : ∀ᵐ x ∂(volume.restrict W : Measure ℝ), ‖w x‖ ≤ 1 :=
      (ae_restrict_mem measurableSet_Icc).mono hw_bound
    simpa only [IntegrableOn, mul_comm] using
      ((hdi.integrableOn (s := W)).const_mul (c s)).mul_bdd
        hw.aestronglyMeasurable hw_bound_ae
  have hpoint (s : ι) (hs : s ∈ S) :
      exp (-2 * δ) * exp (y s - z) ≤ ∫ x in W, w x * d s x := by
    have htest : (∫ x in W, w x * d s x) = ∫ x, φ x ∂(μ s : Measure ℝ) := by
      rw [← integral_indicator (s := W) measurableSet_Icc, ← hidentity s hs φ hφ hφ_bound]
      congr 1
      funext x
      change W.indicator (fun x => w x * d s x) x = W.indicator w x * d s x
      by_cases hx : x ∈ W
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    have hφi : Integrable φ (μ s : Measure ℝ) :=
      (integrable_const (1 : ℝ)).mono' hφ.aestronglyMeasurable (ae_of_all _ hφ_bound)
    rw [htest, ← exp_add]
    calc
      exp (-2 * δ + (y s - z)) =
          ∫ _ : ℝ, exp (-2 * δ + (y s - z)) ∂(μ s : Measure ℝ) := by
        rw [integral_const, probReal_univ, one_smul]
      _ ≤ ∫ x, φ x ∂(μ s : Measure ℝ) := by
        apply integral_mono_ae (integrable_const _) hφi
        filter_upwards [hsupport s hs] with x hx
        have hxW : x ∈ W := by
          exact ⟨by linarith [hx.1, (hy s hs).1], by linarith [hx.2, (hy s hs).2]⟩
        change exp _ ≤ W.indicator w x
        rw [indicator_of_mem hxW]
        change exp _ ≤ exp (x - z - δ)
        rw [exp_le_exp]
        linarith [hx.1]
  change IntegrableOn (fun x => w x * ∑ s ∈ S, c s * d s x) W ∧
    _ ≤ ∫ x in W, w x * ∑ s ∈ S, c s * d s x
  simp_rw [Finset.mul_sum]
  refine ⟨integrable_finsetSum S hterm, ?_⟩
  rw [integral_finsetSum S hterm]
  apply Finset.sum_le_sum
  intro s hs
  rw [mul_left_comm (exp (-2 * δ)) (c s)]
  simp_rw [mul_left_comm (w _) (c s), integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hpoint s hs) (hc s hs)

theorem exists_redSampling_ge {ι : Type*} (S : Finset ι) (y c : ι → ℝ)
    (μ : ι → ProbabilityMeasure ℝ) (d : ι → ℝ → ℝ) {z B δ : ℝ}
    (hB : 0 < B) (hδ : 0 ≤ δ)
    (hy : ∀ s ∈ S, y s ∈ Icc (z - B) z) (hc : ∀ s ∈ S, 0 ≤ c s)
    (hidentity : ∀ s ∈ S, ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      (∫ x, φ x * d s x) = ∫ x, φ x ∂(μ s : Measure ℝ))
    (hsupport : ∀ s ∈ S, ∀ᵐ x ∂(μ s : Measure ℝ), x ∈ Icc (y s - δ) (y s + δ))
    (hne : (∑ s ∈ S, c s * exp (y s - z)) ≠ 0) {E : Set ℝ} (hE : E.Finite) :
    ∃ x ∈ Icc (z - B - δ) (z + δ), x ∉ E ∧
      exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z)) ≤ ∑ s ∈ S, c s * d s x := by
  let W := Icc (z - B - δ) (z + δ)
  let m := exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z))
  let w (x : ℝ) := exp (x - z - δ)
  change ∃ x ∈ W, x ∉ E ∧ m ≤ ∑ s ∈ S, c s * d s x
  have hsum : 0 ≤ ∑ s ∈ S, c s * exp (y s - z) :=
    Finset.sum_nonneg fun s hs => mul_nonneg (hc s hs) (exp_pos _).le
  have hm : 0 < m := mul_pos (exp_pos _) (lt_of_le_of_ne hsum hne.symm)
  have hw : IntegrableOn w W := by
    have hcont : Continuous w := by dsimp [w]; fun_prop
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc
  obtain ⟨hi, hlower⟩ := redSampling_integral_lower S y c μ d hy hc hidentity hsupport
  by_contra! h
  have hle : (∫ x in W, w x * ∑ s ∈ S, c s * d s x) ≤ ∫ x in W, w x * m := by
    apply integral_mono_ae hi (hw.mul_const m)
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (s := W) measurableSet_Icc,
      ae_restrict_of_ae (s := W) (hE.countable.ae_notMem (volume : Measure ℝ))] with x hx hxE
    exact mul_le_mul_of_nonneg_left (h x hx hxE).le (exp_pos _).le
  have hmass : (∫ x in W, w x) < 1 := by
    change (∫ x in Icc (z - B - δ) (z + δ), exp (x - z - δ)) < 1
    rw [redSampling_weight_integral hB hδ]
    exact sub_lt_self _ (exp_pos _)
  exact (not_lt_of_ge (hlower.trans hle)) (by
    rw [integral_mul_const]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hmass hm)

theorem exists_redSampling_labelDensity_ge {ι : Type*} (S : Finset ι) (y c : ι → ℝ)
    (i : ι → Label) (L : ι → List Label) {z B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hy : ∀ s ∈ S, y s ∈ Icc (z - B) z) (hc : ∀ s ∈ S, 0 ≤ c s)
    (hsupport : ∀ s ∈ S, ∀ᵐ x ∂(labelSum limitFactor (i s :: L s) : Measure ℝ),
      x ∈ Icc (y s - δ) (y s + δ))
    (hne : (∑ s ∈ S, c s * exp (y s - z)) ≠ 0) {E : Set ℝ} (hE : E.Finite) :
    ∃ x ∈ Icc (z - B - δ) (z + δ), x ∉ E ∧
      exp (-2 * δ) * (∑ s ∈ S, c s * exp (y s - z)) ≤
        ∑ s ∈ S, c s * (labelDensity (i s) (L s) x / log ((i s).hi / (i s).lo)) := by
  refine exists_redSampling_ge S y c (fun s => labelSum limitFactor (i s :: L s))
    (fun s x => labelDensity (i s) (L s) x / log ((i s).hi / (i s).lo))
    hB hδ hy hc ?_ hsupport hne hE
  intro s _ φ _ _
  have hm := (log_pos ((one_lt_div (i s).positive).mpr (i s).nonempty)).ne'
  simp_rw [← mul_div_assoc]
  rw [integral_div, integral_mul_labelDensity, mul_div_cancel_left₀ _ hm]

end Erdos490PrimeCells
end


/- WordLaw -/
section
open Finset Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace Erdos490PrimeCells

theorem labelSum_ofFn {n : ℕ} (law : Label → ProbabilityMeasure ℝ) (labels : Fin n → Label) :
    Measure.map (fun v : Fin n → ℝ => ∑ i,v i) (Measure.pi (fun i => (law (labels i) : Measure ℝ))) =
      (labelSum law (List.ofFn labels) : Measure ℝ) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty,Measure.map_dirac' (by fun_prop)]
    simp [labelSum]
  | succ n ih =>
    let tail (j : Fin n) := labels j.succ

    let ν := Measure.pi (fun j : Fin n => (law (tail j) : Measure ℝ))
    let tot (v : Fin n → ℝ) := ∑ j,v j
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    let add (z : ℝ × ℝ) := z.1 + z.2
    have he := (measurePreserving_piFinSuccAbove (fun j => (law (labels j) : Measure ℝ)) (0 : Fin (n+1))).map_eq
    have ht : Measure.map tot ν = (labelSum law (List.ofFn tail) : Measure ℝ) := ih tail
    have ec : Measure.map e (Measure.pi (fun j => (law (labels j) : Measure ℝ))) =
        (law (labels 0) : Measure ℝ).prod ν := by simpa [e,ν,tail] using he
    have proj : Measurable (Prod.map tot (id : ℝ → ℝ)) := by dsimp [tot]; fun_prop
    have hadd : Measurable add := by dsimp [add]; fun_prop
    rw [List.ofFn_succ]
    change _ = Measure.map add ((labelSum law (List.ofFn tail) : Measure ℝ).prod (law (labels 0) : Measure ℝ))
    rw [← ht]
    conv_rhs => arg 2; arg 2; rw [← Measure.map_id (μ := (law (labels 0) : Measure ℝ))]
    rw [Measure.map_prod_map _ _ (by dsimp [tot]; fun_prop) measurable_id,
      ←Measure.prod_swap (μ := (law (labels 0) : Measure ℝ)) (ν := ν),← ec]
    rw [Measure.map_map measurable_swap e.measurable,Measure.map_map proj (measurable_swap.comp e.measurable),
      Measure.map_map hadd (proj.comp (measurable_swap.comp e.measurable))]
    congr 1
    funext v
    change ∑ j,v j = (∑ j : Fin n,v j.succ) + v 0
    rw [Fin.sum_univ_succ,add_comm]

end Erdos490PrimeCells
end


/- FamilyAtoms -/
section
open Real MeasureTheory Set Finset

open scoped ENNReal NNReal

namespace Erdos490PrimeCells

theorem atomic_family {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (w : (i : ι) → κ i → ℝ≥0) (v : (i : ι) → κ i → ℝ) :
    Measure.pi (fun i => ∑ k, w i k • Measure.dirac (v i k)) =
      ∑ f : (i : ι) → κ i, (∏ i, w i (f i)) • Measure.dirac (fun i => v i (f i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hset := MeasurableSet.univ_pi hs
  simp only [Measure.finsetSum_apply,Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,Measure.dirac_apply' _ hset]
  simp_rw [Measure.dirac_apply' _ (hs _)]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro f _
  simp only [Set.indicator_apply,Pi.one_apply,Set.mem_univ_pi]
  by_cases h : ∀ i, v i (f i) ∈ s i
  · simp [h]
  · push Not at h
    obtain ⟨i,hi⟩ := h
    rw [if_neg (fun hh => hi (hh i)),mul_zero]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

theorem pi_restore_family {ι : Type*} [Fintype ι] (μ : ι → FiniteMeasure ℝ) :
    Measure.pi (fun i => (μ i : Measure ℝ)) =
      (∏ i, (μ i).mass) • (ProbabilityMeasure.pi (fun i => (μ i).normalize) : Measure (ι → ℝ)) := by
  classical
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,ProbabilityMeasure.toMeasure_pi,Measure.pi_pi]
  have h (i : ι) : (μ i : Measure ℝ) (s i) = ((μ i).mass:ℝ≥0∞) * ((μ i).normalize : Measure ℝ) (s i) := by
    simpa only [ENNReal.coe_mul,FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      congrArg (fun a : ℝ≥0 => (a:ℝ≥0∞)) ((μ i).self_eq_mass_mul_normalize (s i))
  simp_rw [h]
  simp [Finset.prod_mul_distrib]

theorem prime_family_expansion {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℝ) (labels : ι → Label) :
    Measure.pi (fun i => (primeLaw t (labels i).lo (labels i).hi : Measure ℝ)) =
    ∑ f : (i : ι) → primeBand t (labels i).lo (labels i).hi,
      (∏ i, ((f i : ℕ):ℝ≥0)⁻¹) • Measure.dirac (fun i => log (f i : ℕ)/t) := by
  classical
  let S (i : ι) := primeBand t (labels i).lo (labels i).hi
  let w (i : ι) (p : S i) : ℝ≥0 := (p.val:ℝ≥0)⁻¹
  let v (i : ι) (p : S i) := log p.val/t
  have H (i : ι) : (primeLaw t (labels i).lo (labels i).hi : Measure ℝ) = ∑ p : S i,w i p • Measure.dirac (v i p) :=
    (Finset.sum_attach (S i) _).symm
  simp_rw [H]
  exact atomic_family w v

end Erdos490PrimeCells
end


/- WordIntegral -/
section
open Finset Real MeasureTheory

open scoped Topology NNReal ENNReal

namespace Erdos490PrimeCells

theorem sum_tuple_test {n : ℕ} (t : ℝ) (i : Fin n → Label) (g : ℝ → ℝ)
    (hg : Measurable g) {C : ℝ} (hC : ∀ y, ‖g y‖ ≤ C) :
    (∑ f : (j : Fin n) → primeBand t (i j).lo (i j).hi,
      (∏ j,((f j : ℕ):ℝ)⁻¹) * g (∑ j,log (f j : ℕ)/t)) =
      (∏ j,((primeLaw t (i j).lo (i j).hi).mass:ℝ)) *
        ∫ y, g y ∂(labelSum (primeFactor t) (List.ofFn i) : Measure ℝ) := by
  classical
  let μ (j : Fin n) := primeLaw t (i j).lo (i j).hi
  let s (v : Fin n → ℝ) := ∑ j,v j
  let ν := Measure.pi (fun j => (μ j : Measure ℝ))
  have hs : Measurable s := by dsimp [s]; fun_prop
  let f (v : Fin n → ℝ) := g (s v)
  have hf : Measurable f := hg.comp hs
  have hfin (m : Measure (Fin n → ℝ)) [IsFiniteMeasure m] : Integrable f m :=
    (integrable_const (μ := m) C).mono' hf.aestronglyMeasurable (ae_of_all _ (fun v => hC (s v)))
  calc
    _ = ∫ v, f v ∂ν := by
      dsimp only [ν,μ]
      rw [prime_family_expansion,integral_finsetSum_measure]
      · apply Finset.sum_congr rfl
        intro vals _
        rw [← Measure.coe_nnreal_smul,integral_smul_measure,integral_dirac]
        simp [f,s,NNReal.coe_prod]
      · intro _ _
        apply hfin
    _ = _ := by
      change (∫ v, g (s v) ∂Measure.pi (fun j => (μ j : Measure ℝ))) = _
      rw [pi_restore_family,← Measure.coe_nnreal_smul,integral_smul_measure,smul_eq_mul]
      simp only [ENNReal.coe_toReal,NNReal.coe_prod]
      congr 1
      rw [←labelSum_ofFn (primeFactor t) i,integral_map hs.aemeasurable hg.aestronglyMeasurable]
      rfl

end Erdos490PrimeCells
end


/- CellTuple -/
section
open Finset Filter Real MeasureTheory Set

open scoped Topology NNReal ENNReal

namespace Erdos490PrimeCells

noncomputable def cellLabel (b : ℝ) (p : ℕ) (hp : p.Prime) : Label where
  lo := boundary b p
  hi := boundary b (p+1)
  positive := exp_pos _
  nonempty := by
    rw [boundary_succ b hp]
    exact lt_mul_of_one_lt_right (exp_pos _) (one_lt_exp_iff.mpr (inv_pos.mpr (by exact_mod_cast hp.pos)))

theorem cell_log_mass (b : ℝ) (p : ℕ) (hp : p.Prime) :
    log ((cellLabel b p hp).hi/(cellLabel b p hp).lo) = (p:ℝ)⁻¹ := by
  change log (boundary b (p+1)/boundary b p) = _
  rw [boundary_succ b hp,mul_div_cancel_left₀ _ (show boundary b p ≠ 0 from (exp_pos _).ne'),log_exp]

theorem prime_mass_real (t a b : ℝ) :
    ((primeLaw t a b).mass:ℝ) = reciprocalInterval (exp (t*a)) (exp (t*b)) := by
  change ((∑ p ∈ primeBand t a b, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/t) : Measure ℝ).real univ) = _
  rw [Measure.real,Measure.finsetSum_apply,ENNReal.toReal_sum (fun p _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro p _
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,measure_univ,mul_one,ENNReal.coe_toReal,NNReal.coe_inv,NNReal.coe_natCast]

end Erdos490PrimeCells
end


/- RedArithmetic -/
section
open Real Filter Finset Set MeasureTheory

open scoped Topology

namespace Erdos490PrimeCells

noncomputable def finalCount {n : ℕ} (i : Label) (L : Fin n → Label) (t x c : ℝ) : ℝ :=
  ∑ f : (j : Fin n) → primeBand t (L j).lo (L j).hi,
    cappedCount t i.lo i.hi (t*x-c-log ((∏ j,(f j : ℕ):ℕ):ℝ))

private theorem cancellation {n : ℕ} (t : ℝ) (ht : 0 < t) (x c : ℝ) (i : Label)
    (L : Fin n → Label) (f : (j : Fin n) → primeBand t (L j).lo (L j).hi) :
    (∏ j, ((f j : ℕ):ℝ)⁻¹) *
        movingLabelKernel i c t (x-∑ j, log (f j : ℕ)/t) =
      t*exp (-(t*x-c))*cappedCount t i.lo i.hi (t*x-c-log ((∏ j,(f j : ℕ):ℕ):ℝ)) := by
  have hp (j : Fin n) : (0:ℝ) < (f j : ℕ) := by exact_mod_cast (Finset.mem_filter.mp (f j).property).2.pos
  let D : ℝ := ∏ j, ((f j : ℕ):ℝ)
  have hD : 0 < D := Finset.prod_pos fun j _ => hp j
  have hex : t*(x-∑ j, log (f j : ℕ)/t)-c = t*x-c-log D := by
    rw [←Finset.sum_div]
    dsimp [D]
    rw [Real.log_prod (fun j _ => (hp j).ne')]
    field_simp
    ring
  rw [movingLabelKernel, hex, Finset.prod_inv_distrib, Nat.cast_prod]
  change D⁻¹ * (t * exp (-(t*x-c-log D)) * _) = t*exp (-(t*x-c))*_
  rw [neg_sub,sub_eq_add_neg (log D),exp_add,exp_log hD]
  field_simp
  rfl

theorem weighted_final_count (primeEstimate : EffectivePrimeEstimate) {n : ℕ} (i : Label) (L : Fin n → Label) (x c : ℝ) :
    ∀ᶠ t : ℝ in atTop, t * exp (-(t*x-c)) * finalCount i L t x c =
      (∏ j,((primeLaw t (L j).lo (L j).hi).mass : ℝ)) *
        ∫ y, movingLabelKernel i c t (x-y) ∂(labelSum (primeFactor t) (List.ofFn L) : Measure ℝ) := by
  filter_upwards [(uniform_last_label_bound primeEstimate) i.positive i.hi,eventually_gt_atTop 0] with t he ht
  let g := fun y => movingLabelKernel i c t (x-y)
  have hg : Measurable g := (movingLabelKernel_measurable i c t).comp (by fun_prop)
  have hbound (y : ℝ) : ‖g y‖ ≤ 2/i.lo := by
    rw [Real.norm_of_nonneg (movingLabelKernel_nonneg i c ht.le _),movingLabelKernel_eq_div]
    exact he _
  rw [← sum_tuple_test t L g hg hbound,finalCount,Finset.mul_sum]
  apply sum_congr rfl
  intro f _
  exact (cancellation t ht x c i L f).symm

theorem final_count_lower (primeEstimate : EffectivePrimeEstimate) {n : ℕ} (i : Label) (L : Fin n → Label) (x c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      (∏ j,log ((L j).hi/(L j).lo)) * labelDensity i (List.ofFn L) x - ε ≤
        t*exp (-(t*x-c))* finalCount i L t x c := by
  let A := ∏ j,log ((L j).hi/(L j).lo)
  let M (t : ℝ) := ∏ j,((primeLaw t (L j).lo (L j).hi).mass:ℝ)
  let d := labelDensity i (List.ofFn L) x
  have hA : 0 ≤ A := Finset.prod_nonneg fun j _ => log_nonneg ((one_le_div (L j).positive).mpr (L j).nonempty.le)
  let δ := ε/(2*(A+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have limit : Tendsto M atTop (𝓝 A) := by
    apply tendsto_finsetProd
    intro j _
    simp_rw [prime_mass_real]
    exact dilated_window_mass (L j).positive (L j).nonempty.le
  have hcoef : A*d-ε < A*(d-δ) := by
    have : (2*(A+1))*δ = ε := by dsimp [δ]; field_simp
    nlinarith [mul_nonneg hA hδ.le]
  have hsmall := (limit.mul_const (d-δ)).eventually_const_lt hcoef
  filter_upwards [(weighted_final_count primeEstimate) i L x c,(movingLabel_integral_lower primeEstimate) i (List.ofFn L) x c hδ,hsmall]
    with t he hminor hupper
  rw [he]
  exact hupper.le.trans (mul_le_mul_of_nonneg_left hminor (show 0 ≤ M t by dsimp [M]; positivity))

end Erdos490PrimeCells
end


/- RedWindow -/
section
open Real Filter Finset MeasureTheory Set

open scoped Topology

namespace Erdos490PrimeCells

noncomputable def harmonicSize (i : Label) := log (i.hi/i.lo)

theorem harmonicSize_pos (i : Label) : 0 < harmonicSize i :=
  log_pos ((one_lt_div i.positive).mpr i.nonempty)

theorem red_window_recovery (primeEstimate : EffectivePrimeEstimate) {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (y : ι → ℝ) (i : ι → Label) (n : ι → ℕ) (L : (s : ι) → Fin (n s) → Label)
    {z B δ : ℝ} (hB : 0 < B) (hδ : 0 ≤ δ)
    (hy : ∀ s ∈ S, y s ∈ Icc (z-B) z)
    (hsupport : ∀ s ∈ S, ∀ᵐ v ∂(labelSum limitFactor (i s :: List.ofFn (L s)) : Measure ℝ),
      v ∈ Icc (y s-δ) (y s+δ)) {E : Set ℝ} (hE : E.Finite) :
    let W := fun s => harmonicSize (i s) * ∏ j,harmonicSize (L s j)
    ∃ x ∈ Icc (z-B-δ) (z+δ), x ∉ E ∧ ∀ c : ℝ, ∀ ε > 0, ∀ᶠ t : ℝ in atTop,
      exp (-2*δ)*(∑ s ∈ S,W s * exp (y s-z)) - ε ≤
        t*exp (-(t*x-c))*(∑ s ∈ S,finalCount (i s) (L s) t x c) := by
  classical
  let W (s : ι) := harmonicSize (i s) * ∏ j,harmonicSize (L s j)
  have hw (s : ι) : 0 < W s := mul_pos (harmonicSize_pos _) (Finset.prod_pos fun j _ => harmonicSize_pos _)
  have H := exists_redSampling_labelDensity_ge S y W i (fun s => List.ofFn (L s)) hB hδ hy
    (fun s _ => (hw s).le) hsupport (Finset.sum_pos (fun s _ => mul_pos (hw s) (exp_pos _)) hS).ne' hE
  obtain ⟨x,hx,hreg,hx'⟩ := H
  refine ⟨x,hx,hreg,fun c ε hε => ?_⟩
  let η := ε/(S.card+1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsum := (Finset.eventually_all (I := S)).mpr (fun s _ => (final_count_lower primeEstimate) (i s) (L s) x c hη)
  filter_upwards [hsum] with t ht
  let d (s : ι) := labelDensity (i s) (List.ofFn (L s)) x
  have eq (s : ι) : W s * (d s / log ((i s).hi/(i s).lo)) = (∏ j,harmonicSize (L s j)) * d s := by
    change (harmonicSize (i s) * _) * (d s / harmonicSize (i s)) = _
    field_simp [(harmonicSize_pos (i s)).ne']
  simp only [← show ∀ s,d s=labelDensity (i s) (List.ofFn (L s)) x from fun _ => rfl] at hx'
  simp_rw [eq] at hx'
  nth_rw 2 [Finset.mul_sum]
  have h₁ := Finset.sum_le_sum (fun s hs => ht s hs)
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at h₁
  have hc : (S.card:ℝ)*η ≤ ε := by
    calc
      _ ≤ (S.card+1)*η := by gcongr; linarith
      _ = ε := by dsimp [η]; field_simp
  exact (sub_le_sub hx' hc).trans h₁

end Erdos490PrimeCells
end


/- RedOldWindow -/
section
namespace Erdos490Transfer

open Finset Filter Real MeasureTheory Erdos490PrimeCells

open scoped Topology

noncomputable section

open Classical

structure RedWord (S : Finset ℕ) where
  head : ℕ
  mem : head ∈ S
  length : ℕ
  tail : Fin length ≃ ↥(S.erase head)

def wordOfNonempty {S : Finset ℕ} (h : S.Nonempty) : RedWord S where
  head := h.choose
  mem := h.choose_spec
  length := Fintype.card ↥(S.erase h.choose)
  tail := (Fintype.equivFin _).symm

namespace RedWord

variable {S : Finset ℕ} (r : RedWord S)

def digits : List ℕ := r.head :: List.ofFn fun j => (r.tail j).val

lemma sum_digits (f : ℕ → ℝ) :
    (r.digits.map f).sum = ∑ p ∈ S,f p := by
  calc
    _ = f r.head + ∑ j : Fin r.length, f (r.tail j).val := by simp [digits,List.map_ofFn,Function.comp_def,Fin.sum_ofFn]
    _ = f r.head + ∑ j : ↥(S.erase r.head), f j.val := by rw [r.tail.sum_comp (fun j => f j.val)]
    _ = _ := by rw [← Finset.add_sum_erase S f r.mem]; congr 1; simpa only [Finset.attach_eq_univ] using Finset.sum_attach (S.erase r.head) f

lemma prod_digits (f : ℕ → ℝ) :
    f r.head * (∏ j : Fin r.length,f (r.tail j).val) = ∏ p ∈ S,f p := by
  rw [r.tail.prod_comp (fun j => f j.val), ← Finset.mul_prod_erase S f r.mem]
  congr 1
  simpa only [Finset.attach_eq_univ] using Finset.prod_attach (S.erase r.head) f

lemma all_mem {p : ℕ} (h : p ∈ r.digits) : p ∈ S := by
  rcases List.mem_cons.mp h with h|h
  · simpa only [h] using r.mem
  · obtain ⟨j,hj⟩ := List.mem_ofFn.mp h
    exact hj ▸ Finset.mem_of_mem_erase (r.tail j).property

def headLabel (b : ℝ) := oldLabel b r.head

def tailLabel (b : ℝ) (j : Fin r.length) := oldLabel b (r.tail j).val

lemma as_law (b : ℝ) : labelSum limitFactor (r.headLabel b :: List.ofFn (r.tailLabel b)) =
    law b r.digits := by simp only [law,digits,List.map_cons,List.map_ofFn]; rfl

lemma support {b δ : ℝ} (e : ℕ → ℝ)
    (hp : ∀ p ∈ S, p.Prime)
    (he : ∀ p ∈ S, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (hδ : ∑ p ∈ S,e p ≤ δ) :
    ∀ᵐ v ∂(labelSum limitFactor (r.headLabel b :: List.ofFn (r.tailLabel b)) : Measure ℝ),
    v ∈ Set.Icc (log ((∏ p ∈ S,p : ℕ):ℝ)-δ) (log ((∏ p ∈ S,p : ℕ):ℝ)+δ) := by
  rw [r.as_law]
  have h := law_displacement b r.digits e (fun p h => by
    have hm := r.all_mem h
    simpa only [oldLabel,dif_pos (hp p hm)] using he p hm)
  rw [Nat.cast_prod,log_prod (fun p hm => by exact_mod_cast (hp p hm).ne_zero)]
  filter_upwards [h] with v hv
  rw [r.sum_digits,r.sum_digits] at hv
  exact ⟨by linarith [(abs_le.mp (hv.trans hδ)).1],by linarith [(abs_le.mp (hv.trans hδ)).2]⟩

lemma harmonic (b : ℝ) (hp : ∀ p ∈ S,p.Prime) :
    harmonicSize (r.headLabel b) * (∏ j,harmonicSize (r.tailLabel b j)) =
      ((∏ p ∈ S,p:ℕ):ℝ)⁻¹ := by
  change harmonicSize (oldLabel b r.head) * (∏ j,harmonicSize (oldLabel b (r.tail j).val)) = _
  rw [r.prod_digits (fun p => harmonicSize (oldLabel b p)),Nat.cast_prod,← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p h
  change log ((oldLabel b p).hi/(oldLabel b p).lo) = _
  simpa only [oldLabel,dif_pos (hp p h),cellLabel] using cell_log_mass b p (hp p h)

end RedWord

theorem red_old_words (primeEstimate : EffectivePrimeEstimate) (G : Finset ℕ) (hne : G.Nonempty)
    (word : (m : G) → RedWord m.val.primeFactors) {b z B δ : ℝ}
    (hB : 0 < B) (hδ : 0 ≤ δ) (e : ℕ → ℝ)
    (hprod : ∀ m : G, (∏ p ∈ m.val.primeFactors,p) = m.val)
    (he : ∀ m : G, ∀ p ∈ m.val.primeFactors, ∀ v ∈ Set.Ioc (boundary b p) (boundary b (p+1)), |v-log p| ≤ e p)
    (herr : ∀ m : G, ∑ p ∈ m.val.primeFactors,e p ≤ δ)
    (hm : ∀ m : G, log (m.val:ℝ) ∈ Set.Icc (z-B) z)
    {E : Set ℝ} (hE : E.Finite) :
    ∃ x ∈ Set.Icc (z-B-δ) (z+δ), x ∉ E ∧ ∀ c : ℝ, ∀ ε > 0, ∀ᶠ t : ℝ in atTop,
      exp (-2*δ)*(exp (-z)*G.card)-ε ≤ t*exp (-(t*x-c))*
        ∑ m : G, finalCount ((word m).headLabel b) ((word m).tailLabel b) t x c := by
  classical
  let y (m : G) := log (m.val:ℝ)
  have hp (m : G) : ∀ p ∈ m.val.primeFactors, p.Prime := fun _ h => Nat.prime_of_mem_primeFactors h
  have hs (m : G) := (word m).support e (hp m) (he m) (herr m)
  have hi : Nonempty ↥G := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  have ht := (red_window_recovery primeEstimate) (Finset.univ : Finset ↥G) Finset.univ_nonempty y
    (fun m => (word m).headLabel b) (fun m => (word m).length) (fun m => (word m).tailLabel b) hB hδ
    (fun m _ => hm m) (fun m _ => by simpa only [hprod m,y] using hs m) hE
  have hterm (m : G) :
      (harmonicSize ((word m).headLabel b) * ∏ j, harmonicSize ((word m).tailLabel b j)) *
        exp (y m-z) = exp (-z) := by
    have hm0 : 0 < m.val := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp (word m).mem).2.2
    rw [(word m).harmonic b (hp m),hprod m,sub_eq_add_neg,exp_add]
    dsimp [y]
    rw [exp_log (by exact_mod_cast hm0),inv_mul_cancel_left₀ (by exact_mod_cast hm0.ne')]
  simpa only [hterm,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,
    mul_comm (G.card:ℝ) (exp (-z))] using ht

end

end Erdos490Transfer
end


/- CountedWords -/
section
open Real Filter Finset MeasureTheory

open scoped Topology

namespace Erdos490PrimeCells

abbrev PrimeChoices {n : ℕ} (t : ℝ) (L : Fin n → Label) :=
  (j : Fin n) → primeBand t (L j).lo (L j).hi

def choiceProduct {n : ℕ} {t : ℝ} {L : Fin n → Label} (f : PrimeChoices t L) : ℕ :=
  ∏ j, (f j : ℕ)

noncomputable def countedWords {n : ℕ} (i : Label) (L : Fin n → Label) (t : ℝ) (cap : ℕ) :=
  (Finset.univ : Finset (PrimeChoices t L)).sigma (fun f =>
    (primeBand t i.lo i.hi).filter (fun q => choiceProduct f * q ≤ cap))

private theorem lastCell_eq (t z : ℝ) (i : Label) {D : ℕ} (hD : 0 < D) :
    (Finset.Ioc ⌊exp (t*i.lo)⌋₊ ⌊min (exp (t*i.hi)) (exp (z-log (D:ℝ)))⌋₊).filter Nat.Prime =
    (primeBand t i.lo i.hi).filter (fun q => D*q ≤ ⌊exp z⌋₊) := by
  ext q
  simp only [primeBand,Finset.mem_filter,Finset.mem_Ioc,Nat.floor_mono.map_min,le_min_iff]
  have hD' : 0 < (D:ℝ) := by exact_mod_cast hD
  have hcut : q ≤ ⌊exp (z-log (D:ℝ))⌋₊ ↔ D*q ≤ ⌊exp z⌋₊ := by
    rw [Nat.le_floor_iff (exp_pos _).le, Nat.le_floor_iff (exp_pos _).le,exp_sub,exp_log hD',
      le_div_iff₀ hD',Nat.cast_mul,mul_comm (q:ℝ)]
  tauto

theorem finalCount_eq_card {n : ℕ} (i : Label) (L : Fin n → Label) (t x c : ℝ) :
    finalCount i L t x c = (countedWords i L t ⌊exp (t*x-c)⌋₊).card := by
  unfold finalCount countedWords
  rw [Finset.card_sigma,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro f _
  have h0 : 0 < choiceProduct f := Finset.prod_pos fun j _ => (Finset.mem_filter.mp (f j).property).2.pos
  exact congrArg (fun V : Finset ℕ => (V.card:ℝ)) (lastCell_eq t (t*x-c) i h0)

end Erdos490PrimeCells
end


/- RedProducts -/
section
namespace Erdos490Transfer

open Finset Erdos490PrimeCells

noncomputable section

open Classical

private def supportEquiv {S : Finset ℕ} {p n : ℕ} (hp : p ∈ S)
    (tail : Fin n ≃ ↥(S.erase p)) : Option (Fin n) ≃ S := by
  let rest : ↥(S.erase p) ≃ {q : S // q ≠ (⟨p, hp⟩ : S)} :=
    { toFun := fun q => ⟨⟨q.val, mem_of_mem_erase q.property⟩,
        fun h => (mem_erase.mp q.property).1 (congrArg Subtype.val h)⟩
      invFun := fun q => ⟨q.val.val, mem_erase.mpr
        ⟨fun h => q.property (Subtype.ext h), q.val.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.optionCongr (tail.trans rest)).trans (Equiv.optionSubtypeNe (⟨p, hp⟩ : S))

theorem countedWords_eq_newProducts_card {b t : ℝ} (ht : 0 < t)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p n : ℕ} (hp : p ∈ S)
    (tail : Fin n ≃ ↥(S.erase p)) (cap : ℕ) :
    (countedWords (cellLabel b p (hS p hp))
      (fun j => cellLabel b (tail j).val (hS _ (mem_of_mem_erase (tail j).property)))
      t cap).card = ((newProducts b t S).filter (· ≤ cap)).card := by
  let i := cellLabel b p (hS p hp)
  let L (j : Fin n) := cellLabel b (tail j).val (hS _ (mem_of_mem_erase (tail j).property))
  let e := supportEquiv hp tail
  let F := (Fintype.piFinset (fun q : S => newCell b t q.val)).filter (fun f => high f ≤ cap)
  have valid {f : S → ℕ} (hf : f ∈ F) : ∀ q : S, f q ∈ newCell b t q.val :=
    Fintype.mem_piFinset.mp (mem_filter.mp hf).1
  have prod_eq (f : S → ℕ) : high f = (∏ j : Fin n, f (e (some j))) * f (e none) := by
    rw [high, ← Fintype.prod_equiv e (fun j => f (e j)) f (fun _ => rfl)]
    rw [Fintype.prod_option, mul_comm]
  have himage : F.image high = (newProducts b t S).filter (· ≤ cap) := by
    ext z
    simp only [F, newProducts, mem_image, mem_filter]
    aesop
  have hinj : Set.InjOn high (F : Set (S → ℕ)) := by
    intro f hf g hg h
    exact high_injective (cell := fun q : S => newCell b t q.val)
      (fun _ _ hq => (mem_filter.mp hq).2)
      (fun q r hqr => newCell_disjoint ht.le (fun eq => hqr (Subtype.ext eq)))
      (fun q => Or.inr (valid hf q)) (fun q => Or.inr (valid hg q)) h
  rw [← himage, card_image_of_injOn hinj]
  change (countedWords i L t cap).card = F.card
  symm
  let word (f : S → ℕ) (hf : f ∈ F) : Σ _ : PrimeChoices t L, ℕ :=
    ⟨fun j => ⟨f (e (some j)), valid hf (e (some j))⟩, f (e none)⟩
  apply card_bij word
  · intro f hf
    refine mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨valid hf (e none), ?_⟩⟩
    exact (prod_eq f).symm ▸ (mem_filter.mp hf).2
  · intro f hf g hg h
    funext q
    obtain ⟨j, rfl⟩ := e.surjective q
    cases j with
    | none => exact congrArg (fun w => w.2) h
    | some j => exact congrArg (fun w => (w.1 j).val) h
  · rintro ⟨v, q⟩ hw
    obtain ⟨hq, hcap⟩ := mem_filter.mp (mem_sigma.mp hw).2
    let f (r : S) := (e.symm r).elim q (fun j => (v j).val)
    have head : f (e none) = q := by simp [f]
    have rest (j : Fin n) : f (e (some j)) = (v j).val := by simp [f]
    have hf : f ∈ F := by
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
      · intro r
        obtain ⟨j, rfl⟩ := e.surjective r
        cases j with
        | none => exact head.symm ▸ hq
        | some j => exact (rest j).symm ▸ (v j).property
      · simpa only [prod_eq f, rest, head, choiceProduct] using hcap
    refine ⟨f, hf, ?_⟩
    have hv : (word f hf).1 = v := funext (fun j => Subtype.ext (rest j))
    exact Sigma.ext hv (heq_of_eq head)

theorem finalCount_eq_newProducts_card {b t : ℝ} (ht : 0 < t)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p n : ℕ} (hp : p ∈ S)
    (tail : Fin n ≃ ↥(S.erase p)) (x c : ℝ) :
    finalCount (cellLabel b p (hS p hp))
      (fun j => cellLabel b (tail j).val (hS _ (mem_of_mem_erase (tail j).property)))
      t x c = (((newProducts b t S).filter (· ≤ ⌊Real.exp (t * x - c)⌋₊)).card : ℝ) := by
  rw [finalCount_eq_card, countedWords_eq_newProducts_card ht hS hp tail]

theorem sum_newProducts_card_le_semigroup_card {b t : ℝ} (ht : 0 < t)
    (C : Finset ℕ) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C) (cap : ℕ) :
    (∑ S ∈ G, ((newProducts b t S).filter (· ≤ cap)).card) ≤
      (semigroup (bands b t C) cap).card := by
  let P (S : Finset ℕ) := (newProducts b t S).filter (· ≤ cap)
  have apart : (G : Set (Finset ℕ)).PairwiseDisjoint P :=
    fun _ _ _ _ h => (products_apart ht.le h).mono (filter_subset _ _) (filter_subset _ _)
  change (∑ S ∈ G, (P S).card) ≤ _
  rw [← card_biUnion apart]
  apply card_le_card
  intro z hz
  obtain ⟨S, hS, hz⟩ := mem_biUnion.mp hz
  obtain ⟨hz, hcap⟩ := mem_filter.mp hz
  exact mem_semigroup.mpr ⟨newProduct_active (hG S hS) hz, hcap⟩

end

end Erdos490Transfer
end


/- RedScale -/
section
namespace Erdos490Transfer

open Finset Filter Real Shift490

open scoped Topology

noncomputable section

theorem red_at_prescribed {C : Finset ℕ} {b x M : ℝ} (hx : 0 < x)
    (A : ℝ → ℝ → ℝ)
    (count : ∀ {t}, 0 < t → ∀ c, A t c ≤ ((semigroup (bands b t C) ⌊exp (t*x-c)⌋₊).card:ℝ))
    (recovery : ∀ c : ℝ, ∀ ε > 0, ∀ᶠ t : ℝ in atTop,
      M-ε ≤ t*exp (-(t*x-c))*A t c) :
    ∀ u : ℕ, 0 < u → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      let t := log n/x
      M-ε ≤ t*density (bands b t C) n u := by
  intro u hu ε hε
  have scale : Tendsto (fun n : ℕ => log n/x) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hx
  filter_upwards [scale.eventually (recovery (log u) ε hε),scale.eventually_gt_atTop 0,
    eventually_gt_atTop (0:ℕ)] with n hr ht hn
  let t := log (n:ℝ)/x
  have htx : t*x = log n := div_mul_cancel₀ _ hx.ne'
  have h := (hr.trans (mul_le_mul_of_nonneg_left (count ht (log u))
    (mul_nonneg ht.le (exp_pos _).le)))
  change M-ε ≤ t*density (bands b t C) n u
  rw [← shifted_density _ hn hu, F_eq_semigroup, ← htx, ← mul_assoc]
  exact h

end

end Erdos490Transfer
end


/- RedRealization -/
section
namespace Erdos490Transfer

open Filter Finset Real Erdos490PrimeCells

open scoped Topology

noncomputable section

open Classical

private theorem word_finalCount {S : Finset ℕ} (word : RedWord S) (hp : ∀ p ∈ S,p.Prime)
    {b t : ℝ} (ht : 0 < t) (x c : ℝ) :
    finalCount (word.headLabel b) (word.tailLabel b) t x c =
      (((newProducts b t S).filter (· ≤ ⌊exp (t*x-c)⌋₊)).card:ℝ) := by
  have a : word.headLabel b = cellLabel b word.head (hp _ word.mem) := by
    simp only [RedWord.headLabel,oldLabel,dif_pos (hp _ word.mem),cellLabel]
  have g : word.tailLabel b = (fun j => cellLabel b (word.tail j).val
      (hp _ (mem_of_mem_erase (word.tail j).property))) := by
    funext j
    simp only [RedWord.tailLabel,oldLabel,dif_pos (hp _ (mem_of_mem_erase (word.tail j).property)),cellLabel]
  rw [a,g]
  exact finalCount_eq_newProducts_card ht hp word.mem word.tail x c

theorem red_good_realization (primeEstimate : EffectivePrimeEstimate) : RedGoodRealization := by
  intro C hp c hc z B δ hB hδ hpos
  let e (p : ℕ) := c/log p^2
  let G := goodWindow C (z-B) z δ e
  dsimp only
  intro nonempty
  change G.Nonempty at nonempty
  have prop (m : G) := good_properties hp m.property
  have hprod (m : G) : (∏ p ∈ m.val.primeFactors,p) = m.val := (prop m).2.1
  have has (m : G) : m.val.primeFactors.Nonempty := by
    by_contra! hh
    have h1 : m.val = 1 := by simpa only [hh,prod_empty] using (hprod m).symm
    have hl := (prop m).2.2.2.1
    rw [h1,Nat.cast_one,log_one] at hl
    linarith
  let word (m : G) := wordOfNonempty (has m)
  have he (m : G) := fun p (h : p ∈ m.val.primeFactors) v (h' : v ∈ Set.Ioc (boundary Mertens.M p)
    (boundary Mertens.M (p+1))) => hc p ((prop m).1 h) v ⟨h'.1.le,h'.2⟩
  obtain ⟨x,hx,_,hr⟩ := (red_old_words primeEstimate) G nonempty word hB hδ.le e hprod he
    (fun m => (prop m).2.2.1) (fun m => ⟨(prop m).2.2.2.1.le,(prop m).2.2.2.2⟩) Set.finite_empty
  refine ⟨x,hx,?_⟩
  let mass (t c' : ℝ) := ∑ m : G,finalCount ((word m).headLabel Mertens.M) ((word m).tailLabel Mertens.M) t x c'
  have count {t : ℝ} (ht : 0 < t) (c' : ℝ) : mass t c' ≤
      ((semigroup (bands Mertens.M t C) ⌊exp (t*x-c')⌋₊).card:ℝ) := by
    let cap := ⌊exp (t*x-c')⌋₊
    let f (S : Finset ℕ) := ((newProducts Mertens.M t S).filter (· ≤ cap)).card
    have inj : Set.InjOn Nat.primeFactors G := by
      intro m hm n hn heq
      simpa only [hprod ⟨m,hm⟩,hprod ⟨n,hn⟩] using congrArg (fun S : Finset ℕ => ∏ p ∈ S,p) heq
    have bound := sum_newProducts_card_le_semigroup_card (b:=Mertens.M) ht C (G.image Nat.primeFactors)
      (fun _ h => by obtain ⟨m,hm,rfl⟩ := mem_image.mp h; exact (prop ⟨m,hm⟩).1) cap
    rw [sum_image inj] at bound
    calc
      mass t c' = ∑ m : G,(f m.val.primeFactors:ℝ) := sum_congr rfl (fun m _ =>
        word_finalCount (word m) (fun _ h => Nat.prime_of_mem_primeFactors h) ht x c')
      _ = ↑(∑ m ∈ G,f m.primeFactors) := by
        rw [Nat.cast_sum,← Finset.sum_attach G (fun m => (f m.primeFactors:ℝ)),Finset.attach_eq_univ]
      _ ≤ _ := by exact_mod_cast bound
  have h := red_at_prescribed (show 0 < x from hpos.trans_le hx.1) mass count hr
  simpa only [mul_assoc] using h

end

end Erdos490Transfer
end

open Finset Filter Real Classical

theorem OMA.solution : OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2.H3 := by
  intro primeEstimate
  dsimp only
  have h : Erdos490Transfer.StableRecovery := Erdos490Transfer.stableRecovery_of_sampled
    (Erdos490Transfer.sampled_of_large_labels (Erdos490Transfer.large_labels_of_red_good primeEstimate
      (Erdos490Transfer.red_good_realization primeEstimate)))
  intro Y K η hη N hN c b stable
  let old (k : ℕ) : Erdos490Transfer.Colors Y (N k) :=
    ⟨(c k).val.1, (c k).val.2, (c k).property.1, (c k).property.2⟩
  have hst : Erdos490Transfer.Stable N old b := by
    intro H hH θ hθ
    filter_upwards [stable H hH θ hθ] with k hk
    simpa only [Shift490.F_eq_card, Shift490.countSet, Erdos490Transfer.eulerScale,
      Erdos490Transfer.euler, Erdos490Transfer.pick, old] using hk
  apply (h Y K η hη N hN old b hst).mono
  rintro k ⟨hn,w,hw,d,hq,hr⟩
  exact ⟨hn,w,hw,fun m => ⟨((d m).red,(d m).blue),(d m).cover,(d m).separate⟩,hq,hr⟩


/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

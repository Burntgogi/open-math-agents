import Dilation

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

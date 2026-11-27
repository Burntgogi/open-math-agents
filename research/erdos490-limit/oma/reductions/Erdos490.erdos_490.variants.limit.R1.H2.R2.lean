import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1
import Mathlib

/-!
# Shift stability and recovery for the separated-pair transfer

The target is the scale-transfer step of @Burntgogi's R1 for the
Erdős–Szemerédi product-injective pair problem. The finite argument
adapts Cofactor, Weights, Matching and H2 in the local transfer-lean
development. The analytic argument adapts Harmonic, PrimeColorTransfer,
EulerScale, EulerTransfer and StableTransfer. A color is represented by a
pair of disjoint finite sets covering all available primes. The increment
of a maximal fiber size is either zero or one, so simultaneous control of
the finite matrix of cofactor counts suffices for every quotient graph.
-/

namespace OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2
open Finset Filter Real Classical
noncomputable section

/-- An inverse-cubic logarithmic error estimate for the first Chebyshev function. -/
def H1 : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 3

/-- One fixed color on one subsequence works for every bounded logarithmic shift. -/
def H2 : Prop :=
  (∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 3) →
  let side (Y : ℕ) (x : ℝ) (q : ℕ → Bool) (b : Bool) := ((Icc Y ⌊x⌋₊).filter Nat.Prime).filter (fun p => q p = b)
  let F (C : Finset ℕ) (w : ℝ) := exp (-w) * (((range (⌊exp w⌋₊ + 1)).filter (· ∈ Nat.factoredNumbers C)).card : ℝ)
  let euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹
  ∀ Y, ∀ X : ℕ → ℝ, Tendsto X atTop atTop → ∀ q : ℕ → ℕ → Bool,
    ∃ (σ : ℕ → ℕ) (b : Bool), StrictMono σ ∧
      ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop,
        let C := side Y (X (σ i)) (q (σ i)) b
        let w := log (X (σ i))
        ∀ s : ℝ, |s| ≤ H → |F C (w+s) - F C w| ≤ η * (euler C / w)

/-- Recover a sparse shifted sample and the stable unshifted sample with one new coloring. -/
def H3 : Prop :=
  (∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ K * x / Real.log x ^ 3) →
  let colors (Y n : ℕ) := {t : Finset ℕ × Finset ℕ // t.1 ∪ t.2 = (Icc Y n).filter Nat.Prime ∧ Disjoint t.1 t.2}
  let semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ Nat.factoredNumbers C)
  let density (C : Finset ℕ) (n u : ℕ) : ℝ :=
    ((semigroup C (n/u)).card : ℝ)*u/n
  let pick {Y n} (c : colors Y n) (b : Bool) := if b then c.val.1 else c.val.2
  let F (C : Finset ℕ) (w : ℝ) := exp (-w) * (((range (⌊exp w⌋₊ + 1)).filter (· ∈ Nat.factoredNumbers C)).card : ℝ)
  let euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹
  let eulerScale (C : Finset ℕ) (n : ℕ) := euler C / log n
  let Stable {Y} (N : ℕ → ℕ) (c : ∀ k, colors Y (N k)) (b : Bool) : Prop :=
    ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, |s| ≤ H →
        |F (pick (c k) b) (log (N k)+s) - F (pick (c k) b) (log (N k))|
          ≤ η*eulerScale (pick (c k) b) (N k)
  ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
      ∀ (c : ∀ k, colors Y (N k)) (b : Bool), Stable N c b → ∃ᶠ k in atTop,
        2 ≤ N k ∧ ∃ w : ℝ, 0 < w ∧ ∃ d : (m : ℕ) → colors Y m,
        (∀ i < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) (!b)) (N k) (i+1) ≤
          (w*(log m/log (N k))) * density (pick (d m) (!b)) m (i+1) + η*eulerScale (pick (c k) (!b)) (N k)) ∧
        (∀ j < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) b) (N k) 1 ≤
          w⁻¹*density (pick (d m) b) m (j+1) + η*eulerScale (pick (c k) b) (N k))

/-
The elementary von Mangoldt estimates and partial summation below are
adapted from PrimeNumberTheoremAnd/IEANTN/Mertens.lean, commit
650d31264be65f4cd6e70c45d8b25d86d482a761, by the PrimeNumberTheoremAnd
contributors (Apache License 2.0), via the local Mertens490 port.
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/650d31264be65f4cd6e70c45d8b25d86d482a761/PrimeNumberTheoremAnd/IEANTN/Mertens.lean
The
upstream proof credits Leo Goldmakher, “A quick proof of Mertens' theorem”.
The full Apache license appears at the end of this file.
-/
section
open Asymptotics Topology
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

theorem sum_mangoldt_div_eq (x : ℝ) :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
  intro E₁Λ
  dsimp [E₁Λ]
  ring

theorem errOne_ge {x : ℝ} (hx : 1 ≤ x) :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  E₁Λ x  ≥ -2 := by
  intro E₁Λ
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

theorem errOne_le {x : ℝ} (hx : 1 ≤ x) :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  E₁Λ x ≤ log 4 + 4 := by
  intro E₁Λ
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
  exact abs_le.mpr ⟨by linarith [errOne_ge hx, log_nonneg (by norm_num : (1:ℝ) ≤ 4)], errOne_le hx⟩

theorem errOne_bounded' :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  intro E₁Λ
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩

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

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  intro E₁Λ
  obtain ⟨c, hc1, hc2⟩ := errOne_bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact (((measurable_floor_sum (fun d => (Λ d) / d)).sub Real.measurable_log).div
      (measurable_id.mul (Real.measurable_log.pow_const 2))).aestronglyMeasurable
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

theorem errTwo_eq {x : ℝ} (hx : 2 ≤ x) :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  let γ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)
  let E₂Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / (d * log d) - log (log x) - γ
  E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  intro E₁Λ γ E₂Λ
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

theorem errTwo_upper {x : ℝ} (hx : 2 ≤ x) :
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  let γ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)
  let E₂Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / (d * log d) - log (log x) - γ
  E₂Λ x ≤ (log 4 + 6) / log x := by
  intro E₁Λ γ E₂Λ
  have : 0 < log x := by apply log_pos; linarith
  have eqn : E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := errTwo_eq hx
  have ub {t : ℝ} (ht : 1 ≤ t) : E₁Λ t ≤ log 4 + 4 := errOne_le ht
  rw [eqn]
  grw [ub (by linarith)]
  have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
    _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
      apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
        (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
      intro y hy; simp at hy
      have : 1 < y := by linarith
      have : 0 < log y := log_pos this
      gcongr; exact errOne_ge (by linarith)
    _ = _ := integ_div_mul_log_sq (-2) hx
  grw [this]
  grind

/-- The logarithm of the finite Euler product differs from the prime reciprocal
sum by a bounded amount, since the quadratic remainders are summable. -/
lemma full_product_bound : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
    (∏ p ∈ n.primesLE, (1 - (p : ℝ)⁻¹)⁻¹) ≤ B * log n := by
  let E₁Λ (x : ℝ) := ∑ d ∈ Ioc 0 ⌊x⌋₊, (Λ d) / d - log x
  let γ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)
  let R := ∑' k : ℕ, (2 : ℝ) / (k : ℝ)^2
  let A := (log 4 + 6) / log 2
  refine ⟨exp (γ+A+R), exp_pos _, ?_⟩
  intro n hn
  have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < log (n:ℝ) := log_pos (by linarith)
  have hA : (log 4+6)/log (n:ℝ) ≤ A :=
    div_le_div_of_nonneg_left (by positivity) (log_pos (by norm_num)) (log_le_log (by norm_num) h2)
  have he := errTwo_upper h2
  change (∑ d ∈ Ioc 0 ⌊(n:ℝ)⌋₊, Λ d / (d * log d)) - log (log n) - γ ≤ _ at he
  rw [Nat.floor_natCast] at he
  have hp (p : ℕ) (h : p ∈ n.primesLE) := (Nat.mem_primesLE.mp h).2
  have recip : (∑ p ∈ n.primesLE, (p:ℝ)⁻¹) ≤ ∑ d ∈ Ioc 0 n, Λ d / (d * log d) := by
    calc
      _ = ∑ p ∈ n.primesLE, Λ p / (p * log p) := by
        apply sum_congr rfl
        intro p h
        rw [vonMangoldt_apply_prime (hp p h)]
        field_simp [(log_pos (by exact_mod_cast (hp p h).one_lt) : 0 < log (p:ℝ)).ne']
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg
        (fun p h => mem_Ioc.mpr ⟨(hp p h).pos, (Nat.mem_primesLE.mp h).1⟩)
        (fun p _ _ => div_nonneg vonMangoldt_nonneg (mul_nonneg (Nat.cast_nonneg _) (log_natCast_nonneg _)))
  have err (p : ℕ) (h : p ∈ n.primesLE) :
      log ((1-(p:ℝ)⁻¹)⁻¹) ≤ (p:ℝ)⁻¹ + 2 / (p:ℝ)^2 := by
    have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (hp p h).two_le
    have hp0 : (0:ℝ) < p := by linarith
    have hi := inv_lt_one_of_one_lt₀ (show 1 < (p:ℝ) by linarith)
    have hlog := log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr hi))
    apply hlog.trans
    have hden : 0 < (p:ℝ)-1 := by linarith
    have hrewrite : (1-(p:ℝ)⁻¹)⁻¹ - 1 = 1/((p:ℝ)-1) := by field_simp; ring
    rw [hrewrite]
    field_simp
    nlinarith
  have hterm (p : ℕ) (h : p ∈ n.primesLE) : 0 < (1 - (p:ℝ)⁻¹)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hp p h).one_lt)))
  have herr : (∑ p ∈ n.primesLE, 2 / (p:ℝ)^2) ≤ R :=
    Summable.sum_le_tsum _ (fun _ _ => by positivity)
      (Summable.const_div (by simp) (2:ℝ))
  rw [← exp_log (prod_pos hterm), log_prod (fun p h => (hterm p h).ne'),
    ← exp_log hL, ← exp_add, exp_le_exp]
  linarith [sum_le_sum err, sum_add_distrib (s:=n.primesLE)
    (f:=fun p : ℕ => (p:ℝ)⁻¹) (g:=fun p : ℕ => 2/(p:ℝ)^2)]
end

/-- A common target coloring that recovers every matrix entry recovers every separated pair. -/
lemma transfer_of_matrix :
  let colors (Y n : ℕ) := {t : Finset ℕ × Finset ℕ // t.1 ∪ t.2 = (Icc Y n).filter Nat.Prime ∧ Disjoint t.1 t.2}
  let semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ Nat.factoredNumbers C)
  let value (n a b : ℕ) := (a : ℝ) * b * log n / (n : ℝ)^2
  let entry {Y n} (c : colors Y n) (u s : ℕ) :=
    value n (semigroup c.val.1 (n/u)).card (semigroup c.val.2 (n/s)).card
  (∀ Y K, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ c : colors Y n,
    ∀ᶠ m : ℕ in atTop, ∃ d : colors Y m, ∀ i < K, ∀ j < K,
      entry c (i+1) (j+1) ≤ entry d (i+1) (j+1) + δ) → OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 := by
  intro colors semigroup value entry transfer
  let Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C
  let vertices (Y K : ℕ) := semigroup Y.primesBelow K
  have mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
    simp only [semigroup, mem_filter, mem_Icc, Active]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩
  let Adm (n : ℕ) (A B : Finset ℕ) := A ⊆ Icc 1 n ∧ B ⊆ Icc 1 n ∧
    ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ A, ∀ d ∈ B, a*b=c*d → a=c ∧ b=d
  let Sep (Y K : ℕ) (A B : Finset ℕ) :=
    (∀ a ∈ A, ∀ b ∈ B, ∀ p : ℕ, p.Prime → Y ≤ p → p ∣ a → ¬p ∣ b) ∧
    ∀ z ∈ A ∪ B, ∃ u : ℕ, u ≤ K ∧ u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p
  let primes (Y n : ℕ) := (Icc Y n).filter Nat.Prime
  have color_large {Y n} (c : colors Y n) : ∀ p ∈ c.val.1 ∪ c.val.2, Y ≤ p := by
    rw [c.property.1]
    exact fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).1
  have small_disjoint {Y n} (c : colors Y n) :
      Disjoint c.val.1 Y.primesBelow ∧ Disjoint c.val.2 Y.primesBelow := by
    constructor <;> apply disjoint_left.mpr <;> intro p hp h
    · exact (Nat.mem_primesBelow.mp h).1.not_ge ((color_large c) _ (mem_union_left _ hp))
    · exact (Nat.mem_primesBelow.mp h).1.not_ge ((color_large c) _ (mem_union_right _ hp))
  have coprime_active {C D : Finset ℕ} {a b : ℕ} (hd : Disjoint C D)
      (ha : Active C a) (hb : Active D b) : a.Coprime b :=
    Nat.coprime_of_dvd fun p hp hx hy => disjoint_left.mp hd
      (Nat.mem_factoredNumbers'.mp ha p hp hx) (Nat.mem_factoredNumbers'.mp hb p hp hy)
  have recover {a b c d : ℕ} (had : a.Coprime d) (hcb : c.Coprime b)
      (h : a*b=c*d) : a=c :=
    Nat.dvd_antisymm (had.dvd_of_dvd_mul_right (h ▸ dvd_mul_right a b))
      (hcb.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right c d))
  -- The entire small-prime part divides the bounded cofactor witness.
  have extract {Y K z w : ℕ} (hz : 0 < z) (hw : w ≤ K) (hd : w ∣ z)
      (hr : ∀ p : ℕ, p.Prime → p ∣ z/w → Y ≤ p) :
      ∃ u ∈ vertices Y K, u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p := by
    let S := z.divisors.filter (Active Y.primesBelow)
    have one : Active Y.primesBelow 1 := by
      apply Nat.mem_factoredNumbers'.mpr
      intro p hp hd
      exact (hp.not_dvd_one hd).elim
    obtain ⟨u,hu,hm⟩ := S.exists_max_image id ⟨1,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _,hz.ne'⟩,one⟩⟩
    obtain ⟨hud,hus⟩ := mem_filter.mp hu
    have hdiv := Nat.dvd_of_mem_divisors hud
    have cop : u.Coprime (z/w) := Nat.coprime_of_dvd fun p hp hpu hpz =>
      (Nat.mem_primesBelow.mp (Nat.mem_factoredNumbers'.mp hus p hp hpu)).1.not_ge (hr p hp hpz)
    have huw := cop.dvd_of_dvd_mul_right (show u ∣ w*(z/w) by rwa [Nat.mul_div_cancel' hd])
    refine ⟨u,mem_semigroup.mpr ⟨hus,(Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd hz) huw).trans hw⟩,hdiv,?_⟩
    intro p hp hpu
    by_contra! hh
    have hps : Active Y.primesBelow p := by
      apply Nat.mem_factoredNumbers'.mpr
      intro q hq hqp
      obtain rfl := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      exact Nat.mem_primesBelow.mpr ⟨hh,hq⟩
    have hmax := hm (u*p) (mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Nat.dvd_div_iff_mul_dvd hdiv).mp hpu,hz.ne'⟩,Nat.mul_mem_factoredNumbers hus hps⟩)
    have hlt := Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.pos_of_ne_zero hus.1)
    simp only [id_eq] at hmax
    omega
  let Covers (Y K n : ℕ) (C A : Finset ℕ) := ∀ z ∈ A,
    ∃ h ∈ semigroup C n, ∃ u ∈ vertices Y K, h*u=z
  have colors_cover {Y K n A B} (ha : Adm n A B) (hs : Sep Y K A B) :
      ∃ c : colors Y n, Covers Y K n c.val.1 A ∧ Covers Y K n c.val.2 B := by
    let Q := (primes Y n).filter (fun p => ∃ a ∈ A, p ∣ a)
    let R := primes Y n \ Q
    let c : colors Y n := ⟨(Q,R),by ext; simp [Q,R,primes]; tauto, disjoint_left.mpr (fun {_} h h' => (mem_sdiff.mp h').2 h)⟩
    have split {C T : Finset ℕ} (ht : T ⊆ A ∪ B) (bound : T ⊆ Icc 1 n)
        (color : ∀ z ∈ T, ∀ p ∈ primes Y n, p ∣ z → p ∈ C) : Covers Y K n C T := by
      intro z hz
      obtain ⟨hz0,hzn⟩ := mem_Icc.mp (bound hz)
      obtain ⟨w,hw,hd,hr⟩ := hs.2 z (ht hz)
      obtain ⟨u,hu,hd,hr⟩ := extract hz0 hw hd hr
      refine ⟨z/u,mem_semigroup.mpr ⟨Nat.mem_factoredNumbers'.mpr ?_,(Nat.div_le_self ..).trans hzn⟩,u,hu,Nat.div_mul_cancel hd⟩
      intro p hp hpd
      have hdv := hpd.trans (Nat.div_dvd_of_dvd hd)
      exact color z hz p (mem_filter.mpr ⟨mem_Icc.mpr ⟨hr p hp hpd,(Nat.le_of_dvd hz0 hdv).trans hzn⟩,hp⟩) hdv
    refine ⟨c,split subset_union_left ha.1 (fun z hz p hp hd => mem_filter.mpr ⟨hp,z,hz,hd⟩),
      split subset_union_right ha.2.1 ?_⟩
    intro b hb p hp hd
    refine mem_sdiff.mpr ⟨hp,?_⟩
    intro h
    obtain ⟨a,ha',hd'⟩ := (mem_filter.mp h).2
    exact hs.1 a ha' b hb p (mem_filter.mp hp).2 (mem_Icc.mp (mem_filter.mp hp).1).1 hd' hd
  let ratios (S : Finset ℕ) : Finset ℚ :=
    ((S ×ˢ S).filter (fun t => t.1 < t.2)).image (fun t => (t.2 : ℚ)/t.1)
  have mem_ratios {S q} : q ∈ ratios S ↔ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (b:ℚ)/a=q := by
    simp only [ratios,mem_image,mem_filter,mem_product, Prod.exists]
    constructor
    · rintro ⟨a,b,⟨⟨ha,hb⟩,hlt⟩,he⟩
      exact ⟨a,ha,b,hb,hlt,he⟩
    · rintro ⟨a,ha,b,hb,hlt,he⟩
      exact ⟨a,b,⟨⟨ha,hb⟩,hlt⟩,he⟩
  have ratios_mono {S T : Finset ℕ} (h : S ⊆ T) : ratios S ⊆ ratios T := by
    intro q hq
    obtain ⟨a,ha,b,hb,hl,he⟩ := mem_ratios.mp hq
    exact mem_ratios.mpr ⟨a,h ha,b,h hb,hl,he⟩
  let fiber (U A : Finset ℕ) (h : ℕ) := U.filter (fun u => h*u ∈ A)
  let oldGraph (U H A : Finset ℕ) := H.biUnion (fun h => ratios (fiber U A h))
  have oldGraph_subset (U H A) : oldGraph U H A ⊆ ratios U := by
    intro q hq
    obtain ⟨h,_,hm⟩ := mem_biUnion.mp hq
    exact ratios_mono (filter_subset ..) hm
  have ratio_eq {a b c d : ℕ} (ha : a ≠ 0) (hc : c ≠ 0) :
      (b:ℚ)/a=(d:ℚ)/c ↔ b*c=d*a := by
    rw [div_eq_div_iff (by exact_mod_cast ha) (by exact_mod_cast hc)]
    exact_mod_cast Iff.rfl
  have old_blue {Y K n A B} (ha : Adm n A B) (c : colors Y n)
      {h} (_hh : h ∈ semigroup c.val.2 n) : Disjoint
        (ratios (fiber (vertices Y K) B h)) (oldGraph (vertices Y K) (semigroup c.val.1 n) A) := by
    apply disjoint_left.mpr
    intro q hq hg
    obtain ⟨k,hk,hg⟩ := mem_biUnion.mp hg
    obtain ⟨a,ha',b,hb',hlt,he⟩ := mem_ratios.mp hg
    obtain ⟨d,hd,e,he',_,hf⟩ := mem_ratios.mp hq
    have ha0 := (mem_semigroup.mp (mem_filter.mp ha').1).1.1
    have hd0 := (mem_semigroup.mp (mem_filter.mp hd).1).1.1
    have eq := (ratio_eq ha0 hd0).mp (he.trans hf.symm)
    have coll := ha.2.2 _ (mem_filter.mp hb').2 _ (mem_filter.mp hd).2 _
      (mem_filter.mp ha').2 _ (mem_filter.mp he').2 (by nlinarith only [congrArg (fun v => (k*h)*v) eq])
    exact hlt.ne (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mem_semigroup.mp hk).1.1) coll.1.symm)
  -- Maximize the compatible small cofactors separately on each prefix.
  let choices (U : Finset ℕ) (G : Finset ℚ) (t : ℕ) :=
    ((U.filter (· ≤ t)).powerset).filter (fun S => ratios S ⊆ G)
  have mem_choices {U G t S} : S ∈ choices U G t ↔
      (∀ u ∈ S, u ∈ U ∧ u ≤ t) ∧ ratios S ⊆ G := by
    simp only [choices,mem_filter,mem_powerset,subset_iff,mem_filter]
  have has_best (U G t) : ∃ S ∈ choices U G t, ∀ T ∈ choices U G t, T.card ≤ S.card := by
    apply exists_max_image
    refine ⟨∅,mem_choices.mpr ⟨by simp,by simp [ratios]⟩⟩
  let best (U G t) := (has_best U G t).choose
  have best_mem (U G t) : best U G t ∈ choices U G t := (has_best U G t).choose_spec.1
  let rank (U G t) := (best U G t).card
  have le_rank {U G t S} (h : S ∈ choices U G t) : S.card ≤ rank U G t :=
    (has_best U G t).choose_spec.2 _ h
  have rank_mono (U G) : Monotone (rank U G) := by
    intro a b hab
    apply le_rank
    obtain ⟨hp,hr⟩ := mem_choices.mp (best_mem U G a)
    exact mem_choices.mpr ⟨fun u hu => ⟨(hp u hu).1,(hp u hu).2.trans hab⟩,hr⟩
  have rank_zero {U} (hU : 0 ∉ U) (G) : rank U G 0 = 0 := by
    simp only [rank]
    rw [card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨hm,hl⟩ := (mem_choices.mp (best_mem U G 0)).1 u hu
    exact hU (Nat.eq_zero_of_le_zero hl ▸ hm)
  let weight (U G) (i : ℕ) := rank U G (i+1) - rank U G i
  have rank_step (U G i) : rank U G (i+1) = rank U G i + weight U G i := by
    have : rank U G i ≤ rank U G (i+1) := rank_mono U G (Nat.le_succ i)
    unfold weight
    omega
  have weight_le_one (U G i) : weight U G i ≤ 1 := by
    let S := best U G (i+1)
    obtain ⟨hp,hr⟩ := mem_choices.mp (best_mem U G (i+1))
    have hh : S.erase (i+1) ∈ choices U G i := by
      refine mem_choices.mpr ⟨?_,(ratios_mono (erase_subset ..)).trans hr⟩
      intro u hu
      obtain ⟨hne,hm⟩ := mem_erase.mp hu
      obtain ⟨hU,hl⟩ := hp u hm
      exact ⟨hU,by omega⟩
    have hh' := le_rank hh
    have he : S.card ≤ (S.erase (i+1)).card + 1 := by
      by_cases hm : i+1 ∈ S
      · rw [card_erase_add_one hm]
      · simp [erase_eq_of_notMem hm]
    change S.card - rank U G i ≤ 1
    omega
  have rank_sum {U} (hU : 0 ∉ U) (G t K) :
      rank U G (min K t) = ∑ i ∈ range K, if i+1 ≤ t then weight U G i else 0 := by
    induction K with
    | zero => simp [rank_zero hU]
    | succ k ih =>
      rw [sum_range_succ,← ih]
      by_cases h : k+1 ≤ t
      · rw [if_pos h,min_eq_left h,min_eq_left (by omega)]
        exact rank_step U G k
      · rw [if_neg h,min_eq_right (by omega),min_eq_right (by omega),add_zero]
  let size (U G C K n) := ∑ i ∈ range K, weight U G i * (semigroup C (n/(i+1))).card
  have prefix_count {U} (hU : 0 ∉ U) (G C K n) :
      (∑ h ∈ semigroup C n, rank U G (min K (n/h))) = size U G C K n := by
    simp_rw [rank_sum hU]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    have filt : (semigroup C n).filter (fun h => h ≤ n/(i+1)) = semigroup C (n/(i+1)) := by
      ext h
      simp only [mem_filter,mem_semigroup]
      constructor
      · exact fun x => ⟨x.1.1,x.2⟩
      · exact fun x => ⟨⟨x.1,x.2.trans (Nat.div_le_self ..)⟩,x.2⟩
    calc
      _ = ∑ h ∈ semigroup C n, if h ≤ n/(i+1) then weight U G i else 0 := by
        apply sum_congr rfl
        intro h hh
        simp only [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1),
          Nat.le_div_iff_mul_le (Nat.zero_lt_succ i),mul_comm (i+1) h]
      _ = _ := by rw [← sum_filter, filt]; simp [mul_comm]
  have zero_not_vertex (Y K) : 0 ∉ vertices Y K := fun h => (mem_semigroup.mp h).1.1 rfl
  let assemble (H : Finset ℕ) (F : ℕ → Finset ℕ) :=
    (H.sigma F).image (fun x => x.1 * x.2)
  have mem_assemble {H F z} : z ∈ assemble H F ↔ ∃ h ∈ H, ∃ u ∈ F h, h*u=z := by
    simp only [assemble,mem_image,Sigma.exists,mem_sigma]
    constructor
    · rintro ⟨h,u,⟨hh,hu⟩,he⟩
      exact ⟨h,hh,u,hu,he⟩
    · rintro ⟨h,hh,u,hu,he⟩
      exact ⟨h,u,⟨hh,hu⟩,he⟩
  have assemble_card {C n Y K F} (hd : Disjoint C Y.primesBelow)
      (hf : ∀ h ∈ semigroup C n, F h ⊆ vertices Y K) :
      (assemble (semigroup C n) F).card = ∑ h ∈ semigroup C n, (F h).card := by
    simp only [assemble]
    rw [card_image_of_injOn,card_sigma]
    rintro ⟨h,u⟩ hx ⟨j,v⟩ hy eq
    obtain ⟨hh,hu⟩ := mem_sigma.mp hx
    obtain ⟨hj,hv⟩ := mem_sigma.mp hy
    change h*u=j*v at eq
    obtain rfl := recover (coprime_active hd (mem_semigroup.mp hh).1 (mem_semigroup.mp (hf _ hj hv)).1)
      (coprime_active hd (mem_semigroup.mp hj).1 (mem_semigroup.mp (hf _ hh hu)).1) eq
    obtain rfl := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1) eq
    rfl
  have old_size {Y K n C A G} (cover : Covers Y K n C A) (bound : A ⊆ Icc 1 n)
      (hd : Disjoint C Y.primesBelow)
      (graph : ∀ h ∈ semigroup C n, ratios (fiber (vertices Y K) A h) ⊆ G) :
      A.card ≤ size (vertices Y K) G C K n := by
    let U := vertices Y K
    let F := fiber U A
    have sub : A ⊆ assemble (semigroup C n) F := by
      intro z hz
      obtain ⟨h,hh,u,hu,he⟩ := cover _ hz
      exact mem_assemble.mpr ⟨h,hh,u,mem_filter.mpr ⟨hu,he ▸ hz⟩,he⟩
    apply (card_le_card sub).trans
    rw [assemble_card (F:=F) (K:=K) hd (fun _ _ => filter_subset ..),← prefix_count (zero_not_vertex Y K)]
    apply sum_le_sum
    intro h hh
    refine le_rank (mem_choices.mpr ⟨?_,graph _ hh⟩)
    intro u hu
    obtain ⟨hu',ha⟩ := mem_filter.mp hu
    exact ⟨hu',le_min (mem_semigroup.mp hu').2
      ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1)).mpr
      (mul_comm u h ▸ (mem_Icc.mp (bound ha)).2))⟩
  -- Old red fibers determine a quotient graph. Blue fibers avoid its edges.
  have dominate {Y K n A B} (ha : Adm n A B) (c : colors Y n)
      (ca : Covers Y K n c.val.1 A) (cb : Covers Y K n c.val.2 B) :
      ∃ G ⊆ ratios (vertices Y K),
        A.card ≤ size (vertices Y K) G c.val.1 K n ∧
        B.card ≤ size (vertices Y K) (ratios (vertices Y K) \ G) c.val.2 K n := by
    let U := vertices Y K
    refine ⟨oldGraph U (semigroup c.val.1 n) A,oldGraph_subset ..,
      old_size ca ha.1 (small_disjoint c).1 (fun _ hh => subset_biUnion_of_mem (fun h => ratios (fiber U A h)) hh),
      old_size cb ha.2.1 (small_disjoint c).2 ?_⟩
    intro h hh q hq
    exact mem_sdiff.mpr ⟨ratios_mono (filter_subset ..) hq,disjoint_left.mp (old_blue ha c hh) hq⟩
  let optimal (Y K n : ℕ) (G : Finset ℚ) (C : Finset ℕ) :=
    assemble (semigroup C n) (fun h => best (vertices Y K) G (min K (n/h)))
  have optimal_data {Y K n G C z} (hz : z ∈ optimal Y K n G C) :
      ∃ h ∈ semigroup C n, ∃ u ∈ best (vertices Y K) G (min K (n/h)),
        u ∈ vertices Y K ∧ h*u=z ∧ z ∈ Icc 1 n := by
    obtain ⟨h,hh,u,hu,rfl⟩ := mem_assemble.mp hz
    obtain ⟨hm,hl⟩ := (mem_choices.mp (best_mem ..)).1 u hu
    have hpos := Nat.pos_of_ne_zero (mem_semigroup.mp hh).1.1
    refine ⟨h,hh,u,hu,hm,rfl,mem_Icc.mpr ⟨Nat.mul_pos hpos
      (Nat.pos_of_ne_zero (mem_semigroup.mp hm).1.1),?_⟩⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le hpos).mp (hl.trans (min_le_right ..))
  have optimal_card {Y K n G C} (hd : Disjoint C Y.primesBelow) :
      (optimal Y K n G C).card = size (vertices Y K) G C K n := by
    simp only [optimal]
    rw [assemble_card (K:=K) hd,← prefix_count (zero_not_vertex Y K)]
    · exact fun h _ u hu => ((mem_choices.mp (best_mem ..)).1 u hu).1
  have recover_rough {Y n} (c : colors Y n) {h j k l u v x y : ℕ}
      (hh : Active c.val.1 h) (hj : Active c.val.2 j) (hk : Active c.val.1 k) (hl : Active c.val.2 l)
      (hu : Active Y.primesBelow u) (hv : Active Y.primesBelow v)
      (hx : Active Y.primesBelow x) (hy : Active Y.primesBelow y)
      (he : (h*u)*(j*v)=(k*x)*(l*y)) : h=k ∧ j=l ∧ u*v=x*y := by
    have huv := Nat.mul_mem_factoredNumbers hu hv
    have hxy := Nat.mul_mem_factoredNumbers hx hy
    have eq : h*(j*(u*v))=k*(l*(x*y)) := by linear_combination (norm := ring) he
    have e := recover ((coprime_active c.property.2 hh hl).mul_right
      (coprime_active (small_disjoint c).1 hh hxy)) ((coprime_active c.property.2 hk hj).mul_right
      (coprime_active (small_disjoint c).1 hk huv)) eq
    subst k
    have eq' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh.1) eq
    have e := recover (coprime_active (small_disjoint c).2 hj hxy) (coprime_active (small_disjoint c).2 hl huv) eq'
    subst l
    exact ⟨rfl,rfl,Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hj.1) eq'⟩
  have cofactor_injective {S T : Finset ℕ} (hs : 0 ∉ S) (ht : 0 ∉ T)
      (hg : Disjoint (ratios S) (ratios T)) {u v x y : ℕ}
      (hu : u ∈ S) (hv : v ∈ T) (hx : x ∈ S) (hy : y ∈ T) (he : u*v=x*y) :
      u=x ∧ v=y := by
    have excl {a b c d : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ T) (hd : d ∈ T)
        (hl : a < b) (e : a*d=b*c) : False := by
      have a0 : a ≠ 0 := fun h => hs (h ▸ ha)
      have c0 : c ≠ 0 := fun h => ht (h ▸ hc)
      have hlt : c < d := by
        by_contra! h
        exact (Nat.mul_lt_mul_of_pos_right hl (Nat.pos_of_ne_zero c0)).not_ge
          (e ▸ Nat.mul_le_mul_left a h)
      have eq := (ratio_eq a0 c0).mpr (show b*c=d*a by rw [← e,mul_comm])
      exact disjoint_left.mp hg (mem_ratios.mpr ⟨a,ha,b,hb,hl,rfl⟩)
        (mem_ratios.mpr ⟨c,hc,d,hd,hlt,eq.symm⟩)
    have eq : u=x := by
      rcases lt_trichotomy u x with hl|eq|hl
      · exact (excl hu hx hy hv hl he).elim
      · exact eq
      · exact (excl hx hu hv hy hl he.symm).elim
    subst x
    exact ⟨rfl,Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (fun e => hs (e ▸ hu))) he⟩
  -- At the new cutoff, assemble maximal fibers for the same two graphs.
  have attainable {Y K n} (c : colors Y n) (G : Finset ℚ) :
      let U := vertices Y K
      let A := optimal Y K n G c.val.1
      let B := optimal Y K n (ratios U \ G) c.val.2
      Adm n A B ∧ Covers Y K n c.val.1 A ∧ Covers Y K n c.val.2 B ∧
        A.card = size U G c.val.1 K n ∧ B.card = size U (ratios U \ G) c.val.2 K n := by
    dsimp only
    have bound {D H} : optimal Y K n H D ⊆ Icc 1 n := by
      intro z hz
      obtain ⟨_,_,_,_,_,_,hb⟩ := optimal_data hz
      exact hb
    have cover {D H} : Covers Y K n D (optimal Y K n H D) := by
      intro z hz
      obtain ⟨h,hh,u,_,hu,he,_⟩ := optimal_data hz
      exact ⟨h,hh,u,hu,he⟩
    refine ⟨⟨bound,bound,?_⟩,cover,cover,optimal_card (small_disjoint c).1,optimal_card (small_disjoint c).2⟩
    intro a ha b hb a' ha' b' hb' he
    obtain ⟨h,hh,u,hu,hu',rfl,_⟩ := optimal_data ha
    obtain ⟨j,hj,v,hv,hv',rfl,_⟩ := optimal_data hb
    obtain ⟨k,hk,x,hx,hx',rfl,_⟩ := optimal_data ha'
    obtain ⟨l,hl,y,hy,hy',rfl,_⟩ := optimal_data hb'
    obtain ⟨rfl,rfl,eq⟩ := recover_rough c (mem_semigroup.mp hh).1 (mem_semigroup.mp hj).1
      (mem_semigroup.mp hk).1 (mem_semigroup.mp hl).1 (mem_semigroup.mp hu').1
      (mem_semigroup.mp hv').1 (mem_semigroup.mp hx').1 (mem_semigroup.mp hy').1 he
    have nz {D t} : 0 ∉ best (vertices Y K) D t :=
      fun h => zero_not_vertex Y K (((mem_choices.mp (best_mem ..)).1 _ h).1)
    obtain ⟨rfl,rfl⟩ := cofactor_injective nz nz (disjoint_left.mpr (fun _ hq hr =>
      (mem_sdiff.mp ((mem_choices.mp (best_mem ..)).2 hr)).2 ((mem_choices.mp (best_mem ..)).2 hq)))
      hu hv hx hy eq
    exact ⟨rfl,rfl⟩
  let model {Y n} (c : colors Y n) (U : Finset ℕ) (G H : Finset ℚ) (K : ℕ) :=
    value n (size U G c.val.1 K n) (size U H c.val.2 K n)
  have model_sum {Y n} (c : colors Y n) (U G H K) :
      model c U G H K = ∑ i ∈ range K, ∑ j ∈ range K,
        ((weight U G i : ℝ)*weight U H j) * entry c (i+1) (j+1) := by
    unfold model size entry value
    push_cast
    simp only [sum_mul,mul_sum,sum_div]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have model_loss {Y n m K} (c : colors Y n) (d : colors Y m) (U G H)
      {δ : ℝ} (hδ : 0 ≤ δ)
      (h : ∀ i < K, ∀ j < K, entry c (i+1) (j+1) ≤ entry d (i+1) (j+1)+δ) :
      model c U G H K ≤ model d U G H K + (K:ℝ)^2 * δ := by
    rw [model_sum,model_sum]
    calc
      _ ≤ ∑ i ∈ range K, ∑ j ∈ range K,
          (((weight U G i : ℝ)*weight U H j)*entry d (i+1) (j+1)+δ) := by
        apply sum_le_sum
        intro i hi
        apply sum_le_sum
        intro j hj
        have hw : ((weight U G i : ℝ)*weight U H j) ≤ 1 := by
          exact_mod_cast (Nat.mul_le_mul (weight_le_one U G i) (weight_le_one U H j))
        have := mul_le_mul_of_nonneg_left (h i (mem_range.mp hi) j (mem_range.mp hj))
          (show 0 ≤ (weight U G i : ℝ)*weight U H j by positivity)
        linarith [mul_le_mul_of_nonneg_right hw hδ]
      _ = _ := by simp [sum_add_distrib]; ring
  have value_mono {a b x y : ℕ} (n : ℕ) (h : a ≤ x) (h' : b ≤ y) :
      value n a b ≤ value n x y := by
    unfold value
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.mul_le_mul h h') (Real.log_natCast_nonneg n)) (sq_nonneg _)
  intro ε hε
  apply Eventually.of_forall
  intro Y K
  let δ : ℝ := ε/((K:ℝ)^2+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [transfer Y K δ hδ] with n hn
  intro A B ha hs
  obtain ⟨c,ca,cb⟩ := colors_cover (show Adm n A B from ha) (show Sep Y K A B from hs)
  obtain ⟨G,_,hA,hB⟩ := dominate ha c ca cb
  let U := vertices Y K
  let H := ratios U \ G
  filter_upwards [hn c] with m hm
  obtain ⟨d,hd⟩ := hm
  obtain ⟨hadm,_,_,hL,hR⟩ := attainable (K:=K) d G
  refine ⟨_,_,hadm,?_⟩
  change value n A.card B.card ≤ value m _ _ + ε
  rw [hL,hR]
  have hcost : (K:ℝ)^2*δ ≤ ε := by
    have hpos : 0 < (K:ℝ)^2+1 := by positivity
    have heq : δ*((K:ℝ)^2+1)=ε := div_mul_cancel₀ _ hpos.ne'
    nlinarith
  exact (value_mono n hA hB).trans ((model_loss c d U G H hδ.le hd).trans (add_le_add_right hcost _))


/-- A one-color counting bound and a two-color packing bound for truncated reciprocal masses. -/
lemma harmonic_bounds :
  let semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ Nat.factoredNumbers C)
  let mass (S : Finset ℕ) := ∑ m ∈ S, (m : ℝ)⁻¹
  let scale (C : Finset ℕ) (n : ℕ) := mass (semigroup C n) / log n
  (∀ {n : ℕ}, 0 < log (n:ℝ) → ∀ C, ((semigroup C n).card:ℝ)/n ≤ (log 4+5)*scale C n) ∧
  (∀ {C D : Finset ℕ}, Disjoint C D → ∀ {n : ℕ}, 1 ≤ log (n:ℝ) → log n * scale C n * scale D n ≤ 3) := by
  intro semigroup mass scale
  let Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C
  have mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
    simp only [Active, semigroup, mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩
  let smooth (n : ℕ) (P : ℕ → Prop) : Finset ℕ := by
    classical
    exact (Icc 1 n).filter (fun m => ∀ p, p.Prime → p ∣ m → P p)
  have mem_smooth {n m : ℕ} {P : ℕ → Prop} :
      m ∈ smooth n P ↔ (1 ≤ m ∧ m ≤ n) ∧ ∀ p, Nat.Prime p → p ∣ m → P p := by
    classical
    simp [smooth]
  have transport {α β : Type} (s : Finset α) (t : Finset β)
      (f : α → β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b)
      (hm : ∀ a ∈ s, f a ∈ t) (hi : Set.InjOn f s) :
      ∑ a ∈ s, g (f a) ≤ ∑ b ∈ t, g b := by
    classical
    rw [← sum_image hi]
    apply sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hm)
    exact fun b _ _ => hg b
  have log_sum (n : ℕ) (P : ℕ → Prop) :
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
  have count (n : ℕ) (P : ℕ → Prop) :
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
  have mass_product (n : ℕ) (P : ℕ → Prop) :
      mass (smooth n P) * mass (smooth n (fun p => ¬P p)) ≤ 1 + 2 * Real.log n := by
    let s := smooth n P
    let t := smooth n (fun p => ¬P p)
    let f (x : ℕ × ℕ) := x.1 * x.2
    have cop {a b : ℕ} (ha : a ∈ s) (hb : b ∈ t) : a.Coprime b :=
      Nat.coprime_of_dvd fun p hp hpa hpb =>
        (mem_smooth.mp hb).2 p hp hpb ((mem_smooth.mp ha).2 p hp hpa)
    have hm : ∀ x ∈ s ×ˢ t, f x ∈ Icc 1 (n^2) := by
      rintro ⟨a,b⟩ hx
      obtain ⟨ha,hb⟩ := mem_product.mp hx
      obtain ⟨hap,han⟩ := (mem_smooth.mp ha).1
      obtain ⟨hbp,hbn⟩ := (mem_smooth.mp hb).1
      exact mem_Icc.mpr ⟨Nat.mul_pos hap hbp, by simpa [f, pow_two] using Nat.mul_le_mul han hbn⟩
    have hi : Set.InjOn f (↑(s ×ˢ t : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
      rintro ⟨a,b⟩ hx ⟨c,d⟩ hy he
      obtain ⟨ha,hb⟩ := mem_product.mp hx
      obtain ⟨hc,hd⟩ := mem_product.mp hy
      change a * b = c * d at he
      have ha' : a ∣ c := (cop ha hd).dvd_of_dvd_mul_right (he ▸ dvd_mul_right a b)
      have hc' : c ∣ a := (cop hc hb).dvd_of_dvd_mul_right (he.symm ▸ dvd_mul_right c d)
      obtain rfl := Nat.dvd_antisymm ha' hc'
      have := Nat.eq_of_mul_eq_mul_left (mem_smooth.mp ha).1.1 he
      simp [this]
    calc
      _ = ∑ x ∈ s ×ˢ t, ((f x : ℕ) : ℝ)⁻¹ := by
        simp [s, t, mass, sum_mul_sum, sum_product, f, mul_comm]
      _ ≤ ∑ j ∈ Icc 1 (n^2), (j : ℝ)⁻¹ := transport _ _ f (fun j : ℕ => (j : ℝ)⁻¹) (fun _ => by positivity) hm hi
      _ ≤ 1 + Real.log ((n^2 : ℕ) : ℝ) := by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          using harmonic_le_one_add_log (n^2)
      _ = _ := by simp [Real.log_pow]
  have smooth_eq (C : Finset ℕ) (n) :
      smooth n (· ∈ C) = semigroup C n := by
    ext h
    simp only [mem_smooth,semigroup,mem_filter,mem_Icc,Nat.mem_factoredNumbers']
  have count_le {n : ℕ} (hn : 0 < Real.log n) (C) :
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
  have scale_product {C D : Finset ℕ} (hd : Disjoint C D) {n : ℕ}
      (hn : 1 ≤ Real.log n) :
      Real.log n * scale C n * scale D n ≤ 3 := by
    have h := mass_product n (· ∈ C)
    rw [smooth_eq] at h
    have sub : semigroup D n ⊆ smooth n (fun p => p ∉ C) := by
      intro h hh
      obtain ⟨ha,hl⟩ := mem_semigroup.mp hh
      exact mem_smooth.mpr ⟨⟨Nat.pos_of_ne_zero ha.1,hl⟩,fun p hp hv hC =>
        disjoint_left.mp hd hC (Nat.mem_factoredNumbers'.mp ha p hp hv)⟩
    have le : mass (semigroup D n) ≤ mass (smooth n (fun p => p ∉ C)) :=
      sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => by positivity)
    have h0 : 0 ≤ mass (semigroup C n) := sum_nonneg (fun i _ => by positivity)
    have hm := (mul_le_mul_of_nonneg_left le h0).trans h
    have hl : 0 < Real.log n := by linarith
    unfold scale
    field_simp [hl.ne']
    nlinarith
  exact ⟨@count_le,@scale_product⟩


/-- Compare each Euler product with its own truncated harmonic sum, uniformly in the coloring. -/
lemma euler_comparison :
  let semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ Nat.factoredNumbers C)
  let euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹
  let truncMass (C : Finset ℕ) (n : ℕ) : ℝ := ∑ h ∈ semigroup C n, (h:ℝ)⁻¹
  (∀ {C : Finset ℕ}, (∀ p ∈ C, Nat.Prime p) → 0 < euler C) ∧
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n → ∀ C ⊆ n.primesLE, euler C ≤ B * truncMass C n := by
  intro semigroup euler truncMass
  let Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C
  have mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
    simp only [Active, semigroup, mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩
  have truncMass_nonneg (C n) : 0 ≤ truncMass C n := sum_nonneg (fun _ _ => by positivity)
  have euler_pos {C : Finset ℕ} (hC : ∀ p ∈ C, Nat.Prime p) : 0 < euler C := by
    apply prod_pos
    intro p hp
    have h : 1 < (p:ℝ) := by exact_mod_cast (hC p hp).one_lt
    exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ h))
  have truncMass_le_euler {C : Finset ℕ} (hC : ∀ p ∈ C, Nat.Prime p) (n : ℕ) :
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
  have active_split (C D : Finset ℕ) (z : ℕ) (hz : Active (C ∪ D) z) :
      ∃ a b : ℕ, Active C a ∧ Active D b ∧ a*b=z := by
    have one (S : Finset ℕ) : Active S 1 := Nat.mem_factoredNumbers'.mpr
      (fun p hp hd => (hp.not_dvd_one hd).elim)
    induction z using Nat.recOnMul with
    | zero => exact (hz.1 rfl).elim
    | one => exact ⟨1,1,one _,one _,rfl⟩
    | prime p hp =>
      have h := Nat.mem_factoredNumbers'.mp hz p hp dvd_rfl
      have act {S : Finset ℕ} (hs : p ∈ S) : Active S p := by
        apply Nat.mem_factoredNumbers'.mpr
        intro q hq hd
        exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hd ▸ hs
      rcases mem_union.mp h with h|h
      · exact ⟨p,1,act h,one _,mul_one _⟩
      · exact ⟨1,p,one _,act h,one_mul _⟩
    | mul a b ia ib =>
      obtain ⟨x,y,hx,hy,ex⟩ := ia (Nat.mem_factoredNumbers_of_dvd hz (dvd_mul_right ..))
      obtain ⟨u,v,hu,hv,ev⟩ := ib (Nat.mem_factoredNumbers_of_dvd hz (dvd_mul_left ..))
      exact ⟨x*u,y*v,Nat.mul_mem_factoredNumbers hx hu,Nat.mul_mem_factoredNumbers hy hv,by rw [← ex,← ev]; ring⟩
  have harmonic_le_product {C D : Finset ℕ} {n : ℕ} (hcd : C ∪ D = n.primesLE) :
      (harmonic n:ℝ) ≤ truncMass C n * truncMass D n := by
    let S := semigroup C n ×ˢ semigroup D n
    let f (t : ℕ × ℕ) := t.1*t.2
    have covers : Icc 1 n ⊆ S.image f := by
      intro z hz
      obtain ⟨hz0,hzn⟩ := mem_Icc.mp hz
      have act : Active (C ∪ D) z := Nat.mem_factoredNumbers'.mpr (fun p hp hd => by
        rw [hcd]; exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hz0 hd).trans hzn,hp⟩)
      obtain ⟨a,b,ha,hb,he⟩ := active_split C D z act
      refine mem_image.mpr ⟨(a,b),mem_product.mpr ⟨mem_semigroup.mpr ⟨ha,?_⟩,mem_semigroup.mpr ⟨hb,?_⟩⟩,he⟩
      · exact (Nat.le_of_dvd hz0 (he ▸ dvd_mul_right a b)).trans hzn
      · exact (Nat.le_of_dvd hz0 (he ▸ dvd_mul_left b a)).trans hzn
    calc
      _ = ∑ h ∈ Icc 1 n, (h:ℝ)⁻¹ := by simp [harmonic_eq_sum_Icc]
      _ ≤ ∑ h ∈ S.image f, (h:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg covers (fun _ _ _ => by positivity)
      _ ≤ ∑ t ∈ S, ((f t:ℕ):ℝ)⁻¹ := sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = _ := by simp [S,f,truncMass,sum_mul_sum,sum_product,mul_comm]
  have euler_le_trunc_uniform : ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ C ⊆ n.primesLE, euler C ≤ B*truncMass C n := by
    obtain ⟨B,hB,hm⟩ := full_product_bound
    refine ⟨B,hB,?_⟩
    intro n hn C hC
    let D := n.primesLE \ C
    have hD : ∀ p ∈ D, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (mem_sdiff.mp hp).1).2
    have hall : C ∪ D = n.primesLE := by ext p; simp [D]; grind
    have hd : Disjoint C D := disjoint_left.mpr (fun {_} h h' => (mem_sdiff.mp h').2 h)
    have prod : euler C*euler D=euler n.primesLE := by
      unfold euler
      rw [← prod_union hd,hall]
    have hfull : euler n.primesLE ≤ B * log n := hm n hn
    have hlog : Real.log (n:ℝ) ≤ (harmonic n:ℝ) := by
      simpa using log_le_harmonic_floor (n:ℝ) (by positivity)
    have hmass := (hlog.trans (harmonic_le_product hall)).trans
      (mul_le_mul_of_nonneg_left (truncMass_le_euler hD n) (truncMass_nonneg C n))
    have hfull' : euler C*euler D ≤ B*(truncMass C n*euler D) := by
      rw [prod]
      exact hfull.trans (by gcongr)
    exact (le_of_mul_le_mul_right (by simpa only [mul_assoc] using hfull') (euler_pos hD))
  exact ⟨@euler_pos, euler_le_trunc_uniform⟩


/-- Multiply the two recovered densities and pay a uniform additive error per matrix entry. -/
lemma matrix_of_euler :
  let colors (Y n : ℕ) := {t : Finset ℕ × Finset ℕ // t.1 ∪ t.2 = (Icc Y n).filter Nat.Prime ∧ Disjoint t.1 t.2}
  let semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ Nat.factoredNumbers C)
  let value (n a b : ℕ) := (a : ℝ) * b * log n / (n : ℝ)^2
  let entry {Y n} (c : colors Y n) (u s : ℕ) :=
    value n (semigroup c.val.1 (n/u)).card (semigroup c.val.2 (n/s)).card
  let density (C : Finset ℕ) (n u : ℕ) : ℝ :=
    ((semigroup C (n/u)).card : ℝ)*u/n
  let euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹
  let eulerScale (C : Finset ℕ) (n : ℕ) := euler C / log n
  let EulerPrimeColorTransfer : Prop :=
    ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
      ∀ c : (k : ℕ) → colors Y (N k), ∃ k, 2 ≤ N k ∧
        ∃ redSparse : Bool, ∃ w : ℝ, 0 < w ∧ ∃ d : (m : ℕ) → colors Y m,
        (∀ i < K, ∀ᶠ m : ℕ in atTop,
          density (c k).val.1 (N k) (i+1) ≤
            (if redSparse then w * (Real.log m / Real.log (N k)) else w⁻¹) * density (d m).val.1 m (i+1)
            + η*eulerScale (c k).val.1 (N k)) ∧
        (∀ j < K, ∀ᶠ m : ℕ in atTop,
          density (c k).val.2 (N k) (j+1) ≤
            (if redSparse then w⁻¹ else w * (Real.log m / Real.log (N k))) * density (d m).val.2 m (j+1)
            + η*eulerScale (c k).val.2 (N k))
  EulerPrimeColorTransfer →
  ∀ Y K, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ c : colors Y n,
    ∀ᶠ m : ℕ in atTop, ∃ d : colors Y m, ∀ i < K, ∀ j < K,
      entry c (i+1) (j+1) ≤ entry d (i+1) (j+1) + δ := by
  intro colors semigroup value entry density euler eulerScale EulerPrimeColorTransfer transfer
  let Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C
  have mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
    simp only [Active, semigroup, mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩
  let mass (S : Finset ℕ) := ∑ m ∈ S, (m : ℝ)⁻¹
  let scale (C : Finset ℕ) (n : ℕ) := mass (semigroup C n) / log n
  let OneColorBounds {Y n m} (K : ℕ) (η : ℝ) (c : colors Y n) (d : colors Y m) : Prop :=
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ Real.log n*a*b = Real.log m ∧
      (∀ i < K, density c.val.1 n (i+1) ≤ a*density d.val.1 m (i+1) + η*scale c.val.1 n) ∧
      (∀ j < K, density c.val.2 n (j+1) ≤ b*density d.val.2 m (j+1) + η*scale c.val.2 n)
  let AnalyticPrimeColorTransfer : Prop :=
    ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
      ∀ c : (k : ℕ) → colors Y (N k), ∃ k,
        ∀ᶠ m : ℕ in atTop, ∃ d : colors Y m, OneColorBounds K η (c k) d
  have ⟨count_le,scale_product⟩ := harmonic_bounds
  have ⟨_,euler_le_trunc_uniform⟩ := euler_comparison
  have entry_density {Y n} (c : colors Y n) {u s : ℕ} (hu : 0 < u) (hs : 0 < s) :
      entry c u s = Real.log n * density c.val.1 n u * density c.val.2 n s / (u*s) := by
    unfold entry value density
    have hu' : (u:ℝ) ≠ 0 := by exact_mod_cast hu.ne'
    have hs' : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    by_cases hn : n = 0
    · simp [hn]
    have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have scale_nonneg (C n) : 0 ≤ scale C n := by
    unfold scale mass
    exact div_nonneg (sum_nonneg (fun i _ => by positivity)) (Real.log_natCast_nonneg n)
  have density_nonneg (C n u) : 0 ≤ density C n u := by unfold density; positivity
  let envelope (K : ℕ) : ℝ := (Real.log 4+5)*(K:ℝ)
  have density_le_scale {n K u : ℕ} (hn : 0 < Real.log n) (hu : u ≤ K) (C) :
      density C n u ≤ envelope K * scale C n := by
    have hcard : (semigroup C (n/u)).card ≤ (semigroup C n).card :=
      card_le_card fun h hh => mem_semigroup.mpr ⟨(mem_semigroup.mp hh).1,
        (mem_semigroup.mp hh).2.trans (Nat.div_le_self ..)⟩
    calc
      _ = ((semigroup C (n/u)).card : ℝ)/n*u := by unfold density; ring
      _ ≤ ((semigroup C n).card : ℝ)/n * K := by gcongr
      _ ≤ ((Real.log 4+5)*scale C n) * K := by gcongr; exact count_le hn C
      _ = _ := by unfold envelope; ring
  have product_loss {x y X Y e f : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
      (hX : 0 ≤ X) (hY : 0 ≤ Y) (he : 0 ≤ e) (hf : 0 ≤ f)
      (ha : x ≤ X+e) (hb : y ≤ Y+f) : x*y ≤ X*Y + e*y + x*f := by
    let a := min x X
    let b := min y Y
    have ha0 : 0 ≤ a := le_min hx hX
    have hb0 : 0 ≤ b := le_min hy hY
    have hxa : x-a ≤ e := sub_le_iff_le_add'.mpr (by dsimp [a]; rw [min_add]; exact le_min (by linarith) (by linarith))
    have hyb : y-b ≤ f := sub_le_iff_le_add'.mpr (by dsimp [b]; rw [min_add]; exact le_min (by linarith) (by linarith))
    have hp : a*b ≤ X*Y := mul_le_mul (min_le_right ..) (min_le_right ..) hb0 hX
    have hf' : a*f ≤ x*f := mul_le_mul_of_nonneg_right (min_le_left ..) hf
    nlinarith only [hp,mul_le_mul_of_nonneg_right hxa hy,mul_le_mul_of_nonneg_left hyb ha0,hf']
  have entry_loss {Y n m K} {η : ℝ} {c : colors Y n} {d : colors Y m}
      (hc : OneColorBounds K η c d) (hη : 0 ≤ η) (hn : 1 ≤ Real.log n)
      {i j : ℕ} (hi : i < K) (hj : j < K) :
      entry c (i+1) (j+1) ≤ entry d (i+1) (j+1) + 6*envelope K*η := by
    let L := Real.log (n:ℝ)
    let P := scale c.val.1 n
    let R := scale c.val.2 n
    let x := density c.val.1 n (i+1)
    let y := density c.val.2 n (j+1)
    let X := density d.val.1 m (i+1)
    let Z := density d.val.2 m (j+1)
    obtain ⟨a,b,ha,hb,he,hr,hs⟩ := hc
    have hP : 0 ≤ P := scale_nonneg ..
    have hR : 0 ≤ R := scale_nonneg ..
    have hL : 0 < L := lt_of_lt_of_le zero_lt_one hn
    have hE : 0 ≤ envelope K := by unfold envelope; positivity
    have hx : x ≤ envelope K * P := density_le_scale hL hi c.val.1
    have hy : y ≤ envelope K * R := density_le_scale hL hj c.val.2
    have hpr : L*P*R ≤ 3 := scale_product c.property.2 hn
    have hraw : x*y ≤ (a*X)*(b*Z) + (η*P)*y + x*(η*R) :=
      product_loss (density_nonneg ..) (density_nonneg ..)
        (mul_nonneg ha (density_nonneg ..)) (mul_nonneg hb (density_nonneg ..))
        (mul_nonneg hη hP) (mul_nonneg hη hR) (hr i hi) (hs j hj)
    have heq : L*a*b = Real.log (m:ℝ) := he
    have hmul : L*x*y ≤ Real.log (m:ℝ)*X*Z + 6*envelope K*η := calc
      _ ≤ L*((a*X)*(b*Z) + (η*P)*y + x*(η*R)) := by rw [mul_assoc]; gcongr
      _ ≤ L*((a*X)*(b*Z) + (η*P)*(envelope K*R) + (envelope K*P)*(η*R)) := by gcongr
      _ = (L*a*b)*X*Z + (2*envelope K*η)*(L*P*R) := by ring
      _ ≤ _ := by rw [heq]; nlinarith only [mul_le_mul_of_nonneg_left hpr (show 0 ≤ 2*envelope K*η by positivity)]
    rw [entry_density c (by omega) (by omega),entry_density d (by omega) (by omega)]
    let den : ℝ := ((i+1:ℕ):ℝ)*((j+1:ℕ):ℝ)
    have hden : 1 ≤ den := by dsimp [den]; exact_mod_cast (Nat.mul_pos (Nat.zero_lt_succ i) (Nat.zero_lt_succ j))
    change L*x*y/den ≤ Real.log (m:ℝ)*X*Z/den + _
    have denpos : 0 < den := lt_of_lt_of_le zero_lt_one hden
    rw [div_le_iff₀ denpos,add_mul,div_mul_cancel₀ _ denpos.ne']
    exact hmul.trans (add_le_add_right (le_mul_of_one_le_right (by positivity) hden) _)
  -- A failure at arbitrarily large old cutoffs supplies a bad increasing sequence.
  have matrix_of_analytic (h : AnalyticPrimeColorTransfer) :
      ∀ Y K, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ c : colors Y n,
        ∀ᶠ m : ℕ in atTop, ∃ d : colors Y m, ∀ i < K, ∀ j < K,
          entry c (i+1) (j+1) ≤ entry d (i+1) (j+1) + δ := by
    classical
    intro Y K δ hδ
    let η := δ/(6*envelope K+1)
    have hE : 0 ≤ envelope K := by unfold envelope; positivity
    have hη : 0 < η := by dsimp [η]; positivity
    have hcost : 6*envelope K*η ≤ δ := by
      have he : η*(6*envelope K+1)=δ := div_mul_cancel₀ _ (by positivity)
      nlinarith
    by_contra hbad
    have hfreq := (not_eventually.mp hbad).and_eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
    obtain ⟨N,hN,hfail⟩ := extraction_of_frequently_atTop hfreq
    have fail (k : ℕ) := (hfail k).1
    simp only [not_forall] at fail
    choose c hc using fail
    obtain ⟨k,hk⟩ := h Y K η hη N hN c
    apply hc k
    filter_upwards [hk] with m hm
    obtain ⟨d,hd⟩ := hm
    exact ⟨d,fun i hi j hj => (entry_loss hd hη.le (hfail k).2 hi hj).trans (add_le_add_right hcost _)⟩
  have harmonic_transfer_of_euler (analytic : EulerPrimeColorTransfer) : AnalyticPrimeColorTransfer := by
    obtain ⟨B,hB,bound⟩ := euler_le_trunc_uniform
    intro Y K η hη N hN c
    obtain ⟨k,hk,s,w,hw,d,hr,hb⟩ := analytic Y K (η/B) (div_pos hη hB) N hN c
    have hlog : 0 < Real.log (N k) := Real.log_pos (by exact_mod_cast (show 1 < N k by omega))
    have sub : (c k).val.1 ∪ (c k).val.2 ⊆ (N k).primesLE := by
      rw [(c k).property.1]
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
    have cost {C : Finset ℕ} (hC : C ⊆ (N k).primesLE) :
        η/B*eulerScale C (N k) ≤ η*scale C (N k) := by
      have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (bound _ hk C hC) hlog.le)
        (div_nonneg hη.le hB.le)
      apply h.trans
      change η/B*(B*mass (semigroup C (N k))/Real.log (N k)) ≤ η*(mass (semigroup C (N k))/Real.log (N k))
      field_simp
      rfl
    have hr' := (eventually_all_finset (range K)).mpr (fun i hi => hr i (mem_range.mp hi))
    have hb' := (eventually_all_finset (range K)).mpr (fun j hj => hb j (mem_range.mp hj))
    refine ⟨k,?_⟩
    filter_upwards [hr',hb'] with m hred hblue
    have ht : 0 ≤ Real.log (m:ℝ)/Real.log (N k) := div_nonneg (Real.log_natCast_nonneg _) hlog.le
    refine ⟨d m,(if s then w*(Real.log m/Real.log (N k)) else w⁻¹),
      (if s then w⁻¹ else w*(Real.log m/Real.log (N k))),by split <;> positivity,
      by split <;> positivity,by cases s <;> simp <;> field_simp,?_,?_⟩
    · exact fun i hi => (hred i (mem_range.mpr hi)).trans
        (add_le_add_right (cost (subset_union_left.trans sub)) _)
    · exact fun j hj => (hblue j (mem_range.mpr hj)).trans
        (add_le_add_right (cost (subset_union_right.trans sub)) _)
  exact matrix_of_analytic (harmonic_transfer_of_euler transfer)


theorem main : H1 → H2 → H3 → OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 := by
  intro prime shiftFromTheta recoveryFromTheta
  have shift := shiftFromTheta prime
  have recovery := recoveryFromTheta prime
  clear shiftFromTheta recoveryFromTheta prime
  apply transfer_of_matrix
  apply matrix_of_euler
  let colors (Y n : ℕ) := {t : Finset ℕ × Finset ℕ // t.1 ∪ t.2 = (Icc Y n).filter Nat.Prime ∧ Disjoint t.1 t.2}
  let semigroup (C : Finset ℕ) (n : ℕ) := (Icc 1 n).filter (· ∈ Nat.factoredNumbers C)
  let density (C : Finset ℕ) (n u : ℕ) : ℝ :=
    ((semigroup C (n/u)).card : ℝ)*u/n
  let pick {Y n} (c : colors Y n) (b : Bool) := if b then c.val.1 else c.val.2
  let side (Y : ℕ) (x : ℝ) (q : ℕ → Bool) (b : Bool) := ((Icc Y ⌊x⌋₊).filter Nat.Prime).filter (fun p => q p = b)
  let F (C : Finset ℕ) (w : ℝ) := exp (-w) * (((range (⌊exp w⌋₊ + 1)).filter (· ∈ Nat.factoredNumbers C)).card : ℝ)
  let euler (C : Finset ℕ) : ℝ := ∏ p ∈ C, (1 - (p:ℝ)⁻¹)⁻¹
  let eulerScale (C : Finset ℕ) (n : ℕ) := euler C / log n
  let Stable {Y} (N : ℕ → ℕ) (c : ∀ k, colors Y (N k)) (b : Bool) : Prop :=
    ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
      ∀ s : ℝ, |s| ≤ H →
        |F (pick (c k) b) (log (N k)+s) - F (pick (c k) b) (log (N k))|
          ≤ η*eulerScale (pick (c k) b) (N k)
  let Active (C : Finset ℕ) (h : ℕ) := h ∈ Nat.factoredNumbers C
  have mem_semigroup {C n h} : h ∈ semigroup C n ↔ Active C h ∧ h ≤ n := by
    simp only [Active, semigroup, mem_filter, mem_Icc]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun ⟨ha,hn⟩ => ⟨⟨Nat.pos_of_ne_zero ha.1,hn⟩,ha⟩⟩
  have pick_prime {Y n} (c : colors Y n) (b : Bool) : ∀ p ∈ pick c b, Nat.Prime p := by
    intro p hp
    have h : p ∈ c.val.1 ∪ c.val.2 := by
      cases b
      · exact mem_union_right _ hp
      · exact mem_union_left _ hp
    exact (mem_filter.mp (c.property.1 ▸ h)).2
  have shifted_density (C : Finset ℕ) {n u : ℕ} (hn : 0 < n) (hu : 0 < u) :
      F C (log n-log u) = density C n u := by
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hu' : (0:ℝ) < u := by exact_mod_cast hu
    have hex : exp (log n-log u) = (n:ℝ)/u := by rw [exp_sub,exp_log hn',exp_log hu']
    let countSet (C : Finset ℕ) (w : ℝ) := (range (⌊exp w⌋₊ + 1)).filter (· ∈ Nat.factoredNumbers C)
    have hset : countSet C (log n-log u) = semigroup C (n/u) := by
      ext x
      simp only [countSet,hex,mem_filter,mem_range,Nat.lt_succ_iff,mem_semigroup]
      rw [Nat.le_floor_iff (by positivity),le_div_iff₀ hu',Nat.le_div_iff_mul_le hu]
      constructor
      · intro h
        exact ⟨h.2,by exact_mod_cast h.1⟩
      · intro h
        exact ⟨by exact_mod_cast h.2,h.1⟩
    change exp (-(log n-log u)) * ((countSet C (log n-log u)).card : ℝ) = _
    rw [hset,exp_neg,hex]
    unfold density
    field_simp
  have stable_subsequence {Y}
      (N : ℕ → ℕ) (hN : StrictMono N) (c : ∀ k, colors Y (N k)) :
      ∃ σ : ℕ → ℕ, ∃ b : Bool, StrictMono σ ∧ Stable (N ∘ σ) (fun k => c (σ k)) b := by
    let q (k p : ℕ) := decide (p ∈ (c k).val.1)
    have hside (k b) : side Y (N k) (q k) b = pick (c k) b := by
      have he : (Icc Y ⌊(N k:ℝ)⌋₊).filter Nat.Prime = (c k).val.1 ∪ (c k).val.2 := by
        rw [(c k).property.1]; simp
      ext p
      have hd : p ∈ (c k).val.1 → p ∉ (c k).val.2 := fun hp => disjoint_left.mp (c k).property.2 hp
      cases b <;> simp only [side,he,mem_filter,mem_union,pick,q,decide_eq_false_iff_not,decide_eq_true_eq, Bool.false_eq_true,if_false,if_true] <;> tauto
    obtain ⟨σ,b,hm,hs⟩ := shift Y (fun k => (N k:ℝ))
      (tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop) q
    refine ⟨σ,b,hm,?_⟩
    intro H hH η hη
    filter_upwards [hs H hH η hη] with k hk
    let C := side Y (N (σ k)) (q (σ k)) b
    let w := log (N (σ k):ℝ)
    change ∀ s : ℝ, |s| ≤ H → |F C (w+s) - F C w| ≤ η * eulerScale C (N (σ k)) at hk
    dsimp only [C] at hk
    rw [hside] at hk
    exact hk
  have euler_pos := @euler_comparison.1
  intro Y K η hη N hm c
  obtain ⟨σ,b,hσ,stable⟩ := stable_subsequence N hm c
  let n := N ∘ σ
  let col (k : ℕ) := c (σ k)
  change Stable n col b at stable
  have half := half_pos hη
  have old := stable (log (K+1:ℕ)) (log_natCast_nonneg _) _ half
  have late := recovery Y K _ half n (hm.comp hσ) col b stable
  obtain ⟨k,⟨⟨hn,w,hw,d,hs,hr⟩,hold⟩⟩ := (late.and_eventually old).exists
  have hn0 : 0 < n k := by omega
  have hstable (j : ℕ) (hj : j < K) : ∀ᶠ m : ℕ in atTop,
      density (pick (col k) b) (n k) (j+1) ≤ w⁻¹*density (pick (d m) b) m (j+1)
        + η*eulerScale (pick (col k) b) (n k) := by
    have hjlog : abs (-log (j+1:ℕ)) ≤ log (K+1:ℕ) := by
      rw [abs_neg,abs_of_nonneg (log_natCast_nonneg _)]
      apply log_le_log (by positivity) (by exact_mod_cast (show j+1 ≤ K+1 by omega))
    have diff := (abs_le.mp (hold _ hjlog)).2
    rw [← sub_eq_add_neg,shifted_density _ hn0 (Nat.zero_lt_succ j)] at diff
    have hcenter := shifted_density (pick (col k) b) hn0 (by decide : 0 < 1)
    simp only [Nat.cast_one,log_one,sub_zero] at hcenter
    rw [hcenter] at diff
    filter_upwards [hr j hj] with m h
    change density (pick (col k) b) (n k) 1 ≤ w⁻¹ * density (pick (d m) b) m (j+1)
      + (η/2) * eulerScale (pick (col k) b) (n k) at h
    linarith only [diff,h]
  have hsp (i : ℕ) (hi : i < K) : ∀ᶠ m : ℕ in atTop,
      density (pick (col k) (!b)) (n k) (i+1) ≤
        (w*(log m/log (n k)))*density (pick (d m) (!b)) m (i+1) + η*eulerScale (pick (col k) (!b)) (n k) := by
    filter_upwards [hs i hi] with m hx
    apply hx.trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right (by linarith)
    exact div_nonneg (euler_pos (pick_prime (col k) (!b))).le (log_natCast_nonneg _)
  refine ⟨σ k,hn,!b,w,hw,d,?_⟩
  cases b
  · exact ⟨hsp, hstable⟩
  · exact ⟨hstable, hsp⟩

end
end OMA.R_Erdos490_erdos_490_variants_limit_R1_H2_R2

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

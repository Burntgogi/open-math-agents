import LabelSum
import LastLabel
import Envelope
import Mathlib.MeasureTheory.Function.Floor

open Filter MeasureTheory Real Set
open scoped Topology

namespace Erdos490PrimeCells

/-- The normalized count in the last label at residual log-scale `w`. -/
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

private theorem movingLabelKernel_joint (i : Label) (c : ℝ) {w : ℝ} (hw : w ∈ Ioo i.lo i.hi) :
    Tendsto (fun p : ℝ × ℝ => movingLabelKernel i c p.1 p.2)
      (atTop ×ˢ 𝓝 w) (𝓝 w⁻¹) := by
  apply tendsto_of_subseq_tendsto
  intro u hu
  have ht : Tendsto (fun n => (u n).1) atTop atTop := tendsto_fst.comp hu
  have hv : Tendsto (fun n => (u n).2) atTop (𝓝 w) := tendsto_snd.comp hu
  -- Along strictly increasing times the residual scales extend to a function of time.
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
  have h := (last_label_interior i.positive hw.1 hw.2 hz c).comp ht'
  refine h.congr fun n => ?_
  change T n * cappedCount (T n) i.lo i.hi (T n * z (T n) - c) /
      exp (T n * z (T n) - c) = movingLabelKernel i c (T n) (W n)
  rw [show z (T n) = W n from hT.extend_apply W _ n, movingLabelKernel_eq_div]

/-- The moving last-label kernel converges uniformly on every compact subset of the band interior. -/
theorem movingLabelKernel_uniform (i : Label) (c : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hKi : K ⊆ Ioo i.lo i.hi) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ w ∈ K, |movingLabelKernel i c t w - w⁻¹| < ε := by
  have hlocal : TendstoLocallyUniformlyOn (movingLabelKernel i c) (fun w => w⁻¹) atTop
      (Ioo i.lo i.hi) := by
    apply isOpen_Ioo.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
    intro w hw
    apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
    have hinv := (tendsto_snd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓝 w) (𝓝 w)).inv₀
      (i.positive.trans hw.1).ne'
    simpa only [dist_self] using hinv.dist (movingLabelKernel_joint i c hw)
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

private theorem interiorTest_eventually_le_kernel (i : Label) (x c : ℝ) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in atTop, ∀ y, interiorTest i x n y - δ ≤ movingLabelKernel i c t (x - y) := by
  let d := ((n : ℝ) + 1)⁻¹
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : 0 < d := inv_pos.mpr hn
  let K := Icc (i.lo + d) (i.hi - d)
  have hKi : K ⊆ Ioo i.lo i.hi := by
    intro w hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  filter_upwards [movingLabelKernel_uniform i c (K := K) isCompact_Icc hKi hδ,
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

/-- Weak convergence of the other labels transfers the compact-interior asymptotic
to an eventual lower bound for the integral of the actual capped prime count. -/
theorem movingLabel_integral_lower (i : Label) (L : List Label) (x c : ℝ)
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
  filter_upwards [hg, interiorTest_eventually_le_kernel i x c n (by positivity : 0 < ε / 3),
    uniform_last_label_bound i.positive i.hi, eventually_ge_atTop (0 : ℝ)] with t hgt hpt henv ht
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

#print axioms movingLabelKernel_uniform
#print axioms movingLabel_integral_lower

end Erdos490PrimeCells


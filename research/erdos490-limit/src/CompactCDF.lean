import SegmentMass
import SmoothTail
import Bounds

open Filter MeasureTheory Real Set
open scoped Interval Topology

namespace Erdos490Smooth

/-- Pointwise convergence to a continuous limit is uniform on a compact interval
when the approximating functions are eventually monotone in the interval variable. -/
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

/-- Comparing at a common kernel argument orders the limits by the available primes. -/
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

/-- Boundedness on finite intervals and the uniform tail estimate preserve the total
mass in the pointwise limit. -/
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

#print axioms eventually_uniform_Icc_of_monotone
#print axioms smooth_limit_antitone
#print axioms smooth_limit_mem_Icc
#print axioms smooth_limit_mass

end Erdos490Smooth

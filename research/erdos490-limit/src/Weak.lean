import Weighted

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

/-- Weak convergence of harmonic prime weights on one compact interval after
dilating its log coordinates, tested against an arbitrary continuous function. -/
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

#print axioms weighted_window
end Erdos490PrimeCells


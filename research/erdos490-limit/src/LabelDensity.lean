import MovingLabel
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Real Set
open scoped ENNReal

namespace Erdos490PrimeCells

/-- The open-band integral in `movingLabel_integral_lower`. -/
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
    -- This endpoint is removed under Lebesgue measure after the translation for fixed `y`.
    _ = ∫⁻ t in Ioc i.lo i.hi, ENNReal.ofReal t⁻¹ * φ (y + t) := by
      rw [Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]
    _ = _ := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul _ (measurable_id.inv.ennreal_ofReal)
        (hφ.comp (by fun_prop))

/-- Lebesgue density of the old label sum before division by the first label's log mass. -/
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

/-- Integrating the open-band density against a real test gives the unnormalized label-sum integral. -/
theorem integral_mul_labelDensity (i : Label) (L : List Label) (φ : ℝ → ℝ) :
    (∫ x, φ x * labelDensity i L x) =
      log (i.hi / i.lo) * (∫ x, φ x ∂(labelSum limitFactor (i :: L) : Measure ℝ)) := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    (labelDensity_measurable i L).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) φ
  rw [labelDensity_withDensity, integral_smul_measure,
    ENNReal.toReal_ofReal (log_nonneg ((one_le_div i.positive).2 i.nonempty.le))] at h
  simpa only [smul_eq_mul, ENNReal.toReal_ofReal (labelDensity_bounds i L _).1, mul_comm] using h.symm

/-- A nonnegative weight with integral less than one detects a point with density at least `m`.
The point may be chosen outside any finite exceptional set. -/
theorem exists_labelDensity_ge_of_weighted_integral (i : Label) (L : List Label)
    {s E : Set ℝ} (hs : MeasurableSet s) (hE : E.Finite) {w : ℝ → ℝ}
    (hw : IntegrableOn w s) (hw₀ : ∀ x ∈ s, 0 ≤ w x) {m : ℝ} (hm : 0 < m)
    (hmass : (∫ x in s, w x) < 1)
    (hlower : m ≤ ∫ x in s, w x * labelDensity i L x) :
    ∃ x ∈ s, x ∉ E ∧ m ≤ labelDensity i L x := by
  by_contra! h
  have hle : (∫ x in s, w x * labelDensity i L x) ≤ ∫ x in s, w x * m := by
    apply integral_mono_ae
    · exact hw.mul_bdd (labelDensity_measurable i L).aestronglyMeasurable
        (ae_of_all _ fun x => by
          obtain ⟨hn, hb⟩ := labelDensity_bounds i L x
          rwa [Real.norm_of_nonneg hn])
    · exact hw.mul_const m
    · filter_upwards [ae_restrict_mem hs,
        ae_restrict_of_ae (s := s) (hE.countable.ae_notMem (volume : Measure ℝ))] with x hx hxE
      exact mul_le_mul_of_nonneg_left (h x hx hxE).le (hw₀ x hx)
  rw [integral_mul_const] at hle
  exact (not_lt_of_ge (hlower.trans hle)) (by simpa using mul_lt_mul_of_pos_right hmass hm)

/-- Sampling with the exponential weight on a fixed finite interval. -/
theorem exists_labelDensity_ge_of_exp_integral (i : Label) (L : List Label)
    {A B : ℝ} (c : ℝ) {E : Set ℝ} (hE : E.Finite) {m : ℝ} (hm : 0 < m)
    (hmass : (∫ x in Ioc A B, exp (x - c)) < 1)
    (hlower : m ≤ ∫ x in Ioc A B, exp (x - c) * labelDensity i L x) :
    ∃ x ∈ Ioc A B, x ∉ E ∧ m ≤ labelDensity i L x :=
  exists_labelDensity_ge_of_weighted_integral i L measurableSet_Ioc hE
    ((by fun_prop : Continuous fun x : ℝ => exp (x - c)).intervalIntegrable A B).1
    (fun x _ => (exp_pos (x - c)).le) hm hmass hlower

#print axioms labelDensity_withDensity
#print axioms integral_mul_labelDensity
#print axioms exists_labelDensity_ge_of_exp_integral

end Erdos490PrimeCells

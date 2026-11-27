import CompactCDF
import KernelLimit

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos490PrimeCells

private theorem intervalIntegrable_of_integrableOn_Ioi_zero {K : ℝ → ℝ}
    (hK : IntegrableOn K (Ioi 0)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable K volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (hK.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi ha)))

/-- Each sample bounds the following unit interval from above and the preceding one
from below. In particular the last interval of the lower comparison is `(D+1,D+2]`. -/
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

/-- A finite strip sum loses at most the mass bound on the first two units
and an arbitrarily small tail. -/
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

/-- The mass in this strip contributes at displacements in `[j,j+1)`. -/
def blueStrip (x : ℝ) (j : ℕ) : Set ℝ := Ioc (x - j - 1) (x - j)

/-- The integral over disjoint strips is bounded below by the sum of their
individual mass lower bounds weighted by the right-end kernel samples. -/
theorem blueStrips_integral_lower {K : ℝ → ℝ} {V x m : ℝ} {D : ℕ}
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hmono : AntitoneOn K (Ioi 0))
    (hbound : ∀ z > 0, K z ∈ Icc 0 V)
    (hmass : ∀ j ∈ Finset.Icc 1 D, m ≤ ν.real (blueStrip x j)) :
    m * (∑ j ∈ Finset.Icc 1 D, K ((j : ℝ) + 1)) ≤
      ∫ y in ⋃ j ∈ Finset.Icc 1 D, blueStrip x j, K (x - y) ∂ν := by
  have hdisj : (↑(Finset.Icc 1 D) : Set ℕ).Pairwise
      (Function.onFun Disjoint (blueStrip x)) := by
    intro i _ j _ hij
    apply Set.disjoint_left.2
    intro y hyi hyj
    change x - (i : ℝ) - 1 < y ∧ y ≤ x - (i : ℝ) at hyi
    change x - (j : ℝ) - 1 < y ∧ y ≤ x - (j : ℝ) at hyj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
      linarith [hyi.1, hyj.2]
    · have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt hji
      linarith [hyj.1, hyi.2]
  have hpos {j : ℕ} (hj : j ∈ Finset.Icc 1 D) {y : ℝ} (hy : y ∈ blueStrip x j) :
      0 < x - y := by
    have hj_pos : 0 < (j : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have hyupper : y ≤ x - (j : ℝ) := hy.2
    linarith
  have hint : ∀ j ∈ Finset.Icc 1 D, IntegrableOn (fun y => K (x - y)) (blueStrip x j) ν := by
    intro j hj
    have hmonotone : MonotoneOn (fun y => K (x - y)) (blueStrip x j) := by
      intro y hy z hz hyz
      exact hmono (hpos hj hz) (hpos hj hy) (sub_le_sub_left hyz x)
    exact (integrable_const V).mono'
      (aemeasurable_restrict_of_monotoneOn measurableSet_Ioc hmonotone).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono fun y hy => by
        obtain ⟨hnonneg, hle⟩ := hbound (x - y) (hpos hj hy)
        simpa only [Real.norm_of_nonneg hnonneg] using hle)
  rw [integral_biUnion_finset _ (s := blueStrip x) (fun _ _ => measurableSet_Ioc) hdisj hint,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hsample_pos : 0 < (j : ℝ) + 1 := by positivity
  have hsample := (hbound _ hsample_pos).1
  calc
    m * K ((j : ℝ) + 1) ≤ ν.real (blueStrip x j) * K ((j : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right (hmass j hj) hsample
    _ = ∫ _ in blueStrip x j, K ((j : ℝ) + 1) ∂ν := by rw [setIntegral_const, smul_eq_mul]
    _ ≤ _ := setIntegral_mono_on (integrable_const _)
      (hint j hj) measurableSet_Ioc fun y hy => by
        have hy_lower : x - (j : ℝ) - 1 < y := hy.1
        exact hmono (hpos hj hy) hsample_pos (by linarith)

end Erdos490PrimeCells

namespace Erdos490Smooth

open Erdos490PrimeCells

/-- The same finite cutoff works for every location and every finite measure satisfying
the strip mass estimate. The smooth limit gives the kernel mass, and `V` is any
pointwise upper bound on the positive half-line. -/
theorem exists_smoothKernel_blueStrips_lower (k : ℕ) {w V η : ℝ} (hw : 0 < w)
    (hV : ∀ z > 0, smoothKernel k w hw z ≤ V) (hη : 0 < η) :
    ∃ D : ℕ, 1 ≤ D ∧
      ∀ (ν : Measure ℝ) [IsFiniteMeasure ν] (x m : ℝ), 0 ≤ m →
        (∀ j ∈ Finset.Icc 1 D, m ≤ ν.real (blueStrip x j)) →
        m * (Real.exp Real.eulerMascheroniConstant * smallProduct k * w - 2 * V - η) ≤
          ∫ y in ⋃ j ∈ Finset.Icc 1 D, blueStrip x j, smoothKernel k w hw (x - y) ∂ν := by
  have hlim : ∀ h > 0, Tendsto
      (fun t : ℝ => Shift490.F (smoothLabels k (Real.exp (t * w))) (t * h))
      atTop (𝓝 (smoothKernel k w hw h)) := fun _ hh => smoothKernel_tendsto k hw hh
  have hmono := smooth_limit_antitone k hw hlim
  have hbound (z : ℝ) (hz : 0 < z) : smoothKernel k w hw z ∈ Icc 0 V :=
    ⟨(smooth_limit_mem_Icc k hlim hz).1, hV z hz⟩
  obtain ⟨hint, hmass⟩ := smooth_limit_mass k hw hlim
  obtain ⟨D, hD, hlower, _⟩ := exists_strip_sum_bounds hmono hbound hint hη
  rw [hmass] at hlower
  refine ⟨D, hD, fun ν _ x m hm hstrips => ?_⟩
  exact (mul_le_mul_of_nonneg_left hlower hm).trans (blueStrips_integral_lower ν hmono hbound hstrips)

#print axioms strip_sum_integral_comparison
#print axioms exists_strip_sum_bounds
#print axioms blueStrips_integral_lower
#print axioms exists_smoothKernel_blueStrips_lower

end Erdos490Smooth

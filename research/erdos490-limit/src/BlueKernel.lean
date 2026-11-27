import KernelLimit
import CompactCDF

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

#print axioms smoothKernel_uniform
#print axioms smoothKernel_mass
#print axioms smoothKernel_antitone
end Erdos490Smooth


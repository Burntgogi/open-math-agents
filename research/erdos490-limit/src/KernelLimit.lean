import ArithmeticSimplex
import CDFLimit
import GradeSum
import UniformLimit

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

theorem kernelOn_continuous (k : ℕ) (i : Label) : Continuous (kernelOn k i) := by
  unfold kernelOn
  exact continuous_const.mul (continuous_finsetSum _ (fun j _ => continuous_const.mul (limitingGrade_continuous i j)))

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

#print axioms smoothKernel_tendsto
end Erdos490Smooth


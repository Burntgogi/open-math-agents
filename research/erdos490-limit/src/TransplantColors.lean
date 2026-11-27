import PrimeLabelMass
import SegmentMass

/-! The actual new prime partition for a frozen old coloring, with the
whole initial segment on the stable side. Endpoints agree with the
half-open conventions in the analytic modules. -/
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

/-- At every target integer and positive cofactor simultaneously the two
semigroups of prescribed supports embed in one complete site coloring.
The stable residual support is exactly the one used by the blue kernel. -/
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

/-- The initial segment eventually reaches the fixed template threshold. -/
theorem eventually_transplant_cutoff (Y y : ℕ) (b : ℝ) :
    ∀ᶠ t : ℝ in atTop, Y ≤ ⌊exp (t*boundary b (y+1))⌋₊+1 := by
  have lim := tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const (exp_pos (reciprocalBefore (y+1)-b)))
  filter_upwards [lim.eventually_ge_atTop (Y:ℝ)] with t ht
  exact (Nat.le_floor ht).trans (Nat.le_succ _)

#print axioms transplant_colors
end
end Erdos490Transfer

import KernelLimit
import CompactCDF

open Real Filter Finset Set
open scoped Topology
namespace Erdos490Smooth
open Shift490 Erdos490PrimeCells

theorem smallProduct_eq_local (k : ℕ) : smallProduct k = localProduct (Nat.primesLE k) := by
  unfold smallProduct localProduct
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_Ioc,Nat.mem_primesLE]
  constructor
  · exact fun h => ⟨h.1.2,h.2⟩
  · exact fun h => ⟨⟨h.2.pos,h.1⟩,h.2⟩

private theorem no_large_divisor {t w B h : ℝ} (ht : 0 < t) (hh : 0 < h) (hw : h ≤ w) :
    signedSum (primeBand t w B) (t*h) = 1 := by
  let L := primeBand t w B
  have he : L.powerset.filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊) = {∅} := by
    ext V
    simp only [Finset.mem_filter,Finset.mem_powerset,Finset.mem_singleton]
    constructor
    · rintro ⟨hV,hprod⟩
      by_contra hn
      obtain ⟨p,hp⟩ := Finset.nonempty_iff_ne_empty.mpr hn
      have hpos : 0 < ∏ l ∈ V,l := Finset.prod_pos fun l hl => (Finset.mem_filter.mp (hV hl)).2.pos
      have hp' := (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem id hp)).trans hprod
      have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hV hp)).1).1
      exact (not_lt_of_ge (hp'.trans (Nat.floor_mono (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw ht.le))))) hlow
    · rintro rfl
      simp [Nat.one_le_floor_iff,Real.one_le_exp_iff,(mul_pos ht hh).le]
  change ∑ U ∈ L.powerset.filter (fun V => (∏ p ∈ V,p) ≤ ⌊exp (t*h)⌋₊), _ = _
  simp [he]

theorem smoothKernel_initial (k : ℕ) {w h : ℝ} (hw : 0 < w) (hh : 0 < h) (hb : h ≤ w) :
    smoothKernel k w hw h = smallProduct k := by
  apply tendsto_nhds_unique (smoothKernel_tendsto k hw hh)
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [uniform_sieve_approx k hh hw le_rfl he,eventually_gt_atTop 0] with t ht ht0
  have H := ht h ⟨le_rfl,hb⟩
  rw [← primeBand_eq_smoothLabels,no_large_divisor ht0 hh hb,mul_one] at H
  rwa [Real.dist_eq,smallProduct_eq_local]

theorem smoothKernel_range (k : ℕ) {w h : ℝ} (hw : 0 < w) (hh : 0 < h) :
    smoothKernel k w hw h ∈ Icc 0 (smallProduct k) := by
  refine ⟨(smooth_limit_mem_Icc k (fun _ hx => smoothKernel_tendsto k hw hx) hh).1,?_⟩
  rcases le_total h w with hle|hge
  · exact (smoothKernel_initial k hw hh hle).le
  · rw [← smoothKernel_initial k hw hw le_rfl]
    exact (smooth_limit_antitone k hw (fun _ hx => smoothKernel_tendsto k hw hx)) hw hh hge

#print axioms smoothKernel_initial
#print axioms smoothKernel_range
end Erdos490Smooth

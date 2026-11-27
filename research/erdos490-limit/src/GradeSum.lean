import UniformError
import Weighted

open Finset Real

namespace Erdos490PrimeCells

theorem primeBand_eq_smoothLabels (t w B : ℝ) :
    primeBand t w B = Erdos490Smooth.smoothLabels ⌊exp (t * w)⌋₊ (exp (t * B)) :=
  rfl

end Erdos490PrimeCells

namespace Erdos490Smooth

open Erdos490PrimeCells

/-- The reciprocal mass of the subsets of size `j` whose product meets the cutoff. -/
noncomputable def gradeMass (L : Finset ℕ) (j : ℕ) (z : ℝ) : ℝ :=
  ∑ V ∈ (L.powersetCard j).filter (fun V => (∏ p ∈ V, p) ≤ ⌊exp z⌋₊),
    ∏ p ∈ V, (p : ℝ)⁻¹

theorem gradeMass_zero (L : Finset ℕ) {z : ℝ} (hz : 0 ≤ z) : gradeMass L 0 z = 1 := by
  have hcut : 1 ≤ ⌊exp z⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hz)
  simp [gradeMass, Finset.powersetCard_zero, Finset.filter_singleton, hcut]

private theorem card_le_floor_of_primeBand_product {t w B h : ℝ} (ht : 0 < t)
    (hw : 0 < w) (hwB : w ≤ B) (hhB : h ≤ B) {V : Finset ℕ}
    (hsub : V ⊆ primeBand t w B) (hprod : (∏ p ∈ V, p) ≤ ⌊exp (t * h)⌋₊) :
    V.card ≤ ⌊B / w⌋₊ := by
  have hprime (p : ℕ) (hp : p ∈ V) : p.Prime := (Finset.mem_filter.mp (hsub hp)).2
  have hpos (p : ℕ) (hp : p ∈ V) : 0 < (p : ℝ) := by
    exact_mod_cast (hprime p hp).pos
  have hlog (p : ℕ) (hp : p ∈ V) : t * w ≤ log (p : ℝ) := by
    have hpband := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hsub hp)).1).1
    have hexp : exp (t * w) < (p : ℝ) := (Nat.floor_lt' (hprime p hp).ne_zero).mp hpband
    simpa only [Real.log_exp] using (Real.log_lt_log (exp_pos _) hexp).le
  have hprod' : (∏ p ∈ V, (p : ℝ)) ≤ exp (t * h) := by
    rw [← Nat.cast_prod]
    exact (Nat.le_floor_iff (exp_pos _).le).mp hprod
  have hbound : (V.card : ℝ) * (t * w) ≤ t * B := calc
    _ = ∑ _p ∈ V, t * w := by simp
    _ ≤ ∑ p ∈ V, log (p : ℝ) := Finset.sum_le_sum hlog
    _ = log (∏ p ∈ V, (p : ℝ)) := (Real.log_prod fun p hp => (hpos p hp).ne').symm
    _ ≤ t * h := (Real.log_le_iff_le_exp (Finset.prod_pos hpos)).mpr hprod'
    _ ≤ t * B := mul_le_mul_of_nonneg_left hhB ht.le
  apply (Nat.le_floor_iff (div_nonneg (hw.le.trans hwB) hw.le)).mpr
  apply (le_div_iff₀ hw).mpr
  apply le_of_mul_le_mul_left _ ht
  simpa only [mul_left_comm, mul_assoc] using hbound

/-- Group the signed sum by subset size. The product cutoff bounds the grades uniformly in `t`. -/
theorem signedSum_eq_gradeSum {t w B h : ℝ} (ht : 0 < t) (hw : 0 < w) (hwB : w ≤ B)
    (_hh : 0 < h) (hhB : h ≤ B) :
    signedSum (primeBand t w B) (t * h) =
      ∑ j ∈ Finset.range (⌊B / w⌋₊ + 1), (-1 : ℝ) ^ j * gradeMass (primeBand t w B) j (t * h) := by
  classical
  let L := primeBand t w B
  let P (V : Finset ℕ) := (∏ p ∈ V, p) ≤ ⌊exp (t * h)⌋₊
  let S := L.powerset.filter P
  have hcard (V : Finset ℕ) (hV : V ∈ S) : V.card ∈ Finset.range (⌊B / w⌋₊ + 1) := by
    obtain ⟨hsub, hprod⟩ := Finset.mem_filter.mp hV
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (card_le_floor_of_primeBand_product ht hw hwB hhB (Finset.mem_powerset.mp hsub) hprod))
  have hfiber (j : ℕ) : S.filter (fun V => V.card = j) = (L.powersetCard j).filter P := by
    ext V
    simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    tauto
  change (∑ V ∈ S, (-1 : ℝ) ^ V.card / (∏ p ∈ V, p : ℕ)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hcard]
  apply Finset.sum_congr rfl
  intro j _
  rw [hfiber, gradeMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  have hVcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hV).1).2
  rw [hVcard, div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib]

#print axioms primeBand_eq_smoothLabels
#print axioms gradeMass_zero
#print axioms signedSum_eq_gradeSum

end Erdos490Smooth

import WordLaw
import PrimeCells

open Finset Filter Real MeasureTheory Set
open scoped Topology NNReal ENNReal
namespace Erdos490PrimeCells

noncomputable def cellLabel (b : ℝ) (p : ℕ) (hp : p.Prime) : Label where
  lo := boundary b p
  hi := boundary b (p+1)
  positive := exp_pos _
  nonempty := by
    rw [boundary_succ b hp]
    exact lt_mul_of_one_lt_right (exp_pos _) (one_lt_exp_iff.mpr (inv_pos.mpr (by exact_mod_cast hp.pos)))

theorem cell_log_mass (b : ℝ) (p : ℕ) (hp : p.Prime) :
    log ((cellLabel b p hp).hi/(cellLabel b p hp).lo) = (p:ℝ)⁻¹ := by
  change log (boundary b (p+1)/boundary b p) = _
  rw [boundary_succ b hp,mul_div_cancel_left₀ _ (show boundary b p ≠ 0 from (exp_pos _).ne'),log_exp]

theorem prime_mass_real (t a b : ℝ) :
    ((primeLaw t a b).mass:ℝ) = reciprocalInterval (exp (t*a)) (exp (t*b)) := by
  change ((∑ p ∈ primeBand t a b, ((p:ℝ≥0)⁻¹) • Measure.dirac (log p/t) : Measure ℝ).real univ) = _
  rw [Measure.real,Measure.finsetSum_apply,ENNReal.toReal_sum (fun p _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro p _
  rw [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul,measure_univ,mul_one,ENNReal.coe_toReal,NNReal.coe_inv,NNReal.coe_natCast]

theorem cell_primeMass_tendsto (b : ℝ) (p : ℕ) (hp : p.Prime) :
    let i := cellLabel b p hp
    Tendsto (fun t : ℝ => ((primeLaw t i.lo i.hi).mass:ℝ)) atTop (𝓝 (p:ℝ)⁻¹) := by
  let i := cellLabel b p hp
  have h := dilated_window_mass i.positive i.nonempty.le
  rw [cell_log_mass] at h
  simpa only [prime_mass_real] using h

/-- All new tuples from a good old support have their scaled log in the
same displacement interval, at every positive scale. -/
theorem tuple_displacement {ι : Type*} [Fintype ι] (b : ℝ) (p : ι → ℕ) (hp : ∀ j,(p j).Prime)
    {t : ℝ} (ht : 0 < t) (q : ι → ℕ)
    (hq : ∀ j, q j ∈ primeBand t (boundary b (p j)) (boundary b (p j+1)))
    (e : ι → ℝ) (he : ∀ j, ∀ v ∈ Icc (boundary b (p j)) (boundary b (p j+1)),
      |v-log (p j)| ≤ e j) :
    |log ((∏ j, q j : ℕ):ℝ)/t - log ((∏ j, p j : ℕ):ℝ)| ≤ ∑ j,e j := by
  have hq0 (j : ι) : (q j:ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_filter.mp (hq j)).2.ne_zero
  have hp0 (j : ι) : (p j:ℝ) ≠ 0 := by exact_mod_cast (hp j).ne_zero
  rw [Nat.cast_prod,Nat.cast_prod,log_prod (fun j _ => hq0 j),log_prod (fun j _ => hp0 j),
    Finset.sum_div,←Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => he j _ (band_point ht (hq j)))

#print axioms tuple_displacement
#print axioms cell_primeMass_tendsto
end Erdos490PrimeCells


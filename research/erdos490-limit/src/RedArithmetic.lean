import MovingLabel
import LabelDensity
import WordIntegral
import CellTuple

open Real Filter Finset Set MeasureTheory
open scoped Topology
namespace Erdos490PrimeCells

noncomputable def finalCount {n : ℕ} (i : Label) (L : Fin n → Label) (t x c : ℝ) : ℝ :=
  ∑ f : (j : Fin n) → primeBand t (L j).lo (L j).hi,
    cappedCount t i.lo i.hi (t*x-c-log ((∏ j,(f j : ℕ):ℕ):ℝ))

private theorem cancellation {n : ℕ} (t : ℝ) (ht : 0 < t) (x c : ℝ) (i : Label)
    (L : Fin n → Label) (f : (j : Fin n) → primeBand t (L j).lo (L j).hi) :
    (∏ j, ((f j : ℕ):ℝ)⁻¹) *
        movingLabelKernel i c t (x-∑ j, log (f j : ℕ)/t) =
      t*exp (-(t*x-c))*cappedCount t i.lo i.hi (t*x-c-log ((∏ j,(f j : ℕ):ℕ):ℝ)) := by
  have hp (j : Fin n) : (0:ℝ) < (f j : ℕ) := by exact_mod_cast (Finset.mem_filter.mp (f j).property).2.pos
  let D : ℝ := ∏ j, ((f j : ℕ):ℝ)
  have hD : 0 < D := Finset.prod_pos fun j _ => hp j
  have hex : t*(x-∑ j, log (f j : ℕ)/t)-c = t*x-c-log D := by
    rw [←Finset.sum_div]
    dsimp [D]
    rw [Real.log_prod (fun j _ => (hp j).ne')]
    field_simp
    ring
  rw [movingLabelKernel, hex, Finset.prod_inv_distrib, Nat.cast_prod]
  change D⁻¹ * (t * exp (-(t*x-c-log D)) * _) = t*exp (-(t*x-c))*_
  rw [neg_sub,sub_eq_add_neg (log D),exp_add,exp_log hD]
  field_simp
  rfl

theorem weighted_final_count {n : ℕ} (i : Label) (L : Fin n → Label) (x c : ℝ) :
    ∀ᶠ t : ℝ in atTop, t * exp (-(t*x-c)) * finalCount i L t x c =
      (∏ j,((primeLaw t (L j).lo (L j).hi).mass : ℝ)) *
        ∫ y, movingLabelKernel i c t (x-y) ∂(labelSum (primeFactor t) (List.ofFn L) : Measure ℝ) := by
  filter_upwards [uniform_last_label_bound i.positive i.hi,eventually_gt_atTop 0] with t he ht
  let g := fun y => movingLabelKernel i c t (x-y)
  have hg : Measurable g := (movingLabelKernel_measurable i c t).comp (by fun_prop)
  have hbound (y : ℝ) : ‖g y‖ ≤ 2/i.lo := by
    rw [Real.norm_of_nonneg (movingLabelKernel_nonneg i c ht.le _),movingLabelKernel_eq_div]
    exact he _
  rw [← sum_tuple_test t L g hg hbound,finalCount,Finset.mul_sum]
  apply sum_congr rfl
  intro f _
  exact (cancellation t ht x c i L f).symm

theorem final_count_lower {n : ℕ} (i : Label) (L : Fin n → Label) (x c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      (∏ j,log ((L j).hi/(L j).lo)) * labelDensity i (List.ofFn L) x - ε ≤
        t*exp (-(t*x-c))* finalCount i L t x c := by
  let A := ∏ j,log ((L j).hi/(L j).lo)
  let M (t : ℝ) := ∏ j,((primeLaw t (L j).lo (L j).hi).mass:ℝ)
  let d := labelDensity i (List.ofFn L) x
  have hA : 0 ≤ A := Finset.prod_nonneg fun j _ => log_nonneg ((one_le_div (L j).positive).mpr (L j).nonempty.le)
  let δ := ε/(2*(A+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have limit : Tendsto M atTop (𝓝 A) := by
    apply tendsto_finsetProd
    intro j _
    simp_rw [prime_mass_real]
    exact dilated_window_mass (L j).positive (L j).nonempty.le
  have hcoef : A*d-ε < A*(d-δ) := by
    have : (2*(A+1))*δ = ε := by dsimp [δ]; field_simp
    nlinarith [mul_nonneg hA hδ.le]
  have hsmall := (limit.mul_const (d-δ)).eventually_const_lt hcoef
  filter_upwards [weighted_final_count i L x c,movingLabel_integral_lower i (List.ofFn L) x c hδ,hsmall]
    with t he hminor hupper
  rw [he]
  exact hupper.le.trans (mul_le_mul_of_nonneg_left hminor (show 0 ≤ M t by dsimp [M]; positivity))

#print axioms final_count_lower
end Erdos490PrimeCells



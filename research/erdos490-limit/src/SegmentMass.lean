import SmoothMass
import PrimeNumberTheoremAnd.IEANTN.Mertens

open Filter Finset Real MeasureTheory Set Asymptotics
open scoped Topology
namespace Erdos490Smooth
open Shift490

noncomputable def smoothLabels (k : ℕ) (x : ℝ) := (Finset.Ioc k ⌊x⌋₊).filter Nat.Prime
noncomputable def smallProduct (k : ℕ) :=
  ∏ p ∈ (Finset.Ioc 0 k).filter Nat.Prime, (1 - (p:ℝ)⁻¹)

private theorem smallProduct_pos (k : ℕ) : 0 < smallProduct k := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt
  exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hp1)

theorem segment_product {k : ℕ} {x : ℝ} (hk : k ≤ ⌊x⌋₊) :
    P (smoothLabels k x) = smallProduct k / smallProduct ⌊x⌋₊ := by
  have h := prod_Ioc_consecutive (fun p : ℕ => if p.Prime then 1-(p:ℝ)⁻¹ else 1)
    (Nat.zero_le k) hk
  unfold P smoothLabels
  rw [Finset.filter_filter]
  simp only [and_self,Finset.prod_inv_distrib]
  have h1 : smallProduct k *
      (∏ p ∈ (Finset.Ioc k ⌊x⌋₊).filter Nat.Prime, (1-(p:ℝ)⁻¹)) = smallProduct ⌊x⌋₊ := by
    simpa only [smallProduct,Finset.prod_filter] using h
  rw [← h1]
  field_simp [(smallProduct_pos k).ne']

theorem smoothLabels_mass_limit (k : ℕ) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun t : ℝ => P (smoothLabels k (exp (t*w)))/t) atTop
      (𝓝 (exp eulerMascheroniConstant * smallProduct k * w)) := by
  have hlin := tendsto_id.atTop_mul_const hw
  have hxp : Tendsto (fun t : ℝ => exp (t*w)) atTop atTop := tendsto_exp_atTop.comp hlin
  have hE := ((isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp hxp
  have hlim := (tendsto_const_nhds (x := exp eulerMascheroniConstant * smallProduct k * w)
    (f := atTop)).mul hE.neg.rexp
  simp only [neg_zero,exp_zero,mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0,hxp.eventually_ge_atTop (k:ℝ),hxp.eventually_gt_atTop 1]
    with t ht hk hx
  rw [segment_product (Nat.le_floor hk)]
  have h := Mertens.prod_one_minus_div_prime_eq hx
  simp only [one_div,log_exp] at h
  change smallProduct ⌊exp (t*w)⌋₊ = _ at h
  dsimp only [Function.comp_apply]
  rw [h,exp_neg,exp_neg]
  field_simp

#print axioms smoothLabels_mass_limit
end Erdos490Smooth


import SegmentMass
import Bounds

open Finset Real Filter Asymptotics
open scoped Topology
namespace Erdos490Smooth
open Shift490

theorem supported_subsets_bound {L : Finset ℕ} (hL : ∀ p ∈ L, Nat.Prime p) {z : ℝ}
    (hz : 0 < z) :
    exp (-z) * ((L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ ⌊exp z⌋₊)).card : ℝ) ≤
      K₀ * P L / z := by
  have hc : (L.powerset.filter (fun U => (∏ p ∈ U,p) ≤ ⌊exp z⌋₊)).card ≤ (countSet L z).card := by
    apply Finset.card_le_card_of_injOn (fun U : Finset ℕ => ∏ p ∈ U,p)
    · intro U hU
      have h := Finset.mem_filter.mp hU
      have hsub := Finset.mem_powerset.mp h.1
      have hp : ∀ p ∈ U, p.Prime := fun p h => hL p (hsub h)
      have pos : 0 < ∏ p ∈ U,p := Finset.prod_pos fun p h => (hp p h).pos
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h.2),Nat.mem_factoredNumbers_iff_primeFactors_subset.mpr ⟨pos.ne',?_⟩⟩
      rwa [Nat.primeFactors_prod hp]
    · intro U hU V hV he
      have hsU := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      have hsV := Finset.mem_powerset.mp (Finset.mem_filter.mp hV).1
      have h := congrArg Nat.primeFactors he
      simpa only [Nat.primeFactors_prod (fun p h => hL p (hsU h)),
        Nat.primeFactors_prod (fun p h => hL p (hsV h))] using h
  apply le_trans (b := exp (-z) * ((countSet L z).card : ℝ)) (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (exp_pos _).le)
  rw [← F_eq_card]
  exact counting_bound L z hz

/-- Euler mass of all prime labels in a macroscopic log band. -/
theorem rough_mass_limit {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun t : ℝ => P (smoothLabels ⌊exp (t*a)⌋₊ (exp (t*b)))) atTop (𝓝 (b/a)) := by
  have hb := ha.trans_le hab
  have hlim (r : ℝ) (hr : 0 < r) :
      Tendsto (fun t : ℝ => Mertens.E₃ (exp (t*r))) atTop (𝓝 0) :=
    ((isLittleO_one_iff ℝ).mp Mertens.E₃.bound').comp
      (tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hr))
  have h := (tendsto_const_nhds (x := b/a) (f := atTop)).mul ((hlim a ha).sub (hlim b hb)).rexp
  simp only [sub_zero, exp_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [segment_product (Nat.floor_mono (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab ht.le)))]
  have he (r : ℝ) (hr : 0 < r) : smallProduct ⌊exp (t*r)⌋₊ =
      exp (-eulerMascheroniConstant)*exp (Mertens.E₃ (exp (t*r))) / (t*r) := by
    simpa only [smallProduct,one_div,log_exp] using
      (Mertens.prod_one_minus_div_prime_eq (one_lt_exp_iff.mpr (mul_pos ht hr)))
  rw [he a ha, he b hb, exp_sub]
  field_simp

end Erdos490Smooth

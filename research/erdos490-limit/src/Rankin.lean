import Arithmetic
import PrimeNumberTheoremAnd.IEANTN.Mertens

open Real Finset Filter
open scoped Topology
namespace Erdos490Smooth
open Shift490

noncomputable def tilted (σ : ℝ) : ℕ →* ℝ where
  toFun n := (n:ℝ)⁻¹ * exp (σ * log n)
  map_one' := by simp
  map_mul' a b := by
    rcases eq_or_ne a 0 with rfl|ha
    · simp
    rcases eq_or_ne b 0 with rfl|hb
    · simp
    rw [Nat.cast_mul,log_mul (by exact_mod_cast ha) (by exact_mod_cast hb),mul_add,exp_add,mul_inv_rev]
    ring

theorem tilted_prime_eq (σ : ℝ) {p : ℕ} (hp : p.Prime) :
    tilted σ p = exp ((σ-1)*log p) := by
  change (p:ℝ)⁻¹ * exp (σ * log p) = _
  rw [sub_mul,one_mul,exp_sub,exp_log (by exact_mod_cast hp.pos)]
  ring

theorem tilted_sum (S : Finset ℕ) {σ : ℝ} (hσ : σ < 1) :
    HasSum (fun n : Integers S => tilted σ n)
      (∏ p ∈ S.filter Nat.Prime,(1 - tilted σ p)⁻¹) := by
  apply (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := tilted σ) ?_ S).2
  intro p hp
  rw [tilted_prime_eq σ hp,Real.norm_eq_abs,abs_of_pos (exp_pos _),exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (sub_neg.mpr hσ) (log_pos (by exact_mod_cast hp.one_lt))

private theorem local_tilt_bound {p : ℕ} (hp : p.Prime) {σ : ℝ} (hσ : 0 ≤ σ)
    (hsmall : σ*log p ≤ 1/4) :
    (1-tilted σ p)⁻¹ ≤ (1-(p:ℝ)⁻¹)⁻¹ * exp (8*σ*(log p / p)) := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  have hp2 : 2 ≤ (p:ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p:ℝ) := by linarith
  have hl := log_pos hp1
  have hu := mul_nonneg hσ hl.le
  have hex := abs_exp_sub_one_le (x := σ*log p) (by rw [abs_of_nonneg hu]; linarith)
  rw [abs_of_nonneg hu, abs_of_nonneg (sub_nonneg.mpr (one_le_exp hu))] at hex
  have hq : tilted σ p = exp (σ*log p)/p := by unfold tilted; simp [mul_comm,div_eq_mul_inv]
  have hq' : tilted σ p ≤ 3/4 := by
    rw [hq,div_le_iff₀ hp0]
    linarith
  have hq0 : 0 < 1-tilted σ p := by linarith
  have hpden : 0 < 1-(p:ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ hp0).mpr hp1)
  have hf : (1-(p:ℝ)⁻¹) / (1-tilted σ p) ≤ 1 + 8*σ*(log p/p) := by
    rw [div_le_iff₀ hq0]
    have hu' : 0 ≤ 8*σ*(log p/p) := by positivity
    have ht := mul_le_mul_of_nonneg_right hq' hu'
    have hd : tilted σ p - (p:ℝ)⁻¹ ≤ 2*σ*(log p/p) := by
      rw [hq,← one_div,← sub_div]
      rw [div_le_iff₀ hp0]
      field_simp at *
      linarith
    linarith
  have hmain := hf.trans (by linarith [Real.add_one_le_exp (8*σ*(log p/p))] :
    1 + 8*σ*(log p/p) ≤ exp (8*σ*(log p/p)))
  rw [← div_eq_inv_mul] at *
  exact (le_div_iff₀ hpden).mpr (by simpa [div_eq_mul_inv,mul_comm] using hmain)

theorem tilted_product_bound {X σ : ℝ} {S : Finset ℕ} (hX : 1 ≤ X)
    (hS : ∀ p ∈ S, (p:ℝ) ≤ X) (hσ : 0 ≤ σ) (hsmall : σ * log X ≤ 1/4) :
    (∏ p ∈ S.filter Nat.Prime, (1-tilted σ p)⁻¹) ≤
    P S * exp (8*σ*(log X + log 4 + 4)) := by
  have hloc {p} (hp : p ∈ S.filter Nat.Prime) := local_tilt_bound (Finset.mem_filter.mp hp).2 hσ
    (le_trans (mul_le_mul_of_nonneg_left (log_le_log (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos)
      (hS p (Finset.mem_filter.mp hp).1)) hσ) hsmall)
  have hsum : ∑ p ∈ S.filter Nat.Prime, log (p:ℝ)/p ≤ log X + log 4 + 4 := by
    have hM := (abs_le.mp (Mertens.sum_log_prime_div_eq_log hX)).2
    refine le_trans (b := ∑ p ∈ (Finset.Ioc 0 ⌊X⌋₊).filter Nat.Prime, log (p:ℝ)/p) ?_ (by linarith only [hM])
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp'.2.pos,Nat.le_floor (hS p hp'.1)⟩,hp'.2⟩
    · intro p hp _
      exact div_nonneg (log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∏ p ∈ S.filter Nat.Prime, ((1-(p:ℝ)⁻¹)⁻¹ * exp (8*σ*(log p/p))) := by
      apply Finset.prod_le_prod _ (fun p hp => hloc hp)
      intro p hp
      apply inv_nonneg.mpr
      have hx := hloc hp
      have h0 : 0 < 1-tilted σ p := by
        have hσ' : σ < 1 := by
          have hl := log_le_log (by norm_num : (0:ℝ)<2) (show 2 ≤ (p:ℝ) by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le)
          have ht := log_two_gt_d9
          by_contra! h
          have hge : log X ≤ σ*log X := le_mul_of_one_le_left (log_nonneg hX) h
          linarith [log_le_log (by exact_mod_cast (Finset.mem_filter.mp hp).2.pos) (hS p (Finset.mem_filter.mp hp).1)]
        rw [tilted_prime_eq σ (Finset.mem_filter.mp hp).2]
        exact sub_pos.mpr (exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hσ')
          (log_pos (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt))))
      exact h0.le
    _ = P S * exp (8*σ*(∑ p ∈ S.filter Nat.Prime, log (p:ℝ)/p)) := by
      rw [Finset.prod_mul_distrib,Finset.mul_sum,Real.exp_sum]
      rfl
    _ ≤ _ := by gcongr; exact (P_pos S).le

end Erdos490Smooth

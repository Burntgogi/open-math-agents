import SmoothLaw
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section

private theorem numeric_l1 {p k n : ℝ} (hk : 0 < k) (hn : 0 ≤ n)
    (hp' : p ≤ 2*k^2) (hn' : n ≤ k) :
    Real.sqrt (p*n*(2/(10^24*k))) + k/200000000 ≤ k/100000000 := by
  have h : p*n ≤ (2*k^2)*k := mul_le_mul hp' hn' hn (by positivity)
  have hs : Real.sqrt (p*n*(2/(10^24*k))) ≤ k/200000000 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg k, mul_pos (sq_pos_of_pos hk) hk]
  linarith

private theorem numeric_tail {k : ℝ} {n : ℕ} (hk : 0 < k) (hn : 0 < n) (hn' : (n:ℝ) ≤ k) :
    l1Tail n (k/200000000) ≤ Real.exp (-k/320000000000000000) := by
  unfold l1Tail
  rw [Real.exp_le_exp, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hn' hk.le]

/-- The manuscript's constants with explicit finite failure rates. Here p can be the
cardinality of any finite additive abelian group. Its only size inputs are k² ≤ p ≤ 2k². -/
theorem paper_equation_four {G ι : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (I : Finset ι) (μ : ι → G → ℝ) {k a b : ℕ}
    (hk : 2 ≤ k) (hab : a+b=k) (ha : 0 < a) (hb : 0 < b) (hhalf : 2*a ≤ k)
    (hlo : k^2 ≤ Fintype.card G) (hhi : Fintype.card G ≤ 2*k^2)
    (hn : ∀ i ∈ I, ∀ x, 0 ≤ μ i x) (hm : ∀ i ∈ I, ∑ x, μ i x = 1)
    (hc : ∀ i ∈ I, ∀ x, μ i x ≤ 2/(10^24*(k:ℝ))) :
    splitProb Finset.univ a b (fun A B ↦ ∃ i ∈ I,
      (k:ℝ)/100000000 < l1 (μ i) b B ∨ ∃ v, (1:ℝ)/1000 <
        ∑ z ∈ B, excess (μ i) A ((51:ℝ)/(100*k)) v z) ≤
      (I.card:ℝ)*(2*Real.exp (-(k:ℝ)/320000000000000000) +
        (Fintype.card G:ℝ)*Real.exp (10^24 - (10^24/2)*Real.sqrt k) +
        (Fintype.card G:ℝ)*Real.exp (-(9:ℝ)/10000*Real.sqrt k)) := by
  let p := Fintype.card G
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k:ℝ) := by linarith
  have ha' : (a:ℝ) ≤ k := by exact_mod_cast (show a ≤ k by omega)
  have hb' : (b:ℝ) ≤ k := by exact_mod_cast (show b ≤ k by omega)
  have hhalf' : 2*(a:ℝ) ≤ k := by exact_mod_cast hhalf
  have hlo' : (k:ℝ)^2 ≤ p := by exact_mod_cast hlo
  have hhi' : (p:ℝ) ≤ 2*(k:ℝ)^2 := by exact_mod_cast hhi
  have hp0 : 0 < (p:ℝ) := by nlinarith
  have hkp : a+b ≤ Fintype.card G := by rw [hab]; exact (Nat.le_self_pow (by decide) k).trans hlo
  have hs := Real.sq_sqrt hk0.le
  have hs0 := Real.sqrt_pos.mpr hk0
  have hc' : (a:ℝ)/p ≤ 51/(100*k) := by
    rw [div_le_div_iff₀ hp0 (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hhalf' hk0.le]
  have hE := equation_four I μ (m := 2/(10^24*(k:ℝ))) (by positivity) hn hm hc hkp
    (t := (Real.sqrt k)⁻¹) (T := 1/1000) hc' (inv_pos.mpr hs0)
    (by positivity : 0 ≤ (k:ℝ)/200000000) (by positivity : 0 ≤ (k:ℝ)/200000000)
    (numeric_l1 hk0 (Nat.cast_nonneg a) hhi' ha')
    (numeric_l1 hk0 (Nat.cast_nonneg b) hhi' hb')
  apply hE.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hden : a ≤ p := by change a ≤ Fintype.card G; omega
  have hden' : (0:ℝ) < p-a := by nlinarith
  have hexp : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_d9]
  have he0 : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hmean : ((a:ℝ)/p)*k ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one₀ hp0]
    nlinarith [mul_le_mul_of_nonneg_right ha' hk0.le]
  have hcoord : ((Real.exp 1-1)*((a:ℝ)/p) - (Real.sqrt k)⁻¹)/(2/(10^24*k)) ≤
      10^24 - (10^24/2)*Real.sqrt k := by
    have hprod := mul_le_mul hexp hmean (by positivity : 0 ≤ ((a:ℝ)/p)*k) (by norm_num : (0:ℝ) ≤ 2)
    have hroot : (Real.sqrt k)⁻¹ * k = Real.sqrt k := by
      field_simp
      nlinarith only [hs]
    rw [div_div_eq_mul_div, div_le_iff₀ (by norm_num)]
    nlinarith [hroot]
  have hmean' : (b:ℝ)/(p-a)*((k:ℝ)/100000000) ≤ 2/100000000 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden']
    nlinarith [mul_le_mul_of_nonneg_right hb' hk0.le]
  have hexc : ((Real.exp 1-1)*((b:ℝ)/(p-a : ℕ)*((k:ℝ)/100000000))-1/1000)/(Real.sqrt k)⁻¹ ≤
      -(9:ℝ)/10000*Real.sqrt k := by
    rw [Nat.cast_sub hden, div_inv_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hs0.le
    have hprod := mul_le_mul hexp hmean' (by positivity : 0 ≤ (b:ℝ)/(p-a)*((k:ℝ)/100000000))
      (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have h1 := numeric_tail hk0 ha ha'
  have h2 := numeric_tail hk0 hb hb'
  have h3 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcoord) (Nat.cast_nonneg p (α := ℝ))
  have h4 := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexc) (Nat.cast_nonneg p (α := ℝ))
  change _ ≤ 2*_ + (p:ℝ)*_ + (p:ℝ)*_
  dsimp only [p] at *
  linarith only [h1,h2,h3,h4]

end
end Green39.Smooth

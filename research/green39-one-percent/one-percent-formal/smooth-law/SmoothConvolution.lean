import SliceMoments
import Mathlib.Data.ZMod.Basic

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def conv (μ : G → ℝ) (A : Finset G) (z : G) := ∑ a ∈ A, μ (z-a)

def l1 (μ : G → ℝ) (k : ℕ) (A : Finset G) :=
  ∑ z : G, |conv μ A z - k/(Fintype.card G : ℝ)|

theorem conv_variance (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {k : ℕ} (hk : k ≤ Fintype.card G) (z : G) :
    sliceMean Finset.univ k (fun A ↦ (conv μ A z - k/(Fintype.card G : ℝ))^2) ≤
      (k/(Fintype.card G : ℝ)) * ∑ x, μ x ^ 2 := by
  have h := sm_variance (s := Finset.univ) (by simpa using hk) (fun a ↦ μ (z-a))
    (fun a _ ↦ hn _)
  have h1 : ∑ a, μ (z-a) = 1 := ((Equiv.subLeft z).sum_comp μ).trans hm
  have h2 : ∑ a, μ (z-a)^2 = ∑ x, μ x^2 := (Equiv.subLeft z).sum_comp (fun a ↦ μ a^2)
  simpa only [conv, Finset.card_univ, h1, h2, mul_one] using h

/-- Expected counting-measure ℓ¹ error of the actual convolution under the uniform slice. -/
theorem sm_l1 (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {k : ℕ} (hk : k ≤ Fintype.card G) :
    sliceMean Finset.univ k (l1 μ k) ≤ Real.sqrt ((Fintype.card G : ℝ)*k*∑ x, μ x^2) := by
  let p : ℝ := Fintype.card G
  have hp : 0 < p := by dsimp [p]; exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  let v : ℝ := k/p * ∑ x, μ x^2
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hz (z : G) : sliceMean Finset.univ k (fun A ↦ |conv μ A z - k/p|) ≤ Real.sqrt v := by
    apply Real.le_sqrt_of_sq_le
    calc
      _ ≤ sliceMean Finset.univ k (fun A ↦ |conv μ A z - k/p|^2) := sum_div_card_sq_le_sum_sq_div_card
      _ ≤ v := by simpa only [sq_abs] using conv_variance μ hn hm hk z
  change sliceMean Finset.univ k (fun A ↦ ∑ z : G, |conv μ A z - k/p|) ≤ _
  rw [sm_sum]
  calc
    _ ≤ ∑ _z : G, Real.sqrt v := Finset.sum_le_sum (fun z _ ↦ hz z)
    _ = p * Real.sqrt v := by simp [p,nsmul_eq_mul]
    _ ≤ _ := by
      apply Real.le_sqrt_of_sq_le
      rw [mul_pow, Real.sq_sqrt hv]
      change p^2 * ((k:ℝ)/p * _) ≤ p * k * _
      exact le_of_eq (by field_simp)

omit [DecidableEq G] in
theorem conv_mass (μ : G → ℝ) (hm : ∑ x, μ x = 1) (A : Finset G) :
    ∑ z, conv μ A z = A.card := by
  unfold conv
  rw [Finset.sum_comm]
  have h (a : G) : ∑ z, μ (z-a) = 1 := ((Equiv.subRight a).sum_comp μ).trans hm
  simp_rw [h]
  simp

theorem l1_exchange (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    (s : Finset G) (k : ℕ) : ExchangeLipschitz s k (l1 μ k) 2 := by
  intro A hA B hB hd
  let c := (k : ℝ)/Fintype.card G
  have hBA : (B \ A).card ≤ 1 := by
    rw [Finset.card_sdiff_comm ((Finset.mem_powersetCard.mp hB).2.trans (Finset.mem_powersetCard.mp hA).2.symm)]
    exact hd
  have hdiff (z : G) : conv μ A z - conv μ B z = conv μ (A \ B) z - conv μ (B \ A) z := by
    have h₁ := Finset.sum_inter_add_sum_sdiff A B (fun a ↦ μ (z-a))
    have h₂ := Finset.sum_inter_add_sum_sdiff B A (fun a ↦ μ (z-a))
    rw [Finset.inter_comm B A] at h₂
    unfold conv
    linarith
  change abs ((∑ z : G, |conv μ A z - c|) - ∑ z : G, |conv μ B z - c|) ≤ 2
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ z : G, abs (|conv μ A z - c| - |conv μ B z - c|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z : G, (conv μ (A \ B) z + conv μ (B \ A) z) := by
      apply Finset.sum_le_sum
      intro z _
      apply (abs_abs_sub_abs_le_abs_sub _ _).trans
      rw [sub_sub_sub_cancel_right, hdiff]
      have hnon (D : Finset G) : 0 ≤ conv μ D z := Finset.sum_nonneg (fun _ _ ↦ hn _)
      exact abs_le.mpr ⟨by linarith [hnon (A \ B)], by linarith [hnon (B \ A)]⟩
    _ ≤ 2 := by
      rw [Finset.sum_add_distrib, conv_mass μ hm, conv_mass μ hm]
      exact_mod_cast (show (A \ B).card + (B \ A).card ≤ 2 by omega)

omit [AddCommGroup G] [DecidableEq G] in
theorem law_sum_sq_le_cap (μ : G → ℝ) (hn : ∀ x, 0 ≤ μ x) (hm : ∑ x, μ x = 1)
    {b : ℝ} (hb : ∀ x, μ x ≤ b) : ∑ x, μ x^2 ≤ b := by
  calc
    _ ≤ ∑ x, b * μ x := Finset.sum_le_sum (fun x _ ↦ by rw [sq]; exact mul_le_mul_of_nonneg_right (hb x) (hn x))
    _ = _ := by rw [← Finset.mul_sum, hm, mul_one]

end
end Green39.Smooth

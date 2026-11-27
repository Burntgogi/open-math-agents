import SmoothSieve

open Finset
namespace Erdos490Smooth

noncomputable def localProduct (S : Finset ℕ) : ℝ := ∏ p ∈ S, (1 - (p:ℝ)⁻¹)

theorem localProduct_expand (S : Finset ℕ) : localProduct S =
    ∑ T ∈ S.powerset, (-1:ℝ)^T.card / (∏ p ∈ T, p : ℕ) := by
  unfold localProduct
  calc
    _ = ∏ p ∈ S, ((-1:ℝ)*(p:ℝ)⁻¹ + 1) := by
      apply Finset.prod_congr rfl
      intro p _
      ring
    _ = _ := by
      rw [Finset.prod_add_one]
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.prod_inv_distrib,Nat.cast_prod,div_eq_mul_inv]

private theorem div_error (n : ℕ) {d : ℕ} (hd : 0 < d) :
    |((n/d:ℕ):ℝ) - (n:ℝ)/d| ≤ 1 := by
  have h : ((n%d:ℕ):ℝ) + (d:ℝ)*(n/d:ℕ) = n := by exact_mod_cast Nat.mod_add_div n d
  have hl : ((n%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt n hd
  have hp : 0 < (d:ℝ) := by exact_mod_cast hd
  rw [abs_le]
  constructor
  · apply (le_sub_iff_add_le).mpr
    rw [← le_sub_iff_add_le', div_le_iff₀ hp]
    nlinarith
  · apply (sub_le_iff_le_add).mpr
    rw [add_comm,← sub_le_iff_le_add,le_div_iff₀ hp]
    nlinarith [Nat.cast_nonneg (n%d) (α := ℝ)]

theorem cofactor_rounding (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (n : ℕ) {d : ℕ} (hd : 0 < d) :
    |smallCount S (n/d) - ((n:ℝ)/d)*localProduct S| ≤ 2 ^ S.card := by
  classical
  rw [smallCount_formula S hS,localProduct_expand,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _T ∈ S.powerset, (1:ℝ) := by
      refine Finset.sum_le_sum fun T hT => ?_
      let m := ∏ p ∈ T,p
      have hm : 0 < m := Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
      have hd' : 0 < (d:ℝ) := by exact_mod_cast hd
      have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
      change |(-1:ℝ)^T.card * ((n/d/m:ℕ):ℝ) - ((n:ℝ)/d)*((-1:ℝ)^T.card / m)| ≤ 1
      rw [Nat.div_div_eq_div_mul,show (n:ℝ)/d*((-1:ℝ)^T.card/m) =
        (-1:ℝ)^T.card * ((n:ℝ)/(d*m:ℕ)) by push_cast; ring, ← mul_sub,
        abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      exact div_error n (Nat.mul_pos hd hm)
    _ = _ := by simp

end Erdos490Smooth

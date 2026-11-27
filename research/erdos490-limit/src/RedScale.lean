import OldSparseMass
import BlueProducts

/-! Convert a lower bound at every real dilation into new counts at every
integer cutoff. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490
open scoped Topology
noncomputable section

theorem red_at_prescribed {C : Finset ℕ} {b x M : ℝ} (hx : 0 < x)
    (A : ℝ → ℝ → ℝ)
    (count : ∀ {t}, 0 < t → ∀ c, A t c ≤ ((semigroup (bands b t C) ⌊exp (t*x-c)⌋₊).card:ℝ))
    (recovery : ∀ c : ℝ, ∀ ε > 0, ∀ᶠ t : ℝ in atTop,
      M-ε ≤ t*exp (-(t*x-c))*A t c) :
    ∀ u : ℕ, 0 < u → ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      let t := log n/x
      M-ε ≤ t*density (bands b t C) n u := by
  intro u hu ε hε
  have scale : Tendsto (fun n : ℕ => log n/x) atTop atTop :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hx
  filter_upwards [scale.eventually (recovery (log u) ε hε),scale.eventually_gt_atTop 0,
    eventually_gt_atTop (0:ℕ)] with n hr ht hn
  let t := log (n:ℝ)/x
  have htx : t*x = log n := div_mul_cancel₀ _ hx.ne'
  have h := (hr.trans (mul_le_mul_of_nonneg_left (count ht (log u))
    (mul_nonneg ht.le (exp_pos _).le)))
  change M-ε ≤ t*density (bands b t C) n u
  rw [← shifted_density _ hn hu, F_eq_semigroup, ← htx, ← mul_assoc]
  exact h

#print axioms red_at_prescribed
end
end Erdos490Transfer

import AssemblySmooth
import Mathlib.Data.Nat.Prime.Infinite

/-! Prime moduli, the square-root scale, and scalar limits used for the split estimate. -/

open Filter Topology Real
namespace Green39.Assembly
noncomputable section

abbrev Prime := {p : ℕ // p.Prime}

theorem prime_cofinal : Tendsto (fun p : Prime => p.val) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨n,hn,hp⟩ := Nat.exists_infinite_primes b
  exact (eventually_ge_atTop (⟨n,hp⟩ : Prime)).mono fun _ h => hn.trans h

theorem prime_root : Tendsto (fun p : Prime => p.val.sqrt) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  exact (prime_cofinal.eventually_ge_atTop (b*b)).mono fun _ h => Nat.le_sqrt.mpr h

theorem prime_root_real : Tendsto (fun p : Prime => (p.val.sqrt:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp prime_root

theorem exp_decay (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun p : Prime => exp (-c * (p.val.sqrt:ℝ) ^ a)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_atTop ha).comp prime_root_real
  have hn := tendsto_neg_atTop_atBot.comp (h.const_mul_atTop hc)
  simpa only [Function.comp_def,neg_mul] using tendsto_exp_atBot.comp hn

theorem balance_decay : Tendsto (fun p : Prime => 4*(p.val.sqrt:ℝ)^2 * exp (-(p.val.sqrt:ℝ)/200000000)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/200000000) (by norm_num)).comp prime_root_real
  have h' := h.const_mul (4:ℝ)
  simp only [mul_zero,Function.comp_apply,rpow_two] at h'
  apply h'.congr
  intro p
  rw [mul_assoc]
  congr 2
  ring_nf

theorem eventually_active : ∀ᶠ p : Prime in atTop, 5000 < log ((p.val:ℝ)/p.val.sqrt) := by
  filter_upwards [(tendsto_log_atTop.comp prime_root_real).eventually_gt_atTop 5000,
    prime_root.eventually_ge_atTop 1] with p h hk
  have hk0 : (0:ℝ)<p.val.sqrt := Nat.cast_pos.mpr (show 0 < p.val.sqrt by omega)
  apply h.trans_le (log_le_log hk0 ((le_div_iff₀ hk0).mpr ?_))
  change (p.val.sqrt:ℝ) * (p.val.sqrt:ℝ) ≤ (p.val:ℝ)
  exact_mod_cast Nat.sqrt_le p.val
end
end Green39.Assembly
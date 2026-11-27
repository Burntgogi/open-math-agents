import Remainder

open Finset Filter Real Asymptotics
open scoped Chebyshev Topology

namespace Erdos490PrimeCells

theorem error_increment {x y : ℝ} (hxy : x ≤ y) :
    reciprocalInterval x y - (log (log y) - log (log x)) = Mertens.E₂p y - Mertens.E₂p x := by
  have h := Finset.sum_Ioc_consecutive (fun p : ℕ => if p.Prime then (1:ℝ)/p else 0)
    (Nat.zero_le ⌊x⌋₊) (Nat.floor_mono hxy)
  have hx := Mertens.sum_prime_div_eq x
  have hy := Mertens.sum_prime_div_eq y
  simp only [Finset.sum_filter,one_div] at h hx hy
  unfold reciprocalInterval
  rw [Finset.sum_filter]
  linarith

theorem mertens_error_from_theta {K : ℝ} (hK : 0 ≤ K)
    (hθ : ∀ᶠ t : ℝ in atTop, |θ t - t| ≤ K*t / log t ^ 3) :
    ∀ᶠ x : ℝ in atTop, |Mertens.E₂p x| ≤ 3*K / log x ^ 3 := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp hθ
  filter_upwards [eventually_gt_atTop 1,eventually_ge_atTop X,tendsto_log_atTop.eventually_ge_atTop 1]
    with x hx hxX hlog
  have hlim := (((isLittleO_one_iff ℝ).mp Mertens.E₂p.bound').sub
    (tendsto_const_nhds (x := Mertens.E₂p x) (f := atTop))).abs
  simp only [zero_sub, abs_neg] at hlim
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hy
  rw [← error_increment hy]
  exact reciprocal_remainder hx hy hlog hK fun t ht => hX _ (hxX.trans ht.1)

end Erdos490PrimeCells

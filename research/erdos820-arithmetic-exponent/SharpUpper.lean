import Erdos820ArithmeticIdentity
import Batteries.Tactic.OpenPrivate

/-! # The universal `log 2` upper bound for the Erdős 820 exponent -/

namespace Erdos820Identity

open Filter Real
open private nat_log_real from Erdos820ArithmeticIdentity

private theorem log_divisors_le_split {n b : ℕ} (hn : 0 < n) (hb : 1 < b) :
    log (n.divisors.card : ℝ) ≤
      (b : ℝ) * log ((Nat.log 2 n : ℝ) + 1) + (Nat.log b n : ℝ) * log 2 := by
  have hcard : 0 < n.divisors.card :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hsplit : (n.divisors.card : ℝ) ≤ ((Nat.log 2 n : ℝ) + 1) ^ b * 2 ^ Nat.log b n := by
    exact_mod_cast Erdos820Critical.Upper.divisor_split hn hb
  have h := log_le_log (by exact_mod_cast hcard : (0 : ℝ) < n.divisors.card) hsplit
  rwa [log_mul (by positivity) (by positivity), log_pow, log_pow] at h

/-- At the cutoff `⌈(log n)^a⌉₊`, the small primes cost at most `ε * rate n`
eventually, and the large primes cost at most `(log 2 / a) * rate n`. -/
private theorem log_divisors_eventually_rpow {a ε : ℝ} (ha : 0 < a) (ha' : a < 1)
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, log (n.divisors.card : ℝ) ≤ (log 2 / a + ε) * rate n := by
  have htend : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlittle := (isLittleO_log_rpow_rpow_atTop 2 (sub_pos.mpr ha')).bound
    (show 0 < ε / 4 by positivity)
  filter_upwards [htend.eventually hlittle, htend.eventually (eventually_ge_atTop (3 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with n hsmall ht3 hn
  let t := log (n : ℝ)
  change 3 ≤ t at ht3
  have ht : 0 < t := by linarith
  have htlog : 0 < log t := log_pos (by linarith)
  have hrpow : 1 < t ^ a := one_lt_rpow (by linarith) ha
  let b := ⌈t ^ a⌉₊
  have hbge : t ^ a ≤ (b : ℝ) := Nat.le_ceil _
  have hble : (b : ℝ) ≤ 2 * t ^ a := by
    have h := Nat.ceil_lt_add_one (rpow_nonneg ht.le a)
    change (b : ℝ) < t ^ a + 1 at h
    linarith
  have hb : 1 < b := by exact_mod_cast hrpow.trans_le hbge
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hnat2 := nat_log_real (n := n) hn.ne' (by decide : 1 < 2)
  have hbase : (Nat.log 2 n : ℝ) + 1 ≤ t ^ 2 := by
    norm_num at hnat2
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have hlogn : (Nat.log 2 n : ℝ) / 2 ≤ t := by
      calc
        _ ≤ (Nat.log 2 n : ℝ) * log 2 := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg (Nat.log 2 n))
        _ ≤ t := hnat2
    nlinarith [mul_nonneg ht.le (show 0 ≤ t - 3 by linarith)]
  have hlogbase : log ((Nat.log 2 n : ℝ) + 1) ≤ 2 * log t := by
    simpa [log_pow] using log_le_log (by positivity) hbase
  change ‖log t ^ (2 : ℝ)‖ ≤ ε / 4 * ‖t ^ (1 - a)‖ at hsmall
  rw [rpow_two, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (rpow_nonneg ht.le _)] at hsmall
  have hfirst : (b : ℝ) * log ((Nat.log 2 n : ℝ) + 1) ≤ ε * rate n := by
    change _ ≤ ε * (t / log t)
    rw [← mul_div_assoc, le_div_iff₀ htlog]
    calc
      _ ≤ (2 * t ^ a * (2 * log t)) * log t := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul hble hlogbase ?_ ?_) htlog.le
        · exact log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)])
        · positivity
      _ = 4 * t ^ a * log t ^ 2 := by ring
      _ ≤ 4 * t ^ a * (ε / 4 * t ^ (1 - a)) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = ε * (t ^ a * t ^ (1 - a)) := by ring
      _ = ε * t := by rw [← rpow_add ht, show a + (1 - a) = 1 by ring, rpow_one]
  have hblog : log t * a ≤ log (b : ℝ) := by
    simpa [log_rpow ht, mul_comm] using log_le_log (rpow_pos_of_pos ht a) hbge
  have hlarge : (Nat.log b n : ℝ) ≤ rate n / a := by
    rw [rate, div_div]
    change _ ≤ t / (log t * a)
    apply (le_div_iff₀ (mul_pos htlog ha)).mpr
    calc
      _ ≤ (Nat.log b n : ℝ) * log (b : ℝ) :=
        mul_le_mul_of_nonneg_left hblog (Nat.cast_nonneg _)
      _ ≤ t := nat_log_real hn.ne' hb
  calc
    _ ≤ (b : ℝ) * log ((Nat.log 2 n : ℝ) + 1) + (Nat.log b n : ℝ) * log 2 :=
      log_divisors_le_split hn hb
    _ ≤ ε * rate n + rate n / a * log 2 :=
      add_le_add hfirst (mul_le_mul_of_nonneg_right hlarge hlog2.le)
    _ = _ := by ring

/-- The elementary sharp upper coefficient for the divisor count. -/
theorem log_divisors_eventually_sharp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, log (n.divisors.card : ℝ) ≤ (log 2 + ε) * rate n := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let a := log 2 / (log 2 + ε / 2)
  have hden : 0 < log 2 + ε / 2 := by positivity
  have ha : 0 < a := div_pos hlog2 hden
  have ha' : a < 1 := (div_lt_one hden).mpr (by linarith)
  have hcoeff : log 2 / a + ε / 2 = log 2 + ε := by
    dsimp [a]
    rw [div_div_eq_mul_div, mul_comm (log 2), mul_div_cancel_right₀ _ hlog2.ne']
    ring
  simpa only [hcoeff] using log_divisors_eventually_rpow ha ha' (half_pos hε)

/-- The common maximal-order exponent in Erdős 820 is at most `log 2`. -/
theorem limsup_HExponent_le_log_two : limsup HExponent atTop ≤ log 2 := by
  rw [arithmetic_identity]
  have hlower : IsBoundedUnder (· ≥ ·) atTop primeExponent :=
    ⟨0, primeExponent_bounds.mono fun _ h => h.1⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le hlower.isCoboundedUnder_le
  filter_upwards [log_divisors_eventually_sharp hε, rate_pos,
    eventually_gt_atTop (0 : ℕ)] with n hdiv hr hn
  unfold primeExponent
  apply (div_le_iff₀ hr).mpr
  have hpos : 0 < ((Erdos820Critical.shiftedPrimes n).card : ℝ) := by
    exact_mod_cast (show 0 < (Erdos820Critical.shiftedPrimes n).card from shifted_one hn)
  have hle : ((Erdos820Critical.shiftedPrimes n).card : ℝ) ≤ n.divisors.card := by
    exact_mod_cast shifted_le_divisors hn
  exact (log_le_log hpos hle).trans hdiv

#print axioms log_divisors_eventually_sharp
#print axioms limsup_HExponent_le_log_two

end Erdos820Identity

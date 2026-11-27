import SliceRegularity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Uniform rates for terminal containers

A product of descending-factorial ratios gives both a uniform lower bound
for the hole density and the containment estimate for regularity.
-/

open Finset
open scoped BigOperators Classical

namespace Green39.Terminal

noncomputable section

private theorem choose_div_choose_eq_prod (a b r : ℕ) :
    (a.choose r : ℝ) / (b.choose r : ℝ) =
      ∏ i ∈ range r, (((a - i : ℕ) : ℝ) / ((b - i : ℕ) : ℝ)) := by
  rw [prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  exact (mul_div_mul_left _ _ (by exact_mod_cast (Nat.factorial_pos r).ne')).symm

private theorem contain_ratio_le_pow {p k r : ℕ} (hkp : k ≤ p) (hr : r ≤ k) :
    (((p - r).choose (k - r) : ℕ) : ℝ) / (p.choose k : ℝ) ≤ ((k : ℝ) / p) ^ r := by
  have hpos : 0 < (p.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hkp
  have hpos' : 0 < (p.choose r : ℝ) := by exact_mod_cast Nat.choose_pos (hr.trans hkp)
  have heq : (((p - r).choose (k - r) : ℕ) : ℝ) / (p.choose k : ℝ) =
      (k.choose r : ℝ) / (p.choose r : ℝ) := by
    apply (div_eq_div_iff hpos.ne' hpos'.ne').mpr
    have h := Nat.choose_mul (n := p) hr
    exact_mod_cast (by simpa only [mul_comm] using h.symm :
      (p - r).choose (k - r) * p.choose r = k.choose r * p.choose k)
  rw [heq, choose_div_choose_eq_prod k p r, ← show
    (∏ _i ∈ range r, (k : ℝ) / p) = ((k : ℝ) / p) ^ r by rw [prod_const, card_range]]
  refine prod_le_prod (fun i _ ↦ by positivity) fun i hi ↦ ?_
  have hi' : i < r := by simpa only [card_range, mem_range] using hi
  have hki : i ≤ k := hi'.le.trans hr
  have hpi : i < p := hi'.trans_le (hr.trans hkp)
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Nat.zero_le i).trans_lt hpi
  have hpi' : 0 < ((p - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hpi
  have hkpr : (k : ℝ) ≤ p := by exact_mod_cast hkp
  have h := mul_nonneg (Nat.cast_nonneg i : 0 ≤ (i : ℝ)) (sub_nonneg.mpr hkpr)
  apply (div_le_div_iff₀ hpi' hp).mpr
  rw [Nat.cast_sub hki, Nat.cast_sub hpi.le]
  nlinarith

/-- A usable exponential version of the exact regularity bound. -/
theorem irregularBound_le_exp {p k m L : ℕ} {M : ℝ}
    (hkp : k ≤ p) (hr : L + 1 ≤ k)
    (hm : (m : ℝ) * ((k : ℝ) / p) ≤ M) :
    irregularBound p k m L ≤
      (p : ℝ) * Real.exp (2 * M - ((L + 1 : ℕ) : ℝ) * Real.log 2) := by
  let r := L + 1
  let q : ℝ := (k : ℝ) / p
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbin : (m.choose r : ℝ) * (2 * q) ^ r ≤ Real.exp (2 * M) := by
    by_cases hm' : r ≤ m
    swap
    · simp [Nat.choose_eq_zero_of_lt (lt_of_not_ge hm'), Real.exp_nonneg]
    calc
      _ ≤ (2 * q + 1) ^ m := by
        rw [add_pow]
        have hm'' : r ∈ range (m + 1) := mem_range.mpr (Nat.lt_succ_of_le hm')
        simpa only [one_pow, mul_one, one_mul, mul_comm] using
          (single_le_sum (f := fun i ↦ (2 * q) ^ i * 1 ^ (m - i) * (m.choose i : ℝ))
            (fun i _ ↦ by positivity) hm'')
      _ ≤ (Real.exp (2 * q)) ^ m :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp (2 * ((m : ℝ) * q)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hr2 : 0 < (2 : ℝ) ^ r := by positivity
  have hb : (m.choose r : ℝ) * q ^ r ≤ Real.exp (2 * M - (r : ℝ) * Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    apply (le_div_iff₀ hr2).mpr
    rw [mul_pow] at hbin
    simpa only [mul_left_comm, mul_assoc, mul_comm] using hbin
  calc
    _ = (p : ℝ) * ((m.choose r : ℝ) * (((p - r).choose (k - r) : ℝ) / p.choose k)) := by
      dsimp [irregularBound, r]
      ring
    _ ≤ (p : ℝ) * ((m.choose r : ℝ) * q ^ r) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (contain_ratio_le_pow hkp hr) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)

private theorem exp_neg_twice_le_one_sub {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    Real.exp (-2 * y) ≤ 1 - y := by
  have hpos : 0 < 1 - y := by linarith
  apply (Real.le_log_iff_exp_le hpos).mp
  refine le_trans ?_ (Real.one_sub_inv_le_log_of_pos hpos)
  rw [inv_eq_one_div]
  have h : 1 / (1 - y) ≤ 1 + 2 * y := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg hy (show 0 ≤ 1 - 2 * y by linarith)]
  linarith

/-- If «k + m ≤ p/2», the hole density has a uniform positive lower bound
in terms of «m*k/p». -/
theorem choose_avoidance_ge_exp {p k m : ℕ} (hp : 0 < p) (hkm : 2 * (k + m) ≤ p) :
    Real.exp (-4 * ((m : ℝ) * k / p)) ≤ (p - m).choose k / (p.choose k : ℝ) := by
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hkp : k ≤ p := by omega
  rw [choose_div_choose_eq_prod (p - m) p k]
  calc
    _ = (Real.exp (-4 * ((m : ℝ) / p))) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = ∏ _i ∈ range k, Real.exp (-4 * ((m : ℝ) / p)) := by rw [prod_const, card_range]
    _ ≤ _ := by
      refine prod_le_prod (fun i _ ↦ Real.exp_nonneg _) fun i hi ↦ ?_
      have hi' := mem_range.mp hi
      have hip : i < p := hi'.trans_le hkp
      have hmip : m + i ≤ p := by omega
      have hpi : 0 < ((p : ℝ) - i) := sub_pos.mpr (by exact_mod_cast hip)
      have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - i := by
        have h : 2 * i ≤ p := by omega
        have hh : (2 : ℝ) * i ≤ p := by exact_mod_cast h
        linarith
      have hmhalf : (m : ℝ) / ((p : ℝ) - i) ≤ 1 / 2 := by
        apply (div_le_iff₀ hpi).mpr
        have h : 2 * m + i ≤ p := by omega
        have hh : (2 : ℝ) * m + i ≤ p := by exact_mod_cast h
        linarith
      have hmfrac : (m : ℝ) / ((p : ℝ) - i) ≤ 2 * ((m : ℝ) / p) := by
        apply (div_le_iff₀ hpi).mpr
        have h := mul_le_mul_of_nonneg_left hhalf
          (show 0 ≤ 2 * ((m : ℝ) / p) by positivity)
        have he : 2 * ((m : ℝ) / p) * ((p : ℝ) / 2) = m := by field_simp
        rwa [he] at h
      calc
        _ ≤ Real.exp (-2 * ((m : ℝ) / ((p : ℝ) - i))) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 1 - (m : ℝ) / ((p : ℝ) - i) :=
          exp_neg_twice_le_one_sub (div_nonneg (Nat.cast_nonneg _) hpi.le) hmhalf
        _ = _ := by
          rw [Nat.cast_sub (show i ≤ p - m by omega), Nat.cast_sub (show m ≤ p by omega),
            Nat.cast_sub hip.le]
          field_simp
          ring

end

end Green39.Terminal


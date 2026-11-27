import FormalConjectures.ErdosProblems.«820»
import Mathlib

/-!
# The arithmetic exponent in Erdős problem 820

The shifted-prime product obstruction is due to Paul Erdős and was applied to
the sharper exponent scale by Wouter van Doorn. The fixed-base upper sieve is
due to Liam Price. The independent formalization of that sieve below and its
extension to an averaged choice of the smaller base yield the arithmetic
identity and the finite bound.

* [Erdős (1974), p. 200](https://users.renyi.hu/~p_erdos/1974-27.pdf#page=4)
* [van Doorn, Erdős Problems forum](https://www.erdosproblems.com/forum/thread/820#post-1099)
* [Price, Coprime Power Differences](https://www.overleaf.com/read/kvjrzdkwkgkx#010e4a)
* [Formal Conjectures, pinned statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/820.lean)
-/

section

/- Combined from Critical.lean. -/

/- Common critical exponents for the two bounds in Erdős 820.
The isolated upper and lower number-theoretic inputs are stated explicitly. -/

open Filter

namespace Erdos820Critical

noncomputable def scale (a : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((n : ℝ) ^ (a / Real.log (Real.log (n : ℝ))))

theorem eventually_strictMono : ∀ᶠ n : ℕ in atTop, StrictMono (fun a => scale a n) := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 < Real.log (n : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by positivity : (0:ℝ) < n)).mpr
    linarith [Real.exp_one_lt_three]
  intro a b hab
  exact Real.exp_lt_exp.mpr (Real.rpow_lt_rpow_of_exponent_lt (by linarith)
    (div_lt_div_of_pos_right hab (Real.log_pos hlog)))

/-- The separating exponent need not coincide with either known endpoint. -/
theorem critical_of_separate_bounds (v : ℕ → ℝ) {a b : ℝ} (ha : 0 < a)
    (hlower : ∃ᶠ n : ℕ in atTop, scale a n < v n)
    (hupper : ∀ᶠ n : ℕ in atTop, v n < scale b n) :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ),
      (∃ᶠ n : ℕ in atTop, scale (c-ε) n < v n) ∧
      ∀ᶠ n : ℕ in atTop, v n < scale (c+ε) n := by
  let S : Set ℝ := {s | ∃ᶠ n : ℕ in atTop, scale s n < v n}
  have has : a ∈ S := hlower
  have hne : S.Nonempty := ⟨a, has⟩
  have hbounded : BddAbove S := by
    refine ⟨b, fun s hs => ?_⟩
    by_contra! h
    have hcut : ∀ᶠ n : ℕ in atTop, ¬scale s n < v n := by
      filter_upwards [hupper, eventually_strictMono] with n hupper hmono
      exact not_lt.mpr (hupper.trans (hmono h)).le
    exact hs hcut
  refine ⟨sSup S, ha.trans_le (le_csSup hbounded has), fun ε hε => ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, hcs⟩ := exists_lt_of_lt_csSup hne (show sSup S - ε < sSup S by linarith)
    exact (show ∃ᶠ n : ℕ in atTop, scale s n < v n from hs).and_eventually
      eventually_strictMono |>.mono fun _ h => (h.2 hcs).trans h.1
  · have hs : sSup S + ε/2 ∉ S := fun h => (not_lt.mpr (le_csSup hbounded h)) (by linarith)
    have he : ∀ᶠ n : ℕ in atTop, ¬scale (sSup S + ε/2) n < v n := by
      change ¬(∃ᶠ n : ℕ in atTop, scale (sSup S + ε/2) n < v n) at hs
      simpa only [not_frequently] using hs
    filter_upwards [he, eventually_strictMono] with n hn hm
    exact (le_of_not_gt hn).trans_lt (hm (show sSup S + ε/2 < sSup S + ε by linarith))

theorem H_le_K {n : ℕ} (hn : 2 ≤ n) : Erdos820.H n ≤ Erdos820.K n := by
  have hsize : 4 ≤ 2 ^ n := (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right (by decide) hn
  let l := 2^n - 1
  have hl : 2 < l := by dsimp [l]; omega
  have hne : {k : ℕ | 2 ≤ k ∧ Nat.Coprime (k ^ n - 1) l}.Nonempty := by
    refine ⟨l, hl.le, ?_⟩
    have h1 : 1 ≤ l^n := Nat.one_le_pow _ _ (by omega)
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega : n ≠ 0))
      (((Nat.coprime_self_sub_right h1).2 (Nat.coprime_one_right _)).symm)
  have hk := Nat.sInf_mem hne
  change 2 ≤ Erdos820.K n ∧ Nat.Coprime ((Erdos820.K n)^n-1) l at hk
  have h2 : 2 < Erdos820.K n := by
    by_contra! hh
    have he := Nat.le_antisymm hh hk.1
    have h := hk.2
    rw [he] at h
    change Nat.Coprime l l at h
    have hone : l = 1 := by simpa using h
    omega
  exact Nat.sInf_le ⟨2, by decide, h2, hk.2.symm⟩

theorem official_of_lower_and_upper {a b : ℝ} (ha : 0 < a)
    (hl : ∃ᶠ n : ℕ in atTop, scale a n < Erdos820.H n)
    (hu : ∀ᶠ n : ℕ in atTop, (Erdos820.K n : ℝ) < scale b n) :
    type_of% @Erdos820.erdos_820.variants.log_log_exponent := by
  apply critical_of_separate_bounds _ ha hl
  filter_upwards [hu, eventually_ge_atTop 2] with n hk hn
  exact (show (Erdos820.H n : ℝ) ≤ Erdos820.K n by exact_mod_cast H_le_K hn).trans_lt hk


def shiftedPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range (n+2)).filter fun p => p.Prime ∧ p-1 ∣ n

private theorem forced_prime {p m n : ℕ} (hp : p.Prime) (hd : p-1 ∣ n)
    (hm : 1 ≤ m) (h : ¬p ∣ m) : p ∣ m^n-1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun he => h ((ZMod.natCast_eq_zero_iff _ _).mp he)
  obtain ⟨j,hj⟩ := hd
  have hpow : (m : ZMod p)^n = 1 := by
    rw [hj, pow_mul, ZMod.pow_card_sub_one_eq_one hm0, one_pow]
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hm), Nat.cast_pow, Nat.cast_one, hpow, sub_self]

/-- The forced primes for a minimal coprime pair give the lower bound of van Doorn. -/
theorem shifted_count_le_H_sq {n : ℕ} (hn : 1 ≤ n) :
    2^(shiftedPrimes n).card ≤ Erdos820.H n ^ 2 := by
  obtain ⟨k,hk,hkH,hcop⟩ := Erdos820.H_spec hn
  let l := Erdos820.H n
  have hl : 2 < l := hk.trans_lt hkH
  have hsub : shiftedPrimes n ⊆ (k*l).primeFactors := by
    intro p hp
    obtain ⟨hpr, hdiv⟩ := (Finset.mem_filter.mp hp).2
    refine Nat.mem_primeFactors.mpr ⟨hpr, ?_, Nat.mul_ne_zero (by omega) (by omega)⟩
    by_contra hf
    have hk' : ¬p ∣ k := fun h => hf (dvd_mul_of_dvd_left h _)
    have hl' : ¬p ∣ l := fun h => hf (dvd_mul_of_dvd_right h _)
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hpr,
      forced_prime hpr hdiv (by omega : 1 ≤ k) hk',
      forced_prime hpr hdiv (by omega : 1 ≤ l) hl'⟩) hcop
  calc
    _ ≤ 2^(k*l).primeFactors.card := Nat.pow_le_pow_right (by decide) (Finset.card_le_card hsub)
    _ = ∏ _p ∈ (k*l).primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ (k*l).primeFactors, p := by
      exact Finset.prod_le_prod' (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
    _ ≤ k*l := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) (Nat.prod_primeFactors_dvd _)
    _ ≤ _ := by change k*l ≤ l^2; rw [pow_two]; exact Nat.mul_le_mul_right _ hkH.le

theorem official_of_shifted_primes {a b : ℝ} (ha : 0 < a)
    (hl : ∃ᶠ n : ℕ in atTop, 4 * ((n : ℝ) ^ (a / Real.log (Real.log n))) <
      (shiftedPrimes n).card)
    (hu : ∀ᶠ n : ℕ in atTop, (Erdos820.K n : ℝ) < scale b n) :
    type_of% @Erdos820.erdos_820.variants.log_log_exponent := by
  apply official_of_lower_and_upper ha _ hu
  apply (hl.and_eventually (eventually_ge_atTop 2)).mono
  rintro n ⟨hcount, hn⟩
  have hpow : (2 : ℝ) ^ (shiftedPrimes n).card ≤ (Erdos820.H n : ℝ)^2 := by
    exact_mod_cast shifted_count_le_H_sq (by omega : 1 ≤ n)
  have hlog : (1/2 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hpos : 0 < (n:ℝ) ^ (a / Real.log (Real.log n)) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hlt : (scale a n)^2 < (2:ℝ)^(shiftedPrimes n).card := by
    rw [scale, ← Real.exp_nat_mul, ← Real.exp_log (by norm_num : (0:ℝ) < 2), ← Real.exp_nat_mul]
    apply Real.exp_lt_exp.mpr
    push_cast
    nlinarith [mul_pos (sub_pos.mpr hlog)
      (show 0 < ((shiftedPrimes n).card : ℝ) by linarith)]
  have hsq := hlt.trans_le hpow
  have hv : (0:ℝ) ≤ Erdos820.H n := Nat.cast_nonneg _
  have hw : 0 < scale a n := Real.exp_pos _
  nlinarith


end Erdos820Critical

end

section

/- Combined from upper/DivisorSplit.lean. -/

/- An elementary finite split for the maximal order of the divisor count. -/

open Finset
namespace Erdos820Critical.Upper

theorem divisor_split {n b : ℕ} (hn : 0 < n) (hb : 1 < b) :
    n.divisors.card ≤ (Nat.log 2 n + 1)^b * 2^(Nat.log b n) := by
  let S := n.primeFactors.filter (· < b)
  let T := n.primeFactors.filter (fun p => ¬p < b)
  have hsplit (f : ℕ → ℕ) : (∏ p ∈ S, f p) * (∏ p ∈ T, f p) = ∏ p ∈ n.primeFactors, f p :=
    prod_filter_mul_prod_filter_not _ _ _
  have hexp {p : ℕ} (hp : p ∈ n.primeFactors) : n.factorization p ≤ Nat.log 2 n := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    exact Nat.le_log_of_pow_le (by decide) ((Nat.pow_le_pow_left hpr.two_le _).trans
      (Nat.le_of_dvd hn ((hpr.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl)))
  have hScard : S.card ≤ b := by
    simpa using card_le_card (show S ⊆ range b from fun p hp => mem_range.mpr (mem_filter.mp hp).2)
  have hsmall : (∏ p ∈ S, (n.factorization p + 1)) ≤ (Nat.log 2 n + 1)^b := by
    calc
      _ ≤ ∏ _p ∈ S, (Nat.log 2 n + 1) :=
        prod_le_prod' (fun p hp => Nat.add_le_add_right (hexp (mem_filter.mp hp).1) _)
      _ = _ ^ S.card := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hScard
  have hTsum : (∑ p ∈ T, n.factorization p) ≤ Nat.log b n := by
    apply Nat.le_log_of_pow_le hb
    calc
      _ = ∏ p ∈ T, b^(n.factorization p) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ ∏ p ∈ T, p^(n.factorization p) :=
        prod_le_prod' (fun p hp => Nat.pow_le_pow_left (Nat.le_of_not_gt (mem_filter.mp hp).2) _)
      _ ≤ n := by
        apply Nat.le_of_dvd hn
        exact (dvd_mul_left _ _).trans (dvd_of_eq ((hsplit (fun p => p^(n.factorization p))).trans (Nat.prod_primeFactors_pow_factorization hn.ne').symm))

  have hlarge : (∏ p ∈ T, (n.factorization p + 1)) ≤ 2^(Nat.log b n) := by
    calc
      _ ≤ ∏ p ∈ T, 2^(n.factorization p) :=
        prod_le_prod' (fun p _ => Nat.succ_le_of_lt (Nat.lt_two_pow_self))
      _ = 2^(∑ p ∈ T, n.factorization p) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) hTsum
  rw [Nat.card_divisors hn.ne', ← hsplit]
  exact Nat.mul_le_mul hsmall hlarge

private theorem nat_log_real {n b : ℕ} (hn : n ≠ 0) (hb : 1 < b) :
    (Nat.log b n : ℝ) * Real.log b ≤ Real.log n := by
  rw [← Real.log_pow]
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.pow_log_le_self b hn

/-- A finite absolute constant suffices for the upper input in Erdős 820. -/
theorem log_divisors_eventually : ∀ᶠ n : ℕ in Filter.atTop,
    Real.log (n.divisors.card : ℝ) ≤ 4 * Real.log n / Real.log (Real.log n) := by
  let x : ℕ → ℝ := fun n => Real.sqrt (Real.log n)
  have ht : Filter.Tendsto x Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0:ℝ) < 1/6 by norm_num)
  filter_upwards [ht.eventually hlittle, ht.eventually (Filter.eventually_ge_atTop 3),
    Filter.eventually_ge_atTop 2] with n hsmall hx hn
  let y := x n
  change 3 ≤ y at hx
  have hy : 0 < y := by linarith
  have hylog : 0 < Real.log y := Real.log_pos (by linarith)
  have hsq : y^2 = Real.log n := Real.sq_sqrt (Real.log_natCast_nonneg n)
  have hL : Real.log (Real.log n) = 2 * Real.log y := by rw [← hsq, Real.log_pow]; norm_num
  change ‖Real.log y ^ 2‖ ≤ 1/6 * ‖y‖ at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log y)), abs_of_pos hy] at hsmall
  let b := ⌈y⌉₊
  have hby : y ≤ b := Nat.le_ceil y
  have hby' : (b : ℝ) ≤ y + 1 := (Nat.ceil_lt_add_one hy.le).le
  have hb : 1 < b := by exact_mod_cast (show (1 : ℝ) < b by linarith)
  have hh := divisor_split (n := n) (by omega) hb
  have hnat := nat_log_real (n := n) (by omega) (by decide : 1 < 2)
  norm_num at hnat
  have hnat' := nat_log_real (n := n) (by omega) hb
  have h2 : (1/2:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hd : 0 < n.divisors.card := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr (by omega)⟩
  have hlog := Real.log_le_log (show 0 < (n.divisors.card:ℝ) by exact_mod_cast hd)
    (show (n.divisors.card:ℝ) ≤ ((Nat.log 2 n : ℝ) + 1)^b * 2^(Nat.log b n) by exact_mod_cast hh)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hbase : (Nat.log 2 n : ℝ) + 1 ≤ y^3 := by
    have hk : 0 ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (y-2), mul_nonneg hk (sub_nonneg.mpr h2.le), mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hx)]
  have hlogbase : Real.log ((Nat.log 2 n:ℝ)+1) ≤ 3*Real.log y := by
    have h := Real.log_le_log (by positivity) hbase
    simpa [Real.log_pow] using h
  have hfirst : (b:ℝ) * Real.log ((Nat.log 2 n:ℝ)+1) ≤ 6*y*Real.log y := by
    calc
      _ ≤ (2*y) * (3*Real.log y) := mul_le_mul (by linarith) hlogbase (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)])) (by positivity)
      _ = _ := by ring
  have hsecond : (Nat.log b n : ℝ) * Real.log 2 * Real.log y ≤ Real.log n := by
    have hb' := Real.log_le_log hy hby
    calc
      _ ≤ (Nat.log b n : ℝ) * 1 * Real.log b := mul_le_mul
        (mul_le_mul_of_nonneg_left h2' (by positivity)) hb' hylog.le (by positivity)
      _ ≤ _ := by simpa using hnat'
  rw [hL]
  apply (le_div_iff₀ (by positivity)).mpr
  have hterm := mul_le_mul_of_nonneg_right hfirst hylog.le
  have hsum := mul_le_mul_of_nonneg_right hlog hylog.le
  nlinarith [mul_nonneg hy.le (show 0 ≤ y-6*(Real.log y)^2 by linarith)]

end Erdos820Critical.Upper

end

section

/- Combined from upper/Assemble.lean. -/

/- The analytic implication from a finite sieve bound to the second submission step. -/
open Filter
namespace Erdos820Critical.Upper

/-- Any fixed power of log in the sieve error is absorbed in a finite exponent. -/
theorem eventual_upper_of_sieve (C : ℝ) (hC : 0 < C) (r : ℕ)
    (hsieve : ∀ᶠ n : ℕ in atTop, Real.log (Erdos820.K n : ℝ) ≤
      C * n.divisors.card * (1 + Real.log n)^r) :
    ∀ᶠ n : ℕ in atTop, (Erdos820.K n : ℝ) <
      Real.exp ((n : ℝ) ^ (5 / Real.log (Real.log n))) := by
  let D := |Real.log C| + 2*(r:ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0:ℝ) < 1/(2*D) by positivity)
  have ht : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsieve, log_divisors_eventually, ht.eventually hsmall,
    ht.eventually (eventually_ge_atTop 4), eventually_ge_atTop 2] with n hK hτ hsmall ht hn
  let t := Real.log (n:ℝ)
  change 4 ≤ t at ht
  have ht0 : 0 < t := by linarith
  have hl : 1 ≤ Real.log t := ((Real.lt_log_iff_exp_lt ht0).2 (by linarith [Real.exp_one_lt_three])).le
  have hl0 : 0 < Real.log t := by linarith
  change ‖Real.log t ^ 2‖ ≤ 1/(2*D) * ‖t‖ at hsmall
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log t)), abs_of_pos ht0] at hsmall
  have hscale : D*(Real.log t)^2 < t := by
    have hh : (Real.log t)^2 * (2*D) ≤ t := by
      apply (le_div_iff₀ (by positivity : 0 < 2*D)).mp
      simpa [div_eq_mul_inv, mul_comm] using hsmall
    nlinarith [mul_pos hD (sq_pos_of_pos hl0)]
  have hone : Real.log (1+t) ≤ 2*Real.log t := by
    have h := Real.log_le_log (by linarith : 0 < 1+t) (show 1+t ≤ t^2 by nlinarith [sq_nonneg (t-2)])
    simpa [Real.log_pow] using h
  have habs := le_abs_self (Real.log C)
  have hcoef : Real.log C + (r:ℝ)*Real.log (1+t) ≤ D*Real.log t := by
    have hr := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg r)
    have ha := mul_le_mul_of_nonneg_left hl (abs_nonneg (Real.log C))
    dsimp [D]
    nlinarith
  have he : Real.log C + (r:ℝ)*Real.log (1+t) < t / Real.log t := by
    apply (lt_div_iff₀ hl0).mpr
    exact (mul_le_mul_of_nonneg_right hcoef hl0.le).trans_lt (by nlinarith only [hscale])
  have hτ0 : 0 < (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr (by omega)⟩
  have hprod : C*(n.divisors.card:ℝ)*(1+t)^r < (n:ℝ) ^ (5 / Real.log t) := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ)<n)]
    apply (Real.log_lt_iff_lt_exp (by positivity)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hC.ne' hτ0.ne', Real.log_pow]
    change Real.log (n.divisors.card:ℝ) ≤ 4*t / Real.log t at hτ
    change Real.log C + Real.log (n.divisors.card:ℝ) + _ < t * _
    linarith [show 4*t/Real.log t + t/Real.log t = t*(5/Real.log t) by ring]
  by_cases hpos : 0 < (Erdos820.K n : ℝ)
  · exact (Real.log_lt_iff_lt_exp hpos).mp (hK.trans_lt hprod)
  · exact lt_of_le_of_lt (le_of_not_gt hpos) (Real.exp_pos _)

end Erdos820Critical.Upper

end

section

/- Combined from upper/sieve/LocalRoots.lean. -/

/- Independent formalization of the fixed-base sieve argument of Liam Price. -/
open Finset
open scoped Count
namespace Erdos820Critical.Sieve

def root (n d x : ℕ) : Prop := (x : ZMod d)^n = 1
instance (n d x : ℕ) : Decidable (root n d x) := inferInstanceAs (Decidable (_ = (_ : ZMod d)))

def roots (n d : ℕ) := Nat.count (root n d) d

theorem roots_card (n d : ℕ) [NeZero d] :
    roots n d = Fintype.card {x : ZMod d // x ^ n = 1} := by
  rw [roots, Nat.count_eq_card_fintype]
  apply Fintype.card_congr
  exact
    { toFun := fun ⟨x, _, h⟩ => ⟨x, h⟩
      invFun := fun ⟨x, h⟩ => ⟨x.val, x.val_lt, by simpa [root] using h⟩
      left_inv := fun ⟨x, hx, _⟩ => Subtype.ext (ZMod.val_natCast_of_lt hx)
      right_inv := fun ⟨x, _⟩ => Subtype.ext (ZMod.natCast_zmod_val x) }

theorem roots_mul (n : ℕ) {d e : ℕ} [NeZero d] [NeZero e] (hc : d.Coprime e) :
    roots n (d * e) = roots n d * roots n e := by
  rw [roots_card, roots_card, roots_card, ← Fintype.card_prod]
  let E := ZMod.chineseRemainder hc
  apply Fintype.card_congr
  refine (E.toEquiv.subtypeEquiv (q := fun x => x.1 ^ n = 1 ∧ x.2 ^ n = 1) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun x : ZMod d => x^n = 1)
      (q := fun y : ZMod e => y^n = 1))
  intro x
  rw [← E.injective.eq_iff]
  simp [Prod.ext_iff]

theorem roots_prime_le {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    roots n p ≤ n.gcd (p-1) := by
  let : Fact p.Prime := ⟨hp⟩
  let d := n.gcd (p-1)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  rw [roots_card, Fintype.card_subtype]
  calc
    _ ≤ ((Polynomial.nthRoots d (1 : ZMod p)).toFinset).card := by
      apply card_le_card
      intro x hx
      have h := (mem_filter.mp hx).2
      have hx0 : x ≠ 0 := by rintro rfl; simp [hn] at h
      apply Multiset.mem_toFinset.mpr
      apply (Polynomial.mem_nthRoots hd).mpr
      exact orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h)
        (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hx0)))
    _ ≤ _ := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

def hits (n d b N : ℕ) := ((Ico b (b+N)).filter (root n d)).card

theorem hits_period (n d b : ℕ) : hits n d b d = roots n d := by
  apply Nat.filter_Ico_card_eq_of_periodic
  intro x
  simp [root]

theorem hits_blocks (n d b q : ℕ) : hits n d b (q*d) = q * roots n d := by
  induction q with
  | zero => simp [hits]
  | succ q ih =>
    rw [Nat.succ_mul, Nat.succ_mul, ← ih, ← hits_period n d (b+q*d)]
    unfold hits
    rw [← card_union_of_disjoint]
    · congr 1
      ext x
      simp only [mem_filter, mem_union, mem_Ico]
      by_cases h : root n d x <;> (simp [h]; try omega)
    · apply disjoint_left.mpr
      intro x h k
      have := (mem_Ico.mp (mem_filter.mp h).1).2
      have := (mem_Ico.mp (mem_filter.mp k).1).1
      omega

theorem hits_error (n d b N : ℕ) (hd : 0 < d) :
    |(hits n d b N : ℝ) - (N : ℝ) * ((roots n d : ℝ) / d)| ≤ roots n d := by
  let q := N / d
  have hlo : q*d ≤ N := Nat.div_mul_le_self N d
  have hhi : N ≤ (q+1)*d := by
    have := Nat.mod_add_div N d
    have := Nat.mod_lt N hd
    dsimp [q]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (N/d) d]
    omega
  have mono : Monotone (hits n d b) := fun _ _ h => card_le_card
    (filter_subset_filter _ (Ico_subset_Ico le_rfl (Nat.add_le_add_left h _)))
  have hl := mono hlo
  have hu := mono hhi
  rw [hits_blocks] at hl hu
  have hL : (q:ℝ) * roots n d ≤ hits n d b N := by exact_mod_cast hl
  have hU : (hits n d b N:ℝ) ≤ ((q:ℝ)+1)*roots n d := by exact_mod_cast hu
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hq : (q:ℝ) ≤ (N:ℝ)/d := (le_div_iff₀ hd').mpr (by exact_mod_cast hlo)
  have hq' : (N:ℝ)/d ≤ (q:ℝ)+1 := (div_le_iff₀ hd').mpr (by exact_mod_cast hhi)
  rw [show (N:ℝ) * ((roots n d:ℝ)/d) = ((N:ℝ)/d)*roots n d by ring, abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (α := ℝ) (roots n d)),
    mul_le_mul_of_nonneg_right hq' (Nat.cast_nonneg (α := ℝ) (roots n d))]

theorem root_iff_dvd {n d x : ℕ} (hx : 1 ≤ x) : root n d x ↔ d ∣ x^n-1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hx)]
  simp [root, sub_eq_zero]

theorem modulus_pos {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) : 0 < ∏ p ∈ P, p :=
  prod_pos fun p h => (hp p h).pos

theorem local_product {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    roots n (∏ p ∈ P, p) = ∏ p ∈ P, roots n p := by
  induction P using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    rw [roots_card]
    let := uniqueOfSubsingleton (⟨1,one_pow _⟩ : {x : ZMod 1 // x^n = 1})
    exact Fintype.card_unique
  | @insert p t hpt ih =>
    have ht : ∀ q ∈ t, Nat.Prime q := fun q h => hp q (mem_insert_of_mem h)
    have hpr := hp p (mem_insert_self ..)
    let : NeZero p := ⟨hpr.ne_zero⟩
    let : NeZero (∏ q ∈ t, q) := ⟨(modulus_pos ht).ne'⟩
    have hc : p.Coprime (∏ q ∈ t, q) := Nat.coprime_prod_right_iff.mpr fun q h =>
      (Nat.coprime_primes hpr (ht q h)).mpr (fun he => hpt (he ▸ h))
    rw [prod_insert hpt, prod_insert hpt, roots_mul n hc, ih ht]

theorem root_product_iff {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {x n : ℕ} (hx : 1 ≤ x) :
    root n (∏ p ∈ P, p) x ↔ ∀ p ∈ P, root n p x := by
  simp only [root_iff_dvd hx]
  constructor
  · intro h p hi
    exact (dvd_prod_of_mem _ hi).trans h
  · intro h
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
      have ht : ∀ q ∈ t, Nat.Prime q := fun q h => hp q (mem_insert_of_mem h)
      have hc : p.Coprime (∏ q ∈ t, q) := Nat.coprime_prod_right_iff.mpr fun q h =>
        (Nat.coprime_primes (hp p (mem_insert_self ..)) (ht q h)).mpr (fun he => hpt (he ▸ h))
      rw [prod_insert hpt]
      exact hc.mul_dvd_of_dvd_of_dvd (h p (mem_insert_self ..))
        (ih ht fun q hq => h q (mem_insert_of_mem hq))

theorem prime_count {n : ℕ} (hn : 0 < n) : (2^n-1 : ℕ).primeFactors.card ≤ n := by
  have hpow : 1 < (2:ℕ)^n := one_lt_pow₀ (by decide) hn.ne'
  let m : ℕ := 2^n-1
  have hm : 0 < m := Nat.sub_pos_of_lt hpow
  have h : 2^m.primeFactors.card ≤ m := calc
    _ = ∏ _p ∈ m.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ m.primeFactors, p := prod_le_prod' fun p h => (Nat.prime_of_mem_primeFactors h).two_le
    _ ≤ m := Nat.le_of_dvd hm m.prod_primeFactors_dvd
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (h.trans (Nat.sub_le ..))

theorem coprime_of_survivor {n x : ℕ} (hn : 0 < n) (hx : 2 ≤ x)
    (hs : ∀ p ∈ (2^n-1 : ℕ).primeFactors, ¬root n p x) : (x^n-1).Coprime (2^n-1) := by
  by_contra hc
  obtain ⟨p,hp,ha,hb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hpow : 1 < (2:ℕ)^n := one_lt_pow₀ (by decide) hn.ne'
  exact hs p (Nat.mem_primeFactors.mpr ⟨hp,hb,by omega⟩) ((root_iff_dvd (by omega)).mpr ha)

end Erdos820Critical.Sieve

end

section

/- Combined from upper/sieve/Bonferroni.lean. -/

/- A finite odd Bonferroni lower bound and a weighted bound for its model tail.
Written independently for the sieve argument of Liam Price. -/
open Finset
namespace Erdos820Critical.Sieve

def shortSets {α : Type*} (P : Finset α) (r : ℕ) := P.powerset.filter (fun t => t.card ≤ r)

theorem short_sum {α : Type*} {M : Type*} [AddCommMonoid M] (P : Finset α) (r : ℕ)
    (f : Finset α → M) :
    ∑ t ∈ shortSets P r, f t = ∑ j ∈ range (r+1), ∑ t ∈ P.powersetCard j, f t := by
  classical
  symm
  convert (sum_fiberwise_of_maps_to (s := shortSets P r) (t := range (r+1))
    (g := fun t : Finset α => t.card) (fun t ht => mem_range.mpr (by
      have := (mem_filter.mp ht).2; omega)) f) using 1
  apply sum_congr rfl
  intro j hj
  apply sum_congr _ (fun _ _ => rfl)
  ext t
  simp [shortSets, mem_powersetCard]
  have := mem_range.mp hj
  omega

theorem odd_weights {α : Type*} (B : Finset α) (r : ℕ) (hr : Odd r) (hb : B.Nonempty) :
    ∑ t ∈ shortSets B r, (-1:ℝ)^t.card ≤ 0 := by
  rw [short_sum]
  have h (j : ℕ) :
      ∑ t ∈ B.powersetCard j, (-1:ℝ)^t.card = (-1:ℝ)^j * B.card.choose j := by
    trans ∑ _ ∈ B.powersetCard j, (-1:ℝ)^j
    · exact sum_congr rfl fun t ht => by rw [(mem_powersetCard.mp ht).2]
    · simp [mul_comm]
  simp_rw [h]
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.mpr hb).ne'
  rw [hk]
  have hz := @Int.alternating_sum_range_choose_eq_choose k r
  rw [hr.neg_one_pow] at hz
  have he : ∑ j ∈ range (r+1), (-1:ℝ)^j * (k+1).choose j = (-1:ℝ)* k.choose r := by
    exact_mod_cast hz
  rw [he]
  nlinarith [Nat.cast_nonneg (α := ℝ) (k.choose r)]

/-- If every point is covered, the signed short sum of intersection counts is nonpositive. -/
theorem covered_upper {α β : Type*} [DecidableEq α] (P : Finset α) (I : Finset β)
    (B : β → Finset α) (r : ℕ) (hr : Odd r) (hB : ∀ x ∈ I, B x ⊆ P)
    (hn : ∀ x ∈ I, (B x).Nonempty) :
    ∑ t ∈ shortSets P r, (-1:ℝ)^t.card * ((I.filter (fun x => t ⊆ B x)).card : ℝ) ≤ 0 := by
  classical
  have h (t : Finset α) : (-1:ℝ)^t.card * ((I.filter (fun x => t ⊆ B x)).card : ℝ) =
      ∑ x ∈ I, if t ⊆ B x then (-1:ℝ)^t.card else 0 := by
    rw [← sum_filter]
    simp [mul_comm]
  simp_rw [h]
  rw [sum_comm]
  apply sum_nonpos
  intro x hx
  rw [← sum_filter]
  have he : (shortSets P r).filter (· ⊆ B x) = shortSets (B x) r := by
    ext t
    simp only [shortSets, mem_filter, mem_powerset]
    exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans (hB x hx),h.2⟩,h.1⟩⟩
  rw [he]
  exact odd_weights _ _ hr (hn x hx)

/-- The model expansion loses at most an exponentially discounted weighted product. -/
theorem model_lower {α : Type*} (P : Finset α) (u : α → ℝ) (hu : ∀ p ∈ P, 0 ≤ u p)
    (r : ℕ) :
    (∏ p ∈ P, (1-u p)) - Real.exp (-(r:ℝ)) * (∏ p ∈ P, (1+Real.exp 1*u p)) ≤
      ∑ t ∈ shortSets P r, (-1:ℝ)^t.card * ∏ p ∈ t, u p := by
  classical
  let f := fun t : Finset α => (-1:ℝ)^t.card * ∏ p ∈ t, u p
  have expand : (∏ p ∈ P, (1-u p)) = ∑ t ∈ P.powerset, f t := by
    simp only [sub_eq_add_neg, prod_one_add, f, prod_neg]
  have decomp := sum_filter_add_sum_filter_not (s := P.powerset) (fun t => t.card ≤ r) f
  have tail : ∑ t ∈ P.powerset with ¬t.card ≤ r, f t ≤
      Real.exp (-(r:ℝ)) * ∏ p ∈ P, (1+Real.exp 1*u p) := by
    rw [prod_one_add, mul_sum]
    apply (sum_le_sum _).trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) ?_)
    · intro t ht
      obtain ⟨htP, hrt⟩ := mem_filter.mp ht
      have hnon : 0 ≤ ∏ p ∈ t, u p := prod_nonneg fun p hp => hu p (mem_powerset.mp htP hp)
      calc f t ≤ ∏ p ∈ t, u p := mul_le_of_le_one_left hnon (by simpa using (le_abs_self ((-1:ℝ)^t.card)))
           _ ≤ Real.exp (-(r:ℝ)) * ∏ p ∈ t, (Real.exp 1*u p) := by
              rw [prod_mul_distrib, prod_const, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
              apply le_mul_of_one_le_left hnon
              apply Real.one_le_exp_iff.mpr
              have : r < t.card := by omega
              have hc : (r:ℝ) < t.card := by exact_mod_cast this
              linarith
    · intro t ht _
      exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun p hp =>
        mul_nonneg (Real.exp_pos _).le (hu p (mem_powerset.mp ht hp)))
  change _ ≤ ∑ t ∈ P.powerset with t.card ≤ r, f t
  rw [expand]
  linarith

end Erdos820Critical.Sieve

end

section

/- Combined from upper/sieve/Density.lean. -/

/- Harmonic and product estimates for the fixed-base sieve of Liam Price. -/
open Finset Real
namespace Erdos820Critical.Sieve

noncomputable def density (n p : ℕ) : ℝ := (roots n p : ℝ) / p

private theorem reciprocal_sum {Q : Finset ℕ} {n : ℕ} (hn : 0 < n) (hq : Q.card ≤ n)
    (j : ℕ → ℕ) (hj : ∀ p ∈ Q, 0 < j p) (hi : Set.InjOn j Q) :
    ∑ p ∈ Q, ((j p:ℝ))⁻¹ ≤ 2 + log n := by
  classical
  let A := Q.filter (fun p => j p ≤ n)
  let B := Q.filter (fun p => ¬j p ≤ n)
  have himg : A.image j ⊆ Icc 1 n := by
    intro k hk
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    obtain ⟨hq,hk⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨hj p hq,hk⟩
  have ha : ∑ p ∈ A, (j p:ℝ)⁻¹ ≤ 1+log n := calc
    _ = ∑ k ∈ A.image j, (k:ℝ)⁻¹ := (sum_image (fun p hp q hq h =>
      hi (mem_filter.mp hp).1 (mem_filter.mp hq).1 h)).symm
    _ ≤ ∑ k ∈ Icc 1 n, (k:ℝ)⁻¹ := sum_le_sum_of_subset_of_nonneg himg (by intros; positivity)
    _ ≤ _ := by simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log n
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hb : ∑ p ∈ B, (j p:ℝ)⁻¹ ≤ 1 := calc
    _ ≤ ∑ _p ∈ B, (n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro p hp
      apply inv_anti₀ hn'
      exact_mod_cast (le_of_lt (lt_of_not_ge (mem_filter.mp hp).2))
    _ = (B.card:ℝ)/n := by simp [div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hn').mpr (by exact_mod_cast (card_filter_le ..).trans hq)
  have hs := sum_filter_add_sum_filter_not (s := Q) (fun p => j p ≤ n) (fun p => (j p:ℝ)⁻¹)
  change (∑ p ∈ A, _) + (∑ p ∈ B, _) = _ at hs
  linarith

theorem density_sum {n : ℕ} (hn : 0 < n) (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p)
    (hcard : P.card ≤ n) :
    ∑ p ∈ P, density n p ≤ (n.divisors.card:ℝ) * (2+log n) := by
  classical
  let d := fun p => n.gcd (p-1)
  let j := fun p => (p-1)/d p
  have hd (p) : 0 < d p := Nat.gcd_pos_of_pos_left _ hn
  have hjd (p) : j p * d p = p-1 := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have hj (p) (h : p ∈ P) : 0 < j p := by
    have := (hp p h).two_le
    have := hjd p
    by_contra! hz
    rw [Nat.le_zero.mp hz, zero_mul] at this
    omega
  have maps (p) (_ : p ∈ P) : d p ∈ n.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left ..,hn.ne'⟩
  rw [← sum_fiberwise_of_maps_to maps]
  calc
    _ ≤ ∑ _a ∈ n.divisors, (2+log n) := by
      apply sum_le_sum
      intro a ha
      let Q := P.filter (fun p => d p = a)
      have sub : Q ⊆ P := filter_subset .. 
      have inj : Set.InjOn j Q := by
        intro p h q k he
        have hp' := (hp p (sub h)).two_le
        have hq' := (hp q (sub k)).two_le
        have e := hjd p
        rw [he, (mem_filter.mp h).2, ← (mem_filter.mp k).2, hjd] at e
        omega
      apply le_trans _ (reciprocal_sum hn ((card_le_card sub).trans hcard) j (fun p h => hj p (sub h)) inj)
      apply sum_le_sum
      intro p h
      have hpr := hp p (sub h)
      have hr := roots_prime_le hn.ne' hpr
      have he := hjd p
      have hp1 := hpr.two_le
      have he' : j p * d p ≤ p := he.le.trans (Nat.sub_le ..)
      have hm : (roots n p:ℝ) * (j p:ℝ) ≤ p := by
        exact_mod_cast (Nat.mul_le_mul_right (j p) hr).trans (by simpa [mul_comm] using he')
      rw [density, ← one_div]
      exact (div_le_div_iff₀ (by exact_mod_cast hpr.pos) (by exact_mod_cast hj p (sub h))).mpr (by simpa using hm)
    _ = _ := by simp [mul_add]

private theorem log_complement_small {u : ℝ} (hu : 0 ≤ u) (hh : u ≤ 1/2) :
    -2*u ≤ log (1-u) := by
  have hpos : 0 < 1-u := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [log_inv] at h
  have hk : (1-u)⁻¹ ≤ 1+2*u := by
    rw [← one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hh)]
  linarith

theorem product_lower {n : ℕ} (hn : 0 < n) (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) :
    exp (-(2*∑ p ∈ P, density n p) - n.divisors.card * log (n+1)) ≤
      ∏ p ∈ P, (1-density n p) := by
  classical
  let cost := fun p : ℕ => if p-1 ∣ n then log ((n:ℝ)+1) else 0
  have hlog : 0 ≤ log ((n:ℝ)+1) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hcost : ∑ p ∈ P, cost p ≤ (n.divisors.card:ℝ)*log (n+1) := by
    let A := P.filter (fun p => p-1 ∣ n)
    have hi : Set.InjOn (fun p : ℕ => p-1) A := by
      intro p h q k he
      have := (hp p (mem_filter.mp h).1).two_le
      have := (hp q (mem_filter.mp k).1).two_le
      dsimp at he
      omega
    have hA : A.image (fun p => p-1) ⊆ n.divisors := by
      intro a ha
      obtain ⟨p,h,rfl⟩ := mem_image.mp ha
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp h).2,hn.ne'⟩
    have hcard := card_le_card hA
    rw [card_image_of_injOn hi] at hcard
    change (∑ p ∈ P, if p-1 ∣ n then _ else _) ≤ _
    rw [← sum_filter]
    simpa using mul_le_mul_of_nonneg_right (show (A.card:ℝ) ≤ n.divisors.card by exact_mod_cast hcard) hlog
  have localBound p (h : p ∈ P) : exp (-(2*density n p) - cost p) ≤ 1-density n p := by
    have hpr := hp p h
    have hp2 := hpr.two_le
    have hr := roots_prime_le hn.ne' hpr
    let d := n.gcd (p-1)
    have hd : d ∣ p-1 := Nat.gcd_dvd_right .. 
    have hdle : d ≤ p-1 := Nat.le_of_dvd (by omega) hd
    have hpp : (0:ℝ) < p := by exact_mod_cast hpr.pos
    have hu : 0 ≤ density n p := by unfold density; positivity
    have hlt : density n p < 1 := (div_lt_one hpp).mpr (by exact_mod_cast (hr.trans_lt (show d < p by omega)))
    apply (le_log_iff_exp_le (by linarith : 0 < 1-density n p)).mp
    by_cases hf : p-1 ∣ n
    · have hpn : p ≤ n+1 := by have := Nat.le_of_dvd hn hf; omega
      have hr1 : roots n p + 1 ≤ p := by omega
      have hfrac : (p:ℝ)⁻¹ ≤ 1-density n p := by
        rw [density, ← one_div, le_sub_iff_add_le, ← add_div, div_le_one hpp]
        exact_mod_cast (by omega : 1+roots n p ≤ p)
      have hl := log_le_log (inv_pos.mpr hpp) hfrac
      rw [log_inv] at hl
      have hpl := log_le_log hpp (show (p:ℝ) ≤ (n:ℝ)+1 by exact_mod_cast hpn)
      simp only [cost, if_pos hf]
      linarith
    · have hne : d ≠ p-1 := by
        intro he
        have hdvd : d ∣ n := Nat.gcd_dvd_left .. 
        exact hf (he ▸ hdvd)
      have hh : 2*d ≤ p-1 := by
        obtain ⟨k,hk⟩ := hd
        have hk2 : 2 ≤ k := by
          by_contra! hz
          interval_cases k <;> simp_all
        nlinarith [Nat.mul_le_mul_left d hk2]
      have hs : density n p ≤ 1/2 := by
        apply (div_le_div_iff₀ hpp (by norm_num : (0:ℝ)<2)).mpr
        exact_mod_cast (by omega : roots n p * 2 ≤ 1*p)
      simpa [cost,hf] using log_complement_small hu hs
  apply le_trans _ (prod_le_prod (fun p _ => (exp_pos _).le) localBound)
  rw [← Real.exp_sum]
  apply exp_le_exp.mpr
  simp only [sum_sub_distrib, sum_neg_distrib, ← mul_sum]
  linarith

end Erdos820Critical.Sieve

end

section

/- Combined from upper/sieve/FiniteSieve.lean. -/

/- Transport of the independent residue model to a finite interval. The fixed-base
application and its mathematical sieve argument are due to Liam Price. -/
open Finset Real
namespace Erdos820Critical.Sieve

theorem intersection_error {n N : ℕ} (hn : 0 < n) {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p)
    {t : Finset ℕ} (ht : t ⊆ P) :
    |(((Ico 2 (2+N)).filter (fun x => t ⊆ P.filter (fun p => root n p x))).card:ℝ) -
      N * ∏ p ∈ t, ((roots n p:ℝ)/p)| ≤ (n:ℝ)^t.card := by
  classical
  have hprime : ∀ p ∈ t, Nat.Prime p := fun p h => hp p (ht h)
  have he : (Ico 2 (2+N)).filter (fun x => t ⊆ P.filter (fun p => root n p x)) =
      (Ico 2 (2+N)).filter (root n (∏ p ∈ t, p)) := by
    ext x
    simp only [mem_filter]
    apply and_congr_right
    intro hx
    rw [root_product_iff hprime (by have := (mem_Ico.mp hx).1; omega)]
    exact ⟨fun h p k => (mem_filter.mp (h k)).2, fun h p k => mem_filter.mpr ⟨ht k,h p k⟩⟩
  rw [he]
  have h := hits_error n (∏ p ∈ t, p) 2 N (modulus_pos hprime)
  rw [local_product hprime, Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib] at h
  apply h.trans
  rw [← prod_const]
  exact prod_le_prod (fun p _ => Nat.cast_nonneg _) fun p k => by
    exact_mod_cast (roots_prime_le hn.ne' (hprime p k)).trans (Nat.gcd_le_left _ hn)

theorem budget_bound {n r : ℕ} (P : Finset ℕ) (hc : P.card ≤ n) :
    ∑ t ∈ shortSets P r, (n:ℝ)^t.card ≤ ((r:ℝ)+1) * ((n:ℝ)+1)^(2*r) := by
  rw [short_sum]
  calc
    _ ≤ ∑ _j ∈ range (r+1), ((n:ℝ)+1)^(2*r) := by
      apply sum_le_sum
      intro j hj
      have hj' : j ≤ r := by simpa using mem_range.mp hj
      calc
        _ = (P.card.choose j:ℝ) * (n:ℝ)^j := by
          trans ∑ _ ∈ P.powersetCard j, (n:ℝ)^j
          · exact sum_congr rfl fun t h => by rw [(mem_powersetCard.mp h).2]
          · simp
        _ ≤ ((n:ℝ)+1)^j * ((n:ℝ)+1)^j := by
          gcongr
          · exact_mod_cast (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega : P.card ≤ n+1) _)
          · linarith
        _ = ((n:ℝ)+1)^(2*j) := by rw [two_mul,pow_add]
        _ ≤ _ := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by omega)
    _ = _ := by simp

theorem exists_survivor {n N r : ℕ} (hn : 0 < n) (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p)
    (hc : P.card ≤ n) (hr : Odd r)
    (u : ℕ → ℝ) (hu : ∀ p ∈ P, u p = (roots n p:ℝ)/p)
    (hsize : ((r:ℝ)+1) * ((n:ℝ)+1)^(2*r) < N * ((∏ p ∈ P, (1-u p)) -
      Real.exp (-(r:ℝ)) * (∏ p ∈ P, (1+Real.exp 1*u p)))) :
    ∃ x ∈ Ico 2 (2+N), ∀ p ∈ P, ¬root n p x := by
  classical
  let I := Ico 2 (2+N)
  let B := fun x => P.filter (fun p => root n p x)
  have hm := model_lower P u (fun p h => by rw [hu p h]; positivity) r
  by_contra! h
  have covered (x) (hx : x ∈ I) : (B x).Nonempty := by
    obtain ⟨p,hp,hx⟩ := h x hx
    exact ⟨p,mem_filter.mpr ⟨hp,hx⟩⟩
  have ha := covered_upper P I B r hr (fun _ _ => filter_subset ..) covered
  have he : (N:ℝ) * (∑ t ∈ shortSets P r, (-1:ℝ)^t.card * ∏ p ∈ t, u p) ≤
      (∑ t ∈ shortSets P r, (-1:ℝ)^t.card * ((I.filter (fun x => t ⊆ B x)).card : ℝ)) +
      ∑ t ∈ shortSets P r, (n:ℝ)^t.card := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro t ht
    have ht' := mem_powerset.mp (mem_filter.mp ht).1
    have hprod := prod_congr rfl (fun p (k : p ∈ t) => hu p (ht' k))
    rw [hprod]
    have herr := abs_le.mp (intersection_error (N := N) hn hp ht')
    change -_ ≤ ((I.filter (fun x => t ⊆ B x)).card:ℝ) - _ ∧ _ ≤ _ at herr
    rcases Nat.even_or_odd t.card with hh|hh
    · rw [hh.neg_one_pow]
      linarith
    · rw [hh.neg_one_pow]
      linarith
  linarith [budget_bound (r := r) P hc, mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) N)]

end Erdos820Critical.Sieve

end

section

/- Combined from upper/sieve/FixedBase.lean. -/

/- An independently implemented quantitative version of Liam Price's fixed-base
upper bound for Erdős problem 820. -/
open Finset Real Filter
namespace Erdos820Critical.Sieve

theorem log_K_bound {n : ℕ} (hn : 1 ≤ n) :
    log (Erdos820.K n : ℝ) ≤ 128 * n.divisors.card * (1+log n)^2 := by
  classical
  let P := (2^n-1 : ℕ).primeFactors
  let u := density n
  let L := log ((n:ℝ)+1)
  let τ : ℝ := n.divisors.card
  let A := τ * (2+L)
  let r := 2 * ⌈4*A⌉₊ + 1
  let Y := 1+3*A+(r:ℝ)*(1+2*L)
  let N := ⌈exp Y⌉₊
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hL : 0 ≤ L := log_nonneg (by linarith)
  have hτ : 1 ≤ τ := by
    have : 0 < n.divisors.card := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr (by omega)⟩
    dsimp [τ]
    exact_mod_cast (show 1 ≤ n.divisors.card from this)
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [mul_nonneg (by linarith : 0 ≤ τ) hL]
  have hr : Odd r := ⟨_,rfl⟩
  have hr' : (r:ℝ) = 2*(⌈4*A⌉₊:ℝ)+1 := by simp [r]
  have hrlo : 8*A ≤ (r:ℝ) := by linarith [Nat.le_ceil (4*A)]
  have hrhi : (r:ℝ) ≤ 8*A+3 := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ 4*A)]
  have hpr : ∀ p ∈ P, Nat.Prime p := fun _ h => Nat.prime_of_mem_primeFactors h
  have hc : P.card ≤ n := prime_count hn
  have hu p (h : p ∈ P) : 0 ≤ u p := by unfold u density; positivity
  have hS : (∑ p ∈ P, u p) ≤ A := by
    apply (density_sum hn P hpr hc).trans
    dsimp [A,τ,L]
    gcongr
    linarith
  have hV : exp (-3*A) ≤ ∏ p ∈ P, (1-u p) := by
    apply le_trans _ (product_lower hn P hpr)
    apply exp_le_exp.mpr
    change -3*A ≤ -(2*∑ p ∈ P, u p) - τ*L
    have hτL : τ*L ≤ A := by dsimp [A]; nlinarith
    linarith
  have hW : (∏ p ∈ P, (1+exp 1*u p)) ≤ exp (3*A) := calc
    _ ≤ ∏ p ∈ P, exp (exp 1*u p) := by
      apply Finset.prod_le_prod
      · intro p hp
        linarith [mul_nonneg (exp_pos 1).le (hu p hp)]
      · intro p hp
        linarith [Real.add_one_le_exp (exp 1*u p)]
    _ = exp (exp 1*∑ p ∈ P, u p) := by rw [← exp_sum, mul_sum]
    _ ≤ _ := exp_le_exp.mpr (mul_le_mul Real.exp_one_lt_three.le hS
      (sum_nonneg hu) (by norm_num))
  have tail : exp (-(r:ℝ)) * (∏ p ∈ P, (1+exp 1*u p)) ≤ exp (-3*A)/2 := calc
    _ ≤ exp (-(r:ℝ))*exp (3*A) := mul_le_mul_of_nonneg_left hW (exp_pos _).le
    _ = exp (-(r:ℝ)+3*A) := (exp_add ..).symm
    _ ≤ exp (-3*A-1) := exp_le_exp.mpr (by linarith)
    _ = exp (-3*A)/exp 1 := exp_sub .. 
    _ ≤ _ := by gcongr; exact exp_one_gt_two.le
  have hbudget : ((r:ℝ)+1)*((n:ℝ)+1)^(2*r) ≤ exp ((r:ℝ)*(1+2*L)) := by
    have hpow : ((n:ℝ)+1)^(2*r) = exp (2*(r:ℝ)*L) := by
      rw [← exp_log (by positivity : 0 < ((n:ℝ)+1)^(2*r)), log_pow]
      push_cast
      rfl
    rw [hpow, show (r:ℝ)*(1+2*L) = r+2*r*L by ring, exp_add]
    gcongr
    exact add_one_le_exp _
  have hpos : exp ((r:ℝ)*(1+2*L)) < exp Y * (exp (-3*A)/2) := by
    rw [← mul_div_assoc, ← exp_add, lt_div_iff₀ (by norm_num : (0:ℝ)<2)]
    have hY : Y+ -3*A = (r:ℝ)*(1+2*L)+1 := by dsimp [Y]; ring
    rw [hY, exp_add]
    exact mul_lt_mul_of_pos_left exp_one_gt_two (exp_pos _)
  have hN : exp Y ≤ (N:ℝ) := Nat.le_ceil _
  obtain ⟨x,hx,hgood⟩ := exists_survivor hn P hpr hc hr u (fun _ _ => rfl)
    (hbudget.trans_lt (hpos.trans_le (mul_le_mul hN (by linarith only [hV,tail])
      (by positivity) (Nat.cast_nonneg N))))
  obtain ⟨hx2,hxN⟩ := mem_Ico.mp hx
  have hk : Erdos820.K n ≤ x := Nat.sInf_le ⟨hx2,coprime_of_survivor hn hx2 hgood⟩
  have hY0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hEY : 1 ≤ exp Y := one_le_exp_iff.mpr hY0
  have hK : (Erdos820.K n:ℝ) ≤ exp (Y+2) := by
    have hx' : (Erdos820.K n:ℝ) ≤ (N:ℝ)+1 := by exact_mod_cast (by omega : Erdos820.K n ≤ N+1)
    have hnceil : (N:ℝ) < exp Y+1 := Nat.ceil_lt_add_one (exp_pos _).le
    rw [exp_add]
    nlinarith [add_one_le_exp (2:ℝ), mul_nonneg (sub_nonneg.mpr hEY)
      (sub_nonneg.mpr (show 3 ≤ exp (2:ℝ) by linarith [add_one_le_exp (2:ℝ)]))]
  have hlog : log (Erdos820.K n : ℝ) ≤ Y+2 := by
    by_cases he : Erdos820.K n = 0
    · simp [he]; linarith
    · exact (log_le_iff_le_exp (by exact_mod_cast Nat.pos_of_ne_zero he)).mpr hK
  let D := 1+log (n:ℝ)
  have hD : 1 ≤ D := by dsimp [D]; linarith [log_nonneg hn']
  have hLD : L ≤ D := by
    have h := log_le_log (by positivity : (0:ℝ)<n+1) (by linarith : (n:ℝ)+1 ≤ 2*n)
    rw [log_mul (by norm_num) hn0.ne'] at h
    dsimp [D,L]
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hTD : 1 ≤ τ*D := one_le_mul_of_one_le_of_one_le hτ hD
  have hAD : A ≤ 3*(τ*D) := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 2+L ≤ 3*D) (by linarith : 0 ≤ τ)]
  have hRD : (r:ℝ) ≤ 27*(τ*D) := by linarith
  have hterm := mul_le_mul hRD (show 1+2*L ≤ 3*D by linarith)
    (by linarith : 0 ≤ 1+2*L) (by linarith : 0 ≤ 27*(τ*D))
  apply hlog.trans
  change Y+2 ≤ 128*τ*D^2
  dsimp [Y]
  nlinarith [mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ τ*D)]

theorem eventual_log_K : ∀ᶠ n : ℕ in atTop,
    log (Erdos820.K n : ℝ) ≤ 128 * n.divisors.card * (1+log n)^2 :=
  (eventually_ge_atTop 1).mono fun _ => log_K_bound

end Erdos820Critical.Sieve

end

section

/- Combined from identity/Average.lean. -/

/- Finite averaging over the smaller base in the arithmetic-exponent argument. -/

open Finset
open Erdos820Critical.Sieve

namespace Erdos820Identity

/-- The number of shifted prime divisors of a positive integer. -/
def W (m : ℕ) : ℕ :=
  ((range (m + 2)).filter fun p => p.Prime ∧ p - 1 ∣ m).card

/-- The maximum shifted-prime count among the first n.divisors.card multiples. -/
def M (n : ℕ) : ℕ :=
  (Icc 1 n.divisors.card).sup fun j => W (j * n)

private theorem divisorCount_pos {n : ℕ} (hn : 0 < n) : 0 < n.divisors.card :=
  card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn.ne'⟩⟩

theorem W_le_M {n : ℕ} (hn : 0 < n) : W n ≤ M n := by
  have h : 1 ∈ Icc 1 n.divisors.card := mem_Icc.mpr ⟨le_rfl, divisorCount_pos hn⟩
  simpa [M] using (le_sup (f := fun j => W (j * n)) h)

private noncomputable def rootWeight (n p : ℕ) : ℝ := (n.gcd (p - 1) : ℝ) / p
private def primeIndex (n p : ℕ) : ℕ := (p - 1) / n.gcd (p - 1)

private theorem rootWeight_nonneg (n p : ℕ) : 0 ≤ rootWeight n p := by
  unfold rootWeight
  positivity

private theorem index_mul (n p : ℕ) : primeIndex n p * n.gcd (p - 1) = p - 1 :=
  Nat.div_mul_cancel (Nat.gcd_dvd_right n (p - 1))

private theorem index_pos {n p : ℕ} (hp : p.Prime) : 0 < primeIndex n p := by
  by_contra! h
  have hm := index_mul n p
  rw [Nat.eq_zero_of_le_zero h, zero_mul] at hm
  have := hp.two_le
  omega

private theorem rootWeight_le_invIndex {n p : ℕ} (hp : p.Prime) :
    rootWeight n p ≤ 1 / (primeIndex n p : ℝ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hj' : (0 : ℝ) < primeIndex n p := by exact_mod_cast index_pos (n := n) hp
  have hm : (primeIndex n p : ℝ) * (n.gcd (p - 1) : ℝ) = (p : ℝ) - 1 := by
    have hf := congrArg (fun t : ℕ => (t : ℝ)) (index_mul n p)
    have := hp.two_le
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one] using hf
  unfold rootWeight
  apply (div_le_div_iff₀ hp' hj').mpr
  rw [mul_comm _ (primeIndex n p : ℝ), hm, one_mul]
  linarith

private theorem indexFiber_card_le_W {P : Finset ℕ} (hp : ∀ p ∈ P, p.Prime)
    {n j : ℕ} (hn : 0 < n) (hj : 0 < j) :
    (P.filter fun p => primeIndex n p = j).card ≤ W (j * n) := by
  apply card_le_card
  intro p h
  obtain ⟨hpP, hpj⟩ := mem_filter.mp h
  have hprime := hp p hpP
  have hpd : p - 1 ∣ j * n := by
    rw [← index_mul n p, hpj]
    exact Nat.mul_dvd_mul_left j (Nat.gcd_dvd_left n (p - 1))
  have := Nat.le_of_dvd (Nat.mul_pos hj hn) hpd
  have := hprime.two_le
  exact mem_filter.mpr ⟨mem_range.mpr (by omega), hprime, hpd⟩

private theorem indexFiber_card_le_divisors {n : ℕ} {P : Finset ℕ} (hn : 0 < n)
    (hp : ∀ p ∈ P, p.Prime) (j : ℕ) :
    (P.filter fun p => primeIndex n p = j).card ≤ n.divisors.card := by
  apply card_le_card_of_injOn (fun p => n.gcd (p - 1))
  · intro p _
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n (p - 1), hn.ne'⟩
  · intro p hp' q hq' h
    obtain ⟨hpP, hpj⟩ := mem_filter.mp hp'
    obtain ⟨hqP, hqj⟩ := mem_filter.mp hq'
    have hmp := index_mul n p
    have hmq := index_mul n q
    change n.gcd (p - 1) = n.gcd (q - 1) at h
    rw [hpj, h] at hmp
    rw [hqj] at hmq
    have := (hp p hpP).two_le
    have := (hp q hqP).two_le
    omega

/-- The reciprocal squares in a finite tail are bounded by telescoping. -/
private theorem invSquares_tail (k b : ℕ) (hk : 2 ≤ k) :
    (∑ j ∈ Ico k b, 1 / (j : ℝ)^2) ≤ 1 / ((k : ℝ) - 1) := by
  suffices ∀ b : ℕ, k ≤ b →
      (∑ j ∈ Ico k b, 1 / (j : ℝ)^2) ≤ 1 / ((k : ℝ) - 1) - 1 / ((b : ℝ) - 1) by
    by_cases hb : k ≤ b
    · have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
      exact (this b hb).trans (sub_le_self _ (by positivity))
    · rw [Ico_eq_empty (by omega : ¬ k < b), sum_empty]
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      positivity
  intro b
  induction b with
  | zero => omega
  | succ b ih =>
    intro hb
    by_cases hkb : k ≤ b
    · rw [sum_Ico_succ_top hkb]
      have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
      have hs : 1 / (b : ℝ)^2 ≤ 1 / ((b : ℝ) - 1) - 1 / (b : ℝ) := by
        have hb0 : (0 : ℝ) < b := by linarith
        have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
        field_simp
        nlinarith
      rw [Nat.cast_succ, add_sub_cancel_right]
      linarith [ih hkb]
    · have h : b + 1 = k := by omega
      rw [h, Ico_self, sum_empty, sub_self]

private theorem invSquares_head (b : ℕ) (hb : 1 < b) :
    (∑ j ∈ Ico 1 b, 1 / (j : ℝ)^2) ≤ 2 := by
  rw [sum_eq_sum_Ico_succ_bot hb]
  norm_num
  have h := invSquares_tail 2 b (by decide)
  norm_num at h
  linarith

/-- Group the small primes by their index, using the shifted-prime count on the
head and the divisor count on the tail. -/
private theorem smallPrimeSquares_le {n X : ℕ} (hn : 0 < n)
    (hJX : n.divisors.card ≤ X) :
    (∑ p ∈ (range (X + 1)).filter Nat.Prime, rootWeight n p ^ 2) ≤
      2 * (M n : ℝ) + 1 := by
  let P := (range (X + 1)).filter Nat.Prime
  let J := n.divisors.card
  have hJ : 0 < J := divisorCount_pos hn
  have hp : ∀ p ∈ P, p.Prime := fun p h => (mem_filter.mp h).2
  have hmap : ∀ p ∈ P, primeIndex n p ∈ Ico 1 (X + 1) := by
    intro p h
    have hlt : p < X + 1 := mem_range.mp (mem_filter.mp h).1
    have hj := Nat.div_le_self (p - 1) (n.gcd (p - 1))
    exact mem_Ico.mpr ⟨index_pos (hp p h), by unfold primeIndex; omega⟩
  change (∑ p ∈ P, rootWeight n p ^ 2) ≤ _
  let F (j : ℕ) := ∑ p ∈ P with primeIndex n p = j, rootWeight n p ^ 2
  rw [← sum_fiberwise_of_maps_to hmap, ← sum_Ico_consecutive _ (by omega : 1 ≤ J + 1)
    (Nat.succ_le_succ hJX)]
  change (∑ j ∈ Ico 1 (J + 1), F j) + (∑ j ∈ Ico (J + 1) (X + 1), F j) ≤ _
  have hf (j K : ℕ) (hK : (P.filter fun p => primeIndex n p = j).card ≤ K) :
      F j ≤ (K : ℝ) * (1 / (j : ℝ)^2) := by
    calc
      F j ≤ ∑ p ∈ P with primeIndex n p = j, 1 / (j : ℝ)^2 := by
        apply sum_le_sum
        intro p h
        obtain ⟨hpP, hj⟩ := mem_filter.mp h
        have hu := rootWeight_le_invIndex (n := n) (hp p hpP)
        rw [hj] at hu
        simpa only [div_pow, one_pow] using pow_le_pow_left₀ (rootWeight_nonneg n p) hu 2
      _ = ((P.filter fun p => primeIndex n p = j).card : ℝ) * (1 / (j : ℝ)^2) := by
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (by positivity)
  have hhead : (∑ j ∈ Ico 1 (J + 1), F j) ≤ 2 * (M n : ℝ) := calc
    _ ≤ ∑ j ∈ Ico 1 (J + 1), (M n : ℝ) * (1 / (j : ℝ)^2) := by
      apply sum_le_sum
      intro j hj
      have hmem := mem_Ico.mp hj
      have hj' : j ∈ Icc 1 n.divisors.card := mem_Icc.mpr ⟨hmem.1, Nat.le_of_lt_succ hmem.2⟩
      exact hf j (M n) ((indexFiber_card_le_W hp hn hmem.1).trans
        (le_sup (f := fun j => W (j * n)) hj'))
    _ = (M n : ℝ) * (∑ j ∈ Ico 1 (J + 1), 1 / (j : ℝ)^2) := (mul_sum ..).symm
    _ ≤ _ := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left (invSquares_head _ (by omega)) (by positivity)
  have htail : (∑ j ∈ Ico (J + 1) (X + 1), F j) ≤ 1 := calc
    _ ≤ ∑ j ∈ Ico (J + 1) (X + 1), (J : ℝ) * (1 / (j : ℝ)^2) :=
      sum_le_sum fun j _ => hf j J (indexFiber_card_le_divisors hn hp j)
    _ = (J : ℝ) * (∑ j ∈ Ico (J + 1) (X + 1), 1 / (j : ℝ)^2) := (mul_sum ..).symm
    _ ≤ (J : ℝ) * (1 / (J : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
        invSquares_tail (J + 1) (X + 1) (by omega)
    _ = 1 := by
      have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
      field_simp
  exact add_le_add hhead htail

/-- The count of hits in the interval is at most twice its unrounded density. -/
private theorem hitCount_le {n p X : ℕ} (hn : 0 < n) (hp : p.Prime) (hpX : p ≤ X) :
    (hits n p 2 X : ℝ) ≤ 2 * (X : ℝ) * rootWeight n p := by
  have herror := (abs_le.mp (hits_error n p 2 X hp.pos)).2
  have hroots : (roots n p : ℝ) ≤ (n.gcd (p - 1) : ℝ) := by
    exact_mod_cast roots_prime_le hn.ne' hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hXp : (p : ℝ) ≤ X := by exact_mod_cast hpX
  have hXnonneg : (0 : ℝ) ≤ X := by positivity
  have hle := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hroots hp'.le) hXnonneg
  have hd : (n.gcd (p - 1) : ℝ) ≤ (X : ℝ) * rootWeight n p := by
    unfold rootWeight
    calc
      _ = (p : ℝ) * ((n.gcd (p - 1) : ℝ) / p) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hXp (by positivity)
  unfold rootWeight at hd ⊢
  linarith

private theorem powerSubOne_pos {a n : ℕ} (ha : 2 ≤ a) (hn : 0 < n) :
    0 < a^n - 1 :=
  Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) hn.ne')

private theorem smallPrimeSum_exists {n X : ℕ} (hn : 0 < n) (hJX : n.divisors.card ≤ X) :
    ∃ a ∈ Ico 2 (2 + X),
      (∑ p ∈ (a^n - 1).primeFactors with p ≤ X, rootWeight n p) ≤
        2 * (2 * (M n : ℝ) + 1) := by
  let A := Ico 2 (2 + X)
  let P := (range (X + 1)).filter Nat.Prime
  let B : ℝ := 2 * (2 * (M n : ℝ) + 1)
  have hX : 0 < X := (divisorCount_pos hn).trans_le hJX
  have hAcard : A.card = X := by simp [A, Nat.card_Ico, Nat.add_comm 2 X]
  have hA : A.Nonempty := card_pos.mp (hAcard.symm ▸ hX)
  have hsum : (∑ a ∈ A, ∑ p ∈ (a^n - 1).primeFactors with p ≤ X, rootWeight n p) ≤
      ∑ _a ∈ A, B := calc
    _ = ∑ a ∈ A, ∑ p ∈ P, if root n p a then rootWeight n p else 0 := by
      apply sum_congr rfl
      intro a ha
      have ha' : 2 ≤ a := (mem_Ico.mp ha).1
      rw [← sum_filter]
      congr 1
      ext p
      simp only [P, mem_filter, mem_range,
        Nat.mem_primeFactors_of_ne_zero (powerSubOne_pos ha' hn).ne',
        root_iff_dvd (by omega : 1 ≤ a)]
      constructor
      · rintro ⟨⟨hp, hdiv⟩, hpX⟩
        exact ⟨⟨Nat.lt_succ_of_le hpX, hp⟩, hdiv⟩
      · rintro ⟨⟨hpX, hp⟩, hdiv⟩
        exact ⟨⟨hp, hdiv⟩, Nat.le_of_lt_succ hpX⟩
    _ = ∑ p ∈ P, (hits n p 2 X : ℝ) * rootWeight n p := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      rw [← sum_filter]
      simp [A, hits]
    _ ≤ ∑ p ∈ P, (2 * (X : ℝ)) * rootWeight n p ^ 2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpX, hp'⟩ := mem_filter.mp hp
      have hhit := hitCount_le hn hp' (Nat.le_of_lt_succ (mem_range.mp hpX))
      calc
        _ ≤ (2 * (X : ℝ) * rootWeight n p) * rootWeight n p :=
          mul_le_mul_of_nonneg_right hhit (rootWeight_nonneg n p)
        _ = _ := by ring
    _ = (2 * (X : ℝ)) * (∑ p ∈ P, rootWeight n p ^ 2) := (mul_sum ..).symm
    _ ≤ (2 * (X : ℝ)) * (2 * (M n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (smallPrimeSquares_le hn hJX) (by positivity)
    _ = _ := by simp [B, hAcard]; ring
  exact exists_le_of_sum_le hA hsum

/-- The product of the large prime factors fits inside the power difference. -/
private theorem largePrimeSum_le {n a : ℕ} (hn : 3 ≤ n) (ha : 2 ≤ a)
    (haX : a ≤ n^3 + 1) :
    (∑ p ∈ (a^n - 1).primeFactors with ¬p ≤ n^3, rootWeight n p) ≤ 2 := by
  let X := n^3
  let m := a^n - 1
  let P := m.primeFactors.filter fun p => ¬p ≤ X
  have hn0 : 0 < n := by omega
  have hm : 0 < m := powerSubOne_pos ha hn0
  have hX : 1 < X := one_lt_pow₀ (by omega) (by decide)
  have haX2 : a ≤ X^2 := calc
    a ≤ X + 1 := haX
    _ ≤ X * 2 := by omega
    _ ≤ X^2 := by rw [pow_two]; exact Nat.mul_le_mul_left X (by omega)
  have hprod : X^P.card ≤ X^(2*n) := calc
    _ = ∏ _p ∈ P, X := by simp
    _ ≤ ∏ p ∈ P, p := prod_le_prod' fun p hp => (not_le.mp (mem_filter.mp hp).2).le
    _ ≤ ∏ p ∈ m.primeFactors, p := prod_le_prod_of_subset_of_one_le'
      (filter_subset _ _) fun p hp _ => (Nat.prime_of_mem_primeFactors hp).pos
    _ ≤ m := Nat.le_of_dvd hm m.prod_primeFactors_dvd
    _ ≤ a^n := Nat.sub_le ..
    _ ≤ (X^2)^n := Nat.pow_le_pow_left haX2 _
    _ = _ := (pow_mul ..).symm
  have hcard : P.card ≤ 2*n := (Nat.pow_le_pow_iff_right hX).mp hprod
  have hX' : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  change (∑ p ∈ P, rootWeight n p) ≤ _
  calc
    _ ≤ ∑ _p ∈ P, (n : ℝ) / X := by
      apply sum_le_sum
      intro p hp
      have hpp := not_le.mp (mem_filter.mp hp).2
      have hXp : (X : ℝ) ≤ p := by exact_mod_cast hpp.le
      have hd : (n.gcd (p - 1) : ℝ) ≤ n := by
        exact_mod_cast Nat.le_of_dvd hn0 (Nat.gcd_dvd_left n (p - 1))
      unfold rootWeight
      exact (div_le_div_of_nonneg_right hd
        (hX'.le.trans hXp)).trans (div_le_div_of_nonneg_left (by positivity) hX' hXp)
    _ = (P.card : ℝ) * ((n : ℝ) / X) := by simp
    _ ≤ (2 * (n : ℝ)) * ((n : ℝ) / X) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hX']
      dsimp [X]
      rw [Nat.cast_pow]
      nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sq_nonneg (n : ℝ))]

/-- Some base in the first n³ candidates has bounded total root weight. -/
theorem exists_base_sum_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a ≤ n^3 + 1 ∧
      (∑ p ∈ (a^n - 1).primeFactors, (n.gcd (p - 1) : ℝ) / p) ≤
        4 * (1 + (M n : ℝ)) := by
  have hn0 : 0 < n := by omega
  have hJX : n.divisors.card ≤ n^3 := (Nat.card_divisors_le_self n).trans
    (by simpa using (Nat.pow_le_pow_right hn0 (show 1 ≤ 3 by decide)))
  obtain ⟨a, ha, hsmall⟩ := smallPrimeSum_exists hn0 hJX
  obtain ⟨ha2, haX⟩ := mem_Ico.mp ha
  have haX' : a ≤ n^3 + 1 := by omega
  refine ⟨a, ha2, haX', ?_⟩
  change (∑ p ∈ (a^n - 1).primeFactors, rootWeight n p) ≤ _
  rw [← sum_filter_add_sum_filter_not _ (fun p => p ≤ n^3)]
  linarith [largePrimeSum_le hn ha2 haX']

end Erdos820Identity

end

section

/- Combined from identity/SieveBound.lean. -/

/- A quantitative bound for an arbitrary base in the Erdős 820 sieve. -/

open Finset Real

namespace Erdos820Critical.Sieve

private theorem base_prime_count {n a : ℕ} (hn : 3 ≤ n) (ha : 2 ≤ a)
    (ha' : a ≤ n^3+1) : (a^n-1).primeFactors.card ≤ n^3 := by
  have hm : 0 < a^n-1 := Nat.sub_pos_of_lt (one_lt_pow₀ (by omega : 1 < a) (by omega))
  have hbase : a ≤ (2^n : ℕ)^3 := calc
    a ≤ (n+1)^3 := by nlinarith
    _ ≤ (2^n)^3 := Nat.pow_le_pow_left (Nat.succ_le_of_lt n.lt_two_pow_self) _
  have hexp : 3*n*n ≤ n^3 := calc
    3*n*n ≤ n*n*n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right n hn)
    _ = _ := by ring
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  calc
    2^(a^n-1).primeFactors.card = ∏ _p ∈ (a^n-1).primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ (a^n-1).primeFactors, p :=
      prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ a^n-1 := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd _)
    _ ≤ a^n := Nat.sub_le ..
    _ ≤ ((2^n)^3)^n := Nat.pow_le_pow_left hbase _
    _ = 2^(3*n*n) := by rw [← pow_mul, ← pow_mul]; ring_nf
    _ ≤ 2^(n^3) := Nat.pow_le_pow_right (by decide) hexp

private theorem product_lower_gcd {n : ℕ} (hn : 0 < n) (P : Finset ℕ)
    (hp : ∀ p ∈ P, Nat.Prime p) :
    exp (-(2+2*log ((n:ℝ)+1)) * ∑ p ∈ P, (n.gcd (p-1):ℝ)/p) ≤
      ∏ p ∈ P, (1-density n p) := by
  let L := log ((n:ℝ)+1)
  let v := fun p : ℕ => (n.gcd (p-1):ℝ)/p
  have hL : 0 ≤ L := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  change exp (-(2+2*L) * ∑ p ∈ P, v p) ≤ _
  rw [mul_sum, exp_sum]
  apply prod_le_prod (fun _ _ => (exp_pos _).le)
  intro p hmem
  have hpr := hp p hmem
  have hp2 := hpr.two_le
  have hp0 : (0:ℝ) < p := by exact_mod_cast hpr.pos
  let d := n.gcd (p-1)
  have hd : d ∣ p-1 := Nat.gcd_dvd_right ..
  have hdle : d ≤ p-1 := Nat.le_of_dvd (by omega) hd
  have hv0 : 0 ≤ v p := by dsimp [v]; positivity
  have hv1 : v p < 1 := (div_lt_one hp0).mpr (by exact_mod_cast (show d < p by omega))
  have hdom : density n p ≤ v p :=
    div_le_div_of_nonneg_right (by exact_mod_cast roots_prime_le hn.ne' hpr) hp0.le
  apply le_trans _ (sub_le_sub_left hdom 1)
  apply (le_log_iff_exp_le (sub_pos.mpr hv1)).mp
  by_cases hf : p-1 ∣ n
  · have hdf : d = p-1 := Nat.gcd_eq_right hf
    have hpn : p ≤ n+1 := by have := Nat.le_of_dvd hn hf; omega
    have hhalf : 1/2 ≤ v p := by
      apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<2) hp0).mpr
      change 1 * (p:ℝ) ≤ (d:ℝ) * 2
      exact_mod_cast (show 1 * p ≤ d * 2 by omega)
    have hfrac : (p:ℝ)⁻¹ ≤ 1-v p := by
      change (p:ℝ)⁻¹ ≤ 1-(d:ℝ)/p
      rw [← one_div, le_sub_iff_add_le, ← add_div, div_le_one hp0]
      exact_mod_cast (show 1+d ≤ p by omega)
    have hlog := log_le_log (inv_pos.mpr hp0) hfrac
    rw [log_inv] at hlog
    have hpl : log (p:ℝ) ≤ L :=
      log_le_log hp0 (by exact_mod_cast hpn)
    nlinarith [mul_nonneg hL (sub_nonneg.mpr hhalf)]
  · have hne : d ≠ p-1 := by
      intro he
      have hdvd : d ∣ n := Nat.gcd_dvd_left ..
      exact hf (he ▸ hdvd)
    obtain ⟨k,hk⟩ := hd
    have hk2 : 2 ≤ k := by
      by_contra! hz
      interval_cases k <;> simp_all
    have hhalf : v p ≤ 1/2 := by
      apply (div_le_div_iff₀ hp0 (by norm_num : (0:ℝ)<2)).mpr
      change (d:ℝ) * 2 ≤ 1 * (p:ℝ)
      exact_mod_cast (show d * 2 ≤ 1 * p from
        (Nat.mul_le_mul_left d hk2).trans (by omega))
    have hinv : (1-v p)⁻¹ ≤ 1+2*v p := by
      rw [← one_div, div_le_iff₀ (sub_pos.mpr hv1)]
      nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hhalf)]
    have hlog := log_le_sub_one_of_pos (inv_pos.mpr (sub_pos.mpr hv1))
    rw [log_inv] at hlog
    nlinarith [mul_nonneg hL hv0]

-- The same periodic residue count works with an arbitrary left endpoint.
private theorem intersection_error_from {n b N : ℕ} (hn : 0 < n) (hb : 1 ≤ b)
    {P : Finset ℕ} (hp : ∀ p ∈ P, Nat.Prime p) {t : Finset ℕ} (ht : t ⊆ P) :
    |(((Ico b (b+N)).filter (fun x => t ⊆ P.filter (fun p => root n p x))).card:ℝ) -
      N * ∏ p ∈ t, density n p| ≤ (n:ℝ)^t.card := by
  classical
  have htprime : ∀ p ∈ t, Nat.Prime p := fun p h => hp p (ht h)
  have he : (Ico b (b+N)).filter (fun x => t ⊆ P.filter (fun p => root n p x)) =
      (Ico b (b+N)).filter (root n (∏ p ∈ t, p)) := by
    ext x
    simp only [mem_filter]
    apply and_congr_right
    intro hx
    rw [root_product_iff htprime (hb.trans (mem_Ico.mp hx).1)]
    exact ⟨fun h p k => (mem_filter.mp (h k)).2, fun h p k => mem_filter.mpr ⟨ht k,h p k⟩⟩
  rw [he]
  have h := hits_error n (∏ p ∈ t, p) b N (modulus_pos htprime)
  rw [local_product htprime, Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib] at h
  change |(hits n (∏ p ∈ t, p) b N : ℝ) - N * ∏ p ∈ t, density n p| ≤ _
  apply h.trans
  rw [← prod_const]
  exact prod_le_prod (fun p _ => Nat.cast_nonneg _) fun p k => by
    exact_mod_cast (roots_prime_le hn.ne' (htprime p k)).trans (Nat.gcd_le_left _ hn)

private theorem exists_survivor_from {n b N r : ℕ} (hn : 0 < n) (hb : 1 ≤ b)
    (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) (hr : Odd r)
    (hsize : ∑ t ∈ shortSets P r, (n:ℝ)^t.card < N *
      ((∏ p ∈ P, (1-density n p)) - exp (-(r:ℝ)) *
        (∏ p ∈ P, (1+exp 1*density n p)))) :
    ∃ x ∈ Ico b (b+N), ∀ p ∈ P, ¬root n p x := by
  classical
  let I := Ico b (b+N)
  let B := fun x => P.filter (fun p => root n p x)
  let u := density n
  have hm := model_lower P u (fun p _ => by unfold u density; positivity) r
  by_contra! h
  have covered (x) (hx : x ∈ I) : (B x).Nonempty := by
    obtain ⟨p,hp,hx⟩ := h x hx
    exact ⟨p,mem_filter.mpr ⟨hp,hx⟩⟩
  have ha := covered_upper P I B r hr (fun _ _ => filter_subset ..) covered
  have he : (N:ℝ) * (∑ t ∈ shortSets P r, (-1:ℝ)^t.card * ∏ p ∈ t, u p) ≤
      (∑ t ∈ shortSets P r, (-1:ℝ)^t.card * ((I.filter (fun x => t ⊆ B x)).card : ℝ)) +
      ∑ t ∈ shortSets P r, (n:ℝ)^t.card := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro t ht
    have ht' := mem_powerset.mp (mem_filter.mp ht).1
    have herr := abs_le.mp (intersection_error_from (N := N) hn hb hp ht')
    change -_ ≤ ((I.filter (fun x => t ⊆ B x)).card:ℝ) - _ ∧ _ ≤ _ at herr
    rcases Nat.even_or_odd t.card with hh|hh
    · rw [hh.neg_one_pow]
      linarith
    · rw [hh.neg_one_pow]
      linarith
  change ∑ t ∈ shortSets P r, (n:ℝ)^t.card < N *
    ((∏ p ∈ P, (1-u p)) - exp (-(r:ℝ)) * (∏ p ∈ P, (1+exp 1*u p))) at hsize
  linarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) N)]

/-- The prime factors from any base `2 ≤ a ≤ n³ + 1` control the logarithm of `H n`
through their sum of gcd densities. -/
theorem log_H_le_gcd_sum {n a : ℕ} (hn : 3 ≤ n) (ha : 2 ≤ a) (ha' : a ≤ n^3+1) :
    log (Erdos820.H n : ℝ) ≤
      256 * (1 + ∑ p ∈ (a^n-1).primeFactors, (n.gcd (p-1):ℝ)/p) * (1+log n)^2 := by
  classical
  let P := (a^n-1).primeFactors
  let u := density n
  let S := ∑ p ∈ P, (n.gcd (p-1):ℝ)/p
  let L := log ((n:ℝ)+1)
  let A := (1+S) * (2+L)
  let r := 2 * ⌈4*A⌉₊ + 1
  let Y := 1+3*A+(r:ℝ)*(1+6*L)
  let N := ⌈exp Y⌉₊
  have hn0 : 0 < n := by omega
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn0
  have hL : 0 ≤ L := log_nonneg (by linarith)
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => by positivity
  have hA : 1 ≤ A := by dsimp [A]; nlinarith [mul_nonneg hS0 hL]
  have hr : Odd r := ⟨_,rfl⟩
  have hr1 : (1:ℝ) ≤ r := by simp [r]
  have hr' : (r:ℝ) = 2*(⌈4*A⌉₊:ℝ)+1 := by simp [r]
  have hrlo : 8*A ≤ (r:ℝ) := by linarith [Nat.le_ceil (4*A)]
  have hrhi : (r:ℝ) ≤ 8*A+3 := by linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ 4*A)]
  have hpr : ∀ p ∈ P, Nat.Prime p := fun _ h => Nat.prime_of_mem_primeFactors h
  have hu : ∀ p ∈ P, 0 ≤ u p := fun _ _ => by unfold u density; positivity
  have hsum : (∑ p ∈ P, u p) ≤ S := by
    apply sum_le_sum
    intro p hp
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
    exact_mod_cast roots_prime_le hn0.ne' (hpr p hp)
  have hSA : S ≤ A := by dsimp [A]; nlinarith [mul_nonneg hS0 hL]
  have hV : exp (-3*A) ≤ ∏ p ∈ P, (1-u p) := by
    apply le_trans _ (product_lower_gcd hn0 P hpr)
    apply exp_le_exp.mpr
    change -3*A ≤ -(2+2*L)*S
    dsimp [A]
    nlinarith [mul_nonneg hS0 hL]
  have hW : (∏ p ∈ P, (1+exp 1*u p)) ≤ exp (3*A) := calc
    _ ≤ ∏ p ∈ P, exp (exp 1*u p) := by
      apply prod_le_prod
      · intro p hp
        linarith [mul_nonneg (exp_pos 1).le (hu p hp)]
      · intro p hp
        linarith [add_one_le_exp (exp 1*u p)]
    _ = exp (exp 1*∑ p ∈ P, u p) := by rw [← exp_sum, mul_sum]
    _ ≤ _ := exp_le_exp.mpr (mul_le_mul exp_one_lt_three.le (hsum.trans hSA)
      (sum_nonneg hu) (by norm_num))
  have htail : exp (-(r:ℝ)) * (∏ p ∈ P, (1+exp 1*u p)) ≤ exp (-3*A)/2 := calc
    _ ≤ exp (-(r:ℝ))*exp (3*A) := mul_le_mul_of_nonneg_left hW (exp_pos _).le
    _ = exp (-(r:ℝ)+3*A) := (exp_add ..).symm
    _ ≤ exp (-3*A-1) := exp_le_exp.mpr (by linarith)
    _ = exp (-3*A)/exp 1 := exp_sub ..
    _ ≤ _ := by gcongr; exact exp_one_gt_two.le
  have hbudget : ∑ t ∈ shortSets P r, (n:ℝ)^t.card ≤ exp ((r:ℝ)*(1+6*L)) := calc
    _ ≤ ∑ t ∈ shortSets P r, (↑(n^3 : ℕ):ℝ)^t.card := by
      have hn3 : n ≤ n^3 := by
        calc n = n^1 := by simp
             _ ≤ n^3 := Nat.pow_le_pow_right hn0 (by decide)
      gcongr
    _ ≤ ((r:ℝ)+1) * ((↑(n^3 : ℕ):ℝ)+1)^(2*r) := budget_bound P (base_prime_count hn ha ha')
    _ ≤ ((r:ℝ)+1) * (((n:ℝ)+1)^3)^(2*r) := by
      push_cast
      gcongr
      nlinarith [sq_nonneg (n:ℝ)]
    _ ≤ _ := by
      have hpow : (((n:ℝ)+1)^3)^(2*r) = exp (6*(r:ℝ)*L) := by
        rw [← exp_log (by positivity : 0 < (((n:ℝ)+1)^3)^(2*r)), log_pow, log_pow]
        push_cast
        dsimp [L]
        ring
      rw [hpow, show (r:ℝ)*(1+6*L) = r+6*r*L by ring, exp_add]
      gcongr
      exact add_one_le_exp _
  have hpos : exp ((r:ℝ)*(1+6*L)) < exp Y * (exp (-3*A)/2) := by
    rw [← mul_div_assoc, ← exp_add, lt_div_iff₀ (by norm_num : (0:ℝ)<2)]
    have hY : Y+ -3*A = (r:ℝ)*(1+6*L)+1 := by dsimp [Y]; ring
    rw [hY, exp_add]
    exact mul_lt_mul_of_pos_left exp_one_gt_two (exp_pos _)
  have hN : exp Y ≤ (N:ℝ) := Nat.le_ceil _
  obtain ⟨x,hx,hgood⟩ := exists_survivor_from (b := a+1) hn0 (by omega) P hpr hr
    (hbudget.trans_lt (hpos.trans_le (mul_le_mul hN (by linarith only [hV,htail])
      (by positivity) (Nat.cast_nonneg N))))
  obtain ⟨hxa,hxN⟩ := mem_Ico.mp hx
  have hcop : (a^n-1).Coprime (x^n-1) := by
    by_contra hc
    obtain ⟨p,hp,hd,he⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
    have hpow : 1 < a^n := one_lt_pow₀ (by omega : 1 < a) hn0.ne'
    exact hgood p (Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩)
      ((root_iff_dvd (by omega)).mpr he)
  have hHx : Erdos820.H n ≤ x := Nat.sInf_le ⟨a,ha,by omega,hcop⟩
  have hstart : (a:ℝ)+1 ≤ exp Y := by
    calc
      _ ≤ ((n:ℝ)+1)^3 := by exact_mod_cast (show a+1 ≤ (n+1)^3 by nlinarith)
      _ = exp (3*L) := by
        change ((n:ℝ)+1)^3 = exp (3*log ((n:ℝ)+1))
        rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, exp_nat_mul, exp_log (by positivity)]
      _ ≤ _ := exp_le_exp.mpr (by dsimp [Y]; nlinarith [mul_nonneg hL (sub_nonneg.mpr hr1)])
  have hY0 : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have hEY : 1 ≤ exp Y := one_le_exp_iff.mpr hY0
  have hH : (Erdos820.H n:ℝ) ≤ exp (Y+2) := by
    have hcast : (Erdos820.H n:ℝ) ≤ (a:ℝ)+1+(N:ℝ) := by
      exact_mod_cast hHx.trans hxN.le
    have hnceil : (N:ℝ) < exp Y+1 := Nat.ceil_lt_add_one (exp_pos _).le
    rw [exp_add]
    nlinarith [mul_le_mul_of_nonneg_left (add_one_le_exp (2:ℝ)) (exp_pos Y).le]
  have hlog : log (Erdos820.H n : ℝ) ≤ Y+2 := by
    obtain ⟨k,hk,hkH,_⟩ := Erdos820.H_spec hn0
    exact (log_le_iff_le_exp (by exact_mod_cast (show 0 < Erdos820.H n by omega))).mpr hH
  let D := 1+log (n:ℝ)
  have hD : 1 ≤ D := by dsimp [D]; linarith [log_nonneg hn']
  have hLD : L ≤ D := by
    have h := log_le_log (by positivity : (0:ℝ)<n+1) (by linarith : (n:ℝ)+1 ≤ 2*n)
    rw [log_mul (by norm_num) (by exact_mod_cast hn0.ne' : (n:ℝ) ≠ 0)] at h
    dsimp [D,L]
    linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hU : 1 ≤ (1+S)*D := one_le_mul_of_one_le_of_one_le (by linarith) hD
  have hAD : A ≤ 3*((1+S)*D) := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 2+L ≤ 3*D) (by linarith : 0 ≤ 1+S)]
  have hRD : (r:ℝ) ≤ 27*((1+S)*D) := by linarith
  have hterm := mul_le_mul hRD (show 1+6*L ≤ 7*D by linarith)
    (by linarith : 0 ≤ 1+6*L) (by linarith : 0 ≤ 27*((1+S)*D))
  apply hlog.trans
  change Y+2 ≤ 256*(1+S)*D^2
  dsimp [Y]
  nlinarith [mul_le_mul_of_nonneg_left hD (by linarith : 0 ≤ (1+S)*D)]


end Erdos820Critical.Sieve

end

section

/- Combined from identity/LimitIdentity.lean. -/

/- The normalization in the maximal-order identity for Erdős 820. -/
namespace Erdos820Identity
open Filter Real Finset
open scoped Topology
noncomputable section

def rate (n : ℕ) : ℝ := log n / log (log n)

private theorem logs_grow : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem rate_pos : ∀ᶠ n : ℕ in atTop, 0 < rate n := by
  filter_upwards [logs_grow.eventually (eventually_gt_atTop (1:ℝ))] with n hn
  exact div_pos (zero_lt_one.trans hn) (log_pos hn)

theorem absorb_polylog (A : ℝ) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, A + r*log (1+log n) ≤ ε*rate n := by
  let D := |A| + 2*(r:ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall := (isLittleO_pow_log_id_atTop (n:=2)).bound (div_pos hε hD)
  filter_upwards [logs_grow.eventually hsmall,
    logs_grow.eventually (eventually_ge_atTop (4:ℝ))] with n he hn
  let t := log (n:ℝ)
  change 4 ≤ t at hn
  change ‖log t ^ 2‖ ≤ ε / D * ‖t‖ at he
  have ht : 0 < t := by linarith
  have hl : 1 ≤ log t := ((lt_log_iff_exp_lt ht).2 (by linarith [exp_one_lt_three])).le
  have hl0 : 0 < log t := by linarith
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (log t)),abs_of_pos ht] at he
  have hone : log (1+t) ≤ 2*log t := by
    have h := log_le_log (by linarith : 0 < 1+t) (show 1+t ≤ t^2 by nlinarith [sq_nonneg (t-2)])
    simpa [log_pow] using h
  have hab : A + r*log (1+t) ≤ D*log t := by
    have h1 := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg (α:=ℝ) r)
    have h2 := mul_le_mul_of_nonneg_left hl (abs_nonneg A)
    dsimp [D]
    linarith [le_abs_self A]
  have h3 : (log t)^2 * D ≤ ε*t := by
    apply (le_div_iff₀ hD).mp
    simpa only [div_mul_eq_mul_div] using he
  change A + r*log (1+t) ≤ ε*(t/log t)
  rw [←mul_div_assoc,le_div_iff₀ hl0]
  nlinarith only [h3,mul_le_mul_of_nonneg_right hab hl0.le]

theorem rate_multiples {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ n.divisors.card →
      rate (j*n) ≤ (1+δ)*rate n := by
  have hll := (tendsto_log_atTop.comp logs_grow).eventually (eventually_gt_atTop (4/δ))
  filter_upwards [Erdos820Critical.Upper.log_divisors_eventually,hll,
    logs_grow.eventually (eventually_gt_atTop (1:ℝ)),eventually_ge_atTop (2:ℕ)] with n hτ hb ht hn j hj hJ
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hj0 : 0 < (j:ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hl : 0 < log (log (n:ℝ)) := log_pos ht
  have hjlog := (log_le_log hj0 (show (j:ℝ) ≤ n.divisors.card by exact_mod_cast hJ)).trans hτ
  have hcoeff : 4 ≤ δ * log (log (n:ℝ)) := by
    change 4/δ < log (log (n:ℝ)) at hb
    linarith [(div_lt_iff₀ hδ).mp hb]
  have hcap : log (j:ℝ) ≤ δ * log (n:ℝ) := by
    apply hjlog.trans
    apply (div_le_iff₀ hl).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff (zero_lt_one.trans ht).le]
  have hm : (n:ℝ) ≤ (j:ℝ)*n := by
    have h := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ j by exact_mod_cast hj) hn0.le
    simpa using h
  have hlog := log_le_log hn0 hm
  have hloglog := log_le_log (zero_lt_one.trans ht) hlog
  unfold rate
  push_cast
  calc
    _ ≤ log ((j:ℝ)*n) / log (log (n:ℝ)) :=
      div_le_div_of_nonneg_left (by linarith : 0 ≤ log ((j:ℝ)*n)) hl hloglog
    _ ≤ ((1+δ)*log (n:ℝ))/log (log (n:ℝ)) := by
      apply div_le_div_of_nonneg_right _ hl.le
      rw [log_mul hj0.ne' hn0.ne']
      linarith
    _ = _ := by ring

theorem shifted_le_divisors {n : ℕ} (hn : 0 < n) :
    (Erdos820Critical.shiftedPrimes n).card ≤ n.divisors.card := by
  apply card_le_card_of_injOn (fun p : ℕ => p-1)
  · intro p hp
    exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hp).2.2,hn.ne'⟩
  · intro p hp q hq h
    change p-1 = q-1 at h
    have hp2 : 2 ≤ p := (mem_filter.mp hp).2.1.two_le
    have hq2 : 2 ≤ q := (mem_filter.mp hq).2.1.two_le
    omega

theorem shifted_one {n : ℕ} (hn : 0 < n) : 1 ≤ (Erdos820Critical.shiftedPrimes n).card := by
  apply card_pos.mpr
  exact ⟨2,mem_filter.mpr ⟨mem_range.mpr (by omega),Nat.prime_two,by simp⟩⟩

def primeExponent (n : ℕ) : ℝ :=
  log ((Erdos820Critical.shiftedPrimes n).card:ℝ)/rate n

def HExponent (n : ℕ) : ℝ := log (log (Erdos820.H n:ℝ))/rate n

theorem primeExponent_bounds : ∀ᶠ n : ℕ in atTop, 0 ≤ primeExponent n ∧ primeExponent n ≤ 4 := by
  filter_upwards [rate_pos,Erdos820Critical.Upper.log_divisors_eventually,
      eventually_gt_atTop (0:ℕ)] with n hr hdiv hn
  have h1 : (1:ℝ) ≤ (Erdos820Critical.shiftedPrimes n).card := by exact_mod_cast shifted_one hn
  have h2 : ((Erdos820Critical.shiftedPrimes n).card:ℝ) ≤ n.divisors.card := by exact_mod_cast shifted_le_divisors hn
  refine ⟨div_nonneg (log_nonneg h1) hr.le,(div_le_iff₀ hr).mpr ?_⟩
  apply (log_le_log (zero_lt_one.trans_le h1) h2).trans
  simpa [rate,mul_div_assoc] using hdiv

private theorem limsup_upper {u v : ℕ → ℝ} (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hu : ∀ᶠ n in atTop, 0 ≤ u n) (hv : ∀ᶠ n in atTop, v n ≤ 6)
    (hc : ∀ ε > (0:ℝ), ∀ᶠ n in atTop, u n ≤ v (m n) + ε) :
    limsup u atTop ≤ limsup v atTop := by
  have lub : IsBoundedUnder (· ≤ ·) atTop v := ⟨6,hv⟩
  have lbu : IsBoundedUnder (· ≥ ·) atTop u := ⟨0,hu⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le lbu.isCoboundedUnder_le
  have h := eventually_lt_of_limsup_lt (show limsup v atTop < limsup v atTop + ε/2 by linarith) lub
  filter_upwards [hm.eventually h,hc (ε/2) (by linarith)] with n h1 h2
  linarith

theorem H_log_positive {n : ℕ} (hn : 1 ≤ n) : 1 ≤ log (Erdos820.H n : ℝ) := by
  obtain ⟨a,ha,hlt,_⟩ := Erdos820.H_spec hn
  have h : (3:ℝ) ≤ Erdos820.H n := by exact_mod_cast (show 3 ≤ Erdos820.H n by omega)
  exact ((lt_log_iff_exp_lt (by linarith)).mpr (exp_one_lt_three.trans_le h)).le

theorem reverse_log {n : ℕ} (hn : 1 ≤ n) :
    log ((Erdos820Critical.shiftedPrimes n).card:ℝ) ≤ log (log (Erdos820.H n : ℝ)) + log 4 := by
  have hpos := H_log_positive hn
  have h : (2:ℝ)^(Erdos820Critical.shiftedPrimes n).card ≤ (Erdos820.H n : ℝ)^2 := by
    exact_mod_cast Erdos820Critical.shifted_count_le_H_sq hn
  have hh := log_le_log (by positivity) h
  rw [log_pow,log_pow] at hh
  have ha : (0:ℝ) ≤ (Erdos820Critical.shiftedPrimes n).card := by positivity
  have hc : ((Erdos820Critical.shiftedPrimes n).card:ℝ) ≤ log (Erdos820.H n:ℝ)*4 := by
    push_cast at hh
    nlinarith [mul_nonneg ha (show 0 ≤ log 2 - 1/2 by linarith [log_two_gt_d9])]
  have hw : (0:ℝ) < (Erdos820Critical.shiftedPrimes n).card := by
    exact_mod_cast (show 0 < (Erdos820Critical.shiftedPrimes n).card from shifted_one hn)
  simpa only [log_mul (by linarith : log (Erdos820.H n:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0)] using
    log_le_log hw hc

/-- A polylogarithmic loss and a divisor-count-sized multiplier preserve the
common normalized upper exponent. -/
theorem identity_of_pointwise (j : ℕ → ℕ) (hj : ∀ᶠ n in atTop, 1 ≤ j n ∧ j n ≤ n.divisors.card)
    (C : ℝ) (hC : 0 < C) (r : ℕ)
    (hbound : ∀ᶠ n in atTop, log (Erdos820.H n : ℝ) ≤
      C * (1 + ((Erdos820Critical.shiftedPrimes (j n*n)).card : ℝ)) * (1+log n)^r) :
    limsup HExponent atTop = limsup primeExponent atTop := by
  let m := fun n => j n*n
  have hm : Tendsto m atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [hj] with n h
    change n ≤ j n*n
    simpa using Nat.mul_le_mul_right n h.1
  have hpos : ∀ᶠ n in atTop, 0 ≤ HExponent n := by
    filter_upwards [rate_pos,eventually_ge_atTop (1:ℕ)] with n hr hn
    exact div_nonneg (log_nonneg (H_log_positive hn)) hr.le
  have hp : ∀ᶠ n in atTop, primeExponent n ≤ 6 :=
    primeExponent_bounds.mono (fun _ h => by linarith [h.2])
  have upper : ∀ ε > (0:ℝ), ∀ᶠ n in atTop, HExponent n ≤ primeExponent (m n) + ε := by
    intro ε hε
    filter_upwards [rate_pos,hm.eventually rate_pos,hj,rate_multiples (show 0 < ε/8 by linarith),
      hm.eventually primeExponent_bounds,hm.eventually (eventually_ge_atTop (1:ℕ)),
      absorb_polylog (log (2*C)) r (show 0 < ε/2 by linarith),hbound,eventually_ge_atTop (1:ℕ)]
      with n hr hmr hj hratio hp hmpos hcost hbound hn
    let W : ℝ := (Erdos820Critical.shiftedPrimes (m n)).card
    have hw : 1 ≤ W := by dsimp [W]; exact_mod_cast shifted_one hmpos
    have hw0 : 0 < W := zero_lt_one.trans_le hw
    have hn0 := log_natCast_nonneg n
    have hHH := H_log_positive hn
    have hhi : log (Erdos820.H n : ℝ) ≤ (2*C)*W*(1+log n)^r := by
      apply hbound.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      change C*(1+W) ≤ 2*C*W
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hw)]
    have hlog := log_le_log (zero_lt_one.trans_le hHH) hhi
    rw [log_mul (by positivity) (by positivity),log_mul (by positivity) hw0.ne',log_pow] at hlog
    have hW : log W = primeExponent (m n) * rate (m n) := by
      exact (div_mul_cancel₀ (log W) hmr.ne').symm
    have hrate := mul_le_mul_of_nonneg_left (hratio (j n) hj.1 hj.2) hp.1
    change primeExponent (m n) * rate (m n) ≤ primeExponent (m n)*((1+ε/8)*rate n) at hrate
    have hcoef : primeExponent (m n)*(1+ε/8) ≤ primeExponent (m n)+ε/2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) hε.le]
    have hend := mul_le_mul_of_nonneg_right hcoef hr.le
    apply (div_le_iff₀ hr).mpr
    rw [hW] at hlog
    nlinarith only [hlog,hcost,hrate,hend]
  have hbu : ∀ᶠ n in atTop, HExponent n ≤ 6 := by
    filter_upwards [upper 1 zero_lt_one,hm.eventually primeExponent_bounds] with n h hb
    linarith [hb.2]
  refine le_antisymm (limsup_upper m hm hpos hp upper) ?_
  apply limsup_upper id tendsto_id (primeExponent_bounds.mono fun _ h => h.1) hbu
  intro ε hε
  filter_upwards [absorb_polylog (log 4) 0 hε,rate_pos,eventually_ge_atTop (1:ℕ)] with n h hr hn
  have hcost : log 4 ≤ ε*rate n := by simpa using h
  have hraw := reverse_log hn
  simp only [id_eq,primeExponent,HExponent]
  rw [div_add',div_le_div_iff_of_pos_right hr]
  · linarith
  · exact hr.ne'

end
end Erdos820Identity

end

section

/- Combined from identity/ArithmeticIdentity.lean. -/

/- # Maximal order of the least coprime-power base -/

namespace Erdos820Identity
open Filter Real Finset
noncomputable section

/-- A pointwise upper bound depending only on the shifted-prime counts of
the first divisor-count-sized segment of multiples of the exponent. -/
theorem pointwise_bound (n : ℕ) (hn : 3 ≤ n) :
    log (Erdos820.H n:ℝ) ≤ 1280*(1+(M n:ℝ))*(1+log n)^2 := by
  obtain ⟨a,ha,ha',hs⟩ := exists_base_sum_le n hn
  have hv := Erdos820Critical.Sieve.log_H_le_gcd_sum hn ha ha'
  apply hv.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  linarith [Nat.cast_nonneg (α:=ℝ) (M n)]

/-- The two maximal-order exponents in Erdős 820 are equal unconditionally. -/
theorem arithmetic_identity :
    limsup HExponent atTop = limsup primeExponent atTop := by
  classical
  have hchoice (n : ℕ) : ∃ j : ℕ, n = 0 ∨
      1 ≤ j ∧ j ≤ n.divisors.card ∧ M n = W (j*n) := by
    by_cases h : 0 < n
    · have hcard : 0 < n.divisors.card := card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr h.ne'⟩
      have hne : (Icc 1 n.divisors.card).Nonempty := ⟨1,mem_Icc.mpr ⟨le_rfl,hcard⟩⟩
      obtain ⟨j,hj,he⟩ := exists_mem_eq_sup _ hne (fun j => W (j*n))
      exact ⟨j,Or.inr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2,he⟩⟩
    · exact ⟨1,Or.inl (by omega)⟩
  choose j hcase using hchoice
  have hj (n : ℕ) (hn : 0 < n) := (hcase n).resolve_left hn.ne'
  refine identity_of_pointwise j ?_ 1280 (by norm_num) 2 ?_
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact ⟨(hj n hn).1,(hj n hn).2.1⟩
  · filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    have h := pointwise_bound n hn
    rw [(hj n (by omega)).2.2] at h
    exact h

end
end Erdos820Identity

end

section

/- Combined from identity/Characterization.lean. -/

/- # The critical exponent and its positivity criterion -/

namespace Erdos820Identity
open Filter Real
open scoped Topology
noncomputable section

private theorem comparisons :
    ∀ᶠ n : ℕ in atTop, ∀ a : ℝ,
      (Erdos820Critical.scale a n < Erdos820.H n ↔ a < HExponent n) ∧
      ((Erdos820.H n : ℝ) < Erdos820Critical.scale a n ↔ HExponent n < a) := by
  filter_upwards [rate_pos,eventually_ge_atTop (1:ℕ)] with n hr hn a
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨m,hm,hmH,_⟩ := Erdos820.H_spec hn
  have hH0 : (0:ℝ) < Erdos820.H n := by exact_mod_cast (show 0 < Erdos820.H n by omega)
  have hlog : 0 < log (Erdos820.H n : ℝ) := zero_lt_one.trans_le (H_log_positive hn)
  have hs : Erdos820Critical.scale a n = exp (exp (a*rate n)) := by
    unfold Erdos820Critical.scale rate
    rw [rpow_def_of_pos hn0]
    congr 2
    ring
  rw [hs]
  constructor
  · rw [← lt_log_iff_exp_lt hH0,← lt_log_iff_exp_lt hlog, HExponent,lt_div_iff₀ hr]
  · rw [← log_lt_iff_lt_exp hH0,← log_lt_iff_lt_exp hlog, HExponent,div_lt_iff₀ hr]

private theorem bounded_exponent : IsBoundedUnder (· ≤ ·) atTop HExponent := by
  have hk := Erdos820Critical.Upper.eventual_upper_of_sieve 128 (by norm_num) 2
    ((eventually_ge_atTop (1:ℕ)).mono fun _ hn => Erdos820Critical.Sieve.log_K_bound hn)
  refine ⟨5,?_⟩
  change ∀ᶠ n : ℕ in atTop, HExponent n ≤ 5
  filter_upwards [hk,comparisons,eventually_ge_atTop (2:ℕ)] with n hk he hn
  have hHK : (Erdos820.H n:ℝ) ≤ Erdos820.K n := by exact_mod_cast Erdos820Critical.H_le_K hn
  exact ((he 5).2.mp (hHK.trans_lt hk)).le

private theorem cobounded_exponent : IsCoboundedUnder (· ≤ ·) atTop HExponent := by
  apply IsBoundedUnder.isCoboundedUnder_le
  refine ⟨0,?_⟩
  change ∀ᶠ n : ℕ in atTop, 0 ≤ HExponent n
  filter_upwards [rate_pos,eventually_ge_atTop (1:ℕ)] with n hr hn
  exact div_nonneg (log_nonneg (H_log_positive hn)) hr.le

/-- The common exponent, including its uniqueness at the stated normalization. -/
theorem common_exponent_iff (c : ℝ) :
    (∀ ε > (0:ℝ),
      (∃ᶠ n : ℕ in atTop, Erdos820Critical.scale (c-ε) n < Erdos820.H n) ∧
      ∀ᶠ n : ℕ in atTop, (Erdos820.H n:ℝ) < Erdos820Critical.scale (c+ε) n) ↔
      c = limsup primeExponent atTop := by
  rw [←arithmetic_identity]
  constructor
  · intro h
    apply le_antisymm
    · apply (le_limsup_iff cobounded_exponent bounded_exponent).mpr
      intro b hb
      have he := (h (c-b) (sub_pos.mpr hb)).1
      apply (he.and_eventually comparisons).mono
      rintro n ⟨h1,h2⟩
      have := (h2 (c-(c-b))).1.mp h1
      linarith
    · apply (limsup_le_iff cobounded_exponent bounded_exponent).mpr
      intro b hb
      filter_upwards [(h (b-c) (sub_pos.mpr hb)).2,comparisons] with n h1 h2
      have := (h2 (c+(b-c))).2.mp h1
      linarith
  · intro hc ε hε
    constructor
    · have hf := frequently_lt_of_lt_limsup cobounded_exponent
          (show c-ε < limsup HExponent atTop by linarith)
      exact (hf.and_eventually comparisons).mono (fun _ h => (h.2 _).1.mpr h.1)
    · have he := eventually_lt_of_limsup_lt (show limsup HExponent atTop < c+ε by linarith)
          bounded_exponent
      filter_upwards [he,comparisons] with n hn hh
      exact (hh _).2.mpr hn

theorem site_iff_positive :
    (type_of% @Erdos820.erdos_820.variants.log_log_exponent) ↔
      0 < limsup primeExponent atTop := by
  constructor
  · rintro ⟨c,hc,h⟩
    exact (common_exponent_iff c |>.mp h) ▸ hc
  · intro h
    exact ⟨_,h,(common_exponent_iff _).mpr rfl⟩

end
end Erdos820Identity

end

#print axioms Erdos820Identity.pointwise_bound
#print axioms Erdos820Identity.arithmetic_identity
#print axioms Erdos820Identity.common_exponent_iff
#print axioms Erdos820Identity.site_iff_positive

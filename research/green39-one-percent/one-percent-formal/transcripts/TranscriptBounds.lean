import TranscriptCount
import Retention
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.GCongr

/-! Finite logarithmic bounds for the one-percent fitting schedule. -/

namespace Green39.Transcripts

open Finset Real

noncomputable section

def logCard {V : Type*} (s : Finset V) : ℝ := log (1 + (s.card : ℝ))

private theorem log_succ_le_of_le_pow {v a : ℝ} (hv : 0 ≤ v) (ha : 1 ≤ a)
    (n : ℕ) (h : v ≤ a ^ n) :
    log (1 + v) ≤ log 2 + (n : ℝ) * log a := by
  have hp : 1 ≤ a ^ n := one_le_pow₀ ha
  have ha' : 0 < a := zero_lt_one.trans_le ha
  calc
    log (1 + v) ≤ log (2 * a ^ n) := log_le_log (by positivity) (by linarith)
    _ = _ := by rw [log_mul (by norm_num) (pow_ne_zero _ ha'.ne'), log_pow]

variable {State A Law Point : Type*} [DecidableEq A]

theorem Stage.logCard_lawList_le [DecidableEq Law] (stage : Stage State A Law Point)
    (alphabet : Finset A) (L : ℕ) :
    logCard (stage.lawList alphabet L) ≤ log 2 + (L : ℝ) * log (1 + alphabet.card) := by
  apply log_succ_le_of_le_pow (Nat.cast_nonneg _)
    (le_add_of_nonneg_right (Nat.cast_nonneg _))
  exact_mod_cast (stage.card_lawList_le alphabet L).trans
    (by simpa only [Nat.add_comm] using wordCount_le alphabet.card L)

theorem Stage.logCard_containerList_le [DecidableEq Point] (stage : Stage State A Law Point)
    (alphabet : Finset A) (L R : ℕ) :
    logCard (stage.containerList alphabet L R) ≤
      log 2 + (R : ℝ) * (log 2 + (L : ℝ) * log (1 + alphabet.card)) := by
  let W := wordCount alphabet.card L
  have hcard : ((stage.containerList alphabet L R).card : ℝ) ≤ (1 + (W : ℝ)) ^ R := by
    exact_mod_cast (stage.card_containerList_le alphabet L R).trans (by
      simpa only [Nat.add_comm] using wordCount_le W R)
  have hword : (W : ℝ) ≤ (1 + (alphabet.card : ℝ)) ^ L := by
    exact_mod_cast (by simpa only [Nat.add_comm] using wordCount_le alphabet.card L :
      W ≤ (1 + alphabet.card) ^ L)
  calc
    logCard (stage.containerList alphabet L R) ≤ log 2 + (R : ℝ) * log (1 + W) :=
      log_succ_le_of_le_pow (Nat.cast_nonneg _) (le_add_of_nonneg_right (Nat.cast_nonneg _))
        R hcard
    _ ≤ _ := by
      have hlog := log_succ_le_of_le_pow (Nat.cast_nonneg _)
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) L hword
      have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) R)
      exact add_le_add (le_refl _) hmul

theorem logCard_mono {V : Type*} {s t : Finset V} (h : s ⊆ t) : logCard s ≤ logCard t := by
  have hc : (s.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast card_le_card h
  exact log_le_log (by positivity) (by linarith only [hc])

/-- Combining stages pays only the logarithm of the number of stages. -/
theorem logCard_biUnion_le {I V : Type*} [DecidableEq V]
    (indices : Finset I) (f : I → Finset V) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ indices, logCard (f i) ≤ B) :
    logCard (indices.biUnion f) ≤ log (1 + (indices.card : ℝ)) + B := by
  have hcount i (hi : i ∈ indices) : ((f i).card : ℝ) ≤ exp B :=
    (by linarith : ((f i).card : ℝ) ≤ 1 + (f i).card).trans
      ((log_le_iff_le_exp (by positivity)).mp (h i hi))
  have hsum : ((indices.biUnion f).card : ℝ) ≤ (indices.card : ℝ) * exp B := calc
    _ ≤ ∑ i ∈ indices, ((f i).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := indices) (t := f))
    _ ≤ ∑ _i ∈ indices, exp B := sum_le_sum hcount
    _ = _ := by simp
  have hexp : 1 ≤ exp B := one_le_exp hB
  calc
    logCard (indices.biUnion f) ≤ log ((1 + (indices.card : ℝ)) * exp B) := by
      apply log_le_log (by positivity)
      linarith
    _ = _ := by rw [log_mul (by positivity) (exp_pos B).ne', log_exp]

def inverseEta (x : ℝ) : ℝ := exp (1000 + (11 / 50 : ℝ) * x)

theorem inv_inverseEta (x : ℝ) : (inverseEta x)⁻¹ = exp (-1000 - (11 / 50 : ℝ) * x) := by
  rw [inverseEta, ← exp_neg]
  congr 1
  ring

def runBudget (p : ℕ) (x : ℝ) : ℕ := ⌈16 * log (p : ℝ) * inverseEta x ^ 2⌉₊ + 1

def removalBudget (x : ℝ) : ℕ := 2 + ⌈2 * inverseEta x * log (2 * x ^ 2)⌉₊

theorem inverseEta_mono : Monotone inverseEta := by
  intro x y hxy
  unfold inverseEta
  exact exp_le_exp.mpr (by linarith)

theorem inverseEta_one_le {x : ℝ} (hx : 0 ≤ x) : 1 ≤ inverseEta x := by
  unfold inverseEta
  exact one_le_exp (by positivity)

theorem inv_inverseEta_le_half {x : ℝ} (hx : 0 ≤ x) :
    (inverseEta x)⁻¹ ≤ 1 / 2 := by
  have he : 2 ≤ inverseEta x := by
    unfold inverseEta
    linarith [add_one_le_exp (1000 + (11 / 50 : ℝ) * x)]
  rw [← one_div, div_le_iff₀ (by linarith : 0 < inverseEta x)]
  linarith

/-- This integer budget satisfies the strict inequality required by the potential argument. -/
theorem runBudget_suffices (p : ℕ) (x : ℝ) :
    16 * log (p : ℝ) < (runBudget p x : ℝ) * (inverseEta x)⁻¹ ^ 2 := by
  have he : 0 < inverseEta x := exp_pos _
  have hceil := Nat.le_ceil (16 * log (p : ℝ) * inverseEta x ^ 2)
  have hb : 16 * log (p : ℝ) * inverseEta x ^ 2 < (runBudget p x : ℝ) := by
    unfold runBudget
    push_cast
    linarith only [hceil]
  rw [inv_pow, ← div_eq_mul_inv]
  exact (lt_div_iff₀ (pow_pos he 2)).mpr hb

theorem runBudget_le {p : ℕ} {x : ℝ} (hp : 0 < p) (hx : 0 ≤ x) :
    (runBudget p x : ℝ) ≤ 18 * inverseEta x ^ 2 * (1 + log (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog := log_nonneg hp'
  have hsq : 1 ≤ inverseEta x ^ 2 := one_le_pow₀ (inverseEta_one_le hx)
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 16 * log (p : ℝ) * inverseEta x ^ 2 by positivity)
  unfold runBudget
  push_cast
  nlinarith only [hceil, hsq, mul_nonneg hlog (sq_nonneg (inverseEta x))]

private theorem log_two_le_one : log 2 ≤ 1 := by
  linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

private theorem removal_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log (2 * x ^ 2) := by
  exact log_nonneg (by nlinarith [sq_nonneg (x - 1)])

theorem removalBudget_lt {x : ℝ} (hx : 1 ≤ x) :
    (removalBudget x : ℝ) < 3 + 2 * inverseEta x * log (2 * x ^ 2) := by
  have he : 0 ≤ inverseEta x := (zero_le_one.trans (inverseEta_one_le (by linarith)))
  have hc := Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he)
    (removal_log_nonneg hx))
  unfold removalBudget
  push_cast
  linarith

/-- Applying the allotted number of removals, each losing at least the fraction
`η/2` of the current target, leaves fewer than `k/x²` points. -/
theorem removalBudget_suffices {x k size : ℝ}
    (hx : 1 ≤ x) (hk : 0 < k) (hsize : size ≤ 2 * k) :
    (1 - (inverseEta x)⁻¹ / 2) ^ removalBudget x * size < k * lossRate x := by
  have hx0 : 0 < x := by linarith
  let E := inverseEta x
  have hE : 1 ≤ E := inverseEta_one_le hx0.le
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  let t := E⁻¹ / 2
  have ht : 0 < t := div_pos (inv_pos.mpr hE0) (by norm_num)
  have hbase : 0 ≤ 1 - t := by
    change 0 ≤ 1 - E⁻¹ / 2
    rw [← one_div]
    have hinv := (div_le_iff₀ hE0).mpr (show (1 : ℝ) ≤ 1 * E by simpa using hE)
    linarith
  have hceil := Nat.le_ceil (2 * E * log (2 * x ^ 2))
  have hcount : 2 * E * log (2 * x ^ 2) < (removalBudget x : ℝ) := by
    unfold removalBudget
    push_cast
    change 2 * E * log (2 * x ^ 2) < 2 + (⌈2 * E * log (2 * x ^ 2)⌉₊ : ℝ)
    linarith only [hceil]
  have hprod : log (2 * x ^ 2) < (removalBudget x : ℝ) * t := calc
    _ = (2 * E * log (2 * x ^ 2)) * t := by
      dsimp only [t]
      field_simp [hE0.ne']
    _ < _ := mul_lt_mul_of_pos_right hcount ht
  have hpow : (1 - t) ^ removalBudget x < (2 * x ^ 2)⁻¹ := calc
    _ ≤ exp (-t) ^ removalBudget x :=
      pow_le_pow_left₀ hbase (by linarith [add_one_le_exp (-t)]) _
    _ = exp ((removalBudget x : ℝ) * (-t)) := (exp_nat_mul _ _).symm
    _ < exp (-log (2 * x ^ 2)) := exp_lt_exp.mpr (by linarith only [hprod])
    _ = _ := by rw [exp_neg, exp_log (by positivity)]
  change (1 - t) ^ removalBudget x * size < k * lossRate x
  calc
    _ ≤ (1 - t) ^ removalBudget x * (2 * k) :=
      mul_le_mul_of_nonneg_left hsize (pow_nonneg hbase _)
    _ < (2 * x ^ 2)⁻¹ * (2 * k) := mul_lt_mul_of_pos_right hpow (by positivity)
    _ = _ := by
      unfold lossRate
      field_simp

private theorem log_alphabet_le {p : ℕ} (hp : 0 < p) :
    log (1 + ((univ : Finset (Instruction p)).card : ℝ)) ≤ 6 * (1 + log (p : ℝ)) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by positivity
  rw [card_univ, card_instruction]
  push_cast
  calc
    log (1 + (4 * (p : ℝ) + 1)) ≤ log (6 * (p : ℝ)) := log_le_log (by positivity) (by linarith)
    _ = log 6 + log (p : ℝ) := log_mul (by norm_num) hp0.ne'
    _ ≤ _ := by linarith [log_le_self (by norm_num : (0 : ℝ) ≤ 6), log_nonneg hp']

private theorem log_word_budget_le {p L : ℕ} {C E x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hx : 0 ≤ x) (hE : inverseEta x ≤ E)
    (hL : (L : ℝ) ≤ C * (inverseEta x) ^ 2 * (1 + log (p : ℝ))) :
    log 2 + (L : ℝ) * log (1 + ((univ : Finset (Instruction p)).card : ℝ)) ≤
      7 * C * E ^ 2 * (1 + log (p : ℝ)) ^ 2 := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hW : 1 ≤ 1 + log (p : ℝ) := by linarith [log_nonneg hp']
  have hE0 : 0 ≤ inverseEta x := zero_le_one.trans (inverseEta_one_le hx)
  have hE' : 1 ≤ E := (inverseEta_one_le hx).trans hE
  have hL' : (L : ℝ) ≤ C * E ^ 2 * (1 + log (p : ℝ)) := by
    refine hL.trans ?_
    gcongr
  have hbase : 1 ≤ C * E ^ 2 * (1 + log (p : ℝ)) ^ 2 := by
    calc
      1 = (1 : ℝ) * 1 ^ 2 * 1 ^ 2 := by norm_num
      _ ≤ _ := by gcongr
  have hprod := mul_le_mul hL' (log_alphabet_le hp)
    (log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg _))) (by positivity)
  nlinarith only [hprod, log_two_le_one, hbase]

variable {p : ℕ} {S V P : Type*}

/-- A per-run bound gives a finite log bound for the laws at this stage. -/
theorem Stage.logCard_laws_of_eta_le [DecidableEq V]
    (stage : Stage S (Instruction p) V P) {L : ℕ} {C E x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hx : 0 ≤ x) (hE : inverseEta x ≤ E)
    (hL : (L : ℝ) ≤ C * (inverseEta x) ^ 2 * (1 + log (p : ℝ))) :
    logCard (stage.lawList univ L) ≤ 7 * C * E ^ 2 * (1 + log (p : ℝ)) ^ 2 :=
  (stage.logCard_lawList_le univ L).trans (log_word_budget_le hp hC hx hE hL)

/-- The outer list costs the removal count times the log cost of a single word.
The hypothesis on `R` can be used with any fitting implementation giving that bound. -/
theorem Stage.logCard_containers_of_eta_le [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {L R : ℕ} {C D E B x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hD : 1 ≤ D) (hx : 0 ≤ x) (hE : inverseEta x ≤ E)
    (hB : 0 ≤ B) (hL : (L : ℝ) ≤ C * (inverseEta x) ^ 2 * (1 + log (p : ℝ)))
    (hR : (R : ℝ) ≤ D * E * (1 + B)) :
    logCard (stage.containerList univ L R) ≤
      8 * C * D * E ^ 3 * (1 + log (p : ℝ)) ^ 2 * (1 + B) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hW : 1 ≤ 1 + log (p : ℝ) := by linarith [log_nonneg hp']
  have hE' : 1 ≤ E := (inverseEta_one_le hx).trans hE
  have hlog : 0 ≤ log (1 + ((univ : Finset (Instruction p)).card : ℝ)) :=
    log_nonneg (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hrun := log_word_budget_le hp hC hx hE hL
  have hbase' : 1 ≤ C * D * E ^ 3 * (1 + log (p : ℝ)) ^ 2 * (1 + B) := by
    have hB1 : 1 ≤ 1 + B := by linarith
    calc
      1 = (1 : ℝ) * 1 * 1 ^ 3 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr
  refine (stage.logCard_containerList_le univ L R).trans ?_
  have hs := mul_le_mul hR hrun
    (add_nonneg (log_nonneg (by norm_num)) (mul_nonneg (Nat.cast_nonneg _) hlog))
    (by positivity)
  nlinarith only [hs, log_two_le_one, hbase']

theorem removals_le_envelope {x E B : ℝ} {R : ℕ} (hx : 1 ≤ x)
    (hE : inverseEta x ≤ E) (hB : log (2 * x ^ 2) ≤ B)
    (hR : R ≤ removalBudget x) :
    (R : ℝ) ≤ 3 * E * (1 + B) := by
  have hE' : 1 ≤ E := (inverseEta_one_le (by linarith)).trans hE
  have hB' : 0 ≤ B := (removal_log_nonneg hx).trans hB
  have hr : (R : ℝ) ≤ removalBudget x := by exact_mod_cast hR
  have hm := mul_le_mul hE hB (removal_log_nonneg hx) (by positivity)
  nlinarith only [hr, hm, hE', mul_nonneg (by positivity : 0 ≤ E) hB',
    removalBudget_lt hx]

/-- The elementary estimate for `k = floor √p` used in the exponents. -/
theorem log_initial_le_log_four_mul {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    (hsqrt : p < (k + 1) ^ 2) :
    log ((p : ℝ) / k) ≤ log (4 * (k : ℝ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : (p : ℝ) < ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hsqrt
  apply log_le_log (by positivity)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr
  calc
    (p : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := hs.le
    _ ≤ (2 * (k : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    _ = _ := by ring

private theorem inverseEta_log_sq {y : ℝ} (hy : 0 < y) :
    inverseEta (log y) ^ 2 = exp 2000 * y ^ (11 / 25 : ℝ) := by
  rw [inverseEta, ← exp_nat_mul, rpow_def_of_pos hy, ← exp_add]
  congr 1
  push_cast
  ring

private theorem inverseEta_log_cube {y : ℝ} (hy : 0 < y) :
    inverseEta (log y) ^ 3 = exp 3000 * y ^ (33 / 50 : ℝ) := by
  rw [inverseEta, ← exp_nat_mul, rpow_def_of_pos hy, ← exp_add]
  congr 1
  push_cast
  ring

private theorem removal_log_le_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log (2 * x ^ 2) ≤ log (2 * y ^ 2) := by
  apply log_le_log (by positivity)
  gcongr

private theorem removal_log_le_log_log {p k : ℕ} (hp : 0 < p) (hk : 0 < k)
    {x : ℝ} (hx : 0 < x) (hupper : x ≤ log ((p : ℝ) / k)) :
    log (2 * x ^ 2) ≤ 1 + 2 * log (1 + log (p : ℝ)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : log ((p : ℝ) / k) ≤ log (p : ℝ) := by
    apply log_le_log (by positivity)
    exact div_le_self (by positivity) hk'
  rw [log_mul (by norm_num) (pow_ne_zero _ hx.ne'), log_pow]
  norm_num
  have hlx := log_le_log hx (show x ≤ 1 + log (p : ℝ) by linarith)
  linarith [log_two_le_one]

/-- At every active stage the log size of the law list has the power `0.44`. -/
theorem Stage.logCard_laws_power [DecidableEq V]
    (stage : Stage S (Instruction p) V P) {k L : ℕ} {C x : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hx : 5000 < x) (hupper : x ≤ log ((p : ℝ) / k))
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + log (p : ℝ))) :
    logCard (stage.lawList univ L) ≤
      7 * C * exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2 := by
  have hE := inverseEta_mono (hupper.trans (log_initial_le_log_four_mul hp hk hsqrt))
  have h := stage.logCard_laws_of_eta_le hp hC (by linarith) hE hL
  rw [inverseEta_log_sq (by positivity : 0 < 4 * (k : ℝ))] at h
  convert h using 1
  ring

/-- At every active stage the log size of the output-container list has the power
`0.66`. This bound uses the manuscript's explicit removal budget. -/
theorem Stage.logCard_containers_power [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {k L R : ℕ} {C x : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hx : 5000 < x) (hupper : x ≤ log ((p : ℝ) / k))
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + log (p : ℝ)))
    (hR : R ≤ removalBudget x) :
    logCard (stage.containerList univ L R) ≤
      48 * C * exp 3000 * (4 * (k : ℝ)) ^ (33 / 50 : ℝ) *
        (1 + log (p : ℝ)) ^ 2 * (1 + log (1 + log (p : ℝ))) := by
  have hE := inverseEta_mono (hupper.trans (log_initial_le_log_four_mul hp hk hsqrt))
  have hB := removal_log_le_log_log hp hk (by linarith : 0 < x) hupper
  have hR' := removals_le_envelope (by linarith : 1 ≤ x) hE hB hR
  have h := stage.logCard_containers_of_eta_le hp hC (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith) hE ((removal_log_nonneg (by linarith)).trans hB) hL hR'
  rw [inverseEta_log_cube (by positivity : 0 < 4 * (k : ℝ))] at h
  convert h using 1
  ring

/-- The last-stage output list has a log size quadratic in `1 + log p`, with
an absolute constant apart from the per-run constant `C`. -/
theorem Stage.logCard_last_containers [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {L R : ℕ} {C x : ℝ}
    (hp : 0 < p) (hC : 1 ≤ C) (hx : 5000 < x) (hstop : x ≤ 10000)
    (hL : (L : ℝ) ≤ C * inverseEta x ^ 2 * (1 + log (p : ℝ)))
    (hR : R ≤ removalBudget x) :
    logCard (stage.containerList univ L R) ≤
      24 * C * (inverseEta 10000) ^ 3 * (1 + log (2 * (10000 : ℝ) ^ 2)) *
        (1 + log (p : ℝ)) ^ 2 := by
  have hE := inverseEta_mono hstop
  have hB := removal_log_le_of_le (by linarith : 0 < x) hstop
  have hR' := removals_le_envelope (by linarith : 1 ≤ x) hE hB hR
  have h := stage.logCard_containers_of_eta_le hp hC (by norm_num : (1 : ℝ) ≤ 3)
    (by linarith) hE (removal_log_nonneg (by norm_num)) hL hR'
  convert h using 1
  ring

/-- Log overhead of the level count. In this application `x₀ = log (p/k)`. -/
theorem last_active_index_le {x₀ : ℝ} {n : ℕ} (hactive : 5000 < level x₀ n) :
    (n : ℝ) < log (x₀ / 5000) / log 2 := by
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have hx : (2 : ℝ) ^ n < x₀ / 5000 := by
    rw [level_eq_div_pow, lt_div_iff₀ hpos] at hactive
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 5000)).mpr
    linarith
  have hlog := log_lt_log hpos hx
  rw [log_pow] at hlog
  exact (lt_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

/-- All levels through an active stage, with a common run-length constant. -/
theorem logCard_all_laws [DecidableEq V]
    (stage : ℕ → Stage S (Instruction p) V P) (L : ℕ → ℕ)
    {k n : ℕ} {C : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hactive : 5000 < level (log ((p : ℝ) / k)) n)
    (hL : ∀ i ≤ n, (L i : ℝ) ≤
      C * inverseEta (level (log ((p : ℝ) / k)) i) ^ 2 * (1 + log (p : ℝ))) :
    logCard ((range (n + 1)).biUnion (fun i => (stage i).lawList univ (L i))) ≤
      log (1 + (n + 1 : ℕ)) +
        7 * C * exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2 := by
  let x₀ := log ((p : ℝ) / k)
  have hx : 0 ≤ x₀ := by
    rw [level_eq_div_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)] at hactive
    linarith [show 0 < (5000 : ℝ) * 2 ^ n by positivity]
  refine le_trans (logCard_biUnion_le _ _ (by positivity : 0 ≤
    7 * C * exp 2000 * (4 * (k : ℝ)) ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2) ?_) ?_
  · intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    exact (stage i).logCard_laws_power hp hk hsqrt hC
      (hactive.trans_le (level_antitone hx hin))
      (show level x₀ i ≤ x₀ from level_antitone hx (Nat.zero_le i)) (hL i hin)
  · rw [card_range]

/-- All stage container lists together pay one additive level-count term. -/
theorem logCard_all_containers [DecidableEq P]
    (stage : ℕ → Stage S (Instruction p) V P) (L R : ℕ → ℕ)
    {k n : ℕ} {C : ℝ}
    (hp : 0 < p) (hk : 0 < k) (hsqrt : p < (k + 1) ^ 2) (hC : 1 ≤ C)
    (hactive : 5000 < level (log ((p : ℝ) / k)) n)
    (hL : ∀ i ≤ n, (L i : ℝ) ≤
      C * inverseEta (level (log ((p : ℝ) / k)) i) ^ 2 * (1 + log (p : ℝ)))
    (hR : ∀ i ≤ n, R i ≤ removalBudget (level (log ((p : ℝ) / k)) i)) :
    logCard ((range (n + 1)).biUnion (fun i => (stage i).containerList univ (L i) (R i))) ≤
      log (1 + (n + 1 : ℕ)) +
        48 * C * exp 3000 * (4 * (k : ℝ)) ^ (33 / 50 : ℝ) *
          (1 + log (p : ℝ)) ^ 2 * (1 + log (1 + log (p : ℝ))) := by
  let x₀ := log ((p : ℝ) / k)
  have hx : 0 ≤ x₀ := by
    rw [level_eq_div_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)] at hactive
    linarith [show 0 < (5000 : ℝ) * 2 ^ n by positivity]
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ log (1 + log (p : ℝ)) := log_nonneg (by linarith [log_nonneg hp'])
  refine le_trans (logCard_biUnion_le _ _ (by positivity : 0 ≤
    48 * C * exp 3000 * (4 * (k : ℝ)) ^ (33 / 50 : ℝ) *
      (1 + log (p : ℝ)) ^ 2 * (1 + log (1 + log (p : ℝ)))) ?_) ?_
  · intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    exact (stage i).logCard_containers_power hp hk hsqrt hC
      (hactive.trans_le (level_antitone hx hin))
      (show level x₀ i ≤ x₀ from level_antitone hx (Nat.zero_le i)) (hL i hin) (hR i hin)
  · rw [card_range]

/-- The manuscript's explicit removal bound is small enough to halve the level. -/
theorem removalBudget_shrink {x : ℝ} (hx : 5000 ≤ x) :
    (10 : ℝ) ^ 24 * (removalBudget x : ℝ) < exp (x / 2) := by
  have hx0 : 0 < x := by linarith
  have hpow (n : ℕ) : log ((2 : ℝ) ^ n) ≤ n := by
    rw [log_pow]
    simpa using mul_le_mul_of_nonneg_left log_two_le_one (Nat.cast_nonneg n)
  have hlog10 : log 10 ≤ 4 :=
    (log_le_log (by norm_num : (0 : ℝ) < 10) (by norm_num : (10 : ℝ) ≤ 2 ^ (4 : ℕ))).trans
      (hpow 4)
  have hlog5000 : log 5000 ≤ 13 :=
    (log_le_log (by norm_num : (0 : ℝ) < 5000)
      (by norm_num : (5000 : ℝ) ≤ 2 ^ (13 : ℕ))).trans (hpow 13)
  have hlogK : log ((10 : ℝ) ^ 24) ≤ 96 := by
    rw [log_pow]
    norm_num
    linarith
  have hlogx : log x ≤ x / 100 := by
    have hquot := log_le_sub_one_of_pos
      (div_pos hx0 (by norm_num : (0 : ℝ) < 5000))
    rw [log_div hx0.ne' (by norm_num)] at hquot
    linarith
  have hn : 0 ≤ log (2 * x ^ 2) := removal_log_nonneg (by linarith)
  have hQ : 0 < 5 + 2 * log (2 * x ^ 2) := by linarith
  have hlogQ : log (5 + 2 * log (2 * x ^ 2)) ≤ 7 + x / 25 := by
    apply (log_le_self hQ.le).trans
    rw [log_mul (by norm_num) (pow_ne_zero _ hx0.ne'), log_pow]
    norm_num
    linarith only [log_two_le_one, hlogx]
  have hE : 1 ≤ inverseEta x := inverseEta_one_le hx0.le
  have hE0 : 0 < inverseEta x := zero_lt_one.trans_le hE
  have hK : 0 < (10 : ℝ) ^ 24 := by positivity
  have hbound : (10 : ℝ) ^ 24 * inverseEta x * (5 + 2 * log (2 * x ^ 2)) < exp (x / 2) := by
    apply (log_lt_iff_lt_exp (mul_pos (mul_pos hK hE0) hQ)).mp
    rw [log_mul (mul_pos hK hE0).ne' hQ.ne', log_mul hK.ne' hE0.ne', inverseEta, log_exp]
    calc
      log ((10 : ℝ) ^ 24) + (1000 + 11 / 50 * x) + log (5 + 2 * log (2 * x ^ 2)) ≤
          96 + (1000 + 11 / 50 * x) + (7 + x / 25) := by gcongr
      _ < x / 2 := by linarith only [hx]
  calc
    (10 : ℝ) ^ 24 * (removalBudget x : ℝ) <
        (10 : ℝ) ^ 24 * (3 + 2 * inverseEta x * log (2 * x ^ 2)) :=
      mul_lt_mul_of_pos_left (removalBudget_lt (by linarith)) hK
    _ ≤ (10 : ℝ) ^ 24 * (inverseEta x * (5 + 2 * log (2 * x ^ 2))) :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hE]) hK.le
    _ = (10 : ℝ) ^ 24 * inverseEta x * (5 + 2 * log (2 * x ^ 2)) := by ring
    _ < exp (x / 2) := hbound

/-- Every candidate built from heavy sets of size at most `K*k` shrinks. -/
theorem Stage.container_card_le_shrink [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {k L R : ℕ} {x : ℝ}
    (hx : 5000 ≤ x) (hR : R ≤ removalBudget x)
    (hheavy : ∀ record ∈ words univ L, (stage.outputHeavy record).card ≤ 10 ^ 24 * k)
    {container : Finset P} (hmem : container ∈ stage.containerList univ L R) :
    (container.card : ℝ) ≤ exp (x / 2) * (k : ℝ) := by
  have hc := stage.card_mem_containerList_le univ L R _ hheavy hmem
  have hc' : (container.card : ℝ) ≤ (R : ℝ) * ((10 : ℝ) ^ 24 * (k : ℝ)) := by
    exact_mod_cast hc
  have hr : (R : ℝ) ≤ (removalBudget x : ℝ) := by exact_mod_cast hR
  have hs := (mul_le_mul_of_nonneg_left hr (show 0 ≤ (10 : ℝ) ^ 24 by positivity)).trans
    (removalBudget_shrink hx).le
  calc
    (container.card : ℝ) ≤ (R : ℝ) * ((10 : ℝ) ^ 24 * (k : ℝ)) := hc'
    _ = ((10 : ℝ) ^ 24 * (R : ℝ)) * (k : ℝ) := by ring
    _ ≤ exp (x / 2) * (k : ℝ) := mul_le_mul_of_nonneg_right hs (by positivity)

/-- At the terminal stage every candidate is within the size cutoff for §1. -/
theorem Stage.terminal_card_le [DecidableEq P]
    (stage : Stage S (Instruction p) V P) {k L R : ℕ} {x : ℝ}
    (hx : 5000 < x) (hstop : x ≤ 10000) (hR : R ≤ removalBudget x)
    (hheavy : ∀ record ∈ words univ L, (stage.outputHeavy record).card ≤ 10 ^ 24 * k)
    {container : Finset P} (hmem : container ∈ stage.containerList univ L R) :
    (container.card : ℝ) ≤ exp 5000 * (k : ℝ) := by
  exact (stage.container_card_le_shrink hx.le hR hheavy hmem).trans
    (mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith)) (by positivity))

end

end Green39.Transcripts

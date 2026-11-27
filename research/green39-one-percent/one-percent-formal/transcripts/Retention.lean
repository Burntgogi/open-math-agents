import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-! The geometric loss and the retained targets from §6. -/

namespace Green39.Transcripts

open Finset

noncomputable section

def level (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | i + 1 => level x₀ i / 2

theorem level_eq_div_pow (x₀ : ℝ) (i : ℕ) : level x₀ i = x₀ / 2 ^ i := by
  induction i with
  | zero => simp [level]
  | succ i ih => rw [level, ih, pow_succ, div_div]

theorem level_pos {x₀ : ℝ} (hx : 0 < x₀) (i : ℕ) : 0 < level x₀ i := by
  rw [level_eq_div_pow]
  positivity

theorem level_antitone {x₀ : ℝ} (hx : 0 ≤ x₀) : Antitone (level x₀) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [level]
  have h : 0 ≤ level x₀ i := by rw [level_eq_div_pow]; positivity
  linarith

theorem last_level_bounds {x₀ : ℝ} {n : ℕ}
    (hactive : 5000 < level x₀ n) (hstop : level x₀ (n + 1) ≤ 5000) :
    5000 < level x₀ n ∧ level x₀ n ≤ 10000 := by
  rw [level] at hstop
  exact ⟨hactive, by linarith⟩

/-- There is a first inactive level whenever the initial level is active. -/
theorem exists_last_active {x₀ : ℝ} (hx : 5000 < x₀) :
    ∃ n, (∀ i ≤ n, 5000 < level x₀ i) ∧ level x₀ (n + 1) ≤ 5000 := by
  have hstop : ∃ n, level x₀ n ≤ 5000 := by
    obtain ⟨n, hn⟩ := exists_nat_gt (x₀ / 5000)
    have hpow : n < 2 ^ n := Nat.lt_two_pow_self
    have hn' : (n : ℝ) < 2 ^ n := by exact_mod_cast hpow
    refine ⟨n, ?_⟩
    rw [level_eq_div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
    linarith
  obtain ⟨n, heq⟩ := Nat.exists_eq_succ_of_ne_zero
    (show Nat.find hstop ≠ 0 by
      intro h
      have hspec := Nat.find_spec hstop
      rw [h, level] at hspec
      linarith)
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    exact lt_of_not_ge (Nat.find_min hstop (by omega))
  · simpa only [heq] using Nat.find_spec hstop

def lossRate (x : ℝ) : ℝ := 1 / x ^ 2

theorem lossRate_halve (x : ℝ) : lossRate (x / 2) = 4 * lossRate x := by
  unfold lossRate
  rw [div_pow, div_div_eq_mul_div]
  ring

/-- Exact sum of the active-stage loss rates through stage `n`. -/
theorem sum_lossRate (x₀ : ℝ) (n : ℕ) :
    3 * (∑ i ∈ range (n + 1), lossRate (level x₀ i)) =
      4 * lossRate (level x₀ n) - lossRate x₀ := by
  induction n with
  | zero => simp [level]; ring
  | succ n ih =>
    have hs : lossRate (level x₀ (n + 1)) = 4 * lossRate (level x₀ n) := by
      rw [level, lossRate_halve]
    rw [sum_range_succ, hs]
    linarith

theorem sum_lossRate_lt {x₀ : ℝ} {n : ℕ} (hactive : 5000 < level x₀ n) :
    (∑ i ∈ range (n + 1), lossRate (level x₀ i)) < 4 / (3 * 5000 ^ 2) := by
  have hlast : lossRate (level x₀ n) < 1 / (5000 : ℝ) ^ 2 := by
    unfold lossRate
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith [sq_nonneg (level x₀ n - 5000)]
  have hfirst : 0 ≤ lossRate x₀ := by unfold lossRate; positivity
  linarith [sum_lossRate x₀ n]

variable {Point : Type*} [DecidableEq Point]

/-- Exact telescoping of the number of target points lost. -/
theorem card_telescope (targets : ℕ → Finset Point) (m : ℕ)
    (hsub : ∀ i < m, targets (i + 1) ⊆ targets i) :
    (targets m).card + ∑ i ∈ range m, ((targets i) \ (targets (i + 1))).card =
      (targets 0).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hstep := card_sdiff_add_card_eq_card (hsub m (Nat.lt_succ_self m))
    have hp := ih (fun i hi => hsub i (Nat.lt_succ_of_lt hi))
    omega

/-- The exact real-valued lower bound obtained by summing the per-stage loss budgets. -/
theorem card_retained_lower (targets : ℕ → Finset Point) (x₀ k : ℝ) (m : ℕ)
    (hsub : ∀ i < m, targets (i + 1) ⊆ targets i)
    (hloss : ∀ i < m, (((targets i) \ (targets (i + 1))).card : ℝ) ≤
      k * lossRate (level x₀ i)) :
    ((targets 0).card : ℝ) - k * (∑ i ∈ range m, lossRate (level x₀ i)) ≤
      (targets m).card := by
  have hcast := congrArg (fun a : ℕ => (a : ℝ)) (card_telescope targets m hsub)
  push_cast at hcast
  have hsum : (∑ i ∈ range m, (((targets i) \ (targets (i + 1))).card : ℝ)) ≤
      k * (∑ i ∈ range m, lossRate (level x₀ i)) := by
    rw [mul_sum]
    exact sum_le_sum fun i hi => hloss i (mem_range.mp hi)
  linarith

/-- The aggregate loss is strictly below the manuscript's geometric bound. -/
theorem card_loss_lt (targets : ℕ → Finset Point) {x₀ k : ℝ} {n : ℕ}
    (hk : 0 < k) (hactive : 5000 < level x₀ n)
    (hsub : ∀ i ≤ n, targets (i + 1) ⊆ targets i)
    (hloss : ∀ i ≤ n, (((targets i) \ (targets (i + 1))).card : ℝ) ≤
      k * lossRate (level x₀ i)) :
    ((targets 0).card : ℝ) - (targets (n + 1)).card < 4 * k / (3 * 5000 ^ 2) := by
  have h := card_retained_lower targets x₀ k (n + 1)
    (fun i hi => hsub i (Nat.lt_succ_iff.mp hi)) (fun i hi => hloss i (Nat.lt_succ_iff.mp hi))
  have hb := mul_lt_mul_of_pos_left (sum_lossRate_lt hactive) hk
  linarith

/-- Retaining the intersection with each output container preserves more than
`0.11 k` good centers at every prefix, including the terminal prefix. -/
theorem retention_each_prefix (targets containers : ℕ → Finset Point) {x₀ k : ℝ} {n : ℕ}
    (hk : 0 < k) (hactive : 5000 < level x₀ n)
    (hstart : k / 9 ≤ (targets 0).card)
    (hnext : ∀ i ≤ n, targets (i + 1) = targets i ∩ containers i)
    (hloss : ∀ i ≤ n, (((targets i) \ containers i).card : ℝ) ≤
      k * lossRate (level x₀ i)) :
    ∀ m ≤ n + 1, (11 / 100 : ℝ) * k < (targets m).card := by
  have hx : 0 ≤ x₀ := by
    have he := level_eq_div_pow x₀ n
    have hp : (0 : ℝ) < 2 ^ n := by positivity
    rw [he, lt_div_iff₀ hp] at hactive
    linarith
  intro m hm
  cases m with
  | zero => linarith
  | succ j =>
    have hj : j ≤ n := by omega
    have hprefix := hactive.trans_le (level_antitone hx hj)
    have hsub (i : ℕ) (hi : i ≤ j) : targets (i + 1) ⊆ targets i := by
      rw [hnext i (hi.trans hj)]
      exact inter_subset_left
    have hstep (i : ℕ) (hi : i ≤ j) :
        (((targets i) \ targets (i + 1)).card : ℝ) ≤ k * lossRate (level x₀ i) := by
      rw [hnext i (hi.trans hj)]
      have heq : targets i \ (targets i ∩ containers i) = targets i \ containers i := by
        ext a
        simp only [mem_sdiff, mem_inter]
        tauto
      rw [heq]
      exact hloss i (hi.trans hj)
    have hb := card_loss_lt targets hk hprefix hsub hstep
    linarith

end

end Green39.Transcripts

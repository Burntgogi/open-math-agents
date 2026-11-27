import PaperConstants
import SmoothRate
import Mathlib.Data.Nat.Sqrt

open Filter Asymptotics
open scoped BigOperators Classical Topology
open Green39.Concentration

namespace Green39.Smooth
noncomputable section

/-- Probability that either assertion of (4) fails, for the manuscript's actual split sizes. -/
def eqFourFailure {p : ℕ} [NeZero p] {ι : Type*} (I : Finset ι) (μ : ι → ZMod p → ℝ) :=
  let k := p.sqrt
  let a := k/2
  splitProb Finset.univ a (k-a) (fun A B ↦ ∃ i ∈ I,
    (k:ℝ)/100000000 < l1 (μ i) (k-a) B ∨ ∃ v, (1:ℝ)/1000 <
      ∑ z ∈ B, excess (μ i) A ((51:ℝ)/(100*k)) v z)

theorem eqFourFailure_le {p : ℕ} [NeZero p] {ι : Type*} (I : Finset ι) (μ : ι → ZMod p → ℝ)
    (hp : 4 ≤ p) (hn : ∀ i ∈ I, ∀ x, 0 ≤ μ i x) (hm : ∀ i ∈ I, ∑ x, μ i x = 1)
    (hc : ∀ i ∈ I, ∀ x, μ i x ≤ 2/(10^24*(p.sqrt:ℝ))) :
    eqFourFailure I μ ≤ paperRate I.card p p.sqrt := by
  have hk : 2 ≤ p.sqrt := Nat.le_sqrt.mpr hp
  have hh : p ≤ 2*p.sqrt^2 := by
    have h := Nat.sqrt_le_add p
    nlinarith [Nat.mul_le_mul_right p.sqrt hk]
  have h := paper_equation_four I μ (k := p.sqrt) (a := p.sqrt/2) (b := p.sqrt-p.sqrt/2)
    hk (by omega) (by omega) (by omega) (by omega) (by rw [ZMod.card]; exact Nat.sqrt_le' p)
    (by rwa [ZMod.card]) hn hm hc
  simpa only [eqFourFailure, paperRate, ZMod.card] using h

private theorem eqFourFailure_nonneg {p : ℕ} [NeZero p] {ι : Type*}
    (I : Finset ι) (μ : ι → ZMod p → ℝ) : 0 ≤ eqFourFailure I μ := by
  unfold eqFourFailure splitProb splitMean sliceMean mean
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro A _
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg (fun _ _ ↦ by dsimp only; split <;> norm_num)

/-- Equation (4) with probability tending to one. The family may vary with p.
The input from §3 is precisely that the logarithm of the law-and-shift count is o(√k). -/
theorem eqFourFailure_tendsto {p : ℕ → ℕ} [∀ n, NeZero (p n)] {ι : ℕ → Type*}
    (I : ∀ n, Finset (ι n)) (μ : ∀ n, ι n → ZMod (p n) → ℝ)
    (hp : Tendsto p atTop atTop)
    (hn : ∀ n i, i ∈ I n → ∀ x, 0 ≤ μ n i x)
    (hm : ∀ n i, i ∈ I n → ∑ x, μ n i x = 1)
    (hc : ∀ n i, i ∈ I n → ∀ x, μ n i x ≤ 2/(10^24*((p n).sqrt:ℝ)))
    (hcost : (fun n ↦ Real.log (1+((I n).card:ℝ)*(p n))) =o[atTop]
      (fun n ↦ Real.sqrt ((p n).sqrt:ℝ))) :
    Tendsto (fun n ↦ eqFourFailure (I n) (μ n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n ↦ (p n).sqrt) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [hp.eventually_ge_atTop (a^2)] with n h
    exact Nat.le_sqrt'.mpr h
  have hr : Tendsto (fun n ↦ ((p n).sqrt:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  have hrate := paperRate_tendsto (N := fun n ↦ ((I n).card:ℝ)) (p := fun n ↦ (p n:ℝ))
    (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne (p n)))
    hr hcost
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ eqFourFailure_nonneg (I n) (μ n))) _ hrate
  filter_upwards [hp.eventually_ge_atTop 4] with n h
  exact eqFourFailure_le _ _ h (hn n) (hm n) (hc n)

end
end Green39.Smooth

import WitnessProbability
import FourierDiscrepancy

/-!
# Fixed fitted witnesses in §5

The sets of centers and the fitted law are fixed before measuring the event.
The three deterministic inequalities concern the pair of sampled halves.
-/

open Finset OnePercent.Fourier
open scoped BigOperators Classical Pointwise

set_option autoImplicit false

namespace Green39.Split

variable {p : ℕ} [NeZero p]

/-- The deterministic estimates that force enough exceptional hits for a fixed fitted piece. -/
def FittedPieceEvent (R S : Finset (ZMod p)) (μ : ZMod p → ℝ) (k : ℕ)
    (q : Finset (ZMod p) × Finset (ZMod p)) : Prop :=
  (0.244 : ℝ) * R.card * S.card ≤ ∑ z ∈ q.2, predicted (q.1 + R) S μ z ∧
    (∑ z ∈ q.2, observed (q.1 + R) S z) ≤ (0.115 : ℝ) * R.card * S.card ∧
    ∀ v ∈ R, (∑ z ∈ q.2, max (smoothed q.1 μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001

/-- The §5 probability bound for the actual Fourier discrepancy, before enumerating witnesses. -/
theorem fitted_hits_probability {k : ℕ} (hk : 0 < k) (hkp : k ≤ p)
    (R S : Finset (ZMod p)) (μ : ZMod p → ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hr : (0.099 : ℝ) ≤ (R.card : ℝ) / k)
    (hfit : FourierFit S μ (7 * Real.exp (-1000 - 0.22 * x) * S.card)) :
    probability (orderedPairs (univ : Finset (ZMod p)) (k / 2) (k - k / 2))
        (fun q ↦ (0.24 : ℝ) * k ≤ (exceptionalHits q.2 (q.1 + R) S μ R.card k).card) ≤
      (2 : ℝ) ^ k * (2 * (71000 * Real.exp (-1000 - 0.22 * x)) ^ 2) ^ ((0.24 : ℝ) * k) := by
  let η := Real.exp (-1000 - 0.22 * x)
  let D (A₁ : Finset (ZMod p)) :=
    exceptional (discrepancy (A₁ + R) S μ) (cutoff R.card S.card k)
  have hsum : k / 2 + (k - k / 2) = k := by omega
  have hpop : (univ : Finset (ZMod p)).card = p := by simp [ZMod.card]
  have hD (A₁ : Finset (ZMod p)) :
      ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * (univ : Finset (ZMod p)).card := by
    rw [hpop]
    exact exceptional_card_section5 (A₁ + R) S μ hk (Real.exp_nonneg _) hr hfit
  have h := witness_hits_probability (s := (univ : Finset (ZMod p)))
    (k₁ := k / 2) (k₂ := k - k / 2) (η := η) (by omega) (by omega) (by omega)
    D (fun A₁ _ ↦ hD A₁) (section5_eta_small hx)
  simpa only [η, D, hsum, exceptionalHits] using h

/-- The same probability bound for one fixed witness satisfying the three deterministic estimates. -/
theorem fitted_witness_probability {k : ℕ} (hk : 0 < k) (hkp : k ≤ p)
    (R S : Finset (ZMod p)) (μ : ZMod p → ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hr : (0.099 : ℝ) ≤ (R.card : ℝ) / k)
    (hfit : FourierFit S μ (7 * Real.exp (-1000 - 0.22 * x) * S.card))
    (hR : R.Nonempty) (hS : S.Nonempty) (hμ : ∀ z, 0 ≤ μ z) :
    probability (orderedPairs (univ : Finset (ZMod p)) (k / 2) (k - k / 2))
        (FittedPieceEvent R S μ k) ≤
      (2 : ℝ) ^ k * (2 * (71000 * Real.exp (-1000 - 0.22 * x)) ^ 2) ^ ((0.24 : ℝ) * k) := by
  refine le_trans (probability_mono ?_) (fitted_hits_probability hk hkp R S μ hx hr hfit)
  rintro ⟨A₁, A₂⟩ hq ⟨hpred, hobs, hcap⟩
  have hcard : A₂.card = k - k / 2 := (mem_orderedPairs.mp hq).2.2.2.1
  exact (exceptionalHits_section5 A₁ A₂ R S μ hk hR hS (by omega) hμ hpred hobs hcap).2.le

end Green39.Split

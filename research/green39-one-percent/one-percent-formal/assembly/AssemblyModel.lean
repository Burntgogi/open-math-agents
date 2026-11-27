import Retention
import FourierDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Sqrt

open Finset
open scoped Pointwise Classical
namespace Green39.Assembly
noncomputable section

abbrev Points (p : ℕ) := Finset (ZMod p)
abbrev Law (p : ℕ) := ZMod p → ℝ
abbrev Sample (p : ℕ) := Points p × Points p
abbrev W (p : ℕ) := Points p × Points p × Law p
abbrev half (k : ℕ) := k / 2
abbrev rest (k : ℕ) := k - k / 2
abbrev rSize (k : ℕ) := k / 10
abbrev sMax (k : ℕ) := k / 1000
def x (p i : ℕ) := Transcripts.level (Real.log ((p : ℝ) / p.sqrt)) i
def eta (x : ℝ) := Real.exp (-1000 - 0.22 * x)

structure Catalog (p : ℕ) where
  stages : ℕ
  containers : ℕ → Finset (Points p)
  laws : ℕ → Finset (Law p)

variable {p : ℕ} [NeZero p]
open OnePercent.Fourier

/-- The input at index zero is the entire group. At the last index the
containers are the outputs of the last active stage alone. -/
structure StageSpec (C : Catalog p) : Prop where
  initial : univ ∈ C.containers 0
  active : ∀ i < C.stages, 5000 < x p i
  stop : x p C.stages ≤ 5000
  containerSize : ∀ i ≤ C.stages, ∀ P ∈ C.containers i,
    (P.card : ℝ) ≤ p.sqrt * Real.exp (x p i)
  capped : ∀ i < C.stages, ∀ μ ∈ C.laws i, (∀ z, 0 ≤ μ z) ∧
    (∑ z, μ z) = 1 ∧ ∀ z, μ z ≤ 2 / (10 ^ 24 * (p.sqrt : ℝ))
  alternative : ∀ i < C.stages, ∀ P ∈ C.containers i, ∀ V ⊆ P,
    (0.11 : ℝ) * p.sqrt ≤ (V.card : ℝ) → (V.card : ℝ) ≤ 2 * p.sqrt →
    (∃ F ⊆ V, (p.sqrt : ℝ) * Transcripts.lossRate (x p i) ≤ (F.card : ℝ) ∧
      ∃ μ ∈ C.laws i, FourierFit F μ (5 * eta (x p i) * F.card)) ∨
    ∃ Q ∈ C.containers (i+1), ((V \ Q).card : ℝ) ≤
      p.sqrt * Transcripts.lossRate (x p i)

def witnesses (C : Catalog p) (i : ℕ) : Finset (W p) :=
  (C.containers i).biUnion fun P =>
    ((P.powersetCard (rSize p.sqrt)) ×ˢ
      ((P.powerset.filter fun S => S.Nonempty ∧ S.card ≤ sMax p.sqrt) ×ˢ C.laws i)).filter
      fun w => FourierFit w.2.1 w.2.2 (7 * eta (x p i) * w.2.1.card)

def hits (w : W p) (q : Sample p) : Prop :=
  (0.24 : ℝ) * p.sqrt ≤
    (exceptionalHits q.2 (q.1 + w.1) w.2.1 w.2.2 w.1.card p.sqrt).card

def typical (μ : Law p) (q : Sample p) : Prop :=
  (∑ u, |convolution (indicator q.2) μ u - (q.2.card : ℝ) / p|) ≤
    (0.00000001 : ℝ) * p.sqrt ∧
  ∀ v, (∑ z ∈ q.2, max (smoothed q.1 μ (z-v) - 0.51 / p.sqrt) 0) ≤ 0.001

theorem numerical {k : ℕ} (hk : 100000 ≤ k) (hp : p < (k+1)^2) :
    (p : ℝ) ≤ 1.0001 * k^2 ∧
    (0.0999 : ℝ) * k ≤ (rSize k : ℝ) ∧
    (0.244 : ℝ) * rSize k ≤
      (rest k : ℝ) * ((half k : ℝ) - 0.0114*k) * rSize k / p - 0.00000001*k := by
  have hk' : (100000 : ℝ) ≤ k := by exact_mod_cast hk
  have hp' : (p : ℝ) < ((k : ℝ)+1)^2 := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have hk2 : (100000 : ℝ) * k ≤ (k : ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk') (Nat.cast_nonneg k)]
  have hpc : (p : ℝ) ≤ 1.0001 * k^2 := by nlinarith
  have hr : (k : ℝ) ≤ 10*(rSize k : ℝ)+9 := by exact_mod_cast (show k ≤ 10*rSize k+9 by dsimp [rSize]; omega)
  have hr' : (0.0999 : ℝ)*k ≤ (rSize k : ℝ) := by linarith
  refine ⟨hpc, hr', ?_⟩
  have h1 : (k : ℝ) ≤ 2*(half k : ℝ)+1 := by exact_mod_cast (show k ≤ 2*half k+1 by dsimp [half]; omega)
  have h2 : (k : ℝ) ≤ 2*(rest k : ℝ) := by exact_mod_cast (show k ≤ 2*rest k by dsimp [rest]; omega)
  have hmul := mul_le_mul (show (0.5:ℝ)*k ≤ rest k by linarith)
    (show (0.48859:ℝ)*k ≤ (half k : ℝ) - 0.0114*k by linarith)
    (by positivity) (Nat.cast_nonneg _)
  have hmul' : (0.2441:ℝ)*p ≤ (rest k : ℝ)*((half k : ℝ)-0.0114*k) := by nlinarith
  have htimes := mul_le_mul_of_nonneg_right hmul' (Nat.cast_nonneg (rSize k))
  have hdiv : (0.2441:ℝ)*rSize k ≤ (rest k : ℝ)*((half k : ℝ)-0.0114*k)*rSize k/p := by
    apply (le_div_iff₀ hp0).mpr
    linarith only [htimes]
  linarith

/-- Retention with early exit: only an actually fitted target produces a witness. -/
theorem iterate {C : Catalog p} (spec : StageSpec C) (G : Points p)
    (hk : 0 < p.sqrt) (hstart : (p.sqrt : ℝ)/9 ≤ G.card)
    (hsize : (G.card : ℝ) ≤ 2*p.sqrt) :
    (∃ i < C.stages, ∃ P ∈ C.containers i, ∃ V ⊆ P, V ⊆ G ∧
      (0.11 : ℝ)*p.sqrt ≤ V.card ∧ ∃ F ⊆ V,
      (p.sqrt : ℝ)*Transcripts.lossRate (x p i) ≤ F.card ∧
      ∃ μ ∈ C.laws i, FourierFit F μ (5*eta (x p i)*F.card)) ∨
    ∃ P ∈ C.containers C.stages, (0.11 : ℝ)*p.sqrt ≤ (G ∩ P).card := by
  classical
  by_cases hf : ∃ i < C.stages, ∃ P ∈ C.containers i, ∃ V ⊆ P, V ⊆ G ∧
      (0.11 : ℝ)*p.sqrt ≤ V.card ∧ ∃ F ⊆ V,
      (p.sqrt : ℝ)*Transcripts.lossRate (x p i) ≤ F.card ∧
      ∃ μ ∈ C.laws i, FourierFit F μ (5*eta (x p i)*F.card)
  · exact Or.inl hf
  right
  let loss (j : ℕ) := ∑ i ∈ range j, Transcripts.lossRate (x p i)
  have margin (j : ℕ) (hj : j ≤ C.stages) :
      (0.11:ℝ)*p.sqrt ≤ (G.card : ℝ) - p.sqrt * loss j := by
    have h : loss j ≤ 4/(3*(5000:ℝ)^2) := by
      cases j with
      | zero => norm_num [loss]
      | succ i => exact (Transcripts.sum_lossRate_lt (spec.active i (by omega))).le
    have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg p.sqrt)
    linarith
  have path (j : ℕ) (hj : j ≤ C.stages) : ∃ P ∈ C.containers j,
      (G.card : ℝ) - p.sqrt * loss j ≤ (G ∩ P).card := by
    induction j with
    | zero => exact ⟨univ, spec.initial, by simp [loss]⟩
    | succ i ih =>
      obtain ⟨P,hP,hV⟩ := ih (by omega)
      let V := G ∩ P
      have hG : V ⊆ G := inter_subset_left
      have hVP : V ⊆ P := inter_subset_right
      have hbig := (margin i (by omega)).trans hV
      rcases spec.alternative i (by omega) P hP V hVP hbig
          ((Nat.cast_le.mpr (card_le_card hG)).trans hsize) with hfit | ⟨Q,hQ,hcut⟩
      · exact (hf ⟨i,by omega,P,hP,V,hVP,hG,hbig,hfit⟩).elim
      · refine ⟨Q,hQ,?_⟩
        have he := card_sdiff_add_card_inter V Q
        have he' : ((V \ Q).card : ℝ) + (V ∩ Q).card = V.card := by exact_mod_cast he
        have hle : ((V ∩ Q).card : ℝ) ≤ (G ∩ Q).card :=
          Nat.cast_le.mpr (card_le_card (inter_subset_inter_right hG))
        have hl : loss (i+1) = loss i + Transcripts.lossRate (x p i) := sum_range_succ _ _
        change _ ≤ (V.card : ℝ) at hV
        rw [hl]
        linarith
  obtain ⟨P,hP,h⟩ := path _ le_rfl
  exact ⟨P,hP,(margin _ le_rfl).trans h⟩

end
end Green39.Assembly
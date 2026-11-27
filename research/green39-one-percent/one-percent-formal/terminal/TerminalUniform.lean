import TerminalConcentration
import TerminalRates
import Mathlib.Data.Nat.Sqrt

/-!
# A uniform bound for bounded-size terminal containers

With «k = floor sqrt p», use «L = floor sqrt (floor sqrt k)». With
«x = L + 1», the resulting bound is a constant times «x^8 exp(-a*x)»,
uniformly over all prescribed containers of size at most «M*k».
-/

open Finset
open scoped BigOperators Classical

namespace Green39.Terminal

noncomputable section

/-- The size parameter for the uniform exponential bound. -/
def scale (p : ℕ) : ℕ := (Nat.sqrt p).sqrt.sqrt + 1

theorem modulus_le_scale_pow (p : ℕ) : p ≤ (scale p) ^ 8 := by
  let k := p.sqrt
  let L := k.sqrt.sqrt
  have h₁ : p < (k + 1) ^ 2 := Nat.lt_succ_sqrt' p
  have h₂ : k < (k.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' k
  have h₃ : k.sqrt + 1 ≤ (L + 1) ^ 2 := Nat.lt_succ_sqrt' k.sqrt
  have h₄ : k + 1 ≤ (L + 1) ^ 4 := by
    calc
      _ ≤ (k.sqrt + 1) ^ 2 := h₂
      _ ≤ ((L + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h₃ _
      _ = _ := by ring
  calc
    _ ≤ (k + 1) ^ 2 := h₁.le
    _ ≤ ((L + 1) ^ 4) ^ 2 := Nat.pow_le_pow_left h₄ _
    _ = _ := by unfold scale; change _ = (L + 1) ^ 8; ring

private theorem scale_le_k_and_cube (p : ℕ) (hk : 1 < p.sqrt) :
    scale p ≤ p.sqrt ∧ scale p ^ 3 ≤ 8 * p.sqrt := by
  let k := p.sqrt
  let L := k.sqrt.sqrt
  have hL : L ≤ k.sqrt := Nat.sqrt_le_self _
  have hL0 : 1 ≤ L := by
    have hh : 1 ≤ k.sqrt := Nat.le_sqrt.mpr (by omega)
    exact Nat.le_sqrt.mpr (by simpa using hh)
  have hpow : L ^ 4 ≤ k := by
    calc
      _ = (L ^ 2) ^ 2 := by ring
      _ ≤ k.sqrt ^ 2 := Nat.pow_le_pow_left (Nat.sqrt_le' k.sqrt) _
      _ ≤ k := Nat.sqrt_le' k
  change L + 1 ≤ k ∧ (L + 1) ^ 3 ≤ 8 * k
  constructor
  · have hks : k.sqrt < k := Nat.sqrt_lt_self hk
    exact Nat.succ_le_of_lt (hL.trans_lt hks)
  · calc
      _ ≤ (2 * L) ^ 3 := Nat.pow_le_pow_left (by omega) _
      _ = 8 * L ^ 3 := by ring
      _ ≤ 8 * L ^ 4 := by
        apply Nat.mul_le_mul_left
        calc
          _ = L ^ 3 * 1 := (Nat.mul_one _).symm
          _ ≤ L ^ 3 * L := Nat.mul_le_mul_left _ hL0
          _ = L ^ 4 := (pow_succ L 3).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hpow

/-- A uniform lower bound for the density of holes. -/
def densityLower (M : ℝ) : ℝ := Real.exp (-4 * M)

/-- Decay rate for the three failure terms. -/
def decay (M δ : ℝ) : ℝ :=
  min (Real.log 2) ((δ * densityLower M) ^ 2 / (256 * (max 1 M) ^ 2))

theorem decay_pos (M : ℝ) {δ : ℝ} (hδ : 0 < δ) : 0 < decay M δ := by
  unfold decay densityLower
  have hB : 0 < max 1 M := zero_lt_one.trans_le (le_max_left _ _)
  have hA := mul_pos hδ (Real.exp_pos (-4 * M))
  exact lt_min (Real.log_pos (by norm_num)) (by positivity)

/-- Uniform probability bound as a function of the scale. -/
def uniformBound (M δ x : ℝ) : ℝ :=
  (Real.exp (2 * M) + 2) * x ^ 8 * Real.exp (-decay M δ * x)

theorem uniformBound_nonneg (M δ x : ℝ) : 0 ≤ uniformBound M δ x := by
  unfold uniformBound
  positivity

private theorem uniform_parameters {p m : ℕ} {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 < δ)
    (hk : 1 < p.sqrt) (hsize : (m : ℝ) ≤ M * (p.sqrt : ℝ))
    (hlarge : 2 * (1 + M) ≤ (p.sqrt : ℝ))
    (hlarge' : 4 * M / δ ≤ (p.sqrt : ℝ))
    (hsmall : uniformBound M δ (scale p) ≤ δ * densityLower M / 4) :
    let k := p.sqrt
    let L := k.sqrt.sqrt
    let u := δ * densityLower M * (k : ℝ) / 4
    0 < rho p k m ∧
    scoreMean p k m + (k : ℝ) * irregularBound p k m L + u ≤ (1 + δ) * k * rho p k m ∧
    failureBound p k m L δ u ≤ uniformBound M δ (scale p) := by
  let k := p.sqrt
  let L := k.sqrt.sqrt
  let x : ℝ := scale p
  let B : ℝ := max 1 M
  let a := δ * densityLower M
  let c := decay M δ
  let u := a * (k : ℝ) / 4
  change 0 < rho p k m ∧
    scoreMean p k m + (k : ℝ) * irregularBound p k m L + u ≤ (1 + δ) * k * rho p k m ∧
    failureBound p k m L δ u ≤ uniformBound M δ x
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hp : 0 < p := (show 0 < k by omega).trans_le (Nat.sqrt_le_self p)
  have hpr : 0 < (p : ℝ) := by exact_mod_cast hp
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have ha : 0 < a := mul_pos hδ (Real.exp_pos _)
  have hc : 0 < c := decay_pos M hδ
  have hx : 0 < x := by dsimp [x, scale]; positivity
  have hxk : x ≤ k := Nat.cast_le.mpr (scale_le_k_and_cube p hk).1
  have hxcube : x ^ 3 ≤ 8 * (k : ℝ) := by
    dsimp only [x, k]
    exact_mod_cast (scale_le_k_and_cube p hk).2
  have hpx : (p : ℝ) ≤ x ^ 8 := by
    dsimp only [x]
    exact_mod_cast modulus_le_scale_pow p
  have hk2 : (k : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  have hkm : 2 * (k + m) ≤ p := by
    have h₁ : (2 : ℝ) * ((k : ℝ) + m) ≤ (2 * (1 + M)) * k := by linarith
    have h₂ := mul_le_mul_of_nonneg_right hlarge hkpos.le
    have hh : (2 : ℝ) * ((k : ℝ) + m) ≤ p := by nlinarith
    exact_mod_cast hh
  have hmp : (m : ℝ) * k / p ≤ M := by
    apply (div_le_iff₀ hpr).mpr
    have h₁ := mul_le_mul_of_nonneg_right hsize hkpos.le
    have h₂ := mul_le_mul_of_nonneg_left hk2 hM
    nlinarith
  have hrho : densityLower M ≤ rho p k m :=
    (Real.exp_le_exp.mpr (by linarith)).trans (choose_avoidance_ge_exp hp hkm)
  have hrhopos : 0 < rho p k m := (Real.exp_pos (-4 * M)).trans_le hrho
  have hQ : irregularBound p k m L ≤
      (p : ℝ) * Real.exp (2 * M) * Real.exp (-c * x) := by
    have h := irregularBound_le_exp (p := p) (k := k) (m := m) (L := L) (M := M)
      (Nat.sqrt_le_self p) (scale_le_k_and_cube p hk).1 (by rwa [← mul_div_assoc])
    refine h.trans ?_
    rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hcLog : c ≤ Real.log 2 := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_right hcLog hx.le
    change -(x * Real.log 2) ≤ -c * x
    linarith [mul_comm (Real.log 2) x]
  have hQsmall : irregularBound p k m L ≤ a / 4 := by
    refine hQ.trans (le_trans ?_ hsmall)
    unfold uniformBound
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc
      _ ≤ x ^ 8 * Real.exp (2 * M) := mul_le_mul_of_nonneg_right hpx (Real.exp_nonneg _)
      _ ≤ _ := by
        rw [mul_comm (Real.exp (2 * M) + 2)]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hpm : m < p := by omega
  have hratio : (p : ℝ) / ((p : ℝ) - m) ≤ 1 + δ / 2 := by
    have h₁ : (4 : ℝ) * m ≤ δ * p := by
      have h₂ := (div_le_iff₀ hδ).mp hlarge'
      have h₃ := mul_le_mul_of_nonneg_right h₂ hkpos.le
      have h₄ := mul_le_mul_of_nonneg_left hk2 hδ.le
      nlinarith
    have h₂ : (2 : ℝ) * m ≤ p := by exact_mod_cast (show 2 * m ≤ p by omega)
    have h₃ := mul_le_mul_of_nonneg_left (show (p : ℝ) / 2 ≤ p - m by linarith)
      (show 0 ≤ δ / 2 by positivity)
    apply (div_le_iff₀ (sub_pos.mpr (by exact_mod_cast hpm))).mpr
    nlinarith
  have hmargin : scoreMean p k m + (k : ℝ) * irregularBound p k m L + u ≤
      (1 + δ) * (k : ℝ) * rho p k m := by
    rw [scoreMean_eq (show 0 < k by omega) hpm]
    have hmean := mul_le_mul_of_nonneg_left hratio (show 0 ≤ (k : ℝ) * rho p k m by positivity)
    have hQk := mul_le_mul_of_nonneg_left hQsmall hkpos.le
    have haρ : a ≤ δ * rho p k m := mul_le_mul_of_nonneg_left hrho hδ.le
    have haρk := mul_le_mul_of_nonneg_right haρ hkpos.le
    dsimp [u]
    nlinarith
  have hMax : max 1 (m : ℝ) ≤ B * (k : ℝ) := by
    apply max_le
    · exact le_trans hk1 (by simpa using (mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) M) hkpos.le))
    · exact hsize.trans (mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) M) hkpos.le)
  have hc₀ : c ≤ a ^ 2 / (256 * B ^ 2) := min_le_right _ _
  have hc₁ : c ≤ a ^ 2 / 256 := hc₀.trans (by
    have hB1 : 1 ≤ B := le_max_left _ _
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
    nlinarith [sq_nonneg (B - 1)])
  have hhole : c * x ≤ (δ * (p : ℝ) * rho p k m) ^ 2 /
      (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2) := by
    have hc₂ : c ≤ a ^ 2 / (2 * B ^ 2) := hc₀.trans (by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      nlinarith [sq_nonneg B])
    have ham : a * (k : ℝ) ^ 2 ≤ δ * (p : ℝ) * rho p k m := by
      calc
        _ ≤ a * (p : ℝ) := mul_le_mul_of_nonneg_left hk2 ha.le
        _ = δ * (p : ℝ) * densityLower M := by dsimp [a]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrho (by positivity)
    have hmaxpos : 0 < max 1 (m : ℝ) := zero_lt_one.trans_le (le_max_left _ _)
    calc
      _ ≤ c * (k : ℝ) := mul_le_mul_of_nonneg_left hxk hc.le
      _ ≤ a ^ 2 / (2 * B ^ 2) * (k : ℝ) := mul_le_mul_of_nonneg_right hc₂ hkpos.le
      _ = (a * (k : ℝ) ^ 2) ^ 2 / (2 * (k : ℝ) * (B * (k : ℝ)) ^ 2) := by
        field_simp
      _ ≤ _ := by gcongr
  have hscore : c * x ≤ u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2) := by
    have hxL : x = 1 + (L : ℝ) := by dsimp [x, scale, L, k]; push_cast; ring
    have hx' : x ≤ 8 * (k : ℝ) / x ^ 2 := (le_div_iff₀ (by positivity)).mpr
      (by calc x * x ^ 2 = x ^ 3 := by ring
               _ ≤ _ := hxcube)
    calc
      _ ≤ a ^ 2 / 256 * x := mul_le_mul_of_nonneg_right hc₁ hx.le
      _ ≤ a ^ 2 / 256 * (8 * (k : ℝ) / x ^ 2) :=
        mul_le_mul_of_nonneg_left hx' (by positivity)
      _ = _ := by
        rw [← hxL]
        dsimp [u]
        field_simp
        ring
  refine ⟨hrhopos, hmargin, ?_⟩
  have hH : Real.exp (-(δ * (p : ℝ) * rho p k m) ^ 2 /
      (2 * (k : ℝ) * (max 1 (m : ℝ)) ^ 2)) ≤ Real.exp (-c * x) := by
    simpa only [neg_div, neg_mul] using Real.exp_le_exp.mpr (neg_le_neg hhole)
  have hX : (p : ℝ) * Real.exp (-u ^ 2 / (2 * (k : ℝ) * (1 + (L : ℝ)) ^ 2)) ≤
      (p : ℝ) * Real.exp (-c * x) := by
    simpa only [neg_div, neg_mul] using
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hscore)) hpr.le
  calc
    _ ≤ (p : ℝ) * Real.exp (2 * M) * Real.exp (-c * x) +
        Real.exp (-c * x) + (p : ℝ) * Real.exp (-c * x) := add_le_add (add_le_add hQ hH) hX
    _ ≤ uniformBound M δ x := by
      unfold uniformBound
      change _ ≤ (Real.exp (2 * M) + 2) * x ^ 8 * Real.exp (-c * x)
      have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp
      have h₁ : (p : ℝ) * Real.exp (2 * M) ≤ x ^ 8 * Real.exp (2 * M) :=
        mul_le_mul_of_nonneg_right hpx (Real.exp_nonneg _)
      have h := mul_le_mul_of_nonneg_right (show (p : ℝ) * Real.exp (2 * M) + 1 + p ≤
        (Real.exp (2 * M) + 2) * x ^ 8 by linarith) (Real.exp_nonneg (-c * x))
      linarith

/-- The bound for a finite list with «|P| ≤ M*k» is uniform in the prescribed sets. -/
theorem probability_not_coversOutside_list_le_uniform {p : ℕ} [NeZero p]
    (Ps : Finset (Finset (ZMod p))) {M δ ζ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hk : 1 < p.sqrt) (hsize : ∀ P ∈ Ps, (P.card : ℝ) ≤ M * (p.sqrt : ℝ))
    (hlarge : 2 * (1 + M) ≤ (p.sqrt : ℝ)) (hlarge' : 4 * M / δ ≤ (p.sqrt : ℝ))
    (hsmall : uniformBound M δ (scale p) ≤ δ * densityLower M / 4)
    (hζ : 1 - ζ ≤ (1 - δ) / (1 + δ)) :
    probability p p.sqrt (fun A ↦ ¬ ∀ P ∈ Ps, CoversOutside P p.sqrt ζ A) ≤
      (Ps.card : ℝ) * uniformBound M δ (scale p) := by
  let q := fun P hP ↦ uniform_parameters hM hδ hk (hsize P hP) hlarge hlarge' hsmall
  have hk' : 0 < p.sqrt := (Nat.zero_lt_one).trans hk
  refine (probability_not_coversOutside_list_le Ps p.sqrt.sqrt.sqrt hk' (Nat.sqrt_le_self p)
    hδ.le (by unfold densityLower; positivity) hζ (fun P hP ↦ (q P hP).1)
    (fun P hP ↦ (q P hP).2.1)).trans ?_
  calc
    _ ≤ ∑ _P ∈ Ps, uniformBound M δ (scale p) := sum_le_sum fun P hP ↦ (q P hP).2.2
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end

end Green39.Terminal


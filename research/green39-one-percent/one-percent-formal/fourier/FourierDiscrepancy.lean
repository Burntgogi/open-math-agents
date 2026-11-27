import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Deterministic Fourier discrepancy for the fitted piece

The counting-measure transform is `ZMod.dft`. The normalized transform divides by the
ambient cardinality. The transform of the uniform probability on a nonempty set instead
divides its indicator transform by the set cardinality.
-/

open Finset
open scoped Pointwise ComplexConjugate

namespace OnePercent.Fourier

variable {p : ℕ} [NeZero p]

/-- Indicator of a finite set, with values in the coefficient ring. -/
def indicator {R : Type*} [Zero R] [One R] (U : Finset (ZMod p)) (z : ZMod p) : R :=
  if z ∈ U then 1 else 0

/-- Counting-measure convolution on `ZMod p`. -/
noncomputable def convolution {R : Type*} [Semiring R] (f g : ZMod p → R) (z : ZMod p) : R :=
  ∑ u, f u * g (z - u)

lemma convolution_indicator {R : Type*} [Semiring R] (U : Finset (ZMod p)) (g : ZMod p → R)
    (z : ZMod p) : convolution (indicator U) g z = ∑ u ∈ U, g (z - u) := by
  simp only [convolution, indicator, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Fourier coefficients with the ambient averaging convention. -/
noncomputable def normalizedDFT (f : ZMod p → ℂ) (a : ZMod p) : ℂ :=
  ZMod.dft f a / (p : ℂ)

/-- The uniform law on `S`, whose mass is one when `S` is nonempty. -/
noncomputable def uniformLaw (S : Finset (ZMod p)) (z : ZMod p) : ℂ :=
  indicator S z / (S.card : ℂ)

/-- The actual number of points of `U` hit at center `z` by a shift in `S`. -/
def observed (U S : Finset (ZMod p)) (z : ZMod p) : ℝ :=
  ((z +ᵥ S) ∩ U).card

/-- The smooth prediction at `z`, using a measure given by its masses `μ`. -/
noncomputable def predicted (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  (S.card : ℝ) * ∑ u ∈ U, μ (u - z)

/-- The real, pointwise discrepancy from Section 5. -/
noncomputable def discrepancy (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  observed U S z - predicted U S μ z

/-- The difference between the indicator of `S` and the fitted mass rescaled by `|S|`. -/
noncomputable def centeredKernel (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  indicator S z - (S.card : ℝ) * μ z

omit [NeZero p] in
lemma observed_eq_sum (U S : Finset (ZMod p)) (z : ZMod p) :
    observed U S z = ∑ u ∈ U, (indicator S (u - z) : ℝ) := by
  simp only [observed, indicator, ← Finset.sum_filter]
  have h : U.filter (fun u ↦ u - z ∈ S) = (z +ᵥ S) ∩ U := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_vadd_finset, vadd_eq_add]
    constructor
    · rintro ⟨huU, huS⟩
      exact ⟨⟨u - z, huS, by abel⟩, huU⟩
    · rintro ⟨⟨v, hvS, rfl⟩, huU⟩
      exact ⟨huU, by simpa using hvS⟩
  rw [h]
  simp

lemma discrepancy_eq_convolution (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) :
    discrepancy U S μ z = convolution (indicator U) (fun t ↦ centeredKernel S μ (-t)) z := by
  rw [discrepancy, observed_eq_sum, predicted, Finset.mul_sum, ← Finset.sum_sub_distrib,
    convolution_indicator]
  simp only [centeredKernel, neg_sub]

lemma dft_convolution (f g : ZMod p → ℂ) (a : ZMod p) :
    ZMod.dft (convolution f g) a = ZMod.dft f a * ZMod.dft g a := by
  simp only [ZMod.dft_apply, smul_eq_mul, convolution]
  conv_lhs => enter [2, z]; rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight u) _ _ fun z ↦ ?_
  change ZMod.stdAddChar (-(z * a)) * (f u * g (z - u)) =
    (ZMod.stdAddChar (-(u * a)) * f u) * (ZMod.stdAddChar (-((z - u) * a)) * g (z - u))
  rw [show -(z * a) = -(u * a) + -((z - u) * a) by ring, AddChar.map_add_eq_mul]
  ring

lemma normalizedDFT_convolution (f g : ZMod p → ℂ) (a : ZMod p) :
    normalizedDFT (convolution f g) a =
      (p : ℂ) * normalizedDFT f a * normalizedDFT g a := by
  simp only [normalizedDFT, dft_convolution]
  field_simp

lemma dft_uniformLaw (S : Finset (ZMod p)) (a : ZMod p) :
    ZMod.dft (uniformLaw S) a = ZMod.dft (indicator S) a / (S.card : ℂ) := by
  simp [uniformLaw, ZMod.dft_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

lemma dft_indicator_eq_card_mul_uniformLaw (S : Finset (ZMod p)) (hS : S.Nonempty)
    (a : ZMod p) :
    ZMod.dft (indicator S) a = (S.card : ℂ) * ZMod.dft (uniformLaw S) a := by
  have hcard : (S.card : ℂ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  rw [dft_uniformLaw, mul_comm (S.card : ℂ), div_mul_cancel₀ _ hcard]

private lemma sum_indicator {R : Type*} [Semiring R] (S : Finset (ZMod p)) :
    (∑ z : ZMod p, (indicator S z : R)) = (S.card : R) := by
  simp [indicator]

lemma dft_centeredKernel (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (a : ZMod p) :
    ZMod.dft (fun z ↦ (centeredKernel S μ z : ℂ)) a =
      ZMod.dft (indicator S) a - (S.card : ℂ) * ZMod.dft (fun z ↦ (μ z : ℂ)) a := by
  have h : (fun z ↦ (centeredKernel S μ z : ℂ)) =
      indicator S - fun z ↦ (S.card : ℂ) * (μ z : ℂ) := by
    funext z
    simp only [Pi.sub_apply, centeredKernel, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_natCast]
    by_cases hz : z ∈ S <;> simp [indicator, hz]
  rw [h, map_sub, ZMod.dft_const_mul, Pi.sub_apply]

/-- The frequency reverses because the kernel in the observed count uses `u - z`. -/
lemma dft_discrepancy (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (a : ZMod p) :
    ZMod.dft (fun z ↦ (discrepancy U S μ z : ℂ)) a =
      ZMod.dft (indicator U) a *
        (ZMod.dft (indicator S) (-a) -
          (S.card : ℂ) * ZMod.dft (fun z ↦ (μ z : ℂ)) (-a)) := by
  have h : (fun z ↦ (discrepancy U S μ z : ℂ)) =
      convolution (indicator U) (fun t ↦ (centeredKernel S μ (-t) : ℂ)) := by
    funext z
    rw [discrepancy_eq_convolution]
    simp only [convolution, Complex.ofReal_sum, Complex.ofReal_mul]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    by_cases hu : u ∈ U <;> simp [indicator, hu]
  rw [h, dft_convolution, ZMod.dft_comp_neg (fun t ↦ (centeredKernel S μ t : ℂ))]
  exact congrArg (ZMod.dft (indicator U) a * ·) (dft_centeredKernel S μ (-a))

/-- Centering cancels the zero Fourier mode when the fitted masses sum to one. -/
lemma sum_discrepancy_eq_zero (U S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (hμ : ∑ z : ZMod p, μ z = 1) : ∑ z : ZMod p, discrepancy U S μ z = 0 := by
  have hfitMass : ∑ z : ZMod p, (μ z : ℂ) = 1 := by exact_mod_cast hμ
  have hzero := dft_discrepancy U S μ (0 : ZMod p)
  simp only [neg_zero, ZMod.dft_apply_zero, sum_indicator, hfitMass, mul_one, sub_self,
    mul_zero] at hzero
  exact_mod_cast hzero

private lemma inverse_sum (f : ZMod p → ℂ) (x : ZMod p) :
    (∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a) = (p : ℂ) * f x := by
  have h := congrFun (ZMod.dft.symm_apply_apply f) x
  rw [ZMod.invDFT_apply] at h
  exact (inv_mul_eq_iff_eq_mul₀ (NeZero.ne (p : ℂ))).mp h

/-- Parseval for the unnormalized transform, with counting measure on both sides. -/
lemma parseval_unnormalized (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖ZMod.dft f a‖ ^ 2) = (p : ℝ) * ∑ x : ZMod p, ‖f x‖ ^ 2 := by
  have h : (∑ a : ZMod p, conj (ZMod.dft f a) * ZMod.dft f a) =
      (p : ℂ) * ∑ x : ZMod p, conj (f x) * f x := by
    calc
      _ = ∑ x : ZMod p, conj (f x) *
          (∑ a : ZMod p, ZMod.stdAddChar (a * x) * ZMod.dft f a) := by
        conv_lhs => enter [2, a, 1]; rw [ZMod.dft_apply, map_sum]
        simp only [Finset.sum_mul, Finset.mul_sum, smul_eq_mul, map_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
        rw [← AddChar.inv_apply_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg, mul_comm x a]
        ring
      _ = _ := by
        simp only [inverse_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ ↦ ?_
        ring
  simp only [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum, ← Complex.ofReal_natCast p,
    ← Complex.ofReal_mul, Complex.ofReal_inj] at h
  exact h

/-- Parseval for coefficients divided by `p`, with the spatial mean square on the right. -/
lemma parseval_normalized (f : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖normalizedDFT f a‖ ^ 2) = (∑ x : ZMod p, ‖f x‖ ^ 2) / (p : ℝ) := by
  simp only [normalizedDFT, norm_div, Complex.norm_natCast, div_pow, ← Finset.sum_div,
    parseval_unnormalized]
  have hp : (p : ℝ) ≠ 0 := NeZero.ne _
  field_simp

/-- The counting-measure form of (5), allowing an arbitrary sup norm bound `B`. -/
def FourierFit (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (B : ℝ) : Prop :=
  ∀ a : ZMod p, ‖ZMod.dft (indicator S) a -
    (S.card : ℂ) * ZMod.dft (fun z ↦ (μ z : ℂ)) a‖ ≤ B

lemma fourierFit_iff_normalizedDFT (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (B : ℝ) :
    FourierFit S μ B ↔ ∀ a : ZMod p, ‖normalizedDFT (indicator S) a -
      (S.card : ℂ) * normalizedDFT (fun z ↦ (μ z : ℂ)) a‖ ≤ B / (p : ℝ) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  simp only [FourierFit, normalizedDFT, ← mul_div_assoc, ← sub_div, norm_div,
    Complex.norm_natCast, div_le_div_iff_of_pos_right hp]

/-- Passing from the normalized empirical law of `S` to (5) costs a factor of `|S|`. -/
lemma fourierFit_iff_uniformLaw (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (hS : S.Nonempty)
    (B : ℝ) : FourierFit S μ (B * S.card) ↔ ∀ a : ZMod p,
      ‖ZMod.dft (uniformLaw S) a - ZMod.dft (fun z ↦ (μ z : ℂ)) a‖ ≤ B := by
  have hs : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  simp only [FourierFit, dft_indicator_eq_card_mul_uniformLaw S hS, ← mul_sub, norm_mul,
    Complex.norm_natCast, mul_comm (S.card : ℝ), mul_le_mul_iff_of_pos_right hs]

lemma mean_sq_discrepancy_le (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {B : ℝ}
    (hfit : FourierFit S μ B) :
    (∑ z : ZMod p, |discrepancy U S μ z| ^ 2) / (p : ℝ) ≤
      B ^ 2 * ((U.card : ℝ) / (p : ℝ)) := by
  have hU : (∑ z : ZMod p, ‖(indicator U z : ℂ)‖ ^ 2) = (U.card : ℝ) := by
    simp [indicator, apply_ite (fun w : ℂ ↦ ‖w‖ ^ 2)]
  have hD := parseval_normalized (fun z ↦ (discrepancy U S μ z : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs] at hD
  rw [← hD, ← hU, ← parseval_normalized, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [normalizedDFT, dft_discrepancy, mul_div_right_comm, norm_mul, mul_pow]
  change ‖normalizedDFT (indicator U) a‖ ^ 2 * _ ≤ B ^ 2 * ‖normalizedDFT (indicator U) a‖ ^ 2
  rw [mul_comm (B ^ 2)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hfit (-a)) _) (sq_nonneg _)

/-- Positions where the absolute discrepancy strictly exceeds the threshold. -/
noncomputable def exceptional (f : ZMod p → ℝ) (δ : ℝ) : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun z ↦ δ < |f z|

@[simp] lemma mem_exceptional (f : ZMod p → ℝ) (δ : ℝ) (z : ZMod p) :
    z ∈ exceptional f δ ↔ δ < |f z| := by
  classical
  simp [exceptional]

lemma exceptional_card_mul_sq_le (f : ZMod p → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((exceptional f δ).card : ℝ) * δ ^ 2 ≤ ∑ z : ZMod p, |f z| ^ 2 := by
  calc
    _ = ∑ z ∈ exceptional f δ, δ ^ 2 := by simp
    _ ≤ ∑ z ∈ exceptional f δ, |f z| ^ 2 := by
      exact Finset.sum_le_sum fun z hz ↦
        pow_le_pow_left₀ hδ ((mem_exceptional f δ z).mp hz).le _
    _ ≤ _ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun z _ _ ↦ sq_nonneg _)

/-- The exceptional fraction, retaining the factor `|U| / p`. -/
lemma exceptional_fraction_le (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {B δ : ℝ}
    (hfit : FourierFit S μ B) (hδ : 0 < δ) :
    ((exceptional (discrepancy U S μ) δ).card : ℝ) / (p : ℝ) ≤
      (B / δ) ^ 2 * ((U.card : ℝ) / (p : ℝ)) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have h := (div_le_div_iff_of_pos_right hp).2
    (exceptional_card_mul_sq_le (discrepancy U S μ) hδ.le)
  have hbound := h.trans (mean_sq_discrepancy_le U S μ hfit)
  have hscaled : (((exceptional (discrepancy U S μ) δ).card : ℝ) / (p : ℝ)) * δ ^ 2 ≤
      B ^ 2 * ((U.card : ℝ) / p) := by
    rwa [div_mul_eq_mul_div]
  calc
    _ ≤ (B ^ 2 * ((U.card : ℝ) / p)) / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).2 hscaled
    _ = _ := by ring

/-- An upper bound on the number of exceptional positions for any positive threshold. -/
lemma exceptional_card_le (U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {B δ : ℝ}
    (hfit : FourierFit S μ B) (hδ : 0 < δ) :
    ((exceptional (discrepancy U S μ) δ).card : ℝ) ≤ (B / δ) ^ 2 * U.card := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  have h := exceptional_fraction_le U S μ hfit hδ
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hp] at h
  exact h

/-- The threshold `0.001 r |S| / k` used for exceptional positions. -/
noncomputable def cutoff (r s k : ℕ) : ℝ := (0.001 : ℝ) * r * s / k

lemma exceptional_fraction_section5 (U S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    {r k : ℕ} {η : ℝ} (hk : 0 < k) (hη : 0 ≤ η)
    (hr : (0.099 : ℝ) ≤ (r : ℝ) / k) (hfit : FourierFit S μ (7 * η * S.card)) :
    ((exceptional (discrepancy U S μ) (cutoff r S.card k)).card : ℝ) / (p : ℝ) ≤
      (71000 * η) ^ 2 := by
  classical
  by_cases hS : S.Nonempty
  · have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    have hr' : 0 < (r : ℝ) := (div_pos_iff_of_pos_right hk').mp (by linarith)
    have hs' : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
    have hδ : 0 < cutoff r S.card k := by unfold cutoff; positivity
    have hcoeff : (7 : ℝ) ≤ 71000 * (0.001 * ((r : ℝ) / k)) := by linarith
    have hratio : 7 * η * (S.card : ℝ) / cutoff r S.card k ≤ 71000 * η := by
      apply (div_le_iff₀ hδ).2
      calc
        _ = 7 * (η * (S.card : ℝ)) := by ring
        _ ≤ 71000 * (0.001 * ((r : ℝ) / k)) * (η * (S.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hη hs'.le)
        _ = _ := by unfold cutoff; ring
    have hU : (U.card : ℝ) / (p : ℝ) ≤ 1 := by
      have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
      have hcard : U.card ≤ p := by simpa [ZMod.card] using Finset.card_le_univ U
      apply (div_le_iff₀ hp).2
      simpa using (Nat.cast_le (α := ℝ)).2 hcard
    calc
      _ ≤ (7 * η * (S.card : ℝ) / cutoff r S.card k) ^ 2 * ((U.card : ℝ) / p) :=
        exceptional_fraction_le U S μ hfit hδ
      _ ≤ (7 * η * (S.card : ℝ) / cutoff r S.card k) ^ 2 :=
        mul_le_of_le_one_right (sq_nonneg _) hU
      _ ≤ _ := pow_le_pow_left₀ (div_nonneg (by positivity) hδ.le) hratio _
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty, exceptional, discrepancy, observed, predicted, cutoff, sq_nonneg]

lemma exceptional_card_section5 (U S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    {r k : ℕ} {η : ℝ} (hk : 0 < k) (hη : 0 ≤ η)
    (hr : (0.099 : ℝ) ≤ (r : ℝ) / k) (hfit : FourierFit S μ (7 * η * S.card)) :
    ((exceptional (discrepancy U S μ) (cutoff r S.card k)).card : ℝ) ≤
      (71000 * η) ^ 2 * (p : ℝ) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p))
  exact (div_le_iff₀ hp).mp (exceptional_fraction_section5 U S μ hk hη hr hfit)

/-- The deterministic lower bound on the aggregate prediction from the first inequality in (4). -/
lemma sum_predicted_ge_of_l1 (A₂ U S : Finset (ZMod p)) (μ : ZMod p → ℝ) {ε : ℝ}
    (hL1 : (∑ u : ZMod p, |convolution (indicator A₂) μ u - (A₂.card : ℝ) / p|) ≤ ε) :
    (S.card : ℝ) * ((A₂.card : ℝ) * U.card / p - ε) ≤ ∑ z ∈ A₂, predicted U S μ z := by
  have hdiff : (∑ u ∈ U, ((A₂.card : ℝ) / p - convolution (indicator A₂) μ u)) ≤ ε := by
    calc
      _ ≤ ∑ u ∈ U, |convolution (indicator A₂) μ u - (A₂.card : ℝ) / p| := by
        apply Finset.sum_le_sum
        intro u _
        rw [← neg_sub]
        apply neg_le_abs
      _ ≤ ∑ u : ZMod p, |convolution (indicator A₂) μ u - (A₂.card : ℝ) / p| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ ↦ abs_nonneg _)
      _ ≤ ε := hL1
  have hmean : (∑ _ ∈ U, (A₂.card : ℝ) / p) = (A₂.card : ℝ) * U.card / p := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_sub_distrib, hmean] at hdiff
  calc
    _ ≤ (S.card : ℝ) * ∑ u ∈ U, convolution (indicator A₂) μ u :=
      mul_le_mul_of_nonneg_left (by linarith only [hdiff]) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [predicted, convolution_indicator, ← Finset.mul_sum]
      rw [Finset.sum_comm]

/-- Exceptional positions that occur in the second half of the sample. -/
noncomputable def exceptionalHits (A₂ U S : Finset (ZMod p)) (μ : ZMod p → ℝ) (r k : ℕ) :
    Finset (ZMod p) :=
  A₂ ∩ exceptional (discrepancy U S μ) (cutoff r S.card k)

/-- The deterministic hit-count implication of the three estimates preceding Parseval in §5. -/
lemma exceptionalHits_lower_of_prediction_cap (A₂ U S : Finset (ZMod p))
    (μ : ZMod p → ℝ) {r k : ℕ} (hr : 0 < r) (hk : 0 < k) (hS : S.Nonempty)
    (hA₂ : A₂.card ≤ k)
    (hpred : (0.244 : ℝ) * r * S.card ≤ ∑ z ∈ A₂, predicted U S μ z)
    (hobs : (∑ z ∈ A₂, observed U S z) ≤ (0.115 : ℝ) * r * S.card)
    (hcap : (∑ z ∈ exceptionalHits A₂ U S μ r k, predicted U S μ z) ≤
      (r : ℝ) * S.card *
        (0.51 * ((exceptionalHits A₂ U S μ r k).card : ℝ) / k + 0.001)) :
    (0.244 - 0.115 - 0.001 - 0.001 : ℝ) / 0.51 ≤
      ((exceptionalHits A₂ U S μ r k).card : ℝ) / k ∧
    (0.24 : ℝ) * k < (exceptionalHits A₂ U S μ r k).card := by
  classical
  let E := exceptionalHits A₂ U S μ r k
  let δ := cutoff r S.card k
  let rs : ℝ := (r : ℝ) * S.card
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hrs : 0 < rs := by dsimp [rs]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ, cutoff]; positivity
  have hE : E ⊆ A₂ := Finset.inter_subset_left
  have hcard : ((A₂ \ E).card : ℝ) ≤ k := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : A₂ \ E ⊆ A₂)).trans hA₂
  have hgood : (∑ z ∈ A₂ \ E, (predicted U S μ z - observed U S z)) ≤ (k : ℝ) * δ := by
    calc
      _ ≤ ∑ _ ∈ A₂ \ E, δ := by
        refine Finset.sum_le_sum fun z hz ↦ ?_
        obtain ⟨hzA, hzE⟩ := Finset.mem_sdiff.mp hz
        have hzδ : |discrepancy U S μ z| ≤ δ := by
          apply le_of_not_gt
          intro hzbad
          exact hzE (Finset.mem_inter.mpr ⟨hzA, (mem_exceptional _ _ _).mpr hzbad⟩)
        have hzLower := (abs_le.mp hzδ).1
        dsimp [discrepancy] at hzLower
        linarith only [hzLower]
      _ = ((A₂ \ E).card : ℝ) * δ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hδ
  have hbad : (∑ z ∈ E, (predicted U S μ z - observed U S z)) ≤
      rs * (0.51 * (E.card : ℝ) / k + 0.001) := by
    refine (Finset.sum_le_sum fun z _ ↦ sub_le_self _ ?_).trans hcap
    exact Nat.cast_nonneg _
  have htotal : (0.244 - 0.115 : ℝ) * rs ≤
      (∑ z ∈ A₂, (predicted U S μ z - observed U S z)) := by
    rw [Finset.sum_sub_distrib]
    dsimp [rs]
    linarith only [hpred, hobs]
  rw [← Finset.sum_sdiff hE] at htotal
  have hcutoff : (k : ℝ) * δ = 0.001 * rs := by
    dsimp [δ, cutoff, rs]
    field_simp
  have hgap := htotal.trans (add_le_add hgood hbad)
  rw [hcutoff] at hgap
  have hcancel : (0.244 - 0.115 : ℝ) ≤ 0.001 + (0.51 * (E.card : ℝ) / k + 0.001) := by
    apply (mul_le_mul_iff_right₀ hrs).mp
    convert hgap using 1 <;> ring
  have hratio : (0.244 - 0.115 - 0.001 - 0.001 : ℝ) / 0.51 ≤ (E.card : ℝ) / k := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.51)]
    rw [mul_div_assoc] at hcancel
    linarith only [hcancel]
  refine ⟨hratio, (lt_div_iff₀ hk').mp ?_⟩
  exact (by norm_num : (0.24 : ℝ) < (0.244 - 0.115 - 0.001 - 0.001) / 0.51).trans_le hratio

/-- The reflected convolution `1_{A₁} * μ̌` appearing in the smoothness assumption (4). -/
noncomputable def smoothed (A₁ : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) : ℝ :=
  ∑ a ∈ A₁, μ (a - z)

lemma smoothed_eq_convolution (A₁ : Finset (ZMod p)) (μ : ZMod p → ℝ) (z : ZMod p) :
    smoothed A₁ μ z = convolution (indicator A₁) (fun t ↦ μ (-t)) z := by
  simp [smoothed, convolution_indicator, neg_sub]

omit [NeZero p] in
private lemma predicted_le_sum_smoothed (A₁ R S : Finset (ZMod p)) (μ : ZMod p → ℝ)
    (hμ : ∀ z, 0 ≤ μ z) (z : ZMod p) :
    predicted (A₁ + R) S μ z ≤ (S.card : ℝ) * ∑ v ∈ R, smoothed A₁ μ (z - v) := by
  unfold predicted
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    (∑ u ∈ A₁ + R, μ (u - z)) ≤ ∑ b ∈ R ×ˢ A₁, μ (b.1 + b.2 - z) := by
      rw [add_comm A₁ R, Finset.add_def]
      exact Finset.sum_image_le_of_nonneg (fun u _ ↦ hμ (u - z))
    _ = _ := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun v _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
      congr 1
      abel

omit [NeZero p] in
/-- Counting all representations in `A₁ + R` and applying the smooth excess bound from (4). -/
lemma sum_predicted_le_of_smooth_cap (A₁ A₂ R S E : Finset (ZMod p)) (μ : ZMod p → ℝ) (k : ℕ)
    (hμ : ∀ z, 0 ≤ μ z) (hE : E ⊆ A₂)
    (hcap : ∀ v ∈ R, (∑ z ∈ A₂, max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001) :
    (∑ z ∈ E, predicted (A₁ + R) S μ z) ≤
      (R.card : ℝ) * S.card * (0.51 * (E.card : ℝ) / k + 0.001) := by
  have hshift (v : ZMod p) (hv : v ∈ R) :
      (∑ z ∈ E, smoothed A₁ μ (z - v)) ≤ 0.51 * (E.card : ℝ) / k + 0.001 := by
    have hexcess : (∑ z ∈ E, max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001 :=
      (Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ ↦ le_max_right _ _)).trans (hcap v hv)
    calc
      _ ≤ ∑ z ∈ E, ((0.51 : ℝ) / k + max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) := by
        refine Finset.sum_le_sum fun z _ ↦ ?_
        have hz := le_max_left (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0
        linarith only [hz]
      _ ≤ _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        have hconst : (E.card : ℝ) * ((0.51 : ℝ) / k) = 0.51 * E.card / k := by ring
        rw [hconst]
        exact add_le_add le_rfl hexcess
  calc
    _ ≤ ∑ z ∈ E, (S.card : ℝ) * ∑ v ∈ R, smoothed A₁ μ (z - v) :=
      Finset.sum_le_sum fun z _ ↦ predicted_le_sum_smoothed A₁ R S μ hμ z
    _ = (S.card : ℝ) * ∑ v ∈ R, ∑ z ∈ E, smoothed A₁ μ (z - v) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (S.card : ℝ) * ∑ _ ∈ R, (0.51 * (E.card : ℝ) / k + 0.001) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hshift) (Nat.cast_nonneg _)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The required hit count using the smooth excess bound and the two aggregate estimates in §5. -/
lemma exceptionalHits_section5 (A₁ A₂ R S : Finset (ZMod p)) (μ : ZMod p → ℝ) {k : ℕ}
    (hk : 0 < k) (hR : R.Nonempty) (hS : S.Nonempty) (hA₂ : A₂.card ≤ k)
    (hμ : ∀ z, 0 ≤ μ z)
    (hpred : (0.244 : ℝ) * R.card * S.card ≤ ∑ z ∈ A₂, predicted (A₁ + R) S μ z)
    (hobs : (∑ z ∈ A₂, observed (A₁ + R) S z) ≤ (0.115 : ℝ) * R.card * S.card)
    (hcap : ∀ v ∈ R, (∑ z ∈ A₂, max (smoothed A₁ μ (z - v) - (0.51 : ℝ) / k) 0) ≤ 0.001) :
    (0.244 - 0.115 - 0.001 - 0.001 : ℝ) / 0.51 ≤
      ((exceptionalHits A₂ (A₁ + R) S μ R.card k).card : ℝ) / k ∧
    (0.24 : ℝ) * k < (exceptionalHits A₂ (A₁ + R) S μ R.card k).card := by
  apply exceptionalHits_lower_of_prediction_cap _ _ _ _ hR.card_pos hk hS hA₂ hpred hobs
  exact sum_predicted_le_of_smooth_cap A₁ A₂ R S _ μ k hμ Finset.inter_subset_left hcap

end OnePercent.Fourier

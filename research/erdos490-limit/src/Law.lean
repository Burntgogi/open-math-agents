import Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
namespace Shift490
open Finset Real Filter MeasureTheory
open scoped Topology

theorem P_union {D B : Finset ℕ} (hd : Disjoint D B) : P (D ∪ B) = P D * P B := by
  simp only [P,filter_union,prod_union (hd.mono (filter_subset Nat.Prime D) (filter_subset Nat.Prime B))]

theorem one_le_P (S : Finset ℕ) : 1 ≤ P S := by
  apply Finset.one_le_prod
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (mem_filter.mp hp).2.one_lt
  apply (one_le_inv₀ (sub_pos.mpr ((inv_lt_one₀ (by positivity)).mpr h))).mpr
  linarith [show 0 ≤ (p:ℝ)⁻¹ by positivity]

lemma hnonneg {D} (a : Integers D) : 0 ≤ harmonic D a :=
  div_nonneg (by positivity) (P_pos D).le

def avg (D : Finset ℕ) (f : ℝ → ℝ) := ∑' a : Integers D, harmonic D a * f (logN a)

lemma avg_summable {D : Finset ℕ} {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) :
    Summable (fun a : Integers D => harmonic D a * f (logN a)) :=
  Summable.of_nonneg_of_le (fun a => mul_nonneg (hnonneg a) (hf _).1)
    (fun a => mul_le_mul_of_nonneg_left (hf _).2 (hnonneg a))
    ((harmonic_probability D).summable.mul_right M)

lemma avg_mul (D) (c : ℝ) (f : ℝ → ℝ) :
    avg D (fun x => c * f x) = c * avg D f := by
  simp only [avg, ← tsum_mul_left, mul_left_comm c]

def rootReciprocal : ℕ →* ℝ where
  toFun n := (√(n:ℝ))⁻¹
  map_one' := by simp
  map_mul' := by simp [Real.sqrt_mul (Nat.cast_nonneg _), mul_comm]

theorem half_moment (D : Finset ℕ) :
    Summable (fun a : Integers D => harmonic D a * exp (logN a / 2)) := by
  have hp {p : ℕ} (h : p.Prime) : ‖rootReciprocal p‖ < 1 := by
    change ‖(√(p:ℝ))⁻¹‖ < 1
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have h' : 1 < (p:ℝ) := by exact_mod_cast h.one_lt
    have hs : 1 < √(p:ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ)]
    exact (inv_lt_one₀ (by positivity)).mpr hs
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := rootReciprocal) hp D).2.summable.div_const (P D)
  apply h.congr
  intro a
  change (√(a.val:ℝ))⁻¹ / P D = ((a.val:ℝ)⁻¹ / P D) * exp (log (a.val:ℝ) / 2)
  rw [Real.exp_half, Real.exp_log (nat_pos a)]
  field_simp [Real.sqrt_ne_zero'.mpr (nat_pos a), (nat_pos a).ne', (P_pos D).ne']
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg a.val)]

def moment (D : Finset ℕ) := ∑' a : Integers D, harmonic D a * exp (logN a / 2)

/-- Dual total-variation formulation for the translate of a smoothed probability law. -/
def blend (D : Finset ℕ) (κ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) :=
  avg D (fun v => ∫ u, f (t - v - u) ∂κ)

def KernelFlat (D : Finset ℕ) (H δ η : ℝ) : Prop :=
  ∃ κ : Measure ℝ, IsProbabilityMeasure κ ∧ (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧
    ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
    ∀ t z : ℝ, |t| ≤ H → |z| ≤ H → blend D κ f t ≤ blend D κ f z + η

/-- Past and future translates of the same kernel sandwich a one-sided regular profile.
The kernel can be any probability on the stated interval. -/
theorem desmooth {D : Finset ℕ} {H δ η : ℝ} (flat : KernelFlat D H δ η)
    {f : ℝ → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hslow : ∀ x y, x ≤ y → f x ≤ exp (y-x) * f y)
    {s t : ℝ} (hs : |s+δ| ≤ H) (ht : |t| ≤ H) (hδ : 0 ≤ δ) :
    avg D (fun v => f (s-v)) ≤ avg D (fun v => f (t-v)) +
      (exp δ - 1)*2 + η := by
  obtain ⟨κ,hκ,hsupp,hflat⟩ := flat
  let _ := hκ
  let I (r v : ℝ) := ∫ u, f (r-v-u) ∂κ
  have hint (r v : ℝ) : Integrable (fun u => f (r-v-u)) κ := by
    apply (integrable_const (μ := κ) (1:ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
    exact ae_of_all _ fun u => by
      change ‖f (r-v-u)‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (h01 _).1]
      exact (h01 _).2
  have hI (r v : ℝ) : 0 ≤ I r v ∧ I r v ≤ 1 :=
    ⟨integral_nonneg (fun _ => (h01 _).1), by
      simpa [I] using integral_mono (hint r v) (integrable_const (μ := κ) (1:ℝ)) (fun u => (h01 _).2)⟩
  have err : 0 ≤ exp δ - 1 := sub_nonneg.mpr (Real.one_le_exp hδ)
  have point (x y : ℝ) (hxy : x ≤ y) (hy : y-x ≤ δ) :
      f x ≤ f y + (exp δ - 1) := by
    have h' := (hslow x y hxy).trans (mul_le_mul_of_nonneg_right (exp_le_exp.mpr hy) (h01 y).1)
    nlinarith [mul_nonneg err (sub_nonneg.mpr (h01 y).2)]
  have past (v : ℝ) : f (s-v) ≤ I (s+δ) v + (exp δ-1) := by
    have h := integral_mono_ae (integrable_const (μ := κ) (f (s-v)))
      ((hint (s+δ) v).add (integrable_const (exp δ-1))) (by
        filter_upwards [hsupp] with u hu
        exact point _ _ (by linarith [hu.2]) (by linarith [hu.1]))
    simpa [I, integral_add (hint (s+δ) v) (integrable_const (exp δ-1))] using h
  have future (v : ℝ) : I t v ≤ f (t-v) + (exp δ-1) := by
    have h := integral_mono_ae (hint t v) (integrable_const (μ := κ) (f (t-v)+(exp δ-1))) (by
      filter_upwards [hsupp] with u hu
      exact point _ _ (by linarith [hu.1]) (by linarith [hu.2]))
    simpa [I] using h
  have lift {f g : ℝ → ℝ} (h1 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
      (h2 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (h : ∀ x, f x ≤ g x + (exp δ-1)) :
      avg D f ≤ avg D g + (exp δ-1) := by
    have hsum := (harmonic_probability D).mul_right (exp δ-1)
    have hb := (avg_summable (D := D) h2).hasSum.add hsum
    simpa [avg] using hasSum_le (fun a => by
      simpa [mul_add] using mul_le_mul_of_nonneg_left (h (logN a)) (hnonneg a))
      (avg_summable (D := D) h1).hasSum hb
  have h1 := lift (fun x => h01 (s-x)) (hI (s+δ)) past
  have h2 := lift (hI t) (fun x => h01 (t-x)) future
  have h3 := hflat f hf h01 (s+δ) t hs ht
  change avg D (I (s+δ)) ≤ avg D (I t) + η at h3
  linarith

#print axioms half_moment
#print axioms desmooth
end Shift490

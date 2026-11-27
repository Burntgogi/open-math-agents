import Grid
import PrimeInput
import Shift

noncomputable section
namespace Shift490
open Finset Real Filter MeasureTheory
open scoped Topology

/-- A prime-free, one-dimensional compact-kernel inequality. Frequencies use exp(i*t*x).
Both sides are homogeneous of degree two in the unnormalized finite atom weights. -/
def CompactKernelEstimate : Prop :=
  ∀ δ H : ℝ, 0 < δ → 0 ≤ H → ∃ (κ : Measure ℝ) (K : ℝ → ℂ) (A C : ℝ),
    IsProbabilityMeasure κ ∧ (∀ᵐ u ∂κ, u ∈ Set.Icc 0 δ) ∧ 0 ≤ C ∧
    Continuous K ∧ (∀ t, ‖K t‖ ≤ A) ∧
    Integrable (fun t : ℝ => t^2 * ‖K t‖^2) ∧
    Integrable (fun t : ℝ => |t| * (t^2 * ‖K t‖^2)) ∧
    ∀ (Ω : Type) (S : Finset Ω) (w v : Ω → ℝ) (a L : ℝ),
      (∀ y ∈ S, 0 ≤ w y ∧ a ≤ v y ∧ v y ≤ a+L) →
      ∀ (f : ℝ → ℝ), Measurable f → (∀ z, 0 ≤ f z ∧ f z ≤ 1) →
      ∀ s r : ℝ, |s| ≤ H → |r| ≤ H →
        (∑ y ∈ S, w y * (testAt κ f s (v y) - testAt κ f r (v y)))^2 ≤
          C * (L+1) * ∫ t : ℝ, t^2 * ‖K t‖^2 * ‖∑ y ∈ S, (w y:ℂ) * phase t (v y)‖^2

private lemma choose_m {c η C A U V : ℝ} (hc : 0 < c) (hη : 0 < η) (hC : 0 ≤ C)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    ∃ m : ℕ, 0 < m ∧ 1/(m:ℝ) ≤ η/2 ∧
    C*((m:ℝ)+1)*(A^2/(c*m)*√(π/(c*m)) + (c*m)⁻¹^2*U + ((m:ℝ)^2)⁻¹*V) ≤ (η/2)^2 := by
  have hinv : Tendsto (fun m : ℕ => (m:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun m : ℕ => C * (2*A^2/c*√((π/c)*(m:ℝ)⁻¹) +
      (2*U/c^2+2*V)*(m:ℝ)⁻¹)) atTop (𝓝 0) := by
    have hh := ((hinv.const_mul (π/c)).sqrt.const_mul (2*A^2/c)).add (hinv.const_mul (2*U/c^2+2*V))
    simpa using hh.const_mul C
  have hev := hlim.eventually (gt_mem_nhds (show 0 < (η/2)^2 by positivity))
  have hev' := hinv.eventually (gt_mem_nhds (show 0 < η/2 by positivity))
  obtain ⟨m,h1,h2,h3⟩ := (hev.and (hev'.and (eventually_gt_atTop 0))).exists
  refine ⟨m,h3,by simpa only [one_div] using h2.le,?_⟩
  have hm : 1 ≤ (m:ℝ) := by exact_mod_cast h3
  have hn : 0 < (m:ℝ) := by linarith
  calc
    _ ≤ C*(2*m)*(A^2/(c*m)*√(π/(c*m))+(c*m)⁻¹^2*U+((m:ℝ)^2)⁻¹*V) := by gcongr; linarith
    _ = C*(2*A^2/c*√((π/c)*(m:ℝ)⁻¹)+(2*U/c^2+2*V)*(m:ℝ)⁻¹) := by
      rw [show π/(c*m) = (π/c)*(m:ℝ)⁻¹ by ring]
      field_simp; ring
    _ ≤ _ := h1.le

private lemma char_cont (A : Finset ℕ) (j : ℕ) : Continuous (char A j) := by unfold char; fun_prop

private lemma char_le_one (A : Finset ℕ) (j : ℕ) (t : ℝ) : ‖char A j t‖ ≤ 1 := by
  unfold char
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ mass A by apply sum_nonneg; intros; positivity)]
  apply div_le_of_le_mul₀ (by apply sum_nonneg; intros; positivity) zero_le_one
  rw [one_mul]
  refine (norm_sum_le ..).trans ?_
  apply sum_le_sum
  intro p _
  change ‖(p:ℂ)⁻¹ * phase t (log p-j)‖ ≤ _
  rw [norm_mul,norm_phase,mul_one]; simp

theorem successful_of_kernel (kernel : CompactKernelEstimate) (Y : ℕ) : SuccessfulComponents Y := by
  intro c H δ η hc hH hδ hη
  obtain ⟨κ,K,A,C,hκ,hsupp,hC,hK,hA,hI,hJ,hkernel⟩ := kernel δ H hδ hH
  let U := ∫ t : ℝ, t^2*‖K t‖^2
  let V := ∫ t : ℝ, |t| * (t^2*‖K t‖^2)
  obtain ⟨m,hm,hfrac,hbound⟩ := choose_m (A := A) (U := U) (V := V) hc hη hC
    (integral_nonneg (fun _ => by positivity)) (integral_nonneg (fun _ => by positivity))
  refine ⟨m,κ,hm,hfrac,hκ,hsupp,?_⟩
  intro J B hB hband I hcard x f hf h01 s r hs hr
  let R := Fintype.piFinset (rect J B I x)
  let W (y : ∀ j, Integers (B j)) := ∏ j, harmonic (B j) (y j)
  let Z (y : ∀ j, Integers (B j)) := ∑ j, logN (y j)
  let N := ∑ y ∈ R, W y
  have hw (y) : 0 ≤ W y := prod_nonneg (fun i _ => hnonneg (y i))
  have hN : 0 ≤ N := sum_nonneg fun y _ => hw y
  obtain ⟨a,ha⟩ := rect_support J B I hB x
  have he := hkernel _ R W Z a I.card (fun y hy => ⟨hw y,ha y hy⟩) f hf h01 s r hs hr
  have ht := rect_transform J B I (fun i p hp => (mem_filter.mp (mem_filter.mp (hB i hp)).1).2) x
  have hχ (t : ℝ) : ‖∑ y ∈ R, (W y:ℂ)*phase t (Z y)‖ = N*‖∏ i ∈ I, char (B i) i t‖ := ht t
  simp_rw [hχ,mul_pow] at he
  have hfun : (fun t : ℝ => t^2 * ‖K t‖^2 * (N^2 * ‖∏ i ∈ I, char (B i) i t‖^2)) =
      (fun t : ℝ => N^2 * (t^2 * ‖K t‖^2 * ‖∏ i ∈ I, char (B i) i t‖^2)) := by funext t; ring
  rw [hfun,integral_const_mul] at he
  have hE := spectral_energy I (fun i t => char (B i) i t) K hc (hcard ▸ hm) hA
    (fun i _ => (hband i).1) (fun i _ t h1 h2 => (hband i).2 t h1 (hcard ▸ h2))
    (fun i _ t => char_le_one (B i) i t) (fun i _ => char_cont ..) hK hI hJ
  rw [hcard] at hE he
  have hfactor : 0 ≤ C * ((m:ℝ)+1) := by positivity
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hfactor) (sq_nonneg N)
  have hh' := mul_le_mul_of_nonneg_left hbound (sq_nonneg N)
  let d := ∑ y ∈ R, W y * (testAt κ f s (Z y)-testAt κ f r (Z y))
  have dsq : d^2 ≤ (N*(η/2))^2 := by
    dsimp only [U,V] at hh'
    dsimp only [d]; nlinarith only [he,hh,hh']
  have hd : d ≤ N*(η/2) := (abs_le_of_sq_le_sq' dsq (by positivity)).2
  change (∑ y ∈ R, W y * testAt κ f s (Z y)) ≤ ∑ y ∈ R, W y * (testAt κ f r (Z y)+η/2)
  simp only [d,mul_sub,sum_sub_distrib,N] at hd
  simp only [mul_add,sum_add_distrib,← sum_mul]
  linarith

/-- The complete stability statement reduced to a pure compact-kernel inequality. -/
theorem one_color_of_kernel (kernel : CompactKernelEstimate) (Y : ℕ) : OneColorShift Y :=
  one_color_shift (prime_cells_of_rectangles (rectangle_pnt Y))
    (smoothing_of_successful (successful_of_kernel kernel Y))

#print axioms one_color_of_kernel
end Shift490

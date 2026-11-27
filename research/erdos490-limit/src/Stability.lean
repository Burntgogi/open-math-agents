import KernelEstimate
import Plancherel

noncomputable section
namespace Shift490
open Filter Finset Real MeasureTheory
open scoped FourierTransform SchwartzMap Topology ENNReal

private lemma supported_sq (d : 𝓢(ℝ,ℂ)) {a b : ℝ} (hab : a < b)
    (hs : ∀ x, x ∉ Set.Icc a b → d x = 0) :
    (∫ x, ‖d x‖)^2 ≤ (b-a) * ∫ x, ‖d x‖^2 := by
  let U := Set.Icc a b
  let c := (∫ x, ‖d x‖)/(b-a)
  have h1 : ∫ x in U, ‖d x‖ = ∫ x, ‖d x‖ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; rw [hs x hx,norm_zero]
  have h2 : ∫ x in U, ‖d x‖^2 = ∫ x, ‖d x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx; rw [hs x hx,norm_zero]; norm_num
  have hvol : volume.real U = b-a := by simp [U,Real.volume_real_Icc_of_le hab.le]
  have hint : IntegrableOn (fun x => ‖d x‖^2) U := (schwartz_sq d).integrableOn
  have hi1 : IntegrableOn (fun x => 2*c*‖d x‖) U := (d.integrable.norm.const_mul _).integrableOn
  have hi0 : IntegrableOn (fun _ : ℝ => c^2) U := by
    exact integrableOn_const measure_Icc_lt_top.ne
  have hnon : 0 ≤ ∫ x in U, (‖d x‖-c)^2 := integral_nonneg fun x => sq_nonneg _
  simp_rw [show ∀ x : ℝ, (‖d x‖-c)^2 = ‖d x‖^2 - 2*c*‖d x‖ + c^2 by intro; ring] at hnon
  have hsub : IntegrableOn (fun x => ‖d x‖^2 - 2*c*‖d x‖) U := hint.sub hi1
  rw [integral_add hsub hi0,integral_sub hint hi1,integral_const_mul,h1,h2,
    setIntegral_const,smul_eq_mul,hvol] at hnon
  have hlen := sub_pos.mpr hab
  have hmean : c*(b-a) = ∫ x, ‖d x‖ := div_mul_cancel₀ _ hlen.ne'
  nlinarith [mul_nonneg hnon hlen.le,congrArg (fun z : ℝ => z^2) hmean,
    congrArg (fun z : ℝ => z*(∫ x, ‖d x‖)) hmean]

private lemma test_integrable (d : 𝓢(ℝ,ℂ)) {f : ℝ → ℝ} (hf : Measurable f)
    (h01 : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    Integrable (fun x => f (-x)*(d x).re) := by
  apply d.integrable.norm.mono' ((hf.comp measurable_neg).mul (Complex.continuous_re.comp d.continuous).measurable).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  change ‖f (-x)*(d x).re‖ ≤ ‖d x‖
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (h01 _).1]
  simpa using mul_le_mul (h01 (-x)).2 (Complex.abs_re_le_norm (d x)) (abs_nonneg _) zero_le_one

private lemma density_test {κ : Measure ℝ} {g : 𝓢(ℝ,ℂ)}
    (h : ∀ (f : ℝ → ℝ) s z, testAt κ f s z = ∫ x : ℝ, f (-x)*(g (x-(z-s))).re)
    {Ω : Type} (S : Finset Ω) (w z : Ω → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (s : ℝ) :
    ∑ y ∈ S, w y * testAt κ f s (z y) = ∫ x : ℝ, f (-x)*(density g S w z s x).re := by
  simp_rw [h,← integral_const_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by
      simp only [density_apply,Complex.re_sum,mul_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact sum_congr rfl (fun _ _ => by ring)
  · intro y _
    exact (test_integrable (g.compSubConstCLM ℂ (z y-s)) hf h01).const_mul _

theorem compact_kernel_estimate : CompactKernelEstimate := by
  intro δ H hδ hH
  obtain ⟨κ,g,hκ,hAE,hsupp,htest⟩ := compact_bump hδ
  let k := -2*π
  have hk : k ≠ 0 := by dsimp [k]; positivity
  let K (t : ℝ) := 𝓕 g (k⁻¹*t)
  obtain ⟨A,hK,hA,hI,hJ⟩ := angular_weights (𝓕 g) (inv_ne_zero hk)
  let C := (1+δ+2*H)*(4*H)^2*|k⁻¹|
  refine ⟨κ,K,A,C,hκ,hAE,by dsimp [C]; positivity,hK,hA,hI,hJ,?_⟩
  intro Ω S w z a L hdata f hf h01 s r hs hr
  by_cases hne : S.Nonempty
  swap
  · simp [not_nonempty_iff_eq_empty.mp hne]
  obtain ⟨y,hy⟩ := hne
  have hL : 0 ≤ L := by linarith [(hdata y hy).2.1,(hdata y hy).2.2]
  let d := density g S w z s - density g S w z r
  have support (q : ℝ) (hq : |q| ≤ H) (x : ℝ) (hx : x ∉ Set.Icc (a-H) (a+L+H+δ)) :
      density g S w z q x = 0 := by
    rw [density_apply]
    apply sum_eq_zero
    intro y hy
    rw [hsupp _ (fun hh => hx ⟨by linarith [hh.1,(hdata y hy).2.1,(abs_le.mp hq).2],
      by linarith [hh.2,(hdata y hy).2.2,(abs_le.mp hq).1]⟩),mul_zero]
  have hsup (x : ℝ) (hx : x ∉ Set.Icc (a-H) (a+L+H+δ)) : d x = 0 := by
    change density g S w z s x - density g S w z r x = _
    rw [support s hs x hx,support r hr x hx,sub_zero]
  have hsq := supported_sq d (by linarith : a-H < a+L+H+δ) hsup
  let E := ∫ t : ℝ, t^2*‖K t‖^2*‖∑ y ∈ S, (w y:ℂ)*phase t (z y)‖^2
  have hE : 0 ≤ E := integral_nonneg fun _ => by positivity
  have hd := density_energy g S w z s r
  change (∫ x, ‖d x‖^2) ≤ (2*|s-r|)^2*|k⁻¹| * E at hd
  have hw : a+L+H+δ-(a-H) ≤ (1+δ+2*H)*(L+1) := by
    nlinarith [mul_nonneg hL (show 0 ≤ δ+2*H by linarith)]
  have hsr : 2*|s-r| ≤ 4*H := by linarith [(abs_sub s r).trans (add_le_add hs hr)]
  have hbound : (∫ x, ‖d x‖)^2 ≤ C*(L+1)*E := by
    calc
      _ ≤ _ := hsq
      _ ≤ ((1+δ+2*H)*(L+1))*((4*H)^2*|k⁻¹| * E) := by
        apply mul_le_mul hw (hd.trans ?_) (integral_nonneg fun _ => sq_nonneg _) (by positivity)
        gcongr
      _ = _ := by dsimp [C]; ring
  simp_rw [mul_sub,sum_sub_distrib,density_test htest S w z f hf h01]
  rw [← integral_sub (test_integrable _ hf h01) (test_integrable _ hf h01)]
  apply le_trans _ hbound
  have hnorm : |∫ x : ℝ, (f (-x)*(density g S w z s x).re - f (-x)*(density g S w z r x).re)| ≤
      ∫ x, ‖d x‖ := by
    rw [← Real.norm_eq_abs]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono ((test_integrable _ hf h01).sub (test_integrable _ hf h01)).norm d.integrable.norm
    intro x
    change ‖f (-x)*(density g S w z s x).re - f (-x)*(density g S w z r x).re‖ ≤ ‖d x‖
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg (h01 _).1]
    change f (-x) * |(d x).re| ≤ ‖d x‖
    simpa using mul_le_mul (h01 (-x)).2 (Complex.abs_re_le_norm (d x)) (abs_nonneg _) zero_le_one
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hnorm 2

theorem prime_cell_input (Y : ℕ) : PrimeCellInput Y := prime_cells_of_rectangles (rectangle_pnt Y)

theorem finite_smoothing (Y : ℕ) : FiniteSmoothing Y :=
  smoothing_of_successful (successful_of_kernel compact_kernel_estimate Y)

/-- Every sequence of two-color prime partitions admits a single stable side on a
subsequence, simultaneously on every bounded log window. -/
theorem one_color_shift_stability (Y : ℕ) : OneColorShift Y := one_color_of_kernel compact_kernel_estimate Y

#print Shift490.OneColorShift
#check @one_color_shift_stability
#print axioms compact_kernel_estimate
#print axioms one_color_shift_stability
end Shift490

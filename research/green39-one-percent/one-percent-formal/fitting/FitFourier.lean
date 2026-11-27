import FitStage

/-! # A finite, deterministically decodable Fourier fit or a small uncovered remainder -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def realTests (χ : σ → ι → ℂ) (j : σ × Bool) (i : ι) : ℝ :=
  if j.2 then (χ j.1 i).re else (χ j.1 i).im

def transform (χ : σ → ι → ℂ) (m : ι → ℝ) (j : σ) : ℂ :=
  ∑ i, χ j i * (m i : ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem realTests_bound {χ : σ → ι → ℂ} (h : ∀ j i, ‖χ j i‖ ≤ 1) :
    ∀ j i, |realTests χ j i| ≤ 1 := by
  rintro ⟨j,b⟩ i
  cases b
  · exact (Complex.abs_im_le_norm _).trans (h j i)
  · exact (Complex.abs_re_le_norm _).trans (h j i)

omit [DecidableEq ι] in
private theorem transform_re (χ : σ → ι → ℂ) (m : ι → ℝ) (j : σ) :
    (transform χ m j).re = testMean m (realTests χ (j,true)) := by
  simp [transform,testMean,realTests,Complex.re_sum,Complex.mul_re,mul_comm]

omit [DecidableEq ι] in
private theorem transform_im (χ : σ → ι → ℂ) (m : ι → ℝ) (j : σ) :
    (transform χ m j).im = testMean m (realTests χ (j,false)) := by
  simp [transform,testMean,realTests,Complex.im_sum,Complex.mul_im,mul_comm]

theorem fourier_fit_of_fitted {F : Finset ι} {χ : σ → ι → ℂ} {η cap : ℝ} {μ : ι → ℝ}
    (he : 0 ≤ η) (hf : Fitted F (realTests χ) η cap μ) (j : σ) :
    ‖transform χ (uniformOn F) j - transform χ μ j‖ ≤ 5*η := by
  let z := transform χ (uniformOn F) j - transform χ μ j
  have hr : |z.re| ≤ 3*η := by simpa only [z,Complex.sub_re,transform_re] using hf.2.2 (j,true)
  have hi : |z.im| ≤ 3*η := by simpa only [z,Complex.sub_im,transform_im] using hf.2.2 (j,false)
  have hrs := sq_le_sq.mpr (show |z.re| ≤ |3*η| by simpa [abs_of_nonneg (by positivity : 0 ≤ 3*η)] using hr)
  have his := sq_le_sq.mpr (show |z.im| ≤ |3*η| by simpa [abs_of_nonneg (by positivity : 0 ≤ 3*η)] using hi)
  have hz := Complex.sq_norm z
  rw [Complex.normSq_apply] at hz
  change ‖z‖ ≤ 5*η
  nlinarith [norm_nonneg z,sq_nonneg η]

theorem cyclic_transform {p : ℕ} [NeZero p] (m : ZMod p → ℝ) (j : ZMod p) :
    transform (fun t i : ZMod p => ZMod.stdAddChar (-(i*t))) m j =
      ZMod.dft (fun i => (m i : ℂ)) j := by
  simp only [transform,ZMod.dft_apply,smul_eq_mul]

omit [DecidableEq ι] in
theorem heavy_card {m : ι → ℝ} (hm : ∀ x, 0 ≤ m x) (hs : ∑ x, m x = 1)
    {cap : ℝ} (hc : 0 < cap) : ((heavy cap m).card : ℝ) ≤ 1/cap := by
  apply (le_div_iff₀ hc).mpr
  calc
    _ = ∑ _ ∈ heavy cap m, cap := by simp
    _ ≤ ∑ i ∈ heavy cap m, m i := by
       apply sum_le_sum
       intro i hi
       exact (mem_filter.mp hi).2.le
    _ ≤ ∑ i, m i := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => hm i)
    _ = _ := hs

theorem recordedUnion_card [Nonempty ι] (g : σ → ι → ℝ) (η : ℝ) {cap : ℝ}
    (hc : 0 < cap) (ws : List (List (Instruction σ))) :
    ((recordedUnion g η cap ws).card : ℝ) ≤ ws.length / cap := by
  induction ws with
  | nil => simp [recordedUnion]
  | cons w ws ih =>
    let J := heavy cap (decode g η cap w)
    have hsub : (recordedUnion g η cap (w::ws)).card ≤ J.card + (recordedUnion g η cap ws).card :=
      card_union_le _ _
    obtain ⟨hm,hs⟩ := decode_law g η cap w
    have hJ := heavy_card (fun i => (hm i).le) hs hc
    calc
      ((recordedUnion g η cap (w::ws)).card : ℝ)
          ≤ (J.card : ℝ) + (recordedUnion g η cap ws).card := by exact_mod_cast hsub
      _ ≤ 1/cap + ws.length/cap := add_le_add hJ ih
      _ = _ := by simp [add_div,add_comm]

def cyclicTests (p : ℕ) [NeZero p] := realTests (fun t i : ZMod p => ZMod.stdAddChar (-(i*t)))

def fittedLaw {p : ℕ} [NeZero p] (η cap : ℝ) (w : List (Instruction (ZMod p × Bool))) :
    ZMod p → ℝ :=
  let m := decode (cyclicTests p) η cap w
  clipped (heavy cap m) m

/-- The §3 dichotomy with a uniform Fourier error 5η, explicit decoder, bounds on both
transcript lengths, and the size of each decoded container. -/
theorem cyclic_stage {p : ℕ} [NeZero p] {η cap θ : ℝ} (he : 0 < η)
    (he' : η ≤ 1/2) (hc : 0 < cap) (ht : 0 < θ)
    (B n : ℕ) (hB : 16*log p < B*η^2) (V : Finset (ZMod p))
    (hN : (1-η/2)^n * V.card < θ) :
    (∃ F ⊆ V, θ ≤ F.card ∧ ∃ w : List (Instruction (ZMod p × Bool)), w.length ≤ B ∧
      let μ := fittedLaw η cap w
      (∑ i, μ i = 1) ∧ (∀ i, 0 ≤ μ i ∧ μ i ≤ 2*cap) ∧ ∀ j : ZMod p,
      ‖ZMod.dft (fun i => (uniformOn F i : ℂ)) j - ZMod.dft (fun i => (μ i : ℂ)) j‖ ≤ 5*η) ∨
    (∃ ws : List (List (Instruction (ZMod p × Bool))), ws.length ≤ n ∧ (∀ w ∈ ws, w.length ≤ B) ∧
      let P := recordedUnion (cyclicTests p) η cap ws
      (P.card : ℝ) ≤ n/cap ∧ ((V \ P).card : ℝ) < θ) := by
  have hg : ∀ j i, |cyclicTests p j i| ≤ 1 := by
    apply realTests_bound
    intro j i
    simp
  have hh := stage_alternative hg he he' hc.le ht B (by simpa [ZMod.card] using hB) n V hN
  rcases hh with ⟨F,hFV,hs,w,hw,hf⟩ | ⟨ws,hn,hlen,hrem⟩
  · refine Or.inl ⟨F,hFV,hs,w,hw,hf.1,hf.2.1,?_⟩
    intro j
    simpa only [fittedLaw,cyclic_transform] using fourier_fit_of_fitted he.le hf j
  · refine Or.inr ⟨ws,hn,hlen,?_,hrem⟩
    exact (recordedUnion_card (cyclicTests p) η hc ws).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hn) hc.le)

#print axioms fourier_fit_of_fitted
#print axioms cyclic_transform
#print axioms cyclic_stage

end
end Green39.Fitting

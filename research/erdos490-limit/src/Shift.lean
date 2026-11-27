import Transfer
import Selection

noncomputable section
namespace Shift490
open Finset Real Filter
open scoped Topology

/-- Uniform little-o, written with an eventual bound for every point in the window.
The side and subsequence precede both the radius and the error tolerance. -/
def OneColorShift (Y : ℕ) : Prop :=
  ∀ (X : ℕ → ℝ), Tendsto X atTop atTop → ∀ q : ℕ → ℕ → Bool,
    ∃ (σ : ℕ → ℕ) (b : Bool), StrictMono σ ∧
    ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      let C := side Y (X (σ i)) (q (σ i)) b
      let w := log (X (σ i))
      ∀ s : ℝ, |s| ≤ H → |F C (w+s) - F C w| ≤ ε * (P C / w)

theorem one_color_shift {Y : ℕ} (primeCells : PrimeCellInput Y)
    (finiteSmoothing : FiniteSmoothing Y) : OneColorShift Y := by
  intro X hX q
  obtain ⟨σ,b,hσ,hside⟩ := fixed_side primeCells finiteSmoothing X hX q
  refine ⟨σ,b,hσ,?_⟩
  intro H hH ε hε
  let δ := log (1 + ε/(64*K₀))
  let η := ε/(32*K₀)
  have hK := K₀_pos
  have hδ : 0 < δ := Real.log_pos (lt_add_of_pos_right 1 (div_pos hε (by positivity)))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨D,hflat,hembed⟩ := hside (H+δ) δ η (by linarith) hδ hη
  let L (i : ℕ) := log (X (σ i))
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp (hX.comp hσ.tendsto_atTop)
  have hquarter : Tendsto (fun i => L i / 4) atTop atTop := hL.atTop_div_const (by norm_num)
  have htail : Tendsto (fun i => L i * (moment D * exp (-L i / 4))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hquarter).const_mul (4*moment D)
    simpa only [mul_zero] using h.congr (fun i => by
      dsimp [Function.comp_def]; rw [pow_one,neg_div]; ring)
  have hbudget : 4*K₀*((exp δ-1)*2+η) = ε/4 := by
    dsimp [δ,η]
    rw [Real.exp_log (by positivity)]
    field_simp
    ring
  filter_upwards [hembed,hL.eventually_gt_atTop (4*H+1),
    htail.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))] with i hi hlarge hsmall
  let C := side Y (X (σ i)) (q (σ i)) b
  let B := C \ D
  have he : D ∪ B = C := union_sdiff_of_subset hi
  have hd : Disjoint D B := Finset.disjoint_left.mpr (fun _ h₁ h₂ => (mem_sdiff.mp h₂).2 h₁)
  change ∀ s : ℝ, |s| ≤ H → |F C (L i+s) - F C (L i)| ≤ ε * (P C / L i)
  have hpos : 0 < L i := by linarith
  have hE := div_nonneg (P_pos C).le hpos.le
  have compare (s t : ℝ) (hs : |s| ≤ H) (ht : |t| ≤ H) :
      F C (L i+s) ≤ F C (L i+t) + ε*(P C/L i) := by
    have hh := window_comparison hd hpos (by linarith : 4*H ≤ L i) hs ht hδ.le hflat
    rw [he,hbudget] at hh
    have hb : ε/4 + L i * (moment D * exp (-L i/4)) ≤ ε := by
      change L i * (moment D * exp (-L i/4)) < ε/2 at hsmall
      linarith
    linarith [mul_le_mul_of_nonneg_left hb hE]
  intro s hs
  have hz : |(0:ℝ)| ≤ H := by simpa
  have h1 := compare s 0 hs hz
  have h2 := compare 0 s hz hs
  rw [add_zero] at h1 h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

#check @one_color_shift
#print axioms one_color_shift
end Shift490

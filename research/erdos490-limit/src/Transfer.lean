import Law
import Bounds

noncomputable section
namespace Shift490
open Filter Finset Real MeasureTheory
open scoped Topology

lemma measurable_F (B : Finset ℕ) : Measurable (F B) := by
  apply Measurable.tsum
  intro a
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

/-- Clip the residual count before testing the smoothed law. Beyond w/2, compensate
using the fixed half moment. The scale of the main error is P(D ∪ B)/w. -/
theorem window_comparison {D B : Finset ℕ} (hd : Disjoint D B) {w H δ η s t : ℝ}
    (hw : 0 < w) (hH : 4*H ≤ w) (hs : |s| ≤ H) (ht : |t| ≤ H)
    (hδ : 0 ≤ δ) (flat : KernelFlat D (H+δ) δ η) :
    F (D ∪ B) (w+s) ≤ F (D ∪ B) (w+t) + P (D ∪ B) / w *
      (4*K₀*((exp δ-1)*2+η) + w * (moment D * exp (-w/4))) := by
  let L := 4*K₀*P B/w
  have hL : 0 < L := div_pos (mul_pos (mul_pos (by norm_num) K₀_pos) (P_pos B)) hw
  let f (x : ℝ) := min 1 (F B (w+x) / L)
  have h01 x : 0 ≤ f x ∧ f x ≤ 1 := ⟨le_min zero_le_one (div_nonneg (F_nonneg ..) hL.le), min_le_left ..⟩
  have hf : Measurable f := measurable_const.min (((measurable_F B).comp
    (measurable_const.add measurable_id)).div_const L)
  have hslow x y (h : x ≤ y) : f x ≤ exp (y-x) * f y := by
    dsimp [f]
    rw [mul_min_of_nonneg _ _ (exp_pos _).le]
    apply le_min
    · simpa using (min_le_left 1 (F B (w+x)/L)).trans (Real.one_le_exp (sub_nonneg.mpr h))
    · have he := slow_decrease B (show w+x ≤ w+y by linarith)
      rw [show w+y-(w+x)=y-x by ring] at he
      exact (min_le_right ..).trans (by rw [← mul_div_assoc]; gcongr)
  have hflat := desmooth flat hf h01 hslow
    (s := s) (t := t) ((abs_add_le ..).trans (by rw [abs_of_nonneg hδ]; linarith))
    (by linarith) hδ
  let R (r v : ℝ) := F B (w+r-v)
  have bound (r v : ℝ) : 0 ≤ R r v ∧ R r v ≤ 1 := ⟨F_nonneg ..,F_le_one ..⟩
  have capped (r v : ℝ) : L*f (r-v) = min L (R r v) := by
    dsimp [f,R]
    rw [mul_min_of_nonneg _ _ hL.le,mul_one,mul_comm L,div_mul_cancel₀ _ hL.ne']
    congr 2; ring
  have scaled (r) : avg D (fun v => min L (R r v)) = L*avg D (fun v => f (r-v)) := by
    rw [← avg_mul]
    exact congrArg _ (funext (fun v => (capped r v).symm))
  have below : L*avg D (fun v => f (t-v)) ≤ avg D (R t) := by
    rw [← scaled]
    exact (avg_summable (D := D) (M := 1) (fun v => ⟨le_min hL.le (bound t v).1,
      (min_le_right ..).trans (bound t v).2⟩)).tsum_le_tsum
      (fun a => mul_le_mul_of_nonneg_left (min_le_right ..) (hnonneg a)) (avg_summable (bound t))
  have point (v : ℝ) : R s v ≤ min L (R s v) + exp (v/2)*exp (-w/4) := by
    by_cases hv : v ≤ w/2
    · have hz : w/4 ≤ w+s-v := by linarith [(abs_le.mp hs).1]
      have hh := counting_bound B (w+s-v) (by linarith)
      have hK := K₀_pos
      have hp := P_pos B
      have hcap : R s v ≤ L := hh.trans (by
        apply (div_le_div_iff₀ (by linarith) hw).mpr
        nlinarith [mul_nonneg (mul_nonneg hK.le hp.le) (show 0 ≤ 4*(w+s-v)-w by linarith)])
      rw [min_eq_right hcap]
      linarith [mul_pos (exp_pos (v/2)) (exp_pos (-w/4))]
    · rw [← exp_add]
      have hh := Real.one_le_exp (show 0 ≤ v/2 + -w/4 by linarith)
      linarith [(bound s v).2, le_min hL.le (bound s v).1]
  have above : avg D (R s) ≤ L*avg D (fun v => f (s-v)) + moment D*exp (-w/4) := by
    rw [← scaled]
    have hcap := avg_summable (D := D) (M := 1) (fun v => ⟨le_min hL.le (bound s v).1,
      (min_le_right ..).trans (bound s v).2⟩)
    apply hasSum_le _ (avg_summable (bound s)).hasSum
      (hcap.hasSum.add ((half_moment D).hasSum.mul_right (exp (-w/4))))
    intro a
    simpa [mul_add,mul_assoc] using mul_le_mul_of_nonneg_left (point (logN a)) (hnonneg a)
  have raw : avg D (R s) ≤ avg D (R t) + L*((exp δ-1)*2+η) + moment D*exp (-w/4) := by
    linarith [mul_le_mul_of_nonneg_left hflat hL.le]
  rw [normalized_convolution hd, normalized_convolution hd, P_union hd]
  change P D * avg D (R s) ≤ P D * avg D (R t) + _
  have htail : 0 ≤ moment D * exp (-w/4) := mul_nonneg
    (tsum_nonneg fun a => mul_nonneg (hnonneg a) (exp_pos _).le) (exp_pos _).le
  have he := mul_le_mul_of_nonneg_left (one_le_P B) htail
  calc
    _ ≤ P D * (avg D (R t) + L*((exp δ-1)*2+η) + P B*(moment D*exp (-w/4))) := by
      apply mul_le_mul_of_nonneg_left _ (P_pos D).le
      linarith
    _ = _ := by dsimp [L]; field_simp; ring

#print axioms window_comparison
end Shift490

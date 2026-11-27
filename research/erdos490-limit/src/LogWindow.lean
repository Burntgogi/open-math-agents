import PrimeCells

open Filter Real
open scoped Topology

namespace Erdos490PrimeCells

private theorem log_ratio_bounds {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (v-u)/v ≤ log v - log u ∧ log v - log u ≤ (v-u)/u := by
  have h1 := log_le_sub_one_of_pos (div_pos hu hv)
  have h2 := log_le_sub_one_of_pos (div_pos hv hu)
  rw [log_div hu.ne' hv.ne'] at h1
  rw [log_div hv.ne' hu.ne'] at h2
  constructor
  · rw [sub_div,div_self hv.ne']; linarith
  · rw [sub_div,div_self hu.ne']; exact h2

/-- The unnormalized harmonic mass of a log-prime subinterval, multiplied by the
cell index, converges to its length. Endpoints can be chosen anywhere in [0,1]. -/
theorem log_window_mass {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun s : ℝ => s * reciprocalInterval (exp (s+a)) (exp (s+b)))
      atTop (𝓝 (b-a)) := by
  obtain ⟨K,hK,hE⟩ := sharp_reciprocal_error
  have hshift (t : ℝ) : Tendsto (fun s : ℝ => exp (s+t)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_atTop_add_const_right atTop t tendsto_id)
  have hbound : ∀ᶠ s : ℝ in atTop,
      |s * reciprocalInterval (exp (s+a)) (exp (s+b)) - (b-a)| ≤ (2*K+1)/s := by
    filter_upwards [eventually_ge_atTop 1,(hshift a).eventually hE,(hshift b).eventually hE]
      with s hs h1 h2
    simp only [log_exp] at h1 h2
    have hs0 : 0 < s := by linarith
    have ha0 : 0 < s+a := by linarith
    have hb0 : 0 < s+b := by linarith
    have hl := log_ratio_bounds ha0 hb0
    have hδ : 0 ≤ b-a := by linarith
    have hδ1 : b-a ≤ 1 := by linarith
    have hL : |s * (log (s+b)-log (s+a)) - (b-a)| ≤ 1/s := by
      rw [abs_le]
      constructor
      · have hh : (b-a)/(s+b) ≤ log (s+b)-log (s+a) := by convert hl.1 using 1; ring
        have hh' := mul_le_mul_of_nonneg_left hh hs0.le
        apply le_trans _ (sub_le_sub_right hh' (b-a))
        field_simp
        have hprod : (b-a)*b ≤ 1 := calc
          _ ≤ (b-a)*1 := mul_le_mul_of_nonneg_left hb hδ
          _ ≤ 1 := by linarith
        nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hprod)]
      · have hh : log (s+b)-log (s+a) ≤ (b-a)/(s+a) := by convert hl.2 using 1; ring
        have hq : (b-a)/(s+a) ≤ (b-a)/s := by gcongr; linarith
        have h := mul_le_mul_of_nonneg_left (hh.trans hq) hs0.le
        have ht : s * ((b-a)/s) = b-a := by field_simp
        rw [ht] at h
        linarith [one_div_pos.mpr hs0]
    have hp := error_increment (exp_le_exp.mpr (by linarith : s+a ≤ s+b))
    simp only [log_exp] at hp
    have herr : |reciprocalInterval (exp (s+a)) (exp (s+b)) -
        (log (s+b)-log (s+a))| ≤ 2*K/s^3 := by
      rw [hp]
      apply (abs_sub _ _).trans
      calc
        _ ≤ K/s^3 + K/s^3 := by
          exact add_le_add (h2.trans (by gcongr; linarith)) (h1.trans (by gcongr; linarith))
        _ = _ := by ring
    set R := reciprocalInterval (exp (s+a)) (exp (s+b))
    set L := log (s+b)-log (s+a)
    calc
      |s*R-(b-a)| = |s*(R-L)+(s*L-(b-a))| := by congr 1; ring
      _ ≤ |s*(R-L)| + |s*L-(b-a)| := abs_add_le _ _
      _ ≤ s*(2*K/s^3)+1/s := by rw [abs_mul,abs_of_pos hs0]; gcongr
      _ ≤ (2*K+1)/s := by
        field_simp
        nlinarith [mul_nonneg hK.le (sub_nonneg.mpr hs)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound
  change Tendsto (fun s : ℝ => (2*K+1)/s) atTop (𝓝 0)
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds (x := 2*K+1) (f := atTop)).mul tendsto_inv_atTop_zero

#print axioms log_window_mass
end Erdos490PrimeCells

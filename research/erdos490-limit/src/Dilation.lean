import Reciprocal

open Filter Real Asymptotics
open scoped Topology

namespace Erdos490PrimeCells

theorem dilated_window_mass {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun s : ℝ => reciprocalInterval (exp (s*a)) (exp (s*b))) atTop
      (𝓝 (log (b/a))) := by
  have hb := ha.trans_le hab
  have lim (c : ℝ) (hc : 0 < c) : Tendsto (fun s : ℝ => exp (s*c)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hc)
  have he := (isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'
  have h := ((he.comp (lim b hb)).sub (he.comp (lim a ha))).add
    (tendsto_const_nhds (x := log (b/a)) (f := atTop))
  simp only [sub_self,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hid := error_increment (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hs.le))
  rw [log_exp,log_exp,log_mul hs.ne' hb.ne',log_mul hs.ne' ha.ne'] at hid
  dsimp [Function.comp_def]
  rw [log_div hb.ne' ha.ne']
  linarith

#print axioms dilated_window_mass
end Erdos490PrimeCells

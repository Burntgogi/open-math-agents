import LastLabel

open Finset Real Filter
open scoped Topology

namespace Erdos490PrimeCells

private theorem cappedCount_le (t a b z : ℝ) : cappedCount t a b z ≤ piReal (exp z) := by
  unfold cappedCount piReal
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast Finset.card_le_card (by
    intro p hp
    obtain ⟨h,hp'⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp h).2.trans (Nat.floor_mono (min_le_right _ _)),hp'⟩)

private theorem cappedCount_zero {t a b z : ℝ} (hz : z ≤ t*a) : cappedCount t a b z = 0 := by
  unfold cappedCount
  have hle := Nat.floor_mono ((min_le_right (exp (t*b)) (exp z)).trans (exp_le_exp.mpr hz))
  simp [Finset.Ioc_eq_empty (not_lt_of_ge hle)]

/-- A single bound applies to every possible sum of all *other* labels,
including throughout either endpoint strip. -/
theorem uniform_last_label_bound {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∀ᶠ t : ℝ in atTop, ∀ z : ℝ, t*cappedCount t a b z / exp z ≤ 2/a := by
  have hb := counting_pnt.eventually_lt_const (by norm_num : (1:ℝ) < 2)
  obtain ⟨X,hX⟩ := eventually_atTop.mp hb
  have hlim : Tendsto (fun t : ℝ => exp (t*a)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const ha)
  filter_upwards [eventually_gt_atTop 0,hlim.eventually_ge_atTop X] with t ht hta
  intro z
  by_cases h : z ≤ t*a
  · rw [cappedCount_zero h,mul_zero,zero_div]
    positivity
  have hx := hX (exp z) (hta.trans (exp_le_exp.mpr (le_of_not_ge h)))
  simp only [log_exp] at hx
  have hz : 0 < z := (mul_pos ht ha).trans (lt_of_not_ge h)
  have hx' : piReal (exp z) * z ≤ 2 * exp z := (le_of_lt ((div_lt_iff₀ (exp_pos z)).mp hx))
  have hn : 0 ≤ piReal (exp z) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (le_of_not_ge h) hn
  calc
    _ ≤ t*piReal (exp z)/exp z := by gcongr; exact cappedCount_le _ _ _ _
    _ ≤ _ := by
      rw [div_le_div_iff₀ (exp_pos z) ha]
      nlinarith only [hh,hx']

end Erdos490PrimeCells


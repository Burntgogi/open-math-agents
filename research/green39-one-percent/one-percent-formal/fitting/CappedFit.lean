import Fitting

/-! # Truncation and normalized fitting for an arbitrary finite test family -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def keep (J : Finset ι) (m : ι → ℝ) (x : ι) : ℝ := if x ∈ J then 0 else m x
def dropMass (J : Finset ι) (m : ι → ℝ) (x : ι) : ℝ := if x ∈ J then m x else 0
def clipped (J : Finset ι) (m : ι → ℝ) (x : ι) : ℝ := keep J m x / ∑ y, keep J m y

omit [Fintype ι] in
private theorem split_mass (J : Finset ι) (m : ι → ℝ) (x : ι) :
    keep J m x + dropMass J m x = m x := by by_cases hx : x ∈ J <;> simp [keep,dropMass,hx]

omit [DecidableEq ι] in
theorem abs_testMean_le {m f : ι → ℝ} (hm : ∀ x, 0 ≤ m x) (hf : ∀ x, |f x| ≤ 1) :
    |testMean m f| ≤ ∑ x, m x := calc
  _ ≤ ∑ x, |m x * f x| := abs_sum_le_sum_abs _ _
  _ ≤ _ := by
    apply sum_le_sum
    intro x _
    rw [abs_mul,abs_of_nonneg (hm x)]
    simpa using mul_le_mul_of_nonneg_left (hf x) (hm x)

/-- Deleting mass h and renormalizing changes every bounded test by at most 2h. -/
theorem clipped_test {m f : ι → ℝ} (J : Finset ι) (hm : ∀ x, 0 ≤ m x)
    (hs : ∑ x, m x = 1) (hf : ∀ x, |f x| ≤ 1) (hl : (∑ x, dropMass J m x) < 1) :
    |testMean (clipped J m) f - testMean m f| ≤ 2*∑ x, dropMass J m x := by
  let r := ∑ x, keep J m x
  let h := ∑ x, dropMass J m x
  have hk (x : ι) : 0 ≤ keep J m x := by simp [keep]; split <;> simp_all
  have hd (x : ι) : 0 ≤ dropMass J m x := by simp [dropMass]; split <;> simp_all
  have hm1 : r + h = 1 := by
    simpa [r,h,←sum_add_distrib,split_mass] using hs
  have hr : 0 < r := by change h < 1 at hl; linarith
  have hh : 0 ≤ h := sum_nonneg fun x _ => hd x
  have hmean : testMean m f = testMean (keep J m) f + testMean (dropMass J m) f := by
    simp only [testMean,←sum_add_distrib,←add_mul,split_mass]
  have hcmean : testMean (clipped J m) f = testMean (keep J m) f / r := by
    simp only [testMean,clipped,←sum_div,r,div_mul_eq_mul_div]
  have heq : testMean (clipped J m) f - testMean m f =
      (h/r)*testMean (keep J m) f - testMean (dropMass J m) f := by
    rw [hcmean,hmean]
    field_simp [hr.ne']
    linear_combination (testMean (keep J m) f) * (-hm1)
  rw [heq]
  calc
    _ ≤ |h/r * testMean (keep J m) f| + |testMean (dropMass J m) f| := abs_sub _ _
    _ ≤ h/r*r + h := by
      rw [abs_mul,abs_of_nonneg (div_nonneg hh hr.le)]
      exact add_le_add (mul_le_mul_of_nonneg_left (abs_testMean_le hk hf) (div_nonneg hh hr.le))
        (abs_testMean_le hd hf)
    _ = _ := by change h/r*r + h = 2*h; field_simp; ring

theorem clipped_law {m : ι → ℝ} {cap : ℝ} (hm : ∀ x, 0 ≤ m x) (hs : ∑ x, m x = 1)
    (hc : 0 ≤ cap) (J : Finset ι) (hout : ∀ x ∉ J, m x ≤ cap)
    (hl : (∑ x, dropMass J m x) ≤ 1/2) :
    (∑ x, clipped J m x = 1) ∧ ∀ x, 0 ≤ clipped J m x ∧ clipped J m x ≤ 2*cap := by
  have hh : (∑ x, keep J m x) + (∑ x, dropMass J m x) = 1 := by
    rw [←sum_add_distrib]; simpa only [split_mass] using hs
  have hr : 1 / 2 ≤ ∑ x, keep J m x := by linarith
  have hp : 0 < ∑ x, keep J m x := by linarith
  constructor
  · simp [clipped,←sum_div,hp.ne']
  · intro x
    have ha : 0 ≤ keep J m x := by by_cases h : x ∈ J <;> simp [keep,h,hm]
    have hb : keep J m x ≤ cap := by by_cases h : x ∈ J <;> simp [keep,h,hout,hc]
    exact ⟨div_nonneg ha hp.le,(div_le_iff₀ hp).mpr (by nlinarith [mul_nonneg hc (sub_nonneg.mpr hr)])⟩

#print axioms clipped_test
#print axioms clipped_law
end
end Green39.Fitting

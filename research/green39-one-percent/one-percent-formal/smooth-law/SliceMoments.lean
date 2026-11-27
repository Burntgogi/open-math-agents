import SliceWeights
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem sm_congr {s : Finset α} {k : ℕ} {f g : Finset α → ℝ}
    (h : ∀ A ∈ s.powersetCard k, f A = g A) : sliceMean s k f = sliceMean s k g := by
  unfold sliceMean mean
  rw [Finset.sum_congr rfl h]

omit [DecidableEq α] in
theorem sm_mono {s : Finset α} {k : ℕ} {f g : Finset α → ℝ}
    (h : ∀ A ∈ s.powersetCard k, f A ≤ g A) : sliceMean s k f ≤ sliceMean s k g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum h) (by positivity)

omit [DecidableEq α] in
theorem sm_sum (s : Finset α) (k : ℕ) (d : Finset ι) (f : ι → Finset α → ℝ) :
    sliceMean s k (fun A ↦ ∑ i ∈ d, f i A) = ∑ i ∈ d, sliceMean s k (f i) := by
  unfold sliceMean mean
  rw [Finset.sum_comm, Finset.sum_div]

theorem sm_inc (s t : Finset α) (k : ℕ) (c : ℝ) :
    sliceMean s k (fun A ↦ if t ⊆ A then c else 0) = incProb s k t * c := by
  unfold sliceMean mean incProb
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sm_const {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (c : ℝ) :
    sliceMean s k (fun _ ↦ c) = c := by simpa [inc_empty hk] using sm_inc s ∅ k c

private theorem restrict_sum {A s : Finset α} (h : A ⊆ s) (f : α → ℝ) :
    ∑ x ∈ A, f x = ∑ x ∈ s, if x ∈ A then f x else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun hx ↦ ⟨h hx, hx⟩, And.right⟩

theorem sm_weight {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ) :
    sliceMean s k (fun A ↦ ∑ x ∈ A, w x) = ((k : ℝ)/s.card) * ∑ x ∈ s, w x := by
  calc
    _ = sliceMean s k (fun A ↦ ∑ x ∈ s, if {x} ⊆ A then w x else 0) := by
      apply sm_congr
      intro A hA
      simpa using restrict_sum (Finset.mem_powersetCard.mp hA).1 w
    _ = _ := by
      rw [sm_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x hx ↦ by rw [sm_inc, inc_singleton hk hx])

theorem sm_variance {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ)
    (hw : ∀ x ∈ s, 0 ≤ w x) :
    sliceMean s k (fun A ↦ ((∑ x ∈ A, w x) - ((k : ℝ)/s.card) * ∑ x ∈ s, w x)^2)
      ≤ ((k : ℝ)/s.card) * ∑ x ∈ s, w x ^ 2 := by
  let q : ℝ := k / (s.card : ℝ)
  let m := q * ∑ x ∈ s, w x
  let X (A : Finset α) := ∑ x ∈ A, w x
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsecond : sliceMean s k (fun A ↦ X A ^ 2) ≤
      q * (∑ x ∈ s, w x ^ 2) + m ^ 2 := by
    calc
      _ = sliceMean s k (fun A ↦ ∑ x ∈ s, ∑ y ∈ s,
          if {x,y} ⊆ A then w x * w y else 0) := by
        apply sm_congr
        intro A hA
        dsimp [X]
        rw [sq, restrict_sum (Finset.mem_powersetCard.mp hA).1 w, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [Finset.insert_subset_iff,hx,hy]
      _ = ∑ x ∈ s, ∑ y ∈ s, incProb s k {x,y} * (w x * w y) := by
        rw [sm_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [sm_sum]
        simp_rw [sm_inc]
      _ ≤ ∑ x ∈ s, ∑ y ∈ s, ((if x = y then q * w x ^ 2 else 0) +
          (q*w x)*(q*w y)) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        by_cases he : x = y
        · subst y
          rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self x), inc_singleton hk hx, if_pos rfl]
          change q * _ ≤ _
          nlinarith [sq_nonneg (q * w x)]
        · have hxy : ({x,y} : Finset α) ⊆ s := by simp [Finset.insert_subset_iff,hx,hy]
          have hi := inc_le_pow hk hxy
          have hn : x ∉ ({y} : Finset α) := by simpa using he
          rw [Finset.card_insert_of_notMem hn, Finset.card_singleton] at hi
          rw [if_neg he, zero_add]
          calc
            _ ≤ q^2 * (w x*w y) := mul_le_mul_of_nonneg_right hi (mul_nonneg (hw _ hx) (hw _ hy))
            _ = _ := by ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [m, Finset.sum_ite_eq, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
  have hmean : sliceMean s k X = m := sm_weight hk w
  have hconst := sm_const hk (m^2)
  change sliceMean s k (fun A ↦ (X A - m)^2) ≤ _
  have he : sliceMean s k (fun A ↦ (X A - m)^2) =
      sliceMean s k (fun A ↦ X A^2) - 2*m*sliceMean s k X + sliceMean s k (fun _ ↦ m^2) := by
    unfold sliceMean mean
    simp_rw [show ∀ z : ℝ, (z-m)^2 = z^2 - 2*m*z + m^2 by intro z; ring,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [he,hmean,hconst]
  linarith

/-- Exponential moment for bounded nonnegative weights in a uniform sample without replacement. -/
theorem sm_weight_exp {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ)
    {b : ℝ} (hb : 0 < b) (hw : ∀ x ∈ s, 0 ≤ w x ∧ w x ≤ b) :
    sliceMean s k (fun A ↦ Real.exp ((∑ x ∈ A, w x)/b)) ≤
      Real.exp ((Real.exp 1 - 1) * (((k : ℝ)/s.card) * ∑ x ∈ s, w x) / b) := by
  let d (x : α) := Real.exp (w x/b) - 1
  let q : ℝ := k / (s.card : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hd (x) (hx : x ∈ s) : 0 ≤ d x := sub_nonneg.mpr
    (Real.one_le_exp (div_nonneg (hw x hx).1 hb.le))
  have hch (x) (hx : x ∈ s) : d x ≤ (Real.exp 1 - 1) * (w x/b) := by
    let u := w x/b
    have hu : 0 ≤ u := div_nonneg (hw x hx).1 hb.le
    have hv : u ≤ 1 := (div_le_one₀ hb).mpr (hw x hx).2
    have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ))
      (sub_nonneg.mpr hv) hu (show 1-u+u=1 by ring)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at h
    change Real.exp u - 1 ≤ (Real.exp 1 - 1)*u
    linarith
  calc
    _ = sliceMean s k (fun A ↦ ∑ t ∈ s.powerset, if t ⊆ A then ∏ x ∈ t, d x else 0) := by
      apply sm_congr
      intro A hA
      have hsub := (Finset.mem_powersetCard.mp hA).1
      rw [Finset.sum_div, Real.exp_sum]
      simp_rw [show ∀ x, Real.exp (w x/b) = 1 + d x by intro x; dsimp [d]; ring]
      rw [Finset.prod_one_add, ← Finset.sum_filter]
      congr 1
      ext t
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h ↦ ⟨h.trans hsub,h⟩, And.right⟩
    _ = ∑ t ∈ s.powerset, incProb s k t * ∏ x ∈ t, d x := by
      rw [sm_sum]; simp_rw [sm_inc]
    _ ≤ ∑ t ∈ s.powerset, ∏ x ∈ t, (q*d x) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      exact mul_le_mul_of_nonneg_right (inc_le_pow hk (Finset.mem_powerset.mp ht))
        (Finset.prod_nonneg (fun x hx ↦ hd x ((Finset.mem_powerset.mp ht) hx)))
    _ = ∏ x ∈ s, (1+q*d x) := (Finset.prod_one_add _).symm
    _ ≤ ∏ x ∈ s, Real.exp (q*d x) := by
      apply Finset.prod_le_prod
      · intro x hx; linarith [mul_nonneg hq (hd x hx)]
      · intro x _; linarith [Real.add_one_le_exp (q*d x)]
    _ ≤ _ := by
      rw [← Real.exp_sum, Real.exp_le_exp]
      calc
        _ ≤ ∑ x ∈ s, q*((Real.exp 1-1)*(w x/b)) :=
          Finset.sum_le_sum (fun x hx ↦ mul_le_mul_of_nonneg_left (hch x hx) hq)
        _ = _ := by simp_rw [← Finset.mul_sum, ← Finset.sum_div]; dsimp [q]; ring

end
end Green39.Smooth

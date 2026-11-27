import OldStrip
import SparseStrip

/-! Common sparse peak and simultaneous old color stripping for a fixed
auxiliary prime pool. No diagonal stabilization of the small colors is needed. -/
namespace Erdos490Transfer
open Finset Filter Real Shift490
noncomputable section
open Classical

lemma P_split {C S : Finset ℕ} (hs : S ⊆ C) : P C = P S * P (C \ S) := by
  rw [← P_union (disjoint_left.mpr (fun {_} hx hy => (mem_sdiff.mp hy).2 hx)),
    union_sdiff_of_subset hs]

private theorem sparse_pool (pool : Finset ℕ) (H η : ℝ) (he : 0 < η) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ L : ℝ in atTop, ∀ S ⊆ pool, ∀ C : Finset ℕ, S ⊆ C →
      ∀ h : ℝ, |h| ≤ H → ∃ v : ℝ, 0 ≤ v ∧ v ≤ J ∧
        F C (L+h) ≤ P S * F (C \ S) (L+h-v) + η*(P C/L) := by
  choose cut hc hlim using (fun S : Finset ℕ => sparse_strip S H η he)
  let J := ∑ S ∈ pool.powerset, cut S
  refine ⟨J,sum_nonneg (fun S _ => hc S),?_⟩
  filter_upwards [(eventually_all_finset pool.powerset).mpr (fun S _ => hlim S)] with L hL
  intro S hS C hs h hh
  have dis : Disjoint S (C \ S) := disjoint_left.mpr (fun {_} hx hy => (mem_sdiff.mp hy).2 hx)
  have hm := mem_powerset.mpr hS
  obtain ⟨v,h0,hv,hx⟩ := hL S hm _ dis h hh
  refine ⟨v,h0,hv.trans (single_le_sum (fun S _ => hc S) hm),?_⟩
  rw [union_sdiff_of_subset hs] at hx
  have hmul := (div_le_iff₀ (P_pos S)).mp hx
  rw [P_split hs]
  linarith only [hmul,
    show (F (C \ S) (L+h-v) + η*(P (C \ S)/L))*P S =
      P S * F (C \ S) (L+h-v) + η*(P S*P (C \ S)/L) by ring]

/-- One old sample z works at every positive cofactor, even when the sparse
color has large oscillations between the original shifted cutoffs. -/
theorem sparse_common_peak (pool : Finset ℕ) (K : ℕ) (η : ℝ) (he : 0 < η) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ᶠ n : ℕ in atTop, ∀ C : Finset ℕ, ∀ S ⊆ pool, S ⊆ C →
      ∃ z : ℝ, |z-log n| ≤ W ∧ ∀ i < K, density C n (i+1) ≤
        P S*F (C \ S) z + η*(P C/log n) := by
  let H := log (K+1:ℕ)
  have hH : 0 ≤ H := log_natCast_nonneg _
  obtain ⟨J,hJ,hl⟩ := sparse_pool pool H η he
  refine ⟨H+J,by positivity,?_⟩
  filter_upwards [(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hl,
    eventually_gt_atTop (0:ℕ)] with n hL hn
  intro C S hS hs
  obtain ⟨i,hi,hmax⟩ := (range (K+1)).exists_max_image (fun i => density C n (i+1))
    ⟨0,mem_range.mpr (Nat.zero_lt_succ _)⟩
  have hih : |-(log (i+1:ℕ))| ≤ H := by
    rw [abs_neg,abs_of_nonneg (log_natCast_nonneg _)]
    apply log_le_log (by positivity)
    exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hi))
  obtain ⟨v,hv0,hv,hval⟩ := hL S hS C hs _ hih
  let z := log (n:ℝ)-log (i+1:ℕ)-v
  refine ⟨z,?_,?_⟩
  · dsimp [z]
    have hi0 := log_natCast_nonneg (i+1)
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hih).1]
  · intro j hj
    simp only [Function.comp_apply,← sub_eq_add_neg] at hval
    rw [shifted_density (u:=i+1) C hn (by omega)] at hval
    exact (hmax j (mem_range.mpr (by omega))).trans hval

/-- A partition of all primes in the original window partitions the auxiliary
pool too. Its removed Euler mass is independent of the original coloring. -/
theorem removed_mass {Y n} (c : Colors Y n) {pool : Finset ℕ} (hp : pool ⊆ primes Y n) :
    P (pool ∩ c.red) * P (pool ∩ c.blue) = P pool := by
  rw [← P_union (c.separate.mono inter_subset_right inter_subset_right)]
  congr 1
  rw [← inter_union_distrib_left,c.cover,inter_eq_left.mpr hp]

#print axioms sparse_common_peak
#print axioms stable_strip
end
end Erdos490Transfer

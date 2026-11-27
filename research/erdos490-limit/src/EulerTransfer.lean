import EulerScale
import FiniteOptimum

/-! Exact H2 from the manuscript's two Euler-normalized, one-color estimates. -/
namespace Erdos490Transfer
open Finset Filter
noncomputable section

def eulerScale (C : Finset ℕ) (n : ℕ) := euler C / Real.log n

/-- For an increasing sequence of arbitrarily colored old cutoffs, freeze one
old index, choose the sparse side, and specify one coloring for each target.
Each individual cofactor has its own eventual threshold. The multiplier on
the sparse side is w * log m/log n; on the stable side it is 1/w.
The frozen gain w permits stripping and reallocating primes below an auxiliary threshold.
The tolerance is in units of P_C/log n for the old color C. -/
def EulerPrimeColorTransfer : Prop :=
  ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
    ∀ c : (k : ℕ) → Colors Y (N k), ∃ k, 2 ≤ N k ∧
      ∃ redSparse : Bool, ∃ w : ℝ, 0 < w ∧ ∃ d : (m : ℕ) → Colors Y m,
      (∀ i < K, ∀ᶠ m : ℕ in atTop,
        density (c k).red (N k) (i+1) ≤
          (if redSparse then w * (Real.log m / Real.log (N k)) else w⁻¹) * density (d m).red m (i+1)
          + η*eulerScale (c k).red (N k)) ∧
      (∀ j < K, ∀ᶠ m : ℕ in atTop,
        density (c k).blue (N k) (j+1) ≤
          (if redSparse then w⁻¹ else w * (Real.log m / Real.log (N k))) * density (d m).blue m (j+1)
          + η*eulerScale (c k).blue (N k))

theorem harmonic_transfer_of_euler (analytic : EulerPrimeColorTransfer) : AnalyticPrimeColorTransfer := by
  obtain ⟨B,hB,bound⟩ := euler_le_trunc_uniform
  intro Y K η hη N hN c
  obtain ⟨k,hk,s,w,hw,d,hr,hb⟩ := analytic Y K (η/B) (div_pos hη hB) N hN c
  have hlog : 0 < Real.log (N k) := Real.log_pos (by exact_mod_cast (show 1 < N k by omega))
  have sub : (c k).red ∪ (c k).blue ⊆ (N k).primesLE := by
    rw [(c k).cover]
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have cost {C : Finset ℕ} (hC : C ⊆ (N k).primesLE) :
      η/B*eulerScale C (N k) ≤ η*Harmonic.scale C (N k) := by
    have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (bound _ hk C hC) hlog.le)
      (div_nonneg hη.le hB.le)
    apply h.trans
    change η/B*(B*truncMass C (N k)/Real.log (N k)) ≤ η*(truncMass C (N k)/Real.log (N k))
    field_simp
    rfl
  have hr' := (eventually_all_finset (range K)).mpr (fun i hi => hr i (mem_range.mp hi))
  have hb' := (eventually_all_finset (range K)).mpr (fun j hj => hb j (mem_range.mp hj))
  refine ⟨k,?_⟩
  filter_upwards [hr',hb'] with m hred hblue
  have ht : 0 ≤ Real.log (m:ℝ)/Real.log (N k) := div_nonneg (Real.log_natCast_nonneg _) hlog.le
  refine ⟨d m,(if s then w*(Real.log m/Real.log (N k)) else w⁻¹),
    (if s then w⁻¹ else w*(Real.log m/Real.log (N k))),by split <;> positivity,
    by split <;> positivity,by cases s <;> simp <;> field_simp,?_,?_⟩
  · exact fun i hi => (hred i (mem_range.mpr hi)).trans
      (add_le_add_right (cost (subset_union_left.trans sub)) _)
  · exact fun j hj => (hblue j (mem_range.mpr hj)).trans
      (add_le_add_right (cost (subset_union_right.trans sub)) _)

/-- The exact site step. The prime-color estimate is a theorem argument. -/
theorem site_H2_of_euler (analytic : EulerPrimeColorTransfer) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2 (harmonic_transfer_of_euler analytic)

#print axioms site_H2_of_euler
end
end Erdos490Transfer

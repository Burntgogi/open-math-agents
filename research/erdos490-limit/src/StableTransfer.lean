import EulerTransfer
import Shift

/-! Connect the integer graph model to the continuous one-color shift theorem.
The stable-side recovery input needs only one old density, at the unshifted
cutoff, even though it must realize all the new cofactor cutoffs. -/
namespace Erdos490Transfer
open Finset Filter Real
noncomputable section
open Classical

def pick {Y n} (c : Colors Y n) (b : Bool) := if b then c.red else c.blue

lemma pick_prime {Y n} (c : Colors Y n) (b : Bool) : ∀ p ∈ pick c b, Nat.Prime p := by
  intro p hp
  have h : p ∈ c.red ∪ c.blue := by
    cases b <;> simp_all [pick]
  exact (mem_filter.mp (c.cover ▸ h)).2

lemma pick_scale {Y n} (c : Colors Y n) (b : Bool) :
    Shift490.P (pick c b)/log n = eulerScale (pick c b) n := by
  simp [Shift490.P,eulerScale,euler,filter_true_of_mem (pick_prime c b)]

theorem shifted_density (C : Finset ℕ) {n u : ℕ} (hn : 0 < n) (hu : 0 < u) :
    Shift490.F C (log n-log u) = density C n u := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hu' : (0:ℝ) < u := by exact_mod_cast hu
  have hex : exp (log n-log u) = (n:ℝ)/u := by rw [exp_sub,exp_log hn',exp_log hu']
  have hset : Shift490.countSet C (log n-log u) = semigroup C (n/u) := by
    ext x
    simp only [Shift490.countSet,hex,mem_filter,mem_range,Nat.lt_succ_iff,mem_semigroup]
    rw [Nat.le_floor_iff (by positivity),le_div_iff₀ hu',Nat.le_div_iff_mul_le hu]
    constructor
    · intro h
      exact ⟨h.2,by exact_mod_cast h.1⟩
    · intro h
      exact ⟨by exact_mod_cast h.2,h.1⟩
  rw [Shift490.F_eq_card,hset,exp_neg,hex]
  unfold density
  field_simp

def Stable {Y} (N : ℕ → ℕ) (c : ∀ k, Colors Y (N k)) (b : Bool) : Prop :=
  ∀ H : ℝ, 0 ≤ H → ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop,
    ∀ s : ℝ, |s| ≤ H →
      |Shift490.F (pick (c k) b) (log (N k)+s) - Shift490.F (pick (c k) b) (log (N k))|
        ≤ η*eulerScale (pick (c k) b) (N k)

lemma stable_subsequence {Y} (shift : Shift490.OneColorShift Y)
    (N : ℕ → ℕ) (hN : StrictMono N) (c : ∀ k, Colors Y (N k)) :
    ∃ σ : ℕ → ℕ, ∃ b : Bool, StrictMono σ ∧ Stable (N ∘ σ) (fun k => c (σ k)) b := by
  let q (k p : ℕ) := decide (p ∈ (c k).red)
  have side (k b) : Shift490.side Y (N k) (q k) b = pick (c k) b := by
    have he : Shift490.primesAt Y (N k) = (c k).red ∪ (c k).blue := by
      rw [(c k).cover]; simp [Shift490.primesAt,primes]
    ext p
    have hd : p ∈ (c k).red → p ∉ (c k).blue := fun hp => disjoint_left.mp (c k).separate hp
    cases b <;> simp [Shift490.side,he,pick,q]
    tauto
  obtain ⟨σ,b,hm,hs⟩ := shift (fun k => (N k:ℝ))
    (tendsto_natCast_atTop_atTop.comp hN.tendsto_atTop) q
  refine ⟨σ,b,hm,?_⟩
  intro H hH η hη
  filter_upwards [hs H hH η hη] with k hk
  simpa only [side,pick_scale,Function.comp_apply] using hk

/-- Transplantation after selecting a stable color. On the sparse side the
old offset is retained. On the stable side only the unshifted old count
occurs. Both lower bounds use one common target coloring on all integers. -/
def StableRecovery : Prop :=
  ∀ Y K, ∀ η : ℝ, 0 < η → ∀ N : ℕ → ℕ, StrictMono N →
    ∀ (c : ∀ k, Colors Y (N k)) (b : Bool), Stable N c b → ∃ᶠ k in atTop,
      2 ≤ N k ∧ ∃ w : ℝ, 0 < w ∧ ∃ d : (m : ℕ) → Colors Y m,
      (∀ i < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) (!b)) (N k) (i+1) ≤
        (w*(log m/log (N k))) * density (pick (d m) (!b)) m (i+1) + η*eulerScale (pick (c k) (!b)) (N k)) ∧
      (∀ j < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) b) (N k) 1 ≤
        w⁻¹*density (pick (d m) b) m (j+1) + η*eulerScale (pick (c k) b) (N k))

theorem euler_of_stable (shift : ∀ Y, Shift490.OneColorShift Y) (recovery : StableRecovery) :
    EulerPrimeColorTransfer := by
  intro Y K η hη N hm c
  obtain ⟨σ,b,hσ,stable⟩ := stable_subsequence (shift Y) N hm c
  let n := N ∘ σ
  let col (k : ℕ) := c (σ k)
  change Stable n col b at stable
  have half := half_pos hη
  have old := stable (log (K+1:ℕ)) (log_natCast_nonneg _) _ half
  have late := recovery Y K _ half n (hm.comp hσ) col b stable
  obtain ⟨k,⟨⟨hn,w,hw,d,hs,hr⟩,hold⟩⟩ := (late.and_eventually old).exists
  have hn0 : 0 < n k := by omega
  have hstable (j : ℕ) (hj : j < K) : ∀ᶠ m : ℕ in atTop,
      density (pick (col k) b) (n k) (j+1) ≤ w⁻¹*density (pick (d m) b) m (j+1)
        + η*eulerScale (pick (col k) b) (n k) := by
    have hjlog : abs (-log (j+1:ℕ)) ≤ log (K+1:ℕ) := by
      rw [abs_neg,abs_of_nonneg (log_natCast_nonneg _)]
      apply log_le_log (by positivity) (by exact_mod_cast (show j+1 ≤ K+1 by omega))
    have diff := (abs_le.mp (hold _ hjlog)).2
    rw [← sub_eq_add_neg,shifted_density _ hn0 (Nat.zero_lt_succ j)] at diff
    have hcenter := shifted_density (pick (col k) b) hn0 (by decide : 0 < 1)
    simp only [Nat.cast_one,log_one,sub_zero] at hcenter
    rw [hcenter] at diff
    filter_upwards [hr j hj] with m h
    linarith
  have hsp (i : ℕ) (hi : i < K) : ∀ᶠ m : ℕ in atTop,
      density (pick (col k) (!b)) (n k) (i+1) ≤
        (w*(log m/log (n k)))*density (pick (d m) (!b)) m (i+1) + η*eulerScale (pick (col k) (!b)) (n k) := by
    filter_upwards [hs i hi] with m hx
    apply hx.trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_right (by linarith)
    exact div_nonneg (euler_pos (pick_prime (col k) (!b))).le (log_natCast_nonneg _)
  refine ⟨σ k,hn,!b,w,hw,d,?_⟩
  cases b
  · simpa [pick,col,n] using And.intro hsp hstable
  · simpa [pick,col,n] using And.intro hstable hsp

theorem site_H2_of_shift_and_recovery
    (cells : ∀ Y, Shift490.PrimeCellInput Y) (smoothing : ∀ Y, Shift490.FiniteSmoothing Y)
    (recovery : StableRecovery) : OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_euler (euler_of_stable (fun Y => Shift490.one_color_shift (cells Y) (smoothing Y)) recovery)

#print axioms site_H2_of_shift_and_recovery
end
end Erdos490Transfer

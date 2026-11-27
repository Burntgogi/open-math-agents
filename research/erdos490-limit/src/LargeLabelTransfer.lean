import TransferEndpoint
import StrippedProfiles

/-! Remaining recovery estimates after old-prime stripping. The old colors
in the two analytic inequalities consist only of primes above the chosen
auxiliary cutoff. -/
namespace Erdos490Transfer
open Finset Filter Shift490 Real
noncomputable section
open Classical

def low (pool C : Finset ℕ) := pool ∩ C
def roughColor (pool C : Finset ℕ) := C \ low pool C

def RoughFlat (N : ℕ → ℕ) (R : ℕ → Finset ℕ) : Prop :=
  ∀ H : ℝ, 0 ≤ H → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ h : ℝ, |h| ≤ H →
    |F (R k) (log (N k)+h) - F (R k) (log (N k))| ≤ ε*(P (R k)/log (N k))

/-- The high-prime portion of estimates (9), (12) and (13) in the auxiliary
threshold proof. A positive tolerance is fixed before the auxiliary cutoff.
The common old sparse peak may move within any fixed window. The multiplier
on the stable side is the reciprocal of the entire removed Euler mass. -/
def LargeLabelRecovery : Prop :=
  ∀ Y K, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ P₀ : ℕ, Y ≤ P₀ ∧
    ∀ N : ℕ → ℕ, StrictMono N → ∀ (c : ∀ k, Colors Y (N k)) (b : Bool),
    let pool := primes Y P₀
    let Q := fun k => roughColor pool (pick (c k) (!b))
    let R := fun k => roughColor pool (pick (c k) b)
    RoughFlat N R → ∀ peak : ℕ → ℝ, (∃ W : ℝ, ∀ᶠ k in atTop, |peak k-log (N k)| ≤ W) →
      ∃ᶠ k in atTop, 2 ≤ N k ∧ ∃ z : ℝ, 0 < z ∧ (1-ε)*log (N k) ≤ z ∧
        ∃ d : (m : ℕ) → Colors Y m,
        (∀ i < K, ∀ᶠ m : ℕ in atTop, F (Q k) (peak k) ≤
          log m/z*density (pick (d m) (!b)) m (i+1) + ε*(P (Q k)/log (N k))) ∧
        (∀ j < K, ∀ᶠ m : ℕ in atTop, F (R k) (log (N k)) ≤
          (P pool)⁻¹*density (pick (d m) b) m (j+1) + ε*(P (R k)/log (N k)))

theorem rough_flat_of_stable {Y N c b} (st : Stable (Y:=Y) N c b)
    (pool : Finset ℕ) (hp : ∀ p ∈ pool, p.Prime) :
    RoughFlat N (fun k => roughColor pool (pick (c k) b)) := by
  intro H hH ε he
  filter_upwards [stable_strip st pool hp H (ε/2) hH (half_pos he)] with k hk
  intro h hh
  let S := low pool (pick (c k) b)
  have step := hk S inter_subset_left inter_subset_right
  have hi := abs_le.mp (step h hh)
  have h0 := abs_le.mp (step 0 (by simpa using hH))
  rw [add_zero] at h0
  unfold roughColor
  rw [abs_le]
  constructor <;> linarith

private lemma combine {p x y f t η E M : ℝ} (hp : 0 < p) (he : p*E=M)
    (hx : x ≤ p*f+η*M) (hf : f ≤ t*y+η*E) :
    x ≤ (p*t)*y + (2*η)*M := by
  have h := mul_le_mul_of_nonneg_left hf hp.le
  nlinarith only [hx,h,congrArg (η * ·) he]

theorem sampled_of_large_labels (labels : LargeLabelRecovery) : SampledRecovery := by
  intro Y K θ hθ hθ1 N hN c b st
  let η := θ/2
  have hη : 0 < η := half_pos hθ
  have heq : 2*η=θ := by dsimp [η]; ring
  obtain ⟨P₀,_,build⟩ := labels Y K η hη (by dsimp [η]; linarith)
  let pool := primes Y P₀
  have hp : ∀ p ∈ pool, p.Prime := fun p h => (mem_filter.mp h).2
  let Q (k) := pick (c k) (!b)
  let R (k) := pick (c k) b
  let q (k) := low pool (Q k)
  let r (k) := low pool (R k)
  let L (k) := log (N k:ℝ)
  obtain ⟨W,_,hpeak⟩ := sparse_common_peak pool K η hη
  let good (k : ℕ) (z : ℝ) := |z-L k| ≤ W ∧ ∀ i < K, density (Q k) (N k) (i+1) ≤
    P (q k)*F (roughColor pool (Q k)) z + η*(P (Q k)/L k)
  have existsPeak : ∀ᶠ k in atTop, ∃ z, good k z := by
    filter_upwards [hN.tendsto_atTop.eventually hpeak] with k hk
    exact hk _ _ inter_subset_left inter_subset_right
  let peak (k : ℕ) := if h : ∃ z, good k z then h.choose else L k
  have chosen : ∀ᶠ k in atTop, good k (peak k) := existsPeak.mono (fun k hk => by
    simp only [peak,dif_pos hk]; exact hk.choose_spec)
  have late := build N hN c b (rough_flat_of_stable st pool hp) peak ⟨W,chosen.mono (fun _ h => h.1)⟩
  have old := stable_strip st pool hp 0 η le_rfl hη
  apply (late.and_eventually ((chosen.and old).and (hN.tendsto_atTop.eventually_ge_atTop P₀))).mono
  rintro k ⟨⟨hn,z,hz,hclose,d,hs,hr⟩,⟨hk,hb⟩,hP⟩
  have hL : 0 < L k := log_pos (by exact_mod_cast (show 1 < N k by omega))
  have hpool : pool ⊆ primes Y (N k) := fun p h => mem_filter.mpr ⟨mem_Icc.mpr
    ⟨(mem_Icc.mp (mem_filter.mp h).1).1,(mem_Icc.mp (mem_filter.mp h).1).2.trans hP⟩,(mem_filter.mp h).2⟩
  have masses : P (q k)*P (r k)=P pool := by
    have h := removed_mass (c k) hpool
    cases b <;> simpa [q,r,Q,R,low,pick,mul_comm] using h
  have split (C : Finset ℕ) : P (low pool C)*(P (roughColor pool C)/L k) = P C/L k := by
    rw [roughColor,← mul_div_assoc,← P_split (show low pool C ⊆ C from inter_subset_right)]
  refine ⟨hn,z,P (q k),hz,?_,P_pos _,d,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (by dsimp [η]; linarith) hL.le).trans hclose
  · intro i hi
    filter_upwards [hs i hi] with m hm
    have h := combine (P_pos _) (split (Q k)) (hk.2 i hi) hm
    rw [heq] at h
    rw [← pick_scale]
    exact h
  · have hh := hb (r k) inter_subset_left inter_subset_right 0 (by simp)
    rw [add_zero] at hh
    have hb0 := (abs_le.mp hh).1
    have hold : density (R k) (N k) 1 ≤
        P (r k)*F (roughColor pool (R k)) (L k) + η*(P (R k)/L k) := by
      have hden := shifted_density (R k) (by omega : 0 < N k) (by decide : 0 < 1)
      simp only [Nat.cast_one,log_one,sub_zero] at hden
      rw [← hden]
      change -(η*(P (roughColor pool (R k))/L k)) ≤
        F (roughColor pool (R k)) (L k) - (P (r k))⁻¹*F (R k) (L k) at hb0
      have h := mul_le_mul_of_nonneg_left hb0 (P_pos (r k)).le
      rw [mul_sub,← mul_assoc,mul_inv_cancel₀ (P_pos _).ne',one_mul] at h
      change F (R k) (L k) ≤ _
      nlinarith only [h,congrArg (η * ·) (split (R k))]
    intro j hj
    filter_upwards [hr j hj] with m hm
    have h := combine (P_pos _) (split (R k)) hold hm
    have gain : P (r k)*(P pool)⁻¹=(P (q k))⁻¹ := by
      rw [← masses]; field_simp [(P_pos (q k)).ne',(P_pos (r k)).ne']
    rw [gain,heq] at h
    rw [← pick_scale]
    exact h

theorem site_H2_of_large_labels (labels : LargeLabelRecovery) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_sampled_recovery (sampled_of_large_labels labels)

#print axioms site_H2_of_large_labels
end
end Erdos490Transfer

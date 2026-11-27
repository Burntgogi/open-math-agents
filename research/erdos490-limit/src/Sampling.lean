import StableTransfer

/-! Absorb the sampled log cutoff into the exact target normalization. -/
namespace Erdos490Transfer
open Filter Real
noncomputable section

/-- The sparse estimate uses the actual dilation log m/z at the common
sample z. The positive scale a accounts for stripped Euler factors. The
stable estimate concerns that same target coloring, at every new shift. -/
def SampledRecovery : Prop :=
  ∀ Y K, ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∀ N : ℕ → ℕ, StrictMono N → ∀ (c : ∀ k, Colors Y (N k)) (b : Bool),
    Stable N c b → ∃ᶠ k in atTop, 2 ≤ N k ∧ ∃ z a : ℝ,
      0 < z ∧ (1-θ)*log (N k) ≤ z ∧ 0 < a ∧ ∃ d : (m : ℕ) → Colors Y m,
      (∀ i < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) (!b)) (N k) (i+1) ≤
        (a*(log m/z))*density (pick (d m) (!b)) m (i+1) + θ*eulerScale (pick (c k) (!b)) (N k)) ∧
      (∀ j < K, ∀ᶠ m : ℕ in atTop, density (pick (c k) b) (N k) 1 ≤
        a⁻¹*density (pick (d m) b) m (j+1) + θ*eulerScale (pick (c k) b) (N k))

lemma sparse_rescale {L M z a x X E B θ : ℝ} (hL : 0 < L) (hM : 0 ≤ M)
    (hz : 0 < z) (ha : 0 ≤ a) (hX : 0 ≤ X) (hE : 0 ≤ E)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hclose : (1-θ)*L ≤ z)
    (hx : x ≤ B*E) (hh : x ≤ (a*(M/z))*X + θ*E) :
    x ≤ (a*(M/L))*X + (B+1)*θ*E := by
  have hdiv : (1-θ)*(M/z) ≤ M/L := by
    rw [le_div_iff₀ hL]
    calc
      _ = ((1-θ)*L)/z*M := by ring
      _ ≤ 1*M := by gcongr; exact (div_le_one hz).mpr hclose
      _ = M := one_mul M
  have h1 := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hθ')
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv ha) hX
  nlinarith only [h1,h2,mul_le_mul_of_nonneg_left hx hθ,mul_nonneg (sq_nonneg θ) hE]

theorem stableRecovery_of_sampled (sample : SampledRecovery) : StableRecovery := by
  intro Y K η hη N hN c b st
  let B := envelope K
  have hB : 0 ≤ B := by dsimp [B,envelope]; positivity
  let θ := min (1/2:ℝ) (η/(B+1))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos hη (by positivity))
  have hθ1 : θ < 1 := (min_le_left ..).trans_lt (by norm_num)
  have hb : (B+1)*θ ≤ η := by
    rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  have hsmall : θ ≤ η := by nlinarith [mul_nonneg hB hθ.le]
  apply (sample Y K θ hθ hθ1 N hN c b st).mono
  rintro k ⟨hn,z,a,hz,hclose,ha,d,hs,hr⟩
  have hL : 0 < log (N k) := log_pos (by exact_mod_cast (show 1 < N k by omega))
  have pos (b : Bool) : 0 ≤ eulerScale (pick (c k) b) (N k) :=
    div_nonneg (euler_pos (pick_prime _ _)).le hL.le
  refine ⟨hn,a,ha,d,?_,?_⟩
  · intro i hi
    filter_upwards [hs i hi] with m hm
    let C := pick (c k) (!b)
    have ec : Harmonic.scale C (N k) ≤ eulerScale C (N k) :=
      div_le_div_of_nonneg_right (truncMass_le_euler (pick_prime _ _) _) hL.le
    have hbound := (density_le_scale hL hi C).trans (mul_le_mul_of_nonneg_left ec hB)
    have hX : 0 ≤ density (pick (d m) (!b)) m (i+1) := by unfold density; positivity
    exact (sparse_rescale hL (log_natCast_nonneg _) hz ha.le hX (pos _) hθ.le hθ1.le hclose
      hbound hm).trans (add_le_add_right (mul_le_mul_of_nonneg_right hb (pos _)) _)
  · intro j hj
    filter_upwards [hr j hj] with m hm
    exact hm.trans (add_le_add_right (mul_le_mul_of_nonneg_right hsmall (pos _)) _)

theorem site_H2_of_sampled
    (cells : ∀ Y, Shift490.PrimeCellInput Y) (smoothing : ∀ Y, Shift490.FiniteSmoothing Y)
    (sample : SampledRecovery) : OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 :=
  site_H2_of_shift_and_recovery cells smoothing (stableRecovery_of_sampled sample)

#print axioms site_H2_of_sampled
end
end Erdos490Transfer

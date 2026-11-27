import AssemblyProbability
import SparsificationRates
import TerminalLimit
import AssemblyRates

/-! Limiting composition along the primes for the uniform coverable proportion. -/

open Filter Topology Finset Real
open scoped Classical Pointwise
namespace Green39.Assembly
noncomputable section

local instance (p : Prime) : NeZero p.val := ⟨p.property.ne_zero⟩

def sliceCover (p : Prime) : ℝ := Concentration.sliceProbability (univ : Points p.val) p.val.sqrt (cover p.val)

/-- Only deterministic catalog data, a last-list counting estimate, and a
one-law deviation rate enter the endpoint. The exponents 0.46 and 0.70
allow slack above the transcript exponents 0.44 and 0.66. -/
theorem tendsto_zero_of_catalog (C : (p : Prime) → Catalog p.val) {L : ℝ} (hL : 0 ≤ L)
    (hstage : ∀ᶠ p in atTop, StageSpec (C p))
    (hterm : ∀ᶠ p in atTop, log (1 + (((C p).containers (C p).stages).card:ℝ)) ≤
      L * log (p.val:ℝ)^ (2:ℝ))
    (hlaws : ∀ᶠ p in atTop, ((allLaws (C p)).card:ℝ) ≤ exp ((p.val.sqrt:ℝ)^(0.46:ℝ)))
    (hcost : ∀ᶠ p in atTop,
      (∑ i ∈ range (C p).stages, (((C p).containers i).card:ℝ)*((C p).laws i).card) ≤
        exp ((p.val.sqrt:ℝ)^(0.70:ℝ)))
    (hsmooth : ∀ᶠ p : Prime in atTop, ∀ μ ∈ allLaws (C p),
      Split.probability (space p.val) (fun q => ¬typical μ q) ≤ exp (-((p.val.sqrt:ℝ)^(0.48:ℝ)))) :
    Tendsto sliceCover atTop (𝓝 0) := by
  let Ps := fun p : Prime => (C p).containers (C p).stages
  have hsize : ∀ᶠ p in atTop, ∀ P ∈ Ps p, (P.card:ℝ) ≤ exp 5000 * p.val.sqrt := by
    filter_upwards [hstage] with p hs P hP
    exact (hs.containerSize _ le_rfl P hP).trans (by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr hs.stop) (Nat.cast_nonneg _))
  have ht := Terminal.coversOutside_tendsto_one_primes Ps (ζ:=0.02) (exp_pos _).le
    (by norm_num) hL (by norm_num) hsize hterm
  let bad (p : Prime) := Concentration.sliceProbability (univ : Points p.val) p.val.sqrt (fun A => ¬ terminalOK (C p) A)
  have hb : Tendsto bad atTop (𝓝 0) := by
    have ht' := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=Prime))).sub ht
    convert ht' using 1
    · funext p
      have h := Terminal.sliceProbability_add_compl (univ : Points p.val)
        (k:=p.val.sqrt) (by simpa using Nat.sqrt_le_self p.val) (terminalOK (C p))
      change _ = 1 - Concentration.sliceProbability _ _ (terminalOK (C p))
      unfold bad
      linarith
    · norm_num
  let k := fun p : Prime => (p.val.sqrt:ℝ)
  have hsu := exp_decay 0.48 0.5 (by norm_num) (by norm_num)
  have hhi := exp_decay 1 467 (by norm_num) (by norm_num)
  simp only [Real.rpow_one] at hhi
  have hupper := ((balance_decay.add hb).add hsu).add hhi
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall fun p => by unfold sliceCover; unfold Concentration.sliceProbability; positivity
  · have hsp := prime_cofinal.eventually (OnePercent.Fourier.sparsification_scale_eventually_sqrt 8 (by norm_num))
    filter_upwards [hstage,hlaws,hcost,hsmooth,prime_root.eventually_ge_atTop 100000,hsp,
      prime_root_real.eventually (power_margin (a:=0.46) (b:=0.48) (by norm_num) 2),
      prime_root_real.eventually (power_margin (a:=0.70) (b:=1) (by norm_num) 1)]
      with p spec hl hc hs hk hsp hmargin hcost'
    have hk0 : 0 < p.val.sqrt := by omega
    have hx : 0 ≤ log ((p.val:ℝ) / p.val.sqrt) := log_nonneg
      ((one_le_div (Nat.cast_pos.mpr hk0)).mpr (Nat.cast_le.mpr (Nat.sqrt_le_self _)))
    have hpar (i : ℕ) (_ : i < (C p).stages) : 8*log (4*(p.val:ℝ)) <
        (sMax p.val.sqrt:ℝ)*eta (x p.val i)^2 :=
      hsp _ (Transcripts.level_antitone hx (Nat.zero_le i))
    unfold sliceCover
    apply (cover_upper spec hk hpar _ hs).trans
    have hp := (numerical (p:=p.val) hk (Nat.lt_succ_sqrt' p.val)).1
    have h₁ : 2*(p.val:ℝ)*exp (-(k p)/200000000) ≤ 4*(k p)^2* exp (-(k p)/200000000) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      dsimp [k]; nlinarith [sq_nonneg (p.val.sqrt:ℝ)]
    have h₂ : ((allLaws (C p)).card:ℝ)*exp (-(k p ^ (0.48:ℝ))) ≤ exp (-0.5*k p ^ (0.48:ℝ)) := by
      apply (mul_le_mul_of_nonneg_right hl (exp_pos _).le).trans
      rw [←exp_add]; apply exp_le_exp.mpr; dsimp [k]; linarith
    have h₃ := mul_le_mul_of_nonneg_right hc (exp_pos (-468*k p)).le
    rw [←exp_add] at h₃
    have h₄ : exp (k p ^ (0.70:ℝ) + -468*k p) ≤ exp (-467*k p) := by
      apply exp_le_exp.mpr; simp only [rpow_one,one_mul] at hcost'; dsimp [k]; linarith
    exact add_le_add (add_le_add (add_le_add h₁ (le_refl (bad p))) h₂) (h₃.trans h₄)

end
end Green39.Assembly

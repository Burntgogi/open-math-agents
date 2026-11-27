import TerminalUniform
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Terminal-container restriction for polylogarithmic transcript lists

For any fixed size bound and any prescribed family whose logarithmic size
grows at most polylogarithmically, the simultaneous event in Section 1,
equation (1), has uniform-slice probability tending to one.
-/

open Filter Topology Asymptotics
open scoped BigOperators Classical

namespace Green39.Terminal

noncomputable section

private theorem tendsto_nat_sqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.mpr fun b ↦ (eventually_ge_atTop (b * b)).mono fun _ h ↦ Nat.le_sqrt.mpr h

private theorem tendsto_scale : Tendsto (fun p : ℕ ↦ (scale p : ℝ)) atTop atTop := by
  apply (tendsto_natCast_atTop_atTop (R := ℝ)).comp
  have h := tendsto_nat_sqrt.comp (tendsto_nat_sqrt.comp tendsto_nat_sqrt)
  exact tendsto_atTop.mpr fun b ↦ (h.eventually_ge_atTop b).mono fun p hp ↦
    (show b ≤ p.sqrt.sqrt.sqrt from hp).trans (Nat.le_succ _)

private theorem tendsto_polynomial_exp (C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ C * x ^ 8 * Real.exp (-a * x)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((8 : ℕ) : ℝ) a ha
  simp only [Real.rpow_natCast] at h
  simpa only [mul_zero, mul_assoc] using h.const_mul C

/-- The simultaneous good event for (1), evaluated on an arbitrary cofinal
family of moduli. The family of prescribed sets may depend on the modulus. -/
theorem coversOutside_tendsto_one {ι : Type*} {l : Filter ι} (p : ι → ℕ)
    [∀ i, NeZero (p i)] (hp : Tendsto p l atTop)
    (Ps : (i : ι) → Finset (Finset (ZMod (p i)))) {M ζ C D : ℝ}
    (hM : 0 ≤ M) (hζ : 0 < ζ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsize : ∀ᶠ i in l, ∀ P ∈ Ps i, (P.card : ℝ) ≤ M * ((p i).sqrt : ℝ))
    (hlist : ∀ᶠ i in l, Real.log (1 + ((Ps i).card : ℝ)) ≤ C * Real.log (p i : ℝ) ^ D) :
    Tendsto (fun i ↦ probability (p i) (p i).sqrt
      (fun A ↦ ∀ P ∈ Ps i, CoversOutside P (p i).sqrt ζ A)) l (𝓝 1) := by
  let δ := min (ζ / 2) (1 / 2)
  let a := decay M δ
  let x (i : ι) : ℝ := scale (p i)
  let k (i : ι) : ℕ := (p i).sqrt
  let E (i : ι) (A : Finset (ZMod (p i))) := ∀ P ∈ Ps i, CoversOutside P (k i) ζ A
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hratio : 1 - ζ ≤ (1 - δ) / (1 + δ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := min_le_left (ζ / 2) (1 / 2 : ℝ)
    change δ ≤ ζ / 2 at h
    nlinarith [mul_nonneg hδ.le hζ.le]
  have ha : 0 < a := decay_pos M hδ
  have hx : Tendsto x l atTop := tendsto_scale.comp hp
  have hk : Tendsto k l atTop := tendsto_nat_sqrt.comp hp
  have hkr : Tendsto (fun i ↦ (k i : ℝ)) l atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hk
  have hSmall : ∀ᶠ i in l, uniformBound M δ (x i) ≤ δ * densityLower M / 4 := by
    have hlim := (tendsto_polynomial_exp (Real.exp (2 * M) + 2) ha).comp hx
    have hc : 0 < δ * densityLower M / 4 := by unfold densityLower; positivity
    exact (hlim.eventually (Iio_mem_nhds hc)).mono fun i hi ↦ hi.le
  have hfinite : ∀ᶠ i in l, probability (p i) (k i) (fun A ↦ ¬ E i A) ≤
      ((Ps i).card : ℝ) * uniformBound M δ (x i) := by
    filter_upwards [hk.eventually_ge_atTop 2, hsize, hkr.eventually_ge_atTop (2 * (1 + M)),
      hkr.eventually_ge_atTop (4 * M / δ), hSmall] with i hi hs h₁ h₂ h₃
    exact probability_not_coversOutside_list_le_uniform (Ps i) hM hδ hi hs h₁ h₂ h₃ hratio
  have hlogLittle : (fun y : ℝ ↦ C * (8 : ℝ) ^ D * Real.log y ^ D) =o[atTop]
      (fun y : ℝ ↦ y) := by
    have h := (isLittleO_log_rpow_rpow_atTop D (s := 1) zero_lt_one).const_mul_left
      (C * (8 : ℝ) ^ D)
    simpa only [Real.rpow_one] using h
  have hlogUpper : ∀ᶠ i in l, Real.log (1 + ((Ps i).card : ℝ)) ≤ a * x i / 2 := by
    have hlo := hx.eventually (hlogLittle.def (show 0 < a / 2 by positivity))
    filter_upwards [hx.eventually_ge_atTop 1, hlo, hlist] with i hxi hl hi
    have hp1 : 1 ≤ (p i : ℝ) := by
      exact_mod_cast (show 1 ≤ p i from Nat.pos_of_ne_zero (NeZero.ne (p i)))
    have hpX : (p i : ℝ) ≤ x i ^ 8 := by
      dsimp only [x]
      exact_mod_cast modulus_le_scale_pow (p i)
    have hlog : Real.log (p i : ℝ) ≤ 8 * Real.log (x i) := by
      calc
        _ ≤ Real.log (x i ^ 8) := Real.log_le_log (zero_lt_one.trans_le hp1) hpX
        _ = _ := by norm_num [Real.log_pow]
    calc
      _ ≤ C * Real.log (p i : ℝ) ^ D := hi
      _ ≤ C * (8 * Real.log (x i)) ^ D :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.log_nonneg hp1) hlog hD) hC
      _ = C * (8 : ℝ) ^ D * Real.log (x i) ^ D := by
        rw [Real.mul_rpow (by norm_num) (Real.log_nonneg hxi), mul_assoc]
      _ ≤ _ := by
        have hxl : 0 ≤ x i := zero_le_one.trans hxi
        change ‖C * (8 : ℝ) ^ D * Real.log (x i) ^ D‖ ≤ (a / 2) * ‖x i‖ at hl
        rw [Real.norm_of_nonneg hxl] at hl
        have hh := (le_abs_self (C * (8 : ℝ) ^ D * Real.log (x i) ^ D)).trans
          (by simpa only [Real.norm_eq_abs] using hl)
        linarith
  have hcounts : ∀ᶠ i in l, ((Ps i).card : ℝ) ≤ Real.exp (a * x i / 2) :=
    hlogUpper.mono fun i hi ↦ by
      have hpos : 0 < 1 + ((Ps i).card : ℝ) := by positivity
      have h := (Real.log_le_iff_le_exp hpos).mp hi
      linarith
  have hlim : Tendsto (fun i ↦ (Real.exp (2 * M) + 2) * x i ^ 8 *
      Real.exp (-(a / 2) * x i)) l (𝓝 0) :=
    (tendsto_polynomial_exp _ (by positivity : 0 < a / 2)).comp hx
  have hfail : Tendsto (fun i ↦ probability (p i) (k i) (fun A ↦ ¬ E i A)) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    · exact Eventually.of_forall fun _ ↦ sliceProbability_nonneg _ _ _
    · filter_upwards [hfinite, hcounts] with i hfin hcount
      refine hfin.trans ((mul_le_mul_of_nonneg_right hcount (uniformBound_nonneg _ _ _)).trans_eq ?_)
      unfold uniformBound
      change Real.exp (a * x i / 2) *
          ((Real.exp (2 * M) + 2) * x i ^ 8 * Real.exp (-a * x i)) = _
      rw [show ∀ z w v : ℝ, z * (w * v) = w * (z * v) by intros; ring, ← Real.exp_add]
      congr 2
      ring
  have hsuccess : Tendsto (fun i ↦ 1 - probability (p i) (k i) (fun A ↦ ¬ E i A))
      l (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hfail
  convert hsuccess using 1
  funext i
  have hki : k i ≤ (Finset.univ : Finset (ZMod (p i))).card := by
    simpa only [Finset.card_univ, ZMod.card] using Nat.sqrt_le_self (p i)
  change probability (p i) (k i) (E i) = 1 - probability (p i) (k i) (fun A ↦ ¬ E i A)
  exact eq_sub_of_add_eq (sliceProbability_add_compl _ hki (E i))

/-- Section 1, equation (1), along the primes. The probability is with
respect to the uniformly chosen «floor sqrt p»-element subset of «ZMod p». -/
theorem coversOutside_tendsto_one_primes
    (Ps : (p : {n : ℕ // n.Prime}) → Finset (Finset (ZMod p.val))) {M ζ C D : ℝ}
    (hM : 0 ≤ M) (hζ : 0 < ζ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hsize : ∀ᶠ p in atTop, ∀ P ∈ Ps p, (P.card : ℝ) ≤ M * (p.val.sqrt : ℝ))
    (hlist : ∀ᶠ p in atTop, Real.log (1 + ((Ps p).card : ℝ)) ≤ C * Real.log (p.val : ℝ) ^ D) :
    Tendsto (fun p : {n : ℕ // n.Prime} ↦
      letI : NeZero p.val := ⟨p.property.ne_zero⟩
      probability p.val p.val.sqrt (fun A ↦ ∀ P ∈ Ps p, CoversOutside P p.val.sqrt ζ A))
      atTop (𝓝 1) := by
  have hp : Tendsto (fun p : {n : ℕ // n.Prime} ↦ p.val) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes b
    exact (eventually_ge_atTop (⟨q, hprime⟩ : {n : ℕ // n.Prime})).mono
      fun _ h ↦ hq.trans h
  exact @coversOutside_tendsto_one _ _ (fun p : {n : ℕ // n.Prime} ↦ p.val)
    (fun p ↦ ⟨p.property.ne_zero⟩) hp Ps _ _ _ _ hM hζ hC hD hsize hlist

end

end Green39.Terminal


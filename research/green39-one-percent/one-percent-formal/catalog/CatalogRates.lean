import ConcreteCatalog

/-! The concrete catalog counts in the form used by the probability endpoint. -/

open Filter Topology Finset Real
open scoped Classical

namespace Green39.Assembly

noncomputable section

private theorem half_le_log_two : (1 / 2 : ℝ) ≤ log 2 := by
  have h := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  linarith

private theorem initial_le_log (p : ℕ) [NeZero p] : x p 0 ≤ log (p : ℝ) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hk : (1 : ℝ) ≤ p.sqrt := by exact_mod_cast Nat.sqrt_pos.mpr hp
  exact log_le_log (div_pos (Nat.cast_pos.mpr hp) (zero_lt_one.trans_le hk))
    (div_le_self (Nat.cast_nonneg _) hk)

private theorem log_stageCount_le (p : ℕ) [NeZero p] :
    log (1 + (stageCount p : ℝ)) ≤ 1 + log (p : ℝ) := by
  have h := stageCount_le p
  have hlog := initial_le_log p
  have hcount := log_le_sub_one_of_pos (show 0 < 1 + (stageCount p : ℝ) by positivity)
  linarith [log_natCast_nonneg p]

private theorem one_add_log_le_sqrt_log {p : ℕ} (hk : 2 ≤ p.sqrt) :
    1 + log (p : ℝ) ≤ 6 * log (p.sqrt : ℝ) := by
  let k : ℝ := p.sqrt
  have hk' : 2 ≤ k := by
    change (2 : ℝ) ≤ (p.sqrt : ℝ)
    exact_mod_cast hk
  have hp : (p : ℝ) ≤ (k + 1) ^ 2 := by
    change (p : ℝ) ≤ ((p.sqrt : ℝ) + 1) ^ 2
    exact_mod_cast (Nat.lt_succ_sqrt' p).le
  have hp2 : (p : ℝ) ≤ (2 * k) ^ 2 := hp.trans
    (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hp0 : 0 < p := Nat.sqrt_pos.mp (by omega)
  have hlog := log_le_log (Nat.cast_pos.mpr hp0) hp2
  rw [log_pow, log_mul (by norm_num) (by positivity : k ≠ 0)] at hlog
  have hklog : log 2 ≤ log k := log_le_log (by norm_num) hk'
  norm_num at hlog
  change 1 + log (p : ℝ) ≤ 6 * log k
  linarith [half_le_log_two]

private theorem log_sqrt_le_initial (p : ℕ) (hk : 0 < p.sqrt) : log (p.sqrt : ℝ) ≤ x p 0 := by
  have hk' : (0 : ℝ) < p.sqrt := Nat.cast_pos.mpr hk
  have hsq : (p.sqrt : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  apply log_le_log hk'
  apply (le_div_iff₀ hk').mpr
  simpa only [pow_two] using hsq

private theorem small_log_eventually :
    ∀ᶠ t : ℝ in atTop, 6 * log t ≤ t ^ (0.005 : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.005)).bound
    (show (0 : ℝ) < 1 / 6 by norm_num)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  change ‖log t‖ ≤ 1 / 6 * ‖t ^ (0.005 : ℝ)‖ at ht
  rw [Real.norm_of_nonneg (log_nonneg ht1), Real.norm_of_nonneg (by positivity)] at ht
  linarith

private theorem absorb_constant {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, C * t ^ a ≤ t ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,
    eventually_gt_atTop (0 : ℝ)] with t hC ht
  rw [show b = (b - a) + a by ring, rpow_add ht]
  exact mul_le_mul_of_nonneg_right hC (rpow_nonneg ht.le _)

private def lawConstant : ℝ := 7 * 18 * exp 2000 * (4 : ℝ) ^ (11 / 25 : ℝ)

private def containerConstant : ℝ := 48 * 18 * exp 3000 * (4 : ℝ) ^ (33 / 50 : ℝ)

private theorem lawExponent_le {p : ℕ} (hlog : 1 + log (p : ℝ) ≤ (p.sqrt : ℝ) ^ (0.005 : ℝ)) :
    lawExponent p ≤ lawConstant * (p.sqrt : ℝ) ^ (0.45 : ℝ) := by
  let k : ℝ := p.sqrt
  have hsq := pow_le_pow_left₀ (by linarith [log_natCast_nonneg p] : 0 ≤ 1 + log (p : ℝ)) hlog 2
  have hnonneg : 0 ≤ lawConstant * k ^ (11 / 25 : ℝ) := by unfold lawConstant; positivity
  have hpow : (k ^ (0.005 : ℝ)) ^ (2 : ℕ) = k ^ (0.01 : ℝ) := by
    rw [← rpow_mul_natCast (by positivity), show (0.005 : ℝ) * (2 : ℕ) = 0.01 by norm_num]
  rw [hpow] at hsq
  unfold lawExponent
  rw [mul_rpow (by norm_num) (Nat.cast_nonneg _), ← mul_assoc]
  change lawConstant * k ^ (11 / 25 : ℝ) * (1 + log (p : ℝ)) ^ 2 ≤ _
  calc
    _ ≤ lawConstant * k ^ (11 / 25 : ℝ) * k ^ (0.01 : ℝ) :=
      mul_le_mul_of_nonneg_left hsq hnonneg
    _ = _ := by
      rw [mul_assoc, ← rpow_add' (by positivity : 0 ≤ k) (by norm_num : (11 / 25 : ℝ) + 0.01 ≠ 0)]
      rw [show (11 / 25 : ℝ) + (0.01 : ℝ) = 0.45 by norm_num]

private theorem containerExponent_le {p : ℕ}
    (hlog : 1 + log (p : ℝ) ≤ (p.sqrt : ℝ) ^ (0.005 : ℝ)) :
    containerExponent p ≤ containerConstant * (p.sqrt : ℝ) ^ (0.675 : ℝ) := by
  let k : ℝ := p.sqrt
  have hL : 0 ≤ 1 + log (p : ℝ) := by linarith [log_natCast_nonneg p]
  have ht := log_le_sub_one_of_pos (show 0 < 1 + log (p : ℝ) by linarith [log_natCast_nonneg p])
  have hcube := pow_le_pow_left₀ hL hlog 3
  have hpow : (k ^ (0.005 : ℝ)) ^ (3 : ℕ) = k ^ (0.015 : ℝ) := by
    rw [← rpow_mul_natCast (by positivity), show (0.005 : ℝ) * (3 : ℕ) = 0.015 by norm_num]
  rw [hpow] at hcube
  have hnonneg : 0 ≤ containerConstant * k ^ (33 / 50 : ℝ) := by unfold containerConstant; positivity
  unfold containerExponent
  rw [mul_rpow (by norm_num) (Nat.cast_nonneg _), ← mul_assoc]
  change containerConstant * k ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 2 *
    (1 + log (1 + log (p : ℝ))) ≤ _
  calc
    _ ≤ containerConstant * k ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 2 *
        (1 + log (p : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = containerConstant * k ^ (33 / 50 : ℝ) * (1 + log (p : ℝ)) ^ 3 := by ring
    _ ≤ containerConstant * k ^ (33 / 50 : ℝ) * k ^ (0.015 : ℝ) :=
      mul_le_mul_of_nonneg_left hcube hnonneg
    _ = _ := by
      rw [mul_assoc, ← rpow_add' (by positivity : 0 ≤ k) (by norm_num : (33 / 50 : ℝ) + 0.015 ≠ 0)]
      rw [show (33 / 50 : ℝ) + (0.015 : ℝ) = 0.675 by norm_num]

def terminalLogConstant : ℝ := 9 * terminalCoefficient

theorem terminalLogConstant_nonneg : 0 ≤ terminalLogConstant := by
  have hlog : 0 ≤ log (2 * (10000 : ℝ) ^ 2) := log_nonneg (by norm_num)
  unfold terminalLogConstant terminalCoefficient Transcripts.inverseEta
  positivity

variable {ι : Type*} {l : Filter ι}

/-- These bounds hold along any cofinal family, in particular along the primes. -/
theorem concreteCatalog_eventual_bounds (m : ι → ℕ) [∀ i, NeZero (m i)]
    (hm : Tendsto m l atTop) :
    ∀ᶠ i in l,
      let C := concreteCatalog (m i)
      let k := ((m i).sqrt : ℝ)
      Transcripts.logCard (C.containers C.stages) ≤ terminalLogConstant * log (m i : ℝ) ^ (2 : ℝ) ∧
      (((range C.stages).biUnion C.laws).card : ℝ) ≤ exp (k ^ (0.46 : ℝ)) ∧
      (∑ j ∈ range C.stages, ((C.containers j).card : ℝ) * (C.laws j).card) ≤ exp (k ^ (0.70 : ℝ)) := by
  have hkNat : Tendsto (fun i => (m i).sqrt) l atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact (hm.eventually_ge_atTop (b * b)).mono fun _ h => Nat.le_sqrt.mpr h
  have hkReal : Tendsto (fun i => ((m i).sqrt : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp hkNat
  have hlaw := hkReal.eventually (absorb_constant (a := 0.45) (b := 0.46) (by norm_num) (1 + lawConstant))
  have hcost := hkReal.eventually
    (absorb_constant (a := 0.675) (b := 0.70) (by norm_num) (1 + containerConstant + lawConstant))
  have hactive := (tendsto_log_atTop.comp hkReal).eventually_gt_atTop 5000
  filter_upwards [hkNat.eventually_ge_atTop 2, hkReal.eventually small_log_eventually, hlaw, hcost,
    hactive] with i hk hs hlaw hcost ha
  dsimp only
  let p := m i
  let k : ℝ := p.sqrt
  have hkP : 2 ≤ p.sqrt := hk
  have hk1 : 1 ≤ k := by
    change (1 : ℝ) ≤ (p.sqrt : ℝ)
    exact_mod_cast (show 1 ≤ p.sqrt from (by decide : 1 ≤ 2).trans hkP)
  have hL : 1 + log (p : ℝ) ≤ k ^ (0.005 : ℝ) := (one_add_log_le_sqrt_log hk).trans hs
  have hcount := (log_stageCount_le p).trans hL
  have hlaw' := lawExponent_le hL
  have hcost' := containerExponent_le hL
  have hsmallLaw : k ^ (0.005 : ℝ) ≤ k ^ (0.45 : ℝ) :=
    rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hlawCost : k ^ (0.45 : ℝ) ≤ k ^ (0.675 : ℝ) :=
    rpow_le_rpow_of_exponent_le hk1 (by norm_num)
  have hpos := stageCount_pos (ha.trans_le (log_sqrt_le_initial p ((by decide : 0 < 2).trans_le hkP)))
  refine ⟨?_, ?_, ?_⟩
  · have hplog : (1 / 2 : ℝ) ≤ log (p : ℝ) := half_le_log_two.trans
      (log_le_log (by norm_num) (by exact_mod_cast hk.trans (Nat.sqrt_le_self p)))
    have hcoeff : 0 ≤ terminalCoefficient := by
      have h := terminalLogConstant_nonneg
      unfold terminalLogConstant at h
      linarith
    apply (concreteCatalog_log_terminal p hpos).trans
    rw [rpow_two, terminalLogConstant]
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + log (p : ℝ))
      (show 1 + log (p : ℝ) ≤ 3 * log (p : ℝ) by linarith) 2
    have hscaled := mul_le_mul_of_nonneg_left hsq hcoeff
    calc
      _ ≤ terminalCoefficient * (3 * log (p : ℝ)) ^ 2 := hscaled
      _ = _ := by ring
  · have hlogCount := concreteCatalog_log_allLaws p
    have hbound : log (1 + (stageCount p : ℝ)) + lawExponent p ≤ k ^ (0.46 : ℝ) := by
      apply (add_le_add (hcount.trans hsmallLaw) hlaw').trans
      rw [← one_add_mul]
      exact hlaw
    have hh := (log_le_iff_le_exp (by positivity)).mp (hlogCount.trans hbound)
    linarith
  · apply (concreteCatalog_sum_card_products p).trans
    have hlawBig : lawExponent p ≤ lawConstant * k ^ (0.675 : ℝ) :=
      hlaw'.trans (mul_le_mul_of_nonneg_left hlawCost (by unfold lawConstant; positivity))
    have hbound : log (1 + (stageCount p : ℝ)) + (containerExponent p + lawExponent p) ≤
        k ^ (0.70 : ℝ) := by
      apply (add_le_add ((hcount.trans hsmallLaw).trans hlawCost) (add_le_add hcost' hlawBig)).trans
      calc
        _ = (1 + containerConstant + lawConstant) * k ^ (0.675 : ℝ) := by
          change k ^ (0.675 : ℝ) + (containerConstant * k ^ (0.675 : ℝ) +
            lawConstant * k ^ (0.675 : ℝ)) = _
          ring
        _ ≤ _ := hcost
    calc
      _ ≤ (1 + (stageCount p : ℝ)) * exp (containerExponent p + lawExponent p) := by gcongr; linarith
      _ = exp (log (1 + (stageCount p : ℝ)) + (containerExponent p + lawExponent p)) := by
        rw [exp_add (log (1 + (stageCount p : ℝ))) (containerExponent p + lawExponent p),
          exp_log (by positivity)]
      _ ≤ _ := exp_le_exp.mpr hbound

end

end Green39.Assembly

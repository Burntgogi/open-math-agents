import FitFourier

/-! # Explicit instruction and removal budgets for the fitting stage -/

namespace Green39.Fitting
open Real
noncomputable section

def wordBudget (p : ℕ) (η : ℝ) : ℕ := ⌊16*log p / η^2⌋₊ + 1
def peelBudget (η ξ : ℝ) : ℕ := ⌊(2/η)*log (2/ξ)⌋₊ + 1

theorem wordBudget_spec (p : ℕ) {η : ℝ} (he : 0 < η) :
    16*log p < (wordBudget p η : ℝ)*η^2 := by
  apply (div_lt_iff₀ (sq_pos_of_pos he)).mp
  simpa [wordBudget] using Nat.lt_floor_add_one (16*log p/η^2)

theorem peelBudget_spec {η ξ : ℝ} (he : 0 < η) (he' : η ≤ 1/2) (hξ : 0 < ξ) :
    (1-η/2)^(peelBudget η ξ) < ξ/2 := by
  let n := peelBudget η ξ
  have hn : (2/η)*log (2/ξ) < (n : ℝ) := by
    simpa [n,peelBudget] using Nat.lt_floor_add_one ((2/η)*log (2/ξ))
  have hlog : log (2/ξ) < (n : ℝ)*η/2 := by
    have hh := mul_lt_mul_of_pos_right hn he
    field_simp [ne_of_gt he] at hh
    linarith
  have hx : 1-η/2 ≤ exp (-(η/2)) := by linarith [add_one_le_exp (-(η/2))]
  calc
    _ ≤ exp (-(η/2))^n := pow_le_pow_left₀ (by linarith) hx _
    _ = exp ((n:ℝ)*(-(η/2))) := (exp_nat_mul _ _).symm
    _ < exp (-log (2/ξ)) := exp_lt_exp.mpr (by linarith)
    _ = _ := by rw [exp_neg,exp_log (by positivity)]; field_simp

theorem wordBudget_le (p : ℕ) (hp : 1 ≤ p) {η : ℝ} (he : 0 < η) :
    (wordBudget p η : ℝ) ≤ 16*log p/η^2 + 1 := by
  simp only [wordBudget,Nat.cast_add,Nat.cast_one,add_le_add_iff_right]
  exact Nat.floor_le (div_nonneg (mul_nonneg (by norm_num)
    (log_nonneg (by exact_mod_cast hp))) (sq_pos_of_pos he).le)

theorem peelBudget_le {η ξ : ℝ} (he : 0 < η) (hξ : 0 < ξ) (hξ' : ξ ≤ 1) :
    (peelBudget η ξ : ℝ) ≤ (2/η)*log (2/ξ) + 1 := by
  simp only [peelBudget,Nat.cast_add,Nat.cast_one,add_le_add_iff_right]
  exact Nat.floor_le (mul_nonneg (by positivity) (log_nonneg ((le_div_iff₀ hξ).mpr (by linarith))))

/-- In particular a successful transcript never uses an implicit search-depth parameter. -/
theorem cyclic_stage_explicit {p : ℕ} [NeZero p] (V : Finset (ZMod p)) {k η ξ K : ℝ}
    (hk : 0 < k) (hV : V.card ≤ 2*k) (he : 0 < η) (he' : η ≤ 1/2)
    (hξ : 0 < ξ) (hK : 0 < K) :
    (∃ F ⊆ V, ξ*k ≤ F.card ∧ ∃ w : List (Instruction (ZMod p × Bool)),
      w.length ≤ wordBudget p η ∧
      let μ := fittedLaw η (1/(K*k)) w
      (∑ i, μ i = 1) ∧ (∀ i, 0 ≤ μ i ∧ μ i ≤ 2*(1/(K*k))) ∧ ∀ j : ZMod p,
      ‖ZMod.dft (fun i => (uniformOn F i : ℂ)) j - ZMod.dft (fun i => (μ i : ℂ)) j‖ ≤ 5*η) ∨
    (∃ ws : List (List (Instruction (ZMod p × Bool))), ws.length ≤ peelBudget η ξ ∧
      (∀ w ∈ ws, w.length ≤ wordBudget p η) ∧
      let P := recordedUnion (cyclicTests p) η (1/(K*k)) ws
      (P.card : ℝ) ≤ (peelBudget η ξ : ℝ) / (1/(K*k)) ∧ ((V \ P).card : ℝ) < ξ*k) := by
  apply cyclic_stage he he' (by positivity) (by positivity) _ _ (wordBudget_spec p he) V
  calc
    _ ≤ (1-η/2)^peelBudget η ξ * (2*k) :=
      mul_le_mul_of_nonneg_left hV (pow_nonneg (by linarith) _)
    _ < (ξ/2)*(2*k) := mul_lt_mul_of_pos_right (peelBudget_spec he he' hξ) (by positivity)
    _ = _ := by ring

#print axioms cyclic_stage_explicit
end
end Green39.Fitting

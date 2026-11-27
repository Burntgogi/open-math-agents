import FormalConjectures.GreensOpenProblems.«39»

/-! # The volume-budget limit implies the exact upstream disproof. -/

open Filter Topology

namespace OnePercent

/-- Monotonicity includes both exceptional branches of the upstream definition. -/
theorem budget_mono (p k c d : ℕ) (h : c ≤ d) :
    Green39.proportionCoverable p k c ≤ Green39.proportionCoverable p k d := by
  unfold Green39.proportionCoverable
  split
  · exact le_rfl
  split
  · exact le_rfl
  let _ : NeZero p := ⟨by assumption⟩
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro A hA
  obtain ⟨hsize, T, ht, hc⟩ := Finset.mem_filter.mp hA
  exact Finset.mem_filter.mpr ⟨hsize, T, ht.trans h, hc⟩

theorem proportion_nonneg (p k c : ℕ) : 0 ≤ Green39.proportionCoverable p k c := by
  unfold Green39.proportionCoverable
  split
  · exact le_rfl
  split
  · exact le_rfl
  positivity

/-- The larger integer budget is precisely the one obtained by clearing 1.01 p/k. -/
theorem budget_comparison (p : ℕ) (hp : 0 < p) :
    ⌊1.01 * (p.sqrt : ℝ)⌋₊ ≤ (101*p) / (100*p.sqrt) := by
  have hk : 1 ≤ p.sqrt := Nat.le_sqrt.mpr (by omega)
  have hs : (p.sqrt : ℝ) * p.sqrt ≤ p := by exact_mod_cast Nat.sqrt_le p
  have hf := Nat.floor_le (by positivity : 0 ≤ 1.01 * (p.sqrt : ℝ))
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 100 * p.sqrt)).mpr
  have h : (⌊1.01 * (p.sqrt : ℝ)⌋₊ : ℝ) * (100 * p.sqrt) ≤ 101 * p := by
    nlinarith [mul_le_mul_of_nonneg_right hf (Nat.cast_nonneg p.sqrt)]
  exact_mod_cast h

/-- Interface for the remaining random-cover proof. The conclusion is the exact upstream negation. -/
theorem disproof_of_volume_limit
    (hzero : Tendsto (fun p : {q : ℕ // q.Prime} =>
      (Green39.proportionCoverable p p.val.sqrt ((101*p.val)/(100*p.val.sqrt)) : ℝ))
      atTop (𝓝 0)) : ¬ (type_of% @Green39.green_39.variant_101) := by
  let _ : Nonempty {q : ℕ // q.Prime} := ⟨⟨2, Nat.prime_two⟩⟩
  intro hone
  have hsmall : Tendsto (fun p : {q : ℕ // q.Prime} =>
      (Green39.proportionCoverable p p.val.sqrt ⌊1.01 * (p.val.sqrt : ℝ)⌋₊ : ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero _ _ hzero
    · intro p
      exact_mod_cast proportion_nonneg p.val _ _
    · intro p
      exact_mod_cast budget_mono p.val _ _ _ (budget_comparison p.val p.property.pos)
  exact zero_ne_one (tendsto_nhds_unique hsmall hone)

end OnePercent

#print axioms OnePercent.disproof_of_volume_limit

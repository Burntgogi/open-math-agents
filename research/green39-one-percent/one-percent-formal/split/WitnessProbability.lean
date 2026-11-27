import SplitLaws
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The §5 hit-count bound

For a particular set of r distinct hits, the probability that the sample
contains all of them is the ratio of two binomial coefficients. Union over
the r-subsets of the bad set before using the bound on its cardinality.
-/

open Finset
open scoped BigOperators Classical

set_option autoImplicit false

namespace Green39.Split

open Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

private theorem choose_le_choose_mul_ratio_pow {m n r : ℕ} (hmn : m ≤ n) (hr : r ≤ n) :
    (m.choose r : ℝ) ≤ (n.choose r : ℝ) * ((m : ℝ) / n) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain h | h := lt_or_ge m (r + 1)
    · rw [Nat.choose_eq_zero_of_lt h]
      simp only [Nat.cast_zero]
      positivity
    have hnr : r ≤ n := by omega
    have hmr : r ≤ m := by omega
    have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hstep : ((m - r : ℕ) : ℝ) ≤ (n - r : ℕ) * ((m : ℝ) / n) := by
      rw [← mul_div_assoc, le_div_iff₀ hn, Nat.cast_sub hmr, Nat.cast_sub hnr]
      have hmul : 0 ≤ (r : ℝ) * ((n : ℝ) - m) :=
        mul_nonneg (by positivity) (sub_nonneg.mpr (by exact_mod_cast hmn))
      nlinarith only [hmul]
    have hrec (a : ℕ) :
        (a.choose (r + 1) : ℝ) * (r + 1 : ℝ) = a.choose r * (a - r : ℕ) := by
      exact_mod_cast Nat.choose_succ_right_eq a r
    apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < r + 1)).mp
    rw [hrec m]
    calc
      (m.choose r : ℝ) * (m - r : ℕ)
          ≤ ((n.choose r : ℝ) * ((m : ℝ) / n) ^ r) *
              ((n - r : ℕ) * ((m : ℝ) / n)) :=
        mul_le_mul (ih hnr) hstep (by positivity) (by positivity)
      _ = ((n.choose r : ℝ) * (n - r : ℕ)) * ((m : ℝ) / n) ^ (r + 1) := by
        rw [pow_succ]
        ring
      _ = ((n.choose (r + 1) : ℝ) * ((m : ℝ) / n) ^ (r + 1)) * (r + 1 : ℝ) := by
        rw [← hrec n]
        ring

/-- Binomial upper bound for at least r hits in a sample of size j. -/
theorem sliceProbability_hits_binomial (s D : Finset α) {j r : ℕ}
    (hj : j ≤ s.card) (hr : r ≤ j) :
    sliceProbability s j (fun B ↦ r ≤ (B ∩ D).card) ≤
      (j.choose r : ℝ) * (((s ∩ D).card : ℝ) / s.card) ^ r := by
  classical
  let W := (s ∩ D).powersetCard r
  have hsubset (B : Finset α) (hB : B ∈ s.powersetCard j) (h : r ≤ (B ∩ D).card) :
      ∃ C ∈ W, C ⊆ B := by
    obtain ⟨C, hC⟩ := powersetCard_nonempty.mpr h
    obtain ⟨hCsub, hCsize⟩ := mem_powersetCard.mp hC
    have hCB : C ⊆ B := hCsub.trans inter_subset_left
    have hCD : C ⊆ D := hCsub.trans inter_subset_right
    exact ⟨C, mem_powersetCard.mpr
      ⟨subset_inter (hCB.trans (mem_powersetCard.mp hB).1) hCD, hCsize⟩, hCB⟩
  have hfixed (C : Finset α) (hC : C ∈ W) :
      sliceProbability s j (fun B ↦ C ⊆ B) =
        ((s.card - r).choose (j - r) : ℝ) / (s.card.choose j : ℝ) := by
    obtain ⟨hCsub, hCsize⟩ := mem_powersetCard.mp hC
    simpa only [hCsize] using sliceProbability_contains s C j (hCsub.trans inter_subset_left)
      (hCsize ▸ hr)
  let n := s.card
  let m := (s ∩ D).card
  have hmn : m ≤ n := card_le_card inter_subset_left
  have hdenj : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hj
  have hdenr : (0 : ℝ) < n.choose r := by exact_mod_cast Nat.choose_pos (hr.trans hj)
  have hchoose : (n.choose j : ℝ) * j.choose r = n.choose r * (n - r).choose (j - r) := by
    exact_mod_cast Nat.choose_mul (n := n) hr
  have hratio : ((n - r).choose (j - r) : ℝ) / (n.choose j : ℝ) =
      (j.choose r : ℝ) / (n.choose r : ℝ) := by
    rw [div_eq_div_iff hdenj.ne' hdenr.ne']
    linarith only [hchoose]
  calc
    sliceProbability s j (fun B ↦ r ≤ (B ∩ D).card)
        ≤ sliceProbability s j (fun B ↦ ∃ C ∈ W, C ⊆ B) := by
      rw [sliceProbability_eq_probability, sliceProbability_eq_probability]
      exact probability_mono hsubset
    _ ≤ ∑ C ∈ W, sliceProbability s j (fun B ↦ C ⊆ B) := by
      simp only [sliceProbability_eq_probability]
      exact probability_exists_le_sum _ _ _
    _ = (m.choose r : ℝ) * ((j.choose r : ℝ) / (n.choose r : ℝ)) := by
      rw [sum_congr rfl hfixed, sum_const, nsmul_eq_mul, show W.card = m.choose r from
        card_powersetCard _ _, hratio]
    _ = (j.choose r : ℝ) * ((m.choose r : ℝ) / (n.choose r : ℝ)) := by ring
    _ ≤ (j.choose r : ℝ) * ((m : ℝ) / n) ^ r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_iff₀ hdenr).mpr
        (by simpa only [mul_comm] using choose_le_choose_mul_ratio_pow hmn (hr.trans hj))

/-- A real threshold rounds up to the corresponding integer binomial count. -/
theorem sliceProbability_hits_real_binomial (s D : Finset α) {j : ℕ} {q t : ℝ}
    (hj : j ≤ s.card) (hq : ((s ∩ D).card : ℝ) / s.card ≤ q) :
    sliceProbability s j (fun B ↦ t ≤ (B ∩ D).card) ≤
      (j.choose ⌈t⌉₊ : ℝ) * q ^ ⌈t⌉₊ := by
  let r := ⌈t⌉₊
  have hnonneg : 0 ≤ q := (by positivity : 0 ≤ ((s ∩ D).card : ℝ) / s.card).trans hq
  have hE : (fun B : Finset α ↦ t ≤ (B ∩ D).card) =
      (fun B : Finset α ↦ r ≤ (B ∩ D).card) :=
    funext fun _ ↦ propext Nat.ceil_le.symm
  rw [hE]
  by_cases hr : r ≤ j
  · exact (sliceProbability_hits_binomial s D hj hr).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _) (by positivity))
  · have hfalse : (s.powersetCard j).filter (fun B ↦ r ≤ (B ∩ D).card) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hB, hhit⟩ := mem_filter.mp hB
      have hcard := (mem_powersetCard.mp hB).2
      have hle : (B ∩ D).card ≤ B.card := card_le_card inter_subset_left
      omega
    unfold sliceProbability
    rw [filter_congr_decidable _ (fun B ↦ r ≤ (B ∩ D).card) _, hfalse]
    simp only [card_empty, Nat.cast_zero, zero_div]
    positivity

/-- Replace the binomial coefficient and the ceiling by the manuscript's simpler bound. -/
theorem sliceProbability_hits_section5 (s D : Finset α) {j k : ℕ} {q : ℝ}
    (hj : j ≤ s.card) (hjk : j ≤ k) (hq : ((s ∩ D).card : ℝ) / s.card ≤ q)
    (hq₁ : q ≤ 1) :
    sliceProbability s j (fun B ↦ (0.24 : ℝ) * k ≤ (B ∩ D).card) ≤
      (2 : ℝ) ^ k * q ^ ((0.24 : ℝ) * k) := by
  let r := ⌈(0.24 : ℝ) * k⌉₊
  have hnonneg : 0 ≤ q := (by positivity : 0 ≤ ((s ∩ D).card : ℝ) / s.card).trans hq
  have hbin : (j.choose r : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.choose_le_two_pow j r).trans (Nat.pow_le_pow_right (by decide) hjk)
  have hceil : (0.24 : ℝ) * k ≤ (r : ℝ) := Nat.le_ceil _
  have hpow : q ^ r ≤ q ^ ((0.24 : ℝ) * k) := by
    rw [← Real.rpow_natCast q r]
    exact Real.rpow_le_rpow_of_exponent_ge' hnonneg hq₁ (by positivity) hceil
  exact (sliceProbability_hits_real_binomial s D hj hq).trans
    (mul_le_mul hbin hpow (by positivity) (by positivity))

private theorem complement_density_le {s A₁ D : Finset α} {k₁ : ℕ} {η : ℝ}
    (hA₁ : A₁ ∈ s.powersetCard k₁) (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card)
    (hD : (D.card : ℝ) ≤ (71000 * η) ^ 2 * s.card) :
    (((s \ A₁) ∩ D).card : ℝ) / (s \ A₁).card ≤ 2 * (71000 * η) ^ 2 := by
  have hcomp : (s \ A₁).card = s.card - k₁ := by
    rw [card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
  have hpos : (0 : ℝ) < (s \ A₁).card := by
    exact_mod_cast (show 0 < (s \ A₁).card by omega)
  have hpop : (s.card : ℝ) ≤ 2 * (s \ A₁).card := by
    exact_mod_cast (show s.card ≤ 2 * (s \ A₁).card by omega)
  apply (div_le_iff₀ hpos).mpr
  have hle : (((s \ A₁) ∩ D).card : ℝ) ≤ D.card := by
    exact_mod_cast card_le_card inter_subset_right
  calc
    _ ≤ (71000 * η) ^ 2 * s.card := hle.trans hD
    _ ≤ (71000 * η) ^ 2 * (2 * (s \ A₁).card) :=
      mul_le_mul_of_nonneg_left hpop (sq_nonneg _)
    _ = _ := by ring

/-- The binomial bound conditional only on A₁. The bad set is fixed on this fiber. -/
theorem conditional_witness_hits_binomial {s A₁ : Finset α} {k₁ k₂ : ℕ} {η : ℝ}
    (hA₁ : A₁ ∈ s.powersetCard k₁) (hk : k₁ + k₂ ≤ s.card)
    (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card) (D : Finset α → Finset α)
    (hD : ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * s.card) :
    let r := ⌈(0.24 : ℝ) * (k₁ + k₂ : ℕ)⌉₊
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁)
        (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card) ≤
      (k₂.choose r : ℝ) * (2 * (71000 * η) ^ 2) ^ r := by
  dsimp only
  have hj : k₂ ≤ (s \ A₁).card := by
    rw [card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
    omega
  rw [conditional_first hA₁ (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card)]
  exact sliceProbability_hits_real_binomial (s \ A₁) (D A₁) hj
    (complement_density_le hA₁ hhalf hs hD)

/-- The §5 bound conditional only on A₁. -/
theorem conditional_witness_hits {s A₁ : Finset α} {k₁ k₂ : ℕ} {η : ℝ}
    (hA₁ : A₁ ∈ s.powersetCard k₁) (hk : k₁ + k₂ ≤ s.card)
    (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card) (D : Finset α → Finset α)
    (hD : ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * s.card)
    (hη : 2 * (71000 * η) ^ 2 ≤ 1) :
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁)
        (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card) ≤
      (2 : ℝ) ^ (k₁ + k₂) * (2 * (71000 * η) ^ 2) ^ ((0.24 : ℝ) * (k₁ + k₂ : ℕ)) := by
  have hj : k₂ ≤ (s \ A₁).card := by
    rw [card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
    omega
  rw [conditional_first hA₁ (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card)]
  exact sliceProbability_hits_section5 (s \ A₁) (D A₁) (j := k₂) (k := k₁ + k₂)
    hj (by omega) (complement_density_le hA₁ hhalf hs hD) hη

/-- The same bound after averaging over A₁, for one fixed witness description. -/
theorem witness_hits_probability {s : Finset α} {k₁ k₂ : ℕ} {η : ℝ}
    (hk : k₁ + k₂ ≤ s.card) (hhalf : 2 * k₁ ≤ s.card) (hs : 0 < s.card)
    (D : Finset α → Finset α)
    (hD : ∀ A₁ ∈ s.powersetCard k₁, ((D A₁).card : ℝ) ≤ (71000 * η) ^ 2 * s.card)
    (hη : 2 * (71000 * η) ^ 2 ≤ 1) :
    probability (orderedPairs s k₁ k₂)
        (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card) ≤
      (2 : ℝ) ^ (k₁ + k₂) * (2 * (71000 * η) ^ 2) ^ ((0.24 : ℝ) * (k₁ + k₂ : ℕ)) := by
  rw [probability_eq_mean_first]
  apply mean_le_of_forall_le (by positivity)
  intro A₁ hA₁
  rw [← conditional_first hA₁ (fun q ↦ (0.24 : ℝ) * (k₁ + k₂ : ℕ) ≤ (q.2 ∩ D q.1).card)]
  exact conditional_witness_hits hA₁ hk hhalf hs D (hD A₁ hA₁) hη

/-- The base of the §5 exponential bound is below one at every active level. -/
theorem section5_eta_small {x : ℝ} (hx : 0 ≤ x) :
    2 * (71000 * Real.exp (-1000 - 0.22 * x)) ^ 2 ≤ 1 := by
  have h₂ : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp 1]
  have hpow : (2 : ℝ) ^ 17 ≤ Real.exp 17 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h₂ 17
    norm_num only [Real.exp_one_pow, Nat.cast_ofNat] at h ⊢
    exact h
  have hη : Real.exp (-1000 - 0.22 * x) ≤ 1 / (2 : ℝ) ^ 17 := calc
    _ ≤ Real.exp (-17) := Real.exp_le_exp.mpr (by linarith only [hx])
    _ = 1 / Real.exp 17 := by rw [Real.exp_neg, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hpow
  calc
    _ ≤ 2 * (71000 * (1 / (2 : ℝ) ^ 17)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hη (by norm_num)) 2)
        (by norm_num)
    _ ≤ 1 := by norm_num

end

end Green39.Split

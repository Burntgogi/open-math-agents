import Matching
import OMAReductions.R_Erdos490_erdos_490_variants_limit_R1

/-! Recovering the site transfer statement from the normalized semigroup count matrix. -/
namespace Erdos490Transfer
open Finset Filter
noncomputable section
open Classical

def value (n a b : ℕ) : ℝ := (a:ℝ)*b*Real.log n/(n:ℝ)^2

/-- Density at the real cutoff n/u, including 1 whenever u ≤ n. -/
def density (C : Finset ℕ) (n u : ℕ) : ℝ :=
  ((semigroup C (n/u)).card : ℝ)*u/n

def entry {Y n} (c : Colors Y n) (u s : ℕ) :=
  value n (semigroup c.red (n/u)).card (semigroup c.blue (n/s)).card

theorem entry_density {Y n} (c : Colors Y n) {u s : ℕ} (hu : 0 < u) (hs : 0 < s) :
    entry c u s = Real.log n * density c.red n u * density c.blue n s / (u*s) := by
  unfold entry value density
  have hu' : (u:ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  have hs' : (s:ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp


def model {Y n} (c : Colors Y n) (U : Finset ℕ) (G H : Finset ℚ) (K : ℕ) :=
  value n (size U G c.red K n) (size U H c.blue K n)

theorem model_sum {Y n} (c : Colors Y n) (U G H K) :
    model c U G H K = ∑ i ∈ range K, ∑ j ∈ range K,
      ((weight U G i : ℝ)*weight U H j) * entry c (i+1) (j+1) := by
  unfold model size entry value
  push_cast
  simp only [sum_mul,mul_sum,sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

/-- The loss is per pair of cofactor cutoffs. The same new coloring must serve
the whole matrix. The bound is independent of the graph. -/
def MatrixTransfer : Prop :=
  ∀ Y K, ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ c : Colors Y n,
    ∀ᶠ m : ℕ in atTop, ∃ d : Colors Y m, ∀ i < K, ∀ j < K,
      entry c (i+1) (j+1) ≤ entry d (i+1) (j+1) + δ

theorem model_loss {Y n m K} (c : Colors Y n) (d : Colors Y m) (U G H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ i < K, ∀ j < K, entry c (i+1) (j+1) ≤ entry d (i+1) (j+1)+δ) :
    model c U G H K ≤ model d U G H K + (K:ℝ)^2 * δ := by
  rw [model_sum,model_sum]
  calc
    _ ≤ ∑ i ∈ range K, ∑ j ∈ range K,
        (((weight U G i : ℝ)*weight U H j)*entry d (i+1) (j+1)+δ) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hw : ((weight U G i : ℝ)*weight U H j) ≤ 1 := by
        exact_mod_cast (Nat.mul_le_mul (weight_le_one U G i) (weight_le_one U H j))
      have := mul_le_mul_of_nonneg_left (h i (mem_range.mp hi) j (mem_range.mp hj))
        (show 0 ≤ (weight U G i : ℝ)*weight U H j by positivity)
      linarith [mul_le_mul_of_nonneg_right hw hδ]
    _ = _ := by simp [sum_add_distrib]; ring

lemma value_mono {a b x y : ℕ} (n : ℕ) (h : a ≤ x) (h' : b ≤ y) :
    value n a b ≤ value n x y := by
  unfold value
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (by exact_mod_cast Nat.mul_le_mul h h') (Real.log_natCast_nonneg n)) (sq_nonneg _)

theorem site_H2_of_matrix (transfer : MatrixTransfer) :
    OMA.R_Erdos490_erdos_490_variants_limit_R1.H2 := by
  intro ε hε
  apply Eventually.of_forall
  intro Y K
  let δ : ℝ := ε/((K:ℝ)^2+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [transfer Y K δ hδ] with n hn
  intro A B ha hs
  obtain ⟨c,ca,cb⟩ := colors_cover (show Adm n A B from ha) (show Sep Y K A B from hs)
  obtain ⟨G,_,hA,hB⟩ := dominate ha c ca cb
  let U := vertices Y K
  let H := ratios U \ G
  filter_upwards [hn c] with m hm
  obtain ⟨d,hd⟩ := hm
  obtain ⟨hadm,_,_,hL,hR⟩ := attainable (K:=K) d G
  refine ⟨_,_,hadm,?_⟩
  change value n A.card B.card ≤ value m _ _ + ε
  rw [hL,hR]
  have hcost : (K:ℝ)^2*δ ≤ ε := by
    have hpos : 0 < (K:ℝ)^2+1 := by positivity
    have heq : δ*((K:ℝ)^2+1)=ε := div_mul_cancel₀ _ hpos.ne'
    nlinarith
  exact (value_mono n hA hB).trans ((model_loss c d U G H hδ.le hd).trans (add_le_add_right hcost _))

end
end Erdos490Transfer

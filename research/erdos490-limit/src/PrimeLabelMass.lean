import LabelEmbedding
import H2
import Cells
import Dilation

/-! Finite labelled rectangles at dilated prime cutoffs. Their unnormalized
harmonic masses converge to the reciprocal of the old squarefree integer. -/
namespace Erdos490Transfer
open Filter Finset Real Erdos490PrimeCells
open scoped Topology
noncomputable section
open Classical

def newCell (b t : ℝ) (p : ℕ) :=
  (Ioc ⌊exp (t*boundary b p)⌋₊ ⌊exp (t*boundary b (p+1))⌋₊).filter Nat.Prime

lemma boundary_mono (b : ℝ) : Monotone (boundary b) := by
  apply monotone_nat_of_le_succ
  intro i
  unfold boundary
  rw [before_succ]
  apply exp_le_exp.mpr
  split_ifs <;> linarith [show (0:ℝ) ≤ (i:ℝ)⁻¹ by positivity]

lemma newCell_disjoint {b t : ℝ} (ht : 0 ≤ t) {p q : ℕ} (hne : p ≠ q) :
    Disjoint (newCell b t p) (newCell b t q) := by
  have ord {u v : ℕ} (hl : u < v) : Disjoint (newCell b t u) (newCell b t v) := by
    apply disjoint_left.mpr
    intro h hu hv
    have hend := (mem_Ioc.mp (mem_filter.mp hu).1).2
    have hstart := (mem_Ioc.mp (mem_filter.mp hv).1).1
    exact hstart.not_ge (hend.trans (Nat.floor_mono (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (boundary_mono b hl) ht))))
  rcases lt_or_gt_of_ne hne with h|h
  · exact ord h
  · exact (ord h).symm

def newProducts (b t : ℝ) (S : Finset ℕ) :=
  (Fintype.piFinset (fun p : S => newCell b t p)).image high

/-- This limit counts distinct new integers, so no ordering or factorial
factor remains. The old squarefree product may be 1. -/
theorem newProducts_mass (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) (b : ℝ) :
    Tendsto (fun t : ℝ => ∑ z ∈ newProducts b t S, (z:ℝ)⁻¹)
      atTop (𝓝 (((∏ p ∈ S, p:ℕ):ℝ)⁻¹)) := by
  have one (p : S) : Tendsto (fun t : ℝ => ∑ q ∈ newCell b t p, (q:ℝ)⁻¹)
      atTop (𝓝 ((p.val:ℝ)⁻¹)) := by
    have hp := hS _ p.property
    have h := dilated_window_mass (a:=boundary b p) (b:=boundary b (p.val+1))
      (exp_pos _) (boundary_mono b (Nat.le_succ _))
    have hpos : 0 < boundary b p := exp_pos _
    have ratio : log (boundary b (p.val+1) / boundary b p) = (p.val:ℝ)⁻¹ := by
      rw [boundary_succ b hp,mul_div_cancel_left₀ _ hpos.ne',log_exp]
    rw [ratio] at h
    exact h
  have h := tendsto_finsetProd (univ : Finset S) (fun p _ => one p)
  have goalEq : (∏ p : S, (p.val:ℝ)⁻¹) = (((∏ p ∈ S, p:ℕ):ℝ)⁻¹) := by
    rw [prod_inv_distrib,Nat.cast_prod]
    congr 1
    exact prod_attach S (fun p => (p:ℝ))
  rw [← goalEq]
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [newProducts,sum_image]
  · exact (label_mass (fun p : S => newCell b t p)).symm
  · intro f hf g hg he
    apply high_injective (cell:=fun p : S => newCell b t p)
      (fun _ _ hq => (mem_filter.mp hq).2)
      (fun i j hne => newCell_disjoint ht (fun he => hne (Subtype.ext he))) _ _ he
    · exact fun i => Or.inr (Fintype.mem_piFinset.mp hf i)
    · exact fun i => Or.inr (Fintype.mem_piFinset.mp hg i)

/-- The stable-side base count at the residual cutoff supplies a lower bound
at each cofactor u of the actual new coloring. -/
theorem labelled_density_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cell : ι → Finset ℕ} {C base : Finset ℕ} (prime : ∀ i p, p ∈ cell i → Nat.Prime p)
    (sub : ∀ i, cell i ⊆ C) (apart : ∀ i j, i ≠ j → Disjoint (cell i) (cell j))
    (sep : Disjoint C base) (F : Finset (ι → ℕ))
    (valid : ∀ f ∈ F, ValidLabels cell f) (n u : ℕ) :
    (∑ f ∈ F, density base n (u*high f)/(high f:ℝ)) ≤ density (C ∪ base) n u := by
  obtain ⟨hs,he⟩ := labelled_embedding prime sub apart sep F valid (n/u)
  have bound := card_le_card hs
  rw [he] at bound
  calc
    _ = (∑ f ∈ F, ((semigroup base (n/u/high f)).card:ℝ))*u/n := by
      rw [sum_mul,sum_div]
      apply sum_congr rfl
      intro f hf
      have h0 : (high f:ℝ) ≠ 0 := by exact_mod_cast (high_active prime sub (valid f hf)).1
      unfold density
      rw [Nat.div_div_eq_div_mul,Nat.cast_mul]
      by_cases hn : n = 0
      · simp [hn]
      field_simp
    _ ≤ _ := by unfold density; gcongr; exact_mod_cast bound

#print axioms newProducts_mass
end
end Erdos490Transfer

import CappedFit

/-! # Target-independent decoding and finite termination of a fitting run -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def heavy (cap : ℝ) (m : ι → ℝ) : Finset ι := univ.filter (fun i => cap < m i)
abbrev Instruction (σ : Type*) := Option (Bool × σ)

def testAt (g : σ → ι → ℝ) (cap : ℝ) (m : ι → ℝ) : Instruction σ → ι → ℝ
  | none, i => if i ∈ heavy cap m then -1 else 0
  | some (true,j), i => g j i
  | some (false,j), i => -g j i

def decode (g : σ → ι → ℝ) (η cap : ℝ) : List (Instruction σ) → ι → ℝ
  | [] => fun _ => (Fintype.card ι : ℝ)⁻¹
  | c :: cs =>
    let m := decode g η cap cs
    tilt m (testAt g cap m c) (η/4)

def stop (ν : ι → ℝ) (g : σ → ι → ℝ) (η cap : ℝ) (m : ι → ℝ) : Prop :=
  let J := heavy cap m
  η/2 ≤ ∑ i, dropMass J ν i ∨
    ((∑ i, clipped J m i = 1) ∧ (∀ i, 0 ≤ clipped J m i ∧ clipped J m i ≤ 2*cap) ∧
    ∀ j, |testMean ν (g j) - testMean (clipped J m) (g j)| ≤ 3*η)

theorem testAt_bound {g : σ → ι → ℝ} (hg : ∀ j i, |g j i| ≤ 1)
    (cap : ℝ) (m : ι → ℝ) (c : Instruction σ) (i : ι) : |testAt g cap m c i| ≤ 1 := by
  cases c with
  | none => by_cases h : i ∈ heavy cap m <;> simp [testAt,h]
  | some c => rcases c with ⟨b,j⟩; cases b <;> simpa [testAt] using hg j i

private theorem heavy_mean (q m : ι → ℝ) (g : σ → ι → ℝ) (cap : ℝ) :
    testMean q (testAt g cap m none) = -(∑ i, dropMass (heavy cap m) q i) := by
  unfold testMean
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i _
  by_cases h : i ∈ heavy cap m <;> simp [testAt,dropMass,h]

theorem stop_or_update {m ν : ι → ℝ} {g : σ → ι → ℝ} {η cap : ℝ}
    (hg : ∀ j i, |g j i| ≤ 1) (hm : ∀ i, 0 < m i) (hs : ∑ i, m i = 1)
    (hc : 0 ≤ cap) (he : 0 ≤ η) (he' : η ≤ 1/2) :
    stop ν g η cap m ∨ ∃ c : Instruction σ,
      η/2 ≤ testMean ν (testAt g cap m c) - testMean m (testAt g cap m c) := by
  classical
  by_cases ht : η/2 ≤ ∑ i, dropMass (heavy cap m) ν i
  · exact Or.inl (Or.inl ht)
  by_cases hw : η < ∑ i, dropMass (heavy cap m) m i
  · refine Or.inr ⟨none,?_⟩
    rw [heavy_mean,heavy_mean]
    linarith
  have hsmall := le_of_not_gt hw
  by_cases htests : ∀ j, |testMean ν (g j)-testMean m (g j)| ≤ η/2
  · have h := clipped_law (fun i => (hm i).le) hs hc (heavy cap m)
        (fun x hx => le_of_not_gt (fun h => hx (mem_filter.mpr ⟨mem_univ _,h⟩)))
        (hsmall.trans he')
    refine Or.inl (Or.inr ⟨h.1,h.2,fun j => ?_⟩)
    have hh := clipped_test (heavy cap m) (fun i => (hm i).le) hs (hg j) (by linarith)
    have hb := abs_sub_le (testMean ν (g j)) (testMean m (g j)) (testMean (clipped (heavy cap m) m) (g j))
    rw [abs_sub_comm (testMean m (g j))] at hb
    linarith [htests j]
  · push Not at htests
    obtain ⟨j,hj⟩ := htests
    rcases lt_abs.mp hj with h | h
    · refine Or.inr ⟨some (true,j),?_⟩
      change η/2 ≤ testMean ν (g j) - testMean m (g j)
      exact h.le
    · refine Or.inr ⟨some (false,j),?_⟩
      simp only [testAt,testMean,mul_neg,sum_neg_distrib] at *
      linarith

variable [Nonempty ι]

theorem decode_law (g : σ → ι → ℝ) (η cap : ℝ) (cs : List (Instruction σ)) :
    (∀ i, 0 < decode g η cap cs i) ∧ ∑ i, decode g η cap cs i = 1 := by
  induction cs with
  | nil => exact trajectory_law (fun _ _ => 0) η 0
  | cons c cs ih => exact ⟨tilt_pos ih.1 _ _,sum_tilt ih.1 _ _⟩

/-- The list of possible transcripts is independent of ν. Reading the successful word
from the right reconstructs the heavy set or capped law that witnesses termination. -/
theorem finite_search {ν : ι → ℝ} (hν : ∀ i, 0 ≤ ν i) (hνs : ∑ i, ν i = 1)
    {g : σ → ι → ℝ} (hg : ∀ j i, |g j i| ≤ 1) {η cap : ℝ} (he : 0 < η)
    (he' : η ≤ 1/2) (hc : 0 ≤ cap) (B : ℕ) (hB : 16*log (Fintype.card ι) < B*η^2) :
    ∃ cs : List (Instruction σ), cs.length ≤ B ∧ stop ν g η cap (decode g η cap cs) := by
  classical
  by_contra! hx
  have extend (j : ℕ) (hj : j ≤ B) : ∃ cs : List (Instruction σ), cs.length = j ∧
      potential ν (decode g η cap cs) + j*(η^2/16) ≤ log (Fintype.card ι) := by
    induction j with
    | zero => exact ⟨[],rfl,by simp [decode,uniform_potential hνs]⟩
    | succ j ih =>
      have hj' : j ≤ B := by omega
      obtain ⟨cs,hlen,hold⟩ := ih hj'
      obtain ⟨hm,hs⟩ := decode_law g η cap cs
      obtain ⟨c,hgap⟩ := (stop_or_update hg hm hs hc he.le he').resolve_left
        (hx cs (hlen ▸ hj'))
      have hd := update_decrement hm hs hνs (testAt_bound hg cap _ c) he.le (by linarith) hgap
      refine ⟨c::cs,by simp [hlen],?_⟩
      simp only [decode,Nat.cast_succ]
      linarith
  obtain ⟨cs,_,h⟩ := extend B le_rfl
  obtain ⟨hm,hs⟩ := decode_law g η cap cs
  linarith [potential_nonneg hν hm hs]

#print axioms finite_search
end
end Green39.Fitting

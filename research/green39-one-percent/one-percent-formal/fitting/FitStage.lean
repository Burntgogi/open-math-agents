import FitSearch

/-! # Peeling a finite target using short, target-independent instructions -/

namespace Green39.Fitting
open Finset Real
noncomputable section
variable {ι σ : Type*} [Fintype ι] [DecidableEq ι]

def uniformOn (F : Finset ι) (i : ι) : ℝ := if i ∈ F then (F.card : ℝ)⁻¹ else 0

omit [Fintype ι] in
theorem uniformOn_nonneg (F : Finset ι) (i : ι) : 0 ≤ uniformOn F i := by
  by_cases hi : i ∈ F <;> simp [uniformOn,hi]

theorem uniformOn_sum {F : Finset ι} (hF : F.Nonempty) : ∑ i, uniformOn F i = 1 := by
  classical
  simp [uniformOn,Finset.sum_ite_mem, (show (F.card : ℝ) ≠ 0 by exact_mod_cast hF.card_pos.ne')]

theorem uniformOn_drop (F J : Finset ι) :
    ∑ i, dropMass J (uniformOn F) i = ((J ∩ F).card : ℝ) / (F.card : ℝ) := by
  classical
  have h (i : ι) : dropMass J (uniformOn F) i =
      if i ∈ J ∩ F then (F.card : ℝ)⁻¹ else 0 := by
    by_cases hi : i ∈ J <;> by_cases hf : i ∈ F <;> simp [dropMass,uniformOn,hi,hf]
  simp only [h,Finset.sum_ite_mem,Finset.univ_inter,sum_const,nsmul_eq_mul,div_eq_mul_inv]

def Fitted (F : Finset ι) (g : σ → ι → ℝ) (η cap : ℝ) (μ : ι → ℝ) : Prop :=
  (∑ i, μ i = 1) ∧ (∀ i, 0 ≤ μ i ∧ μ i ≤ 2*cap) ∧
  ∀ j, |testMean (uniformOn F) (g j) - testMean μ (g j)| ≤ 3*η

def recordedUnion (g : σ → ι → ℝ) (η cap : ℝ) : List (List (Instruction σ)) → Finset ι
  | [] => ∅
  | w :: ws => heavy cap (decode g η cap w) ∪ recordedUnion g η cap ws

variable [Nonempty ι]

/-- One round of the fitting procedure. The pool of words and all laws and unions
decoded from them are determined by the tests, cap, accuracy and budgets. -/
theorem stage_alternative {g : σ → ι → ℝ} (hg : ∀ j i, |g j i| ≤ 1)
    {η cap θ : ℝ} (he : 0 < η) (he' : η ≤ 1/2) (hc : 0 ≤ cap) (ht : 0 < θ)
    (B : ℕ) (hB : 16*log (Fintype.card ι) < B*η^2)
    (n : ℕ) (V : Finset ι) (hN : (1-η/2)^n * V.card < θ) :
    (∃ F ⊆ V, θ ≤ F.card ∧ ∃ w : List (Instruction σ), w.length ≤ B ∧
      Fitted F g η cap (clipped (heavy cap (decode g η cap w)) (decode g η cap w))) ∨
    (∃ ws : List (List (Instruction σ)), ws.length ≤ n ∧ (∀ w ∈ ws, w.length ≤ B) ∧
      ((V \ recordedUnion g η cap ws).card : ℝ) < θ) := by
  classical
  induction n generalizing V with
  | zero => exact Or.inr ⟨[],by simp,by simp,by simpa [recordedUnion] using hN⟩
  | succ n ih =>
    by_cases hv : (V.card : ℝ) < θ
    · exact Or.inr ⟨[],by simp,by simp,by simpa [recordedUnion] using hv⟩
    have hp : V.Nonempty := by
      apply card_pos.mp
      exact_mod_cast ht.trans_le (le_of_not_gt hv)
    obtain ⟨w,hw,hstop⟩ := finite_search (uniformOn_nonneg V) (uniformOn_sum hp) hg he he' hc B hB
    let J := heavy cap (decode g η cap w)
    rcases hstop with hpeel | hfit
    · change η / 2 ≤ ∑ i, dropMass J (uniformOn V) i at hpeel
      rw [uniformOn_drop] at hpeel
      have hsize := (le_div_iff₀ (show 0 < (V.card : ℝ) by exact_mod_cast hp.card_pos)).mp hpeel
      have hcard : (V \ J).card + (J ∩ V).card = V.card := by
        rw [inter_comm J V]
        exact card_sdiff_add_card_inter V J
      have hleft : ((V \ J).card : ℝ) ≤ (1-η/2)*V.card := by
        have hh : ((V \ J).card : ℝ) + (J ∩ V).card = V.card := by exact_mod_cast hcard
        linarith
      have hnext : (1-η/2)^n * (V \ J).card < θ := by
        apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hleft
          (pow_nonneg (by linarith : 0 ≤ 1-η/2) _))
        simpa [pow_succ,mul_assoc] using hN
      rcases ih (V \ J) hnext with ⟨F,hF,hF',w',hw',hf'⟩ | ⟨ws,hws,hs,hsmall⟩
      · exact Or.inl ⟨F,hF.trans sdiff_subset,hF',w',hw',hf'⟩
      · refine Or.inr ⟨w::ws,by simpa using hws,?_,?_⟩
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact hw
          · exact hs u hu
        · have heq : V \ recordedUnion g η cap (w::ws) = (V \ J) \ recordedUnion g η cap ws := by
            ext i
            simp [recordedUnion,J]
            tauto
          simpa only [heq] using hsmall
    · exact Or.inl ⟨V,Subset.rfl,le_of_not_gt hv,w,hw,hfit⟩

#print axioms stage_alternative
end
end Green39.Fitting

import SplitSlice

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem sm_add (s : Finset α) (k : ℕ) (f g : Finset α → ℝ) :
    sliceMean s k (fun A ↦ f A + g A) = sliceMean s k f + sliceMean s k g := by
  unfold sliceMean mean
  rw [Finset.sum_add_distrib, add_div]

omit [DecidableEq α] in
theorem prob_or (s : Finset α) (k : ℕ) (E F : Finset α → Prop) :
    sliceProbability s k (fun A ↦ E A ∨ F A) ≤ sliceProbability s k E + sliceProbability s k F := by
  simp_rw [← sm_event]
  rw [← sm_add]
  apply sm_mono
  intro A _
  by_cases he : E A <;> by_cases hf : F A <;> simp [he,hf]

omit [DecidableEq α] in
theorem prob_one {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (E : Finset α → Prop) :
    sliceProbability s k E ≤ 1 := by
  rw [← sm_event]
  calc
    _ ≤ sliceMean s k (fun _ ↦ 1) := by
      apply sm_mono
      intro A _
      split <;> norm_num
    _ = _ := sm_const hk 1

/-- Joint probability for a uniformly sampled disjoint pair, in exposure order. -/
def splitProb (s : Finset α) (a b : ℕ) (E : Finset α → Finset α → Prop) :=
  splitMean s a b (fun A B ↦ if E A B then 1 else 0)

theorem split_union (s : Finset α) (a b : ℕ) (I : Finset ι) (E : ι → Finset α → Finset α → Prop) :
    splitProb s a b (fun A B ↦ ∃ i ∈ I, E i A B) ≤ ∑ i ∈ I, splitProb s a b (E i) := by
  unfold splitProb splitMean
  rw [← sm_sum]
  apply sm_mono
  intro A _
  simpa only [sm_event] using prob_union (s \ A) b I (fun i ↦ E i A)

theorem split_bad_le {s : Finset α} {a b : ℕ} (hk : a+b ≤ s.card)
    (EA EB : Finset α → Prop) (E : Finset α → Finset α → Prop) {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ A ∈ s.powersetCard a, ¬EA A → sliceProbability (s \ A) b (E A) ≤ q) :
    splitProb s a b (fun A B ↦ EB B ∨ E A B) ≤
      sliceProbability s b EB + sliceProbability s a EA + q := by
  let u (A : Finset α) := sliceProbability (s \ A) b EB
  let v (A : Finset α) := sliceProbability (s \ A) b (E A)
  have hu : sliceMean s a u = sliceProbability s b EB := by
    simpa only [splitMean, sm_event, u] using split_snd hk (fun B ↦ if EB B then (1:ℝ) else 0)
  have hv : sliceMean s a v ≤ sliceProbability s a EA + q := by
    calc
      _ ≤ sliceMean s a (fun A ↦ (if EA A then 1 else 0) + q) := by
        apply sm_mono
        intro A hA
        by_cases he : EA A
        · rw [if_pos he]
          have hc : b ≤ (s \ A).card := by
            rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hA).1,
              (Finset.mem_powersetCard.mp hA).2]; omega
          exact (prob_one hc _).trans (by linarith)
        · simpa [he] using h A hA he
      _ = _ := by rw [sm_add, sm_event, sm_const (by omega : a ≤ s.card)]
  calc
    _ ≤ sliceMean s a (fun A ↦ u A + v A) := by
      apply sm_mono
      intro A _
      rw [sm_event]
      exact prob_or _ _ _ _
    _ ≤ _ := by rw [sm_add, hu]; linarith

end
end Green39.Smooth

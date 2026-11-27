import SliceMoments

open scoped BigOperators Classical
open Green39.Concentration

namespace Green39.Smooth
noncomputable section
variable {α ι : Type*} [DecidableEq α]

/-- Expose a uniform first half, then sample the second from its complement. -/
def splitMean (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :=
  sliceMean s a (fun A ↦ sliceMean (s \ A) b (f A))

private theorem disj_slice (s A : Finset α) (b : ℕ) :
    (s \ A).powersetCard b = (s.powersetCard b).filter (fun B ↦ Disjoint B A) := by
  ext B
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_sdiff]
  tauto

private theorem pair_sum (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :
    (∑ A ∈ s.powersetCard a, ∑ B ∈ (s \ A).powersetCard b, f A B) =
      ∑ B ∈ s.powersetCard b, ∑ A ∈ (s \ B).powersetCard a, f A B := by
  simp_rw [disj_slice, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp_rw [disjoint_comm]

private theorem card_rest {s A : Finset α} {a : ℕ} (hA : A ∈ s.powersetCard a) :
    (s \ A).card = s.card - a := by
  rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp hA).1,
    (Finset.mem_powersetCard.mp hA).2]

private theorem split_formula (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :
    splitMean s a b f =
    (∑ A ∈ s.powersetCard a, ∑ B ∈ (s \ A).powersetCard b, f A B) /
      ((s.card-a).choose b * (s.card.choose a : ℝ)) := by
  unfold splitMean sliceMean mean
  rw [← div_div, Finset.card_powersetCard]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [Finset.card_powersetCard, card_rest hA]

theorem split_swap (s : Finset α) (a b : ℕ) (f : Finset α → Finset α → ℝ) :
    splitMean s a b f = splitMean s b a (fun B A ↦ f A B) := by
  have count (i j : ℕ) :
      (∑ A ∈ s.powersetCard i, ∑ _B ∈ (s \ A).powersetCard j, (1:ℝ)) =
        (s.card-i).choose j * (s.card.choose i : ℝ) := by
    calc
      _ = ∑ _A ∈ s.powersetCard i, ((s.card-i).choose j : ℝ) := by
        apply Finset.sum_congr rfl
        intro A hA
        simp [card_rest hA]
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  rw [split_formula, split_formula, pair_sum s a b f]
  rw [← count a b, ← count b a, pair_sum s a b (fun _ _ ↦ 1)]

theorem split_fst {s : Finset α} {a b : ℕ} (hk : a+b ≤ s.card) (f : Finset α → ℝ) :
    splitMean s a b (fun A _ ↦ f A) = sliceMean s a f := by
  apply sm_congr
  intro A hA
  exact sm_const (by rw [card_rest hA]; omega) _

theorem split_snd {s : Finset α} {a b : ℕ} (hk : a+b ≤ s.card) (f : Finset α → ℝ) :
    splitMean s a b (fun _ B ↦ f B) = sliceMean s b f := by
  rw [split_swap, split_fst (by omega : b+a ≤ s.card)]

omit [DecidableEq α] in
theorem sm_event (s : Finset α) (k : ℕ) (E : Finset α → Prop) :
    sliceMean s k (fun A ↦ if E A then 1 else 0) = sliceProbability s k E := by
  unfold sliceProbability sliceMean mean
  rw [← Finset.sum_filter]
  simp

omit [DecidableEq α] in
theorem prob_mono {s : Finset α} {k : ℕ} {E F : Finset α → Prop}
    (h : ∀ A ∈ s.powersetCard k, E A → F A) :
    sliceProbability s k E ≤ sliceProbability s k F := by
  rw [← sm_event, ← sm_event]
  apply sm_mono
  intro A hA
  by_cases he : E A
  · simp [he,h A hA he]
  · simp [he]; split <;> norm_num

omit [DecidableEq α] in
theorem prob_union (s : Finset α) (k : ℕ) (d : Finset ι) (E : ι → Finset α → Prop) :
    sliceProbability s k (fun A ↦ ∃ i ∈ d, E i A) ≤ ∑ i ∈ d, sliceProbability s k (E i) := by
  simp_rw [← sm_event]
  rw [← sm_sum]
  apply sm_mono
  intro A _
  split
  · rename_i he
    obtain ⟨i,hi,hei⟩ := he
    simpa [hei] using (Finset.single_le_sum (f := fun j ↦ if E j A then (1:ℝ) else 0)
      (fun _ _ ↦ by split <;> norm_num) hi)
  · exact Finset.sum_nonneg (fun _ _ ↦ by split <;> norm_num)

theorem weight_tail {s : Finset α} {k : ℕ} (hk : k ≤ s.card) (w : α → ℝ)
    {b : ℝ} (hb : 0 < b) (hw : ∀ x ∈ s, 0 ≤ w x ∧ w x ≤ b) (t : ℝ) :
    sliceProbability s k (fun A ↦ t ≤ ∑ x ∈ A, w x) ≤
      Real.exp (((Real.exp 1-1) * (((k:ℝ)/s.card)*∑ x ∈ s, w x) - t)/b) := by
  let c := Real.exp (t/b)
  have hc : 0 < c := Real.exp_pos _
  have hm := sm_weight_exp hk w hb hw
  have h : c * sliceProbability s k (fun A ↦ t ≤ ∑ x ∈ A, w x) ≤
      sliceMean s k (fun A ↦ Real.exp ((∑ x ∈ A, w x)/b)) := by
    rw [← sm_event]
    calc
      _ = sliceMean s k (fun A ↦ c * (if t ≤ ∑ x ∈ A, w x then 1 else 0)) := by
        unfold sliceMean mean; rw [← Finset.mul_sum]; ring
      _ ≤ _ := by
        apply sm_mono
        intro A _
        split
        · rename_i h
          simpa [c] using Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h hb.le)
        · simpa only [mul_zero] using Real.exp_nonneg ((∑ x ∈ A, w x)/b)
  apply le_of_le_of_eq ((le_div_iff₀ hc).mpr ((mul_comm _ c).le.trans (h.trans hm)))
  rw [← Real.exp_sub]
  congr 1
  ring

end
end Green39.Smooth

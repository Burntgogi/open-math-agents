import SliceConcentration

/-!
# Uniform ordered splits of a finite population

The two descriptions condition on the first half or on the union. Their
fibers are uniform slices, with constant cardinality on each marginal.
-/

open Finset
open scoped BigOperators Classical

set_option autoImplicit false

namespace Green39.Split

open Concentration

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- The uniform sample space of ordered disjoint pairs with the indicated sizes. -/
def orderedPairs (s : Finset α) (k₁ k₂ : ℕ) : Finset (Finset α × Finset α) :=
  (s.powersetCard k₁ ×ˢ s.powersetCard k₂).filter fun q ↦ Disjoint q.1 q.2

@[simp] theorem mem_orderedPairs {s : Finset α} {k₁ k₂ : ℕ} {q : Finset α × Finset α} :
    q ∈ orderedPairs s k₁ k₂ ↔
      q.1 ⊆ s ∧ q.1.card = k₁ ∧ q.2 ⊆ s ∧ q.2.card = k₂ ∧ Disjoint q.1 q.2 := by
  simp only [orderedPairs, mem_filter, mem_product, mem_powersetCard]
  tauto

/-- Uniform probability on a finite sample space, with value zero for an empty space. -/
def probability {β : Type*} (S : Finset β) (E : β → Prop) : ℝ :=
  ((S.filter E).card : ℝ) / S.card

omit [DecidableEq α] in
theorem probability_mono {S : Finset α} {E F : α → Prop}
    (h : ∀ x ∈ S, E x → F x) :
    probability S E ≤ probability S F := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (show S.filter E ⊆ S.filter F from fun x hx ↦
    mem_filter.mpr ⟨(mem_filter.mp hx).1, h x (mem_filter.mp hx).1 (mem_filter.mp hx).2⟩)

omit [DecidableEq α] in
theorem sliceProbability_eq_probability (s : Finset α) (k : ℕ) (E : Finset α → Prop) :
    sliceProbability s k E = probability (s.powersetCard k) E := rfl

theorem orderedPairs_union_mem {s : Finset α} {k₁ k₂ : ℕ} {q : Finset α × Finset α}
    (hq : q ∈ orderedPairs s k₁ k₂) : q.1 ∪ q.2 ∈ s.powersetCard (k₁ + k₂) := by
  obtain ⟨h₁, hc₁, h₂, hc₂, hd⟩ := mem_orderedPairs.mp hq
  exact mem_powersetCard.mpr ⟨union_subset h₁ h₂, by rw [card_union_of_disjoint hd, hc₁, hc₂]⟩

/-- Counting a restricted first-half fiber leaves precisely the indicated second-half slice. -/
theorem card_firstFiber {s A₁ : Finset α} {k₁ k₂ : ℕ} (hA₁ : A₁ ∈ s.powersetCard k₁)
    (E : Finset α × Finset α → Prop) :
    (((orderedPairs s k₁ k₂).filter E).filter fun q ↦ q.1 = A₁).card =
      (((s \ A₁).powersetCard k₂).filter fun A₂ ↦ E (A₁, A₂)).card := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA₁
  refine card_bij' (fun q _ ↦ q.2) (fun A₂ _ ↦ (A₁, A₂)) ?_ ?_ ?_ ?_
  · rintro ⟨B, C⟩ hq
    simp only [mem_filter, mem_orderedPairs, mem_powersetCard] at hq ⊢
    obtain ⟨⟨⟨_, _, hC, hsize, hd⟩, he⟩, rfl⟩ := hq
    refine ⟨⟨?_, hsize⟩, he⟩
    exact fun x hx ↦ mem_sdiff.mpr ⟨hC hx, fun hx' ↦ disjoint_left.mp hd hx' hx⟩
  · intro C hC
    simp only [mem_filter, mem_powersetCard] at hC
    obtain ⟨⟨hC, hc⟩, he⟩ := hC
    simp only [mem_filter, mem_orderedPairs]
    exact ⟨⟨⟨hsub, hcard, hC.trans sdiff_subset, hc, disjoint_left.mpr
      (fun _ hx hx' ↦ (mem_sdiff.mp (hC hx')).2 hx)⟩, he⟩, trivial⟩
  · rintro ⟨B, C⟩ hq
    have heq : B = A₁ := (mem_filter.mp hq).2
    simp [heq]
  · intro C _
    rfl

/-- Counting a restricted union fiber leaves precisely the indicated first-half slice. -/
theorem card_unionFiber {s A : Finset α} {k₁ k₂ : ℕ} (hA : A ∈ s.powersetCard (k₁ + k₂))
    (E : Finset α × Finset α → Prop) :
    (((orderedPairs s k₁ k₂).filter E).filter fun q ↦ q.1 ∪ q.2 = A).card =
      ((A.powersetCard k₁).filter fun A₁ ↦ E (A₁, A \ A₁)).card := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hA
  refine card_bij' (fun q _ ↦ q.1) (fun B _ ↦ (B, A \ B)) ?_ ?_ ?_ ?_
  · rintro ⟨B, C⟩ hq
    simp only [mem_filter, mem_orderedPairs, mem_powersetCard] at hq ⊢
    obtain ⟨⟨⟨_, hc, _, _, hd⟩, he⟩, rfl⟩ := hq
    exact ⟨⟨subset_union_left, hc⟩, by rwa [union_sdiff_cancel_left hd]⟩
  · intro B hB
    obtain ⟨⟨hB, hc⟩, he⟩ := (show (B ⊆ A ∧ B.card = k₁) ∧ E (B, A \ B) from
      ⟨mem_powersetCard.mp (mem_filter.mp hB).1, (mem_filter.mp hB).2⟩)
    simp only [mem_filter, mem_orderedPairs]
    refine ⟨⟨⟨hB.trans hsub, hc, sdiff_subset.trans hsub, ?_,
        disjoint_left.mpr (fun _ hx hx' ↦ (mem_sdiff.mp hx').2 hx)⟩, he⟩, ?_⟩
    · rw [card_sdiff_of_subset hB, hcard, hc]
      omega
    · exact sup_sdiff_cancel_right hB
  · rintro ⟨B, C⟩ hq
    simp only [mem_filter, mem_orderedPairs] at hq
    obtain ⟨⟨⟨_, _, _, _, hd⟩, _⟩, hUnion⟩ := hq
    rw [← hUnion, union_sdiff_cancel_left hd]
  · intro B _
    rfl

/-- Conditional on a first half of positive mass, the second half is uniform in its complement. -/
theorem conditional_first {s A₁ : Finset α} {k₁ k₂ : ℕ} (hA₁ : A₁ ∈ s.powersetCard k₁)
    (E : Finset α × Finset α → Prop) :
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁) E =
      sliceProbability (s \ A₁) k₂ (fun A₂ ↦ E (A₁, A₂)) := by
  unfold probability sliceProbability
  rw [filter_comm, card_firstFiber hA₁, ← filter_true (orderedPairs s k₁ k₂),
    card_firstFiber hA₁, filter_true]

/-- Conditional on a union of positive mass, the first half is uniform in that union. -/
theorem conditional_union {s A : Finset α} {k₁ k₂ : ℕ} (hA : A ∈ s.powersetCard (k₁ + k₂))
    (E : Finset α × Finset α → Prop) :
    probability ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 ∪ q.2 = A) E =
      sliceProbability A k₁ (fun A₁ ↦ E (A₁, A \ A₁)) := by
  unfold probability sliceProbability
  rw [filter_comm, card_unionFiber hA, ← filter_true (orderedPairs s k₁ k₂),
    card_unionFiber hA, filter_true]

private theorem probability_eq_mean_fibers {β γ : Type*} [DecidableEq γ]
    {S : Finset β} {T : Finset γ} {f : β → γ} {d : ℕ}
    (hmaps : ∀ x ∈ S, f x ∈ T) (hsize : ∀ y ∈ T, (S.filter fun x ↦ f x = y).card = d)
    (E : β → Prop) :
    probability S E = mean T (fun y ↦ probability (S.filter fun x ↦ f x = y) E) := by
  have htotal : S.card = T.card * d := calc
    S.card = ∑ y ∈ T, (S.filter fun x ↦ f x = y).card := card_eq_sum_card_fiberwise hmaps
    _ = ∑ _y ∈ T, d := sum_congr rfl hsize
    _ = T.card * d := by simp
  have hevent : (S.filter E).card =
      ∑ y ∈ T, ((S.filter fun x ↦ f x = y).filter E).card := by
    rw [card_eq_sum_card_fiberwise (fun x hx ↦ hmaps x (mem_filter.mp hx).1)]
    exact sum_congr rfl (fun y _ ↦ by rw [filter_comm])
  unfold probability mean
  rw [htotal, hevent, Nat.cast_mul, Nat.cast_sum]
  have hs : (∑ y ∈ T, (((S.filter fun x ↦ f x = y).filter E).card : ℝ) /
        ((S.filter fun x ↦ f x = y).card : ℝ)) =
      ∑ y ∈ T, (((S.filter fun x ↦ f x = y).filter E).card : ℝ) / (d : ℝ) :=
    sum_congr rfl (fun y hy ↦ by rw [hsize y hy])
  rw [hs, ← sum_div, div_div, mul_comm (d : ℝ)]

/-- Expose the first half uniformly, then sample the second half from its complement. -/
theorem probability_eq_mean_first (s : Finset α) (k₁ k₂ : ℕ)
    (E : Finset α × Finset α → Prop) :
    probability (orderedPairs s k₁ k₂) E =
      mean (s.powersetCard k₁)
        (fun A₁ ↦ sliceProbability (s \ A₁) k₂ (fun A₂ ↦ E (A₁, A₂))) := by
  have hmaps : ∀ q ∈ orderedPairs s k₁ k₂, q.1 ∈ s.powersetCard k₁ := fun _ hq ↦
    mem_powersetCard.mpr ⟨(mem_orderedPairs.mp hq).1, (mem_orderedPairs.mp hq).2.1⟩
  have hsize : ∀ A₁ ∈ s.powersetCard k₁,
      ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 = A₁).card = (s.card - k₁).choose k₂ := by
    intro A₁ hA₁
    have h := card_firstFiber (k₂ := k₂) hA₁ (fun _ ↦ True)
    simp only [filter_true, card_powersetCard] at h
    rw [h, card_sdiff_of_subset (mem_powersetCard.mp hA₁).1, (mem_powersetCard.mp hA₁).2]
  rw [probability_eq_mean_fibers hmaps hsize]
  unfold mean
  congr 1
  exact sum_congr rfl (fun _ hA₁ ↦ conditional_first hA₁ E)

/-- Expose the union uniformly, then sample the first half from that union. -/
theorem probability_eq_mean_union (s : Finset α) (k₁ k₂ : ℕ)
    (E : Finset α × Finset α → Prop) :
    probability (orderedPairs s k₁ k₂) E =
      mean (s.powersetCard (k₁ + k₂))
        (fun A ↦ sliceProbability A k₁ (fun A₁ ↦ E (A₁, A \ A₁))) := by
  have hmaps : ∀ q ∈ orderedPairs s k₁ k₂, q.1 ∪ q.2 ∈ s.powersetCard (k₁ + k₂) :=
    fun _ ↦ orderedPairs_union_mem
  have hsize : ∀ A ∈ s.powersetCard (k₁ + k₂),
      ((orderedPairs s k₁ k₂).filter fun q ↦ q.1 ∪ q.2 = A).card = (k₁ + k₂).choose k₁ := by
    intro A hA
    have h := card_unionFiber hA (k₁ := k₁) (k₂ := k₂) (fun _ ↦ True)
    simpa only [filter_true, card_powersetCard, (mem_powersetCard.mp hA).2] using h
  rw [probability_eq_mean_fibers hmaps hsize]
  unfold mean
  congr 1
  exact sum_congr rfl (fun _ hA ↦ conditional_union hA E)

/-- The union itself has the uniform law on the slice of size k₁ + k₂. -/
theorem probability_union (s : Finset α) (k₁ k₂ : ℕ) (E : Finset α → Prop) :
    probability (orderedPairs s k₁ k₂) (fun q ↦ E (q.1 ∪ q.2)) =
      sliceProbability s (k₁ + k₂) E := by
  rw [probability_eq_mean_union]
  let U := s.powersetCard (k₁ + k₂)
  have hs (A : Finset α) (hA : A ∈ U) :
      sliceProbability A k₁ (fun B ↦ E (B ∪ (A \ B))) = if E A then 1 else 0 := by
    have hcard := (mem_powersetCard.mp hA).2
    have hpos : A.card.choose k₁ ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hfilter : ((A.powersetCard k₁).filter fun B ↦ E (B ∪ (A \ B))) =
        ((A.powersetCard k₁).filter fun _ ↦ E A) := by
      apply filter_congr
      intro B hB
      rw [show B ∪ (A \ B) = A from sup_sdiff_cancel_right (mem_powersetCard.mp hB).1]
    unfold sliceProbability
    rw [hfilter]
    by_cases he : E A
    · simp [he, hpos]
    · simp [he]
  change (∑ A ∈ U, sliceProbability A k₁ (fun B ↦ E (B ∪ (A \ B)))) / U.card = _
  rw [sum_congr rfl hs, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, sliceProbability, U]

omit [DecidableEq α] in
theorem mean_le_of_forall_le {S : Finset α} {f : α → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x ∈ S, f x ≤ b) : mean S f ≤ b := by
  by_cases hS : S.Nonempty
  · unfold mean
    rw [div_le_iff₀ (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card), mul_comm]
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum h
  · simp [mean, not_nonempty_iff_eq_empty.mp hS, hb]

omit [DecidableEq α] in
theorem probability_exists_le_sum {β : Type*} (S : Finset α) (T : Finset β) (E : β → α → Prop) :
    probability S (fun x ↦ ∃ y ∈ T, E y x) ≤ ∑ y ∈ T, probability S (E y) := by
  classical
  unfold probability
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [← Nat.cast_sum, Nat.cast_le]
  apply (card_le_card (t := T.biUnion (fun y ↦ S.filter (E y))) ?_).trans card_biUnion_le
  intro x hx
  simp only [mem_filter] at hx
  obtain ⟨hx, y, hy, he⟩ := hx
  exact mem_biUnion.mpr ⟨y, hy, mem_filter.mpr ⟨hx, he⟩⟩

/-- Complementation interchanges the two uniform slices inside the same union. -/
theorem sliceProbability_complement (A : Finset α) (k₁ k₂ : ℕ)
    (hA : A.card = k₁ + k₂) (E : Finset α → Prop) :
    sliceProbability A k₁ (fun B ↦ E (A \ B)) = sliceProbability A k₂ E := by
  have hmem {i j : ℕ} (hij : A.card = i + j) {B : Finset α}
      (hB : B ∈ A.powersetCard i) : A \ B ∈ A.powersetCard j := by
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hB
    refine mem_powersetCard.mpr ⟨sdiff_subset, ?_⟩
    rw [card_sdiff_of_subset hsub, hij, hcard]
    omega
  have hrev : A.card = k₂ + k₁ := hA.trans (Nat.add_comm _ _)
  have hinv {i : ℕ} {B : Finset α} (hB : B ∈ A.powersetCard i) :
      A \ (A \ B) = B := Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp hB).1
  unfold sliceProbability
  congr 1
  · congr 1
    refine card_bij' (fun B _ ↦ A \ B) (fun B _ ↦ A \ B) ?_ ?_ ?_ ?_
    · intro B hB
      obtain ⟨hb, he⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨hmem hA hb, he⟩
    · intro B hB
      obtain ⟨hb, he⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨hmem hrev hb, by rwa [hinv hb]⟩
    · intro B hB
      exact hinv (mem_filter.mp hB).1
    · intro B hB
      exact hinv (mem_filter.mp hB).1
  · congr 1
    exact card_bij' (fun B _ ↦ A \ B) (fun B _ ↦ A \ B)
      (fun _ ↦ hmem hA) (fun _ ↦ hmem hrev) (fun _ ↦ hinv) (fun _ ↦ hinv)

/-- Exact probability that all the points in a fixed subset appear in a uniform slice. -/
theorem sliceProbability_contains (s C : Finset α) (j : ℕ) (hC : C ⊆ s) (hj : C.card ≤ j) :
    sliceProbability s j (fun B ↦ C ⊆ B) =
      ((s.card - C.card).choose (j - C.card) : ℝ) / (s.card.choose j : ℝ) := by
  unfold sliceProbability
  rw [filter_congr_decidable _ (fun B ↦ C ⊆ B) _,
    card_filter_powersetCard_subset C s j hC hj, card_powersetCard]

end

end Green39.Split

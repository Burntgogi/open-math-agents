import OutsideRestriction
import SliceConcentration

/-!
# Regular samples on a uniform slice

The extension uses the directional difference cardinality, which is symmetric
on the fixed-size slice. The regularity estimate counts actual samples
containing a prescribed set of points.
-/

open Finset
open scoped BigOperators Classical Pointwise

namespace Green39.Terminal

open Concentration

noncomputable section

variable {α ι : Type*}

theorem sliceProbability_nonneg (s : Finset α) (k : ℕ) (E : Finset α → Prop) :
    0 ≤ sliceProbability s k E := by
  unfold sliceProbability
  positivity

theorem sliceProbability_mono {s : Finset α} {k : ℕ} {E F : Finset α → Prop}
    (h : ∀ A ∈ s.powersetCard k, E A → F A) :
    sliceProbability s k E ≤ sliceProbability s k F := by
  unfold sliceProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (card_le_card (fun A hA ↦
    mem_filter.mpr ⟨(mem_filter.mp hA).1, h A (mem_filter.mp hA).1 (mem_filter.mp hA).2⟩) :
    ((s.powersetCard k).filter E).card ≤ ((s.powersetCard k).filter F).card)

theorem sliceProbability_exists_le (s : Finset α) (k : ℕ)
    (J : Finset ι) (E : ι → Finset α → Prop) :
    sliceProbability s k (fun A ↦ ∃ j ∈ J, E j A) ≤
      ∑ j ∈ J, sliceProbability s k (E j) := by
  let S := s.powersetCard k
  have heq : (S.filter fun A ↦ ∃ j ∈ J, E j A) = J.biUnion (fun j ↦ S.filter (E j)) := by
    ext A
    simp only [mem_filter, mem_biUnion]
    exact ⟨fun ⟨hA, j, hj, he⟩ ↦ ⟨j, hj, hA, he⟩,
      fun ⟨j, hj, hA, he⟩ ↦ ⟨hA, j, hj, he⟩⟩
  simp only [sliceProbability, ← sum_div, ← Nat.cast_sum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := (card_le_card heq.le).trans card_biUnion_le
  dsimp only [S] at h
  exact Nat.cast_le.mpr (by convert h using 2 <;> first | rfl | ext A; simp only [mem_filter])

theorem sliceProbability_or_le (s : Finset α) (k : ℕ) (E F : Finset α → Prop) :
    sliceProbability s k (fun A ↦ E A ∨ F A) ≤
      sliceProbability s k E + sliceProbability s k F := by
  let S := s.powersetCard k
  have heq : (S.filter fun A ↦ E A ∨ F A) = S.filter E ∪ S.filter F := by
    ext A
    simp only [mem_filter, mem_union, and_or_left]
  simp only [sliceProbability, ← add_div, ← Nat.cast_add]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := (card_le_card heq.le).trans (card_union_le _ _)
  dsimp only [S] at h
  exact Nat.cast_le.mpr (by convert h using 2 <;> first | rfl | ext A; simp only [mem_filter])

theorem sliceProbability_add_compl (s : Finset α) {k : ℕ} (hk : k ≤ s.card)
    (E : Finset α → Prop) :
    sliceProbability s k E + sliceProbability s k (fun A ↦ ¬ E A) = 1 := by
  have hpos : 0 < ((s.powersetCard k).card : ℝ) := by
    exact_mod_cast (powersetCard_nonempty.mpr hk).card_pos
  rw [sliceProbability, sliceProbability, ← add_div, ← Nat.cast_add,
    card_filter_add_card_filter_not, div_self hpos.ne']

section Extension

variable [DecidableEq α]

private theorem card_sdiff_triangle (A B C : Finset α) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  refine (card_le_card (t := (A \ B) ∪ (B \ C)) ?_).trans (card_union_le _ _)
  intro a ha
  obtain ⟨haA, haC⟩ := mem_sdiff.mp ha
  by_cases haB : a ∈ B
  · exact mem_union_right _ (mem_sdiff.mpr ⟨haB, haC⟩)
  · exact mem_union_left _ (mem_sdiff.mpr ⟨haA, haB⟩)

/-- A clipped finite McShane extension. The input function is nonnegative on the domain. -/
def regularExtension (D : Finset (Finset α)) (hD : D.Nonempty)
    (f : Finset α → ℝ) (L K : ℝ) (A : Finset α) : ℝ :=
  min K (D.inf' hD fun B ↦ f B + L * ((A \ B).card : ℝ))

theorem regularExtension_nonneg {D : Finset (Finset α)} (hD : D.Nonempty)
    {f : Finset α → ℝ} {L K : ℝ}
    (hf : ∀ B ∈ D, 0 ≤ f B) (hL : 0 ≤ L) (hK : 0 ≤ K) (A : Finset α) :
    0 ≤ regularExtension D hD f L K A := by
  refine le_min hK (le_inf' _ _ fun B hB ↦ ?_)
  exact add_nonneg (hf B hB) (by positivity)

theorem regularExtension_le {D : Finset (Finset α)} (hD : D.Nonempty)
    (f : Finset α → ℝ) (L K : ℝ) (A : Finset α) :
    regularExtension D hD f L K A ≤ K := min_le_left _ _

theorem regularExtension_eq {D : Finset (Finset α)} (hD : D.Nonempty)
    {f : Finset α → ℝ} {L K : ℝ}
    (hf : ∀ A ∈ D, ∀ B ∈ D, |f A - f B| ≤ L * ((A \ B).card : ℝ))
    {A : Finset α} (hA : A ∈ D) (hK : f A ≤ K) :
    regularExtension D hD f L K A = f A := by
  apply le_antisymm
  · refine (min_le_right _ _).trans ?_
    have h := inf'_le (s := D) (fun B ↦ f B + L * ((A \ B).card : ℝ)) hA
    simpa only [Finset.sdiff_self, card_empty, Nat.cast_zero, mul_zero, add_zero] using h
  · refine le_min hK (le_inf' _ _ fun B hB ↦ ?_)
    linarith [(le_abs_self (f A - f B)).trans (hf A hA B hB)]

private theorem regularExtension_sub_le {D : Finset (Finset α)} (hD : D.Nonempty)
    (f : Finset α → ℝ) {L : ℝ} (hL : 0 ≤ L) (K : ℝ) (A B : Finset α) :
    regularExtension D hD f L K A - regularExtension D hD f L K B ≤
      L * ((A \ B).card : ℝ) := by
  let g (U : Finset α) := D.inf' hD fun C ↦ f C + L * ((U \ C).card : ℝ)
  have hg : g A ≤ g B + L * ((A \ B).card : ℝ) := by
    obtain ⟨C, hC, heq⟩ := exists_mem_eq_inf' hD (fun C ↦ f C + L * ((B \ C).card : ℝ))
    change g B = f C + L * ((B \ C).card : ℝ) at heq
    rw [heq]
    refine (inf'_le (s := D) (fun C ↦ f C + L * ((A \ C).card : ℝ)) hC).trans ?_
    have h : ((A \ C).card : ℝ) ≤ (A \ B).card + (B \ C).card := by
      exact_mod_cast card_sdiff_triangle A B C
    linarith [mul_le_mul_of_nonneg_left h hL]
  change min K (g A) - min K (g B) ≤ _
  by_cases hB : g B ≤ K
  · rw [min_eq_right hB]
    linarith [min_le_right K (g A)]
  · rw [min_eq_left (le_of_not_ge hB)]
    have h : 0 ≤ L * ((A \ B).card : ℝ) := by positivity
    linarith [min_le_left K (g A)]

theorem regularExtension_exchangeLipschitz {D : Finset (Finset α)} (hD : D.Nonempty)
    (f : Finset α → ℝ) {L : ℝ} (hL : 0 ≤ L) (K : ℝ) (s : Finset α) (k : ℕ) :
    ExchangeLipschitz s k (regularExtension D hD f L K) L := by
  intro A hA B hB hAB
  have hsize : A.card = B.card := (mem_powersetCard.mp hA).2.trans (mem_powersetCard.mp hB).2.symm
  have hBA : (B \ A).card ≤ 1 := card_sdiff_comm hsize ▸ hAB
  have bound {U V : Finset α} (h : (U \ V).card ≤ 1) :
      regularExtension D hD f L K U - regularExtension D hD f L K V ≤ L :=
    (regularExtension_sub_le hD f hL K U V).trans
      (mul_le_of_le_one_right hL (by exact_mod_cast h))
  exact abs_sub_le_iff.mpr ⟨bound hAB, bound hBA⟩

end Extension

/-- Clipping bounds the mean shift by the probability of leaving the regular domain. -/
theorem sliceMean_sub_abs_le {s : Finset α} {k : ℕ} {f g : Finset α → ℝ}
    {E : Finset α → Prop} {K : ℝ}
    (hK : ∀ A ∈ s.powersetCard k, |f A - g A| ≤ K)
    (heq : ∀ A ∈ s.powersetCard k, E A → f A = g A) :
    |sliceMean s k f - sliceMean s k g| ≤
      K * sliceProbability s k (fun A ↦ ¬ E A) := by
  rw [sliceMean, sliceMean, mean, mean, ← sub_div, ← sum_sub_distrib, abs_div,
    abs_of_nonneg (show 0 ≤ ((s.powersetCard k).card : ℝ) from Nat.cast_nonneg _), sliceProbability, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ A ∈ s.powersetCard k, if ¬ E A then K else 0 := by
      refine sum_le_sum fun A hA ↦ ?_
      by_cases h : E A
      · simp [h, heq A hA h]
      · simpa [h] using hK A hA
    _ = _ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      congr 3
      ext A
      simp only [mem_filter]

variable {p k : ℕ} [NeZero p]

/-- Probability on the uniform slice of the cyclic group. -/
abbrev probability (p k : ℕ) [NeZero p] (E : Finset (ZMod p) → Prop) : ℝ :=
  sliceProbability univ k E

/-- The regularity union bound, with the exact containment probability of
each possible witness of size «L + 1». -/
def irregularBound (p k m L : ℕ) : ℝ :=
  (p : ℝ) * (m.choose (L + 1) : ℝ) * ((p - (L + 1)).choose (k - (L + 1)) : ℝ) /
    (p.choose k : ℝ)

/-- To fail regularity, some translate must contain «L + 1» specified sample points. -/
theorem probability_irregular_le (P : Finset (ZMod p)) (L : ℕ) :
    probability p k (fun A ↦ ¬ OutsideRegular A P L) ≤ irregularBound p k P.card L := by
  by_cases hk : L + 1 ≤ k
  · let witnesses (v : ZMod p) := (({v} : Finset (ZMod p)) + P).powersetCard (L + 1)
    have hsub : probability p k (fun A ↦ ¬ OutsideRegular A P L) ≤
        probability p k (fun A ↦ ∃ v ∈ (univ : Finset (ZMod p)),
          ∃ B ∈ witnesses v, B ⊆ A) := by
      apply sliceProbability_mono
      intro A _ hA
      obtain ⟨v, hv⟩ : ∃ v : ZMod p, L < (A ∩ ({v} + P)).card := by
        simpa only [OutsideRegular, not_forall, not_le] using hA
      obtain ⟨B, hB, hc⟩ := exists_subset_card_eq (show L + 1 ≤ _ from hv)
      refine ⟨v, mem_univ _, B, mem_powersetCard.mpr ⟨?_, hc⟩, hB.trans inter_subset_left⟩
      exact hB.trans inter_subset_right
    have hcard (v : ZMod p) : (witnesses v).card = P.card.choose (L + 1) := by
      simp [witnesses, card_powersetCard, card_singleton_add]
    have hprob (v : ZMod p) (B : Finset (ZMod p)) (hB : B ∈ witnesses v) :
        probability p k (fun A ↦ B ⊆ A) =
          ((p - (L + 1)).choose (k - (L + 1)) : ℝ) / (p.choose k : ℝ) := by
      have hc := (mem_powersetCard.mp hB).2
      unfold probability sliceProbability
      have hc' := card_filter_powersetCard_subset B univ k (subset_univ B) (by omega)
      have hnum : (((univ : Finset (ZMod p)).powersetCard k).filter
          (fun A ↦ B ⊆ A)).card = (p - (L + 1)).choose (k - (L + 1)) := by
        simpa only [hc, card_univ, ZMod.card] using hc'
      rw [card_powersetCard, card_univ, ZMod.card]
      congr 2
      convert hnum using 2
      ext A
      simp only [mem_filter]
    refine hsub.trans ((sliceProbability_exists_le _ _ _ _).trans ?_)
    calc
      _ ≤ ∑ v ∈ (univ : Finset (ZMod p)), ∑ B ∈ witnesses v,
          probability p k (fun A ↦ B ⊆ A) :=
        sum_le_sum fun v _ ↦ sliceProbability_exists_le _ _ _ _
      _ = _ := by
        simp only [sum_congr rfl (hprob _), sum_const, hcard, card_univ, ZMod.card,
          nsmul_eq_mul, irregularBound]
        ring
  · have hzero : probability p k (fun A ↦ ¬ OutsideRegular A P L) =
        probability p k (fun _ ↦ False) := by
      apply le_antisymm
      · apply sliceProbability_mono
        intro A hA hv
        exact hv (fun v ↦ (card_le_card inter_subset_left).trans
          (by rw [(mem_powersetCard.mp hA).2]; omega))
      · exact sliceProbability_mono (fun _ _ h ↦ h.elim)
    rw [hzero]
    simp only [probability, sliceProbability, filter_false, card_empty, Nat.cast_zero, zero_div]
    unfold irregularBound
    positivity

end

end Green39.Terminal


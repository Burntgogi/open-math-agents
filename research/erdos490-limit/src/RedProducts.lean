import BlueProducts
import CountedWords

/-! The analytic head-and-tail word count is the exact count of dilated red
products up to the same cutoff. Distinct old supports give disjoint products. -/
namespace Erdos490Transfer
open Finset Erdos490PrimeCells
noncomputable section
open Classical

private def supportEquiv {S : Finset ℕ} {p n : ℕ} (hp : p ∈ S)
    (tail : Fin n ≃ ↥(S.erase p)) : Option (Fin n) ≃ S := by
  let rest : ↥(S.erase p) ≃ {q : S // q ≠ (⟨p, hp⟩ : S)} :=
    { toFun := fun q => ⟨⟨q.val, mem_of_mem_erase q.property⟩,
        fun h => (mem_erase.mp q.property).1 (congrArg Subtype.val h)⟩
      invFun := fun q => ⟨q.val.val, mem_erase.mpr
        ⟨fun h => q.property (Subtype.ext h), q.val.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Equiv.optionCongr (tail.trans rest)).trans (Equiv.optionSubtypeNe (⟨p, hp⟩ : S))

/-- Fix any head in the prime support and enumerate the remaining primes in
any order. The word count equals the number of distinct capped products. -/
theorem countedWords_eq_newProducts_card {b t : ℝ} (ht : 0 < t)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p n : ℕ} (hp : p ∈ S)
    (tail : Fin n ≃ ↥(S.erase p)) (cap : ℕ) :
    (countedWords (cellLabel b p (hS p hp))
      (fun j => cellLabel b (tail j).val (hS _ (mem_of_mem_erase (tail j).property)))
      t cap).card = ((newProducts b t S).filter (· ≤ cap)).card := by
  let i := cellLabel b p (hS p hp)
  let L (j : Fin n) := cellLabel b (tail j).val (hS _ (mem_of_mem_erase (tail j).property))
  let e := supportEquiv hp tail
  let F := (Fintype.piFinset (fun q : S => newCell b t q.val)).filter (fun f => high f ≤ cap)
  have valid {f : S → ℕ} (hf : f ∈ F) : ∀ q : S, f q ∈ newCell b t q.val :=
    Fintype.mem_piFinset.mp (mem_filter.mp hf).1
  have prod_eq (f : S → ℕ) : high f = (∏ j : Fin n, f (e (some j))) * f (e none) := by
    rw [high, ← Fintype.prod_equiv e (fun j => f (e j)) f (fun _ => rfl)]
    rw [Fintype.prod_option, mul_comm]
  have himage : F.image high = (newProducts b t S).filter (· ≤ cap) := by
    ext z
    simp only [F, newProducts, mem_image, mem_filter]
    aesop
  have hinj : Set.InjOn high (F : Set (S → ℕ)) := by
    intro f hf g hg h
    exact high_injective (cell := fun q : S => newCell b t q.val)
      (fun _ _ hq => (mem_filter.mp hq).2)
      (fun q r hqr => newCell_disjoint ht.le (fun eq => hqr (Subtype.ext eq)))
      (fun q => Or.inr (valid hf q)) (fun q => Or.inr (valid hg q)) h
  rw [← himage, card_image_of_injOn hinj]
  change (countedWords i L t cap).card = F.card
  symm
  let word (f : S → ℕ) (hf : f ∈ F) : Σ _ : PrimeChoices t L, ℕ :=
    ⟨fun j => ⟨f (e (some j)), valid hf (e (some j))⟩, f (e none)⟩
  apply card_bij word
  · intro f hf
    refine mem_sigma.mpr ⟨mem_univ _, mem_filter.mpr ⟨valid hf (e none), ?_⟩⟩
    exact (prod_eq f).symm ▸ (mem_filter.mp hf).2
  · intro f hf g hg h
    funext q
    obtain ⟨j, rfl⟩ := e.surjective q
    cases j with
    | none => exact congrArg (fun w => w.2) h
    | some j => exact congrArg (fun w => (w.1 j).val) h
  · rintro ⟨v, q⟩ hw
    obtain ⟨hq, hcap⟩ := mem_filter.mp (mem_sigma.mp hw).2
    let f (r : S) := (e.symm r).elim q (fun j => (v j).val)
    have head : f (e none) = q := by simp [f]
    have rest (j : Fin n) : f (e (some j)) = (v j).val := by simp [f]
    have hf : f ∈ F := by
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
      · intro r
        obtain ⟨j, rfl⟩ := e.surjective r
        cases j with
        | none => exact head.symm ▸ hq
        | some j => exact (rest j).symm ▸ (v j).property
      · simpa only [prod_eq f, rest, head, choiceProduct] using hcap
    refine ⟨f, hf, ?_⟩
    have hv : (word f hf).1 = v := funext (fun j => Subtype.ext (rest j))
    exact Sigma.ext hv (heq_of_eq head)

/-- The same identity at the analytic exponential cutoff. -/
theorem finalCount_eq_newProducts_card {b t : ℝ} (ht : 0 < t)
    {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) {p n : ℕ} (hp : p ∈ S)
    (tail : Fin n ≃ ↥(S.erase p)) (x c : ℝ) :
    finalCount (cellLabel b p (hS p hp))
      (fun j => cellLabel b (tail j).val (hS _ (mem_of_mem_erase (tail j).property)))
      t x c = (((newProducts b t S).filter (· ≤ ⌊Real.exp (t * x - c)⌋₊)).card : ℝ) := by
  rw [finalCount_eq_card, countedWords_eq_newProducts_card ht hS hp tail]

/-- Capped products from a family of distinct supports fit in the capped
semigroup on the union of all available cells. -/
theorem sum_newProducts_card_le_semigroup_card {b t : ℝ} (ht : 0 < t)
    (C : Finset ℕ) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C) (cap : ℕ) :
    (∑ S ∈ G, ((newProducts b t S).filter (· ≤ cap)).card) ≤
      (semigroup (bands b t C) cap).card := by
  let P (S : Finset ℕ) := (newProducts b t S).filter (· ≤ cap)
  have apart : (G : Set (Finset ℕ)).PairwiseDisjoint P :=
    fun _ _ _ _ h => (products_apart ht.le h).mono (filter_subset _ _) (filter_subset _ _)
  change (∑ S ∈ G, (P S).card) ≤ _
  rw [← card_biUnion apart]
  apply card_le_card
  intro z hz
  obtain ⟨S, hS, hz⟩ := mem_biUnion.mp hz
  obtain ⟨hz, hcap⟩ := mem_filter.mp hz
  exact mem_semigroup.mpr ⟨newProduct_active (hG S hS) hz, hcap⟩

/-- Each support may use its own head and its own indexing of the tail. -/
theorem sum_countedWords_le_semigroup_card {b t : ℝ} (ht : 0 < t)
    (C : Finset ℕ) (G : Finset (Finset ℕ)) (hG : ∀ S ∈ G, S ⊆ C)
    (hC : ∀ q ∈ C, q.Prime) (head n : G → ℕ) (hp : ∀ S : G, head S ∈ S.val)
    (tail : ∀ S : G, Fin (n S) ≃ ↥(S.val.erase (head S))) (cap : ℕ) :
    (∑ S : G, (countedWords (cellLabel b (head S) (hC _ (hG _ S.property (hp S))))
      (fun j => cellLabel b (tail S j).val
        (hC _ (hG _ S.property (mem_of_mem_erase (tail S j).property)))) t cap).card) ≤
      (semigroup (bands b t C) cap).card := by
  calc
    _ = ∑ S : G, ((newProducts b t S.val).filter (· ≤ cap)).card := by
      apply sum_congr rfl
      intro S _
      exact countedWords_eq_newProducts_card ht (fun q hq => hC q (hG _ S.property hq))
        (hp S) (tail S) cap
    _ ≤ _ := by
      rw [← attach_eq_univ, sum_attach G
        (fun S : Finset ℕ => ((newProducts b t S).filter (· ≤ cap)).card)]
      exact sum_newProducts_card_le_semigroup_card ht C G hG cap

#print axioms countedWords_eq_newProducts_card
#print axioms finalCount_eq_newProducts_card
#print axioms sum_newProducts_card_le_semigroup_card
#print axioms sum_countedWords_le_semigroup_card

end
end Erdos490Transfer

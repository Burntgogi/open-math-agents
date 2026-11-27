import ProductLaw

noncomputable section
namespace Shift490
open Finset MeasureTheory Filter

/-- A finite product is partitioned by choosing m successful coordinates and recording
the values of every other coordinate. The choice is a function only of the success set. -/
def select {ι : Type*} (m : ℕ) (s : Finset ι) : Finset ι :=
  if h : m ≤ s.card then (exists_subset_card_eq h).choose else ∅

lemma select_sub {ι : Type*} (m : ℕ) (s : Finset ι) : select m s ⊆ s := by
  unfold select; split <;> rename_i h
  · exact (exists_subset_card_eq h).choose_spec.1
  · exact empty_subset _

lemma select_size {ι : Type*} {m : ℕ} {s : Finset ι} (h : m ≤ s.card) :
    (select m s).card = m := by simp only [select,dif_pos h]; exact (exists_subset_card_eq h).choose_spec.2

section Rectangles
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, DecidableEq (V i)]
    (G : ∀ i, Finset (V i)) (m : ℕ)

def successes (x : ∀ i, V i) := univ.filter (fun i => x i ∈ G i)
def allowed (x : ∀ i, V i) (i : ι) : Finset (V i) :=
  if i ∈ select m (successes G x) then G i else {x i}
def component (x : ∀ i, V i) := Fintype.piFinset (allowed G m x)

lemma self_mem_component (x : ∀ i, V i) : x ∈ component G m x := by
  apply Fintype.mem_piFinset.mpr
  intro i
  dsimp [allowed]
  split_ifs with h
  · exact (mem_filter.mp (select_sub m _ h)).2
  · simp

lemma component_successes {x y : ∀ i, V i} (h : y ∈ component G m x) :
    successes G y = successes G x := by
  ext i
  have hi := Fintype.mem_piFinset.mp h i
  by_cases hs : i ∈ select m (successes G x)
  · have hg := (mem_filter.mp (select_sub m _ hs)).2
    simp only [allowed,if_pos hs] at hi
    simp [successes,hi,hg]
  · simp only [allowed,if_neg hs,mem_singleton] at hi
    simp [successes,hi]

lemma component_eq {x y : ∀ i, V i} (h : y ∈ component G m x) :
    component G m y = component G m x := by
  have he := component_successes G m h
  apply congrArg Fintype.piFinset
  funext i
  have hi := Fintype.mem_piFinset.mp h i
  dsimp [allowed]
  rw [he]
  split_ifs with hs
  · rfl
  · simp only [allowed,if_neg hs,mem_singleton] at hi
    rw [hi]

end Rectangles

/-- Reassemble conditional bounds over countably many finite rectangles by countable
additivity. The bound can include a separate error on the exceptional rectangles. -/
theorem integrate_components {Ω : Type*} [Countable Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) (C : Ω → Finset Ω)
    (self : ∀ x, x ∈ C x) (same : ∀ x y, y ∈ C x → C y = C x)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (localBound : ∀ x, ∑ y ∈ C x, μ.real {y} * f y ≤ ∑ y ∈ C x, μ.real {y} * g y) :
    ∫ y, f y ∂μ ≤ ∫ y, g y ∂μ := by
  classical
  let S (k : Set.range C) : Set Ω := ↑k.val
  have hmeas (k) : MeasurableSet (S k) := (Set.to_countable _).measurableSet
  have disj : Pairwise (Function.onFun Disjoint S) := by
    intro k l h
    apply Set.disjoint_left.mpr
    intro y hk hl
    obtain ⟨x,hx⟩ := k.property
    obtain ⟨z,hz⟩ := l.property
    apply h
    apply Subtype.ext
    exact hx ▸ hz ▸ ((same x y (hx.symm ▸ hk)).symm.trans (same z y (hz.symm ▸ hl)))
  have hu : ⋃ k, S k = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.mpr ⟨⟨C x,⟨x,rfl⟩⟩,self x⟩
  have part {v : Ω → ℝ} (hv : Integrable v μ) :
      HasSum (fun k => ∫ y in S k, v y ∂μ) (∫ y, v y ∂μ) := by
    simpa only [hu,Measure.restrict_univ] using hasSum_integral_iUnion hmeas disj
      (hv.integrableOn (s := ⋃ k, S k))
  apply hasSum_le _ (part hf) (part hg)
  rintro ⟨k,x,rfl⟩
  simpa only [S,setIntegral_finset _ hf.integrableOn,setIntegral_finset _ hg.integrableOn,smul_eq_mul]
    using localBound x

#print axioms integrate_components
end Shift490

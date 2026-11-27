import Mathlib

open Finset
namespace Erdos490Smooth

def tupleRange {S : Finset ℕ} {j : ℕ} (f : Fin j → S) : Finset ℕ :=
  univ.image fun i => (f i : ℕ)

theorem tupleRange_card {j : ℕ} {S : Finset ℕ} {f : Fin j → S}
    (hf : StrictMono fun i => (f i : ℕ)) : (tupleRange f).card = j := by
  rw [tupleRange, card_image_of_injective _ hf.injective,card_univ,Fintype.card_fin]

theorem tupleRange_prod {M : Type*} [CommMonoid M] {j : ℕ} {S : Finset ℕ}
    {f : Fin j → S} (hf : StrictMono fun i => (f i : ℕ)) (w : ℕ → M) :
    ∏ p ∈ tupleRange f, w p = ∏ i, w (f i : ℕ) :=
  Finset.prod_image hf.injective.injOn

/-- Each allowed finite set has exactly one increasing enumeration. -/
theorem tuple_subset_sum {M : Type*} [CommMonoid M] [AddCommMonoid M]
    (S : Finset ℕ) (j : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] (w : ℕ → M) :
    ∑ f : Fin j → S with (StrictMono fun i => (f i : ℕ)) ∧ P (tupleRange f),
      ∏ i, w (f i : ℕ) =
      ∑ V ∈ (S.powersetCard j).filter P, ∏ p ∈ V, w p := by
  classical
  apply Finset.sum_bij (fun f _ => tupleRange f)
  · intro f hf
    have h := (Finset.mem_filter.mp hf).2
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨by
      intro p hp
      obtain ⟨i,_,rfl⟩ := mem_image.mp hp
      exact (f i).property,tupleRange_card h.1⟩,h.2⟩
  · intro f hf g hg he
    have hf' := (mem_filter.mp hf).2.1
    have hg' := (mem_filter.mp hg).2.1
    have hfc := tupleRange_card hf'
    have hfm (i : Fin j) : (f i : ℕ) ∈ tupleRange f := mem_image_of_mem _ (mem_univ i)
    have hgm (i : Fin j) : (g i : ℕ) ∈ tupleRange f := he ▸ mem_image_of_mem _ (mem_univ i)
    have h := (orderEmbOfFin_unique hfc hfm hf').trans (orderEmbOfFin_unique hfc hgm hg').symm
    exact funext fun i => Subtype.ext (congrFun h i)
  · intro V hV
    obtain ⟨hV,hP⟩ := mem_filter.mp hV
    obtain ⟨hVS,hc⟩ := mem_powersetCard.mp hV
    let f (i : Fin j) : S := ⟨V.orderEmbOfFin hc i,hVS (V.orderEmbOfFin_mem hc i)⟩
    have he : tupleRange f = V := image_orderEmbOfFin_univ V hc
    exact ⟨f,mem_filter.mpr ⟨mem_univ _,(V.orderEmbOfFin hc).strictMono,he ▸ hP⟩,he⟩
  · intro f hf
    exact (tupleRange_prod (mem_filter.mp hf).2.1 w).symm

end Erdos490Smooth

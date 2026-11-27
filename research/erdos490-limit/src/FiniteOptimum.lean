import H2

/-! The exact fixed-color extremum, and its two weighted density factors. -/
namespace Erdos490Transfer
open Finset
noncomputable section

/-- The optimal fibers at the new cutoff also satisfy the site's separation
and cofactor conditions with the original Y,K. -/
theorem sep_of_covers {Y K n A B} (c : Colors Y n)
    (ha : Covers Y K n c.red A) (hb : Covers Y K n c.blue B) : Sep Y K A B := by
  have rough {p h u z : ℕ} {C : Finset ℕ} (hp : p.Prime) (hy : Y ≤ p)
      (hz : p ∣ z) (hh : h ∈ semigroup C n) (hu : u ∈ vertices Y K)
      (he : h*u=z) : p ∈ C := by
    rw [← he] at hz
    rcases hp.dvd_mul.mp hz with hd|hd
    · exact Nat.mem_factoredNumbers'.mp (mem_semigroup.mp hh).1 p hp hd
    · exact ((Nat.mem_primesBelow.mp (Nat.mem_factoredNumbers'.mp
        (mem_semigroup.mp hu).1 p hp hd)).1.not_ge hy).elim
  have cof {C Z : Finset ℕ} (hC : C ⊆ c.red ∪ c.blue) (hZ : Covers Y K n C Z)
      {z} (hz : z ∈ Z) : ∃ u ≤ K, u ∣ z ∧ ∀ p : ℕ, p.Prime → p ∣ z/u → Y ≤ p := by
    obtain ⟨h,hh,u,hu,rfl⟩ := hZ z hz
    refine ⟨u,(mem_semigroup.mp hu).2,dvd_mul_left ..,?_⟩
    rw [Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (mem_semigroup.mp hu).1.1)]
    exact fun p hp hd => c.large p (hC (Nat.mem_factoredNumbers'.mp (mem_semigroup.mp hh).1 p hp hd))
  constructor
  · intro a ham b hbm p hp hy hpa hpb
    obtain ⟨h,hh,u,hu,he⟩ := ha a ham
    obtain ⟨j,hj,v,hv,hf⟩ := hb b hbm
    exact disjoint_left.mp c.separate (rough hp hy hpa hh hu he) (rough hp hy hpb hj hv hf)
  · intro z hz
    exact (mem_union.mp hz).elim (cof subset_union_left ha) (cof subset_union_right hb)

def candidateGraphs (Y K : ℕ) := (ratios (vertices Y K)).powerset
def graphProduct {Y n} (K : ℕ) (c : Colors Y n) (G : Finset ℚ) : ℕ :=
  let U := vertices Y K
  size U G c.red K n * size U (ratios U \ G) c.blue K n

/-- At a fixed coloring the two finite optimization problems have the same
attained maximum, even for an empty vertex set or an empty prime color. -/
theorem fixed_color_optimum {Y n} (K : ℕ) (c : Colors Y n) :
    ∃ G ∈ candidateGraphs Y K, ∃ A B : Finset ℕ,
      Adm n A B ∧ Sep Y K A B ∧ Covers Y K n c.red A ∧ Covers Y K n c.blue B ∧
      A.card*B.card = graphProduct K c G ∧
      (∀ H ∈ candidateGraphs Y K, graphProduct K c H ≤ graphProduct K c G) ∧
      ∀ S T : Finset ℕ, Adm n S T → Covers Y K n c.red S → Covers Y K n c.blue T →
        S.card*T.card ≤ A.card*B.card := by
  obtain ⟨G,hG,hmax⟩ := (candidateGraphs Y K).exists_max_image (graphProduct K c)
    ⟨∅,mem_powerset.mpr (empty_subset _)⟩
  obtain ⟨had,hL,hR,hA,hB⟩ := attainable (K:=K) c G
  refine ⟨G,hG,_,_,had,sep_of_covers c hL hR,hL,hR,?_,hmax,?_⟩
  · rw [hA,hB]; rfl
  · intro S T hst cs ct
    obtain ⟨H,hH,hs,ht⟩ := dominate hst c cs ct
    rw [hA,hB]
    exact (Nat.mul_le_mul hs ht).trans (hmax H (mem_powerset.mpr hH))

theorem weight_zero_off_vertex (U G i) (h : i+1 ∉ U) : weight U G i = 0 := by
  apply Nat.sub_eq_zero_of_le
  apply le_rank
  obtain ⟨hp,hr⟩ := mem_choices.mp (best_mem U G (i+1))
  refine mem_choices.mpr ⟨?_,hr⟩
  intro u hu
  obtain ⟨hm,hl⟩ := hp u hu
  have ne : u ≠ i+1 := fun he => h (he ▸ hm)
  exact ⟨hm,by omega⟩

/-- Weighted one-color factor of the normalized objective. -/
def weightedDensity (U : Finset ℕ) (G : Finset ℚ) (C : Finset ℕ) (K n : ℕ) : ℝ :=
  ∑ i ∈ range K, (weight U G i:ℝ)*density C n (i+1)/(i+1:ℕ)

theorem weightedDensity_eq (U G C K n) :
    weightedDensity U G C K n = (size U G C K n:ℝ)/n := by
  unfold weightedDensity size density
  push_cast
  rw [sum_div]
  apply sum_congr rfl
  intro i _
  have hi : (i:ℝ)+1 ≠ 0 := by positivity
  field_simp [hi]


theorem model_factors {Y n} (c : Colors Y n) (U G H K) :
    model c U G H K = Real.log n * weightedDensity U G c.red K n *
      weightedDensity U H c.blue K n := by
  rw [weightedDensity_eq,weightedDensity_eq]
  unfold model value
  ring

#print axioms fixed_color_optimum
end
end Erdos490Transfer
